/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Emptiness of nondeterministic Büchi automata
-/
module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Foundations.Data.OmegaSequence.Temporal
public import MathlibExt.Logic.Relation.FiniteReachability

/-!
# Emptiness of nondeterministic Büchi automata

For upstream CSLib's nondeterministic Büchi automata (`Cslib.Automata.NA.Buchi`, built on the
upstream `Cslib.LTS`), this file proves the lasso characterization of nonemptiness and turns it
into a decision procedure.

* `Cslib.Automata.NA.Buchi.HasLasso`: some accepting state is reachable from a start state and
  lies on a nonempty cycle.
* `Cslib.Automata.NA.Buchi.lasso_mem_language`: a lasso `s₀ -u-> s -v-> s` yields the accepted
  ultimately periodic word `u v^ω` (`u ++ω (const v).flatten`).
* `Cslib.Automata.NA.Buchi.language_nonempty_iff_hasLasso`: for finitely many states, the
  language is nonempty iff the automaton has a lasso; `exists_lasso_word_of_nonempty`: a
  nonempty language contains an ultimately periodic word.
* `Cslib.Automata.NA.Buchi.hasLasso_iff_reachable`: the lasso condition only depends on the
  symbol-forgetting transition graph `Step` (reachability plus a cycle).
* `Cslib.Automata.NA.Buchi.lassoStates`, `instDecidableHasLasso`, `isEmptyB`, `isEmptyB_iff`: for
  finite state and symbol types with decidable transitions, start and accepting sets, emptiness is
  decidable: one reachability closure from all start states (`Relation.transGenFinFrom`), then a
  cycle closure (`Relation.transGenFin`) for each reachable accepting state.

Closure of Büchi languages under union and intersection is upstream
(`Cslib.Automata.NA.Buchi.iSum_language_eq`, `Cslib.Automata.NA.Buchi.inter_language_eq`,
`Cslib.ωLanguage.IsRegular.sup`/`inf`), as is complementation (`Cslib.ωLanguage.IsRegular.compl`).

## References

* W. Thomas, "Automata on infinite objects", in *Handbook of Theoretical Computer Science*,
  Vol. B, Elsevier, 1990.
-/

@[expose] public section

namespace Cslib.Automata.NA.Buchi

open Filter ωSequence ωAcceptor
open _root_.Relation

variable {State Symbol : Type*}

/-- **Symbol-forgetting transition graph of a Büchi automaton.** For a nondeterministic Büchi
automaton, the transition graph has an edge from a state $s$ to a state $t$ exactly when the
automaton has a transition from $s$ to $t$ reading some symbol. -/
def Step (na : Buchi State Symbol) (s t : State) : Prop :=
  ∃ x, na.Tr s x t

/-- **Lasso of a Büchi automaton.** A nondeterministic Büchi automaton has a lasso if there are a
start state $s_0$ and an accepting state $s$ such that the automaton can move from $s_0$ to $s$ by
reading some finite word $u$, and from $s$ back to $s$ by reading some nonempty finite word
$v$. -/
def HasLasso (na : Buchi State Symbol) : Prop :=
  ∃ s₀ ∈ na.start, ∃ s ∈ na.accept, (∃ u, na.MTr s₀ u s) ∧ ∃ v, v ≠ [] ∧ na.MTr s v s

variable {na : Buchi State Symbol}

/-- **Büchi acceptance condition.** A nondeterministic Büchi automaton accepts an infinite word
$x = x_0 x_1 x_2 \cdots$ if and only if it has a run on $x$, that is, a sequence of states
$s_0 s_1 s_2 \cdots$ with $s_0$ a start state and a transition from $s_k$ to $s_{k+1}$ reading
$x_k$ for every $k$, such that $s_k$ is an accepting state for infinitely many $k$. -/
theorem mem_language_iff {xs : ωSequence Symbol} :
    xs ∈ language na ↔ ∃ ss, na.Run xs ss ∧ ∃ᶠ k in atTop, ss k ∈ na.accept :=
  Iff.rfl

/-- **Lassos give accepted ultimately periodic words.** Let $\mathcal{A}$ be a nondeterministic
Büchi automaton over a nonempty alphabet. Suppose $s_0$ is a start state and $s$ an accepting
state of $\mathcal{A}$, that reading the finite word $u$ the automaton can move from $s_0$ to $s$,
and that reading a nonempty finite word $v$ it can move from $s$ back to $s$. Then $\mathcal{A}$
accepts the infinite word $u v^\omega = u v v v \cdots$. -/
theorem lasso_mem_language [Inhabited Symbol] {s₀ s : State} {u v : List Symbol}
    (h₀ : s₀ ∈ na.start) (hs : s ∈ na.accept) (hu : na.MTr s₀ u s) (hv : v ≠ [])
    (hvs : na.MTr s v s) : u ++ω (const v).flatten ∈ language na := by
  have hpos : ∀ k, 0 < ((const v : ωSequence (List Symbol)) k).length := fun _ => by
    simpa [get_const] using List.length_pos_of_ne_nil hv
  obtain ⟨ss, hss, hcum⟩ := LTS.OmegaExecution.flatten_mTr (lts := na.toLTS)
    (ts := const s) (μls := const v) (fun _ => by simpa [get_const] using hvs) hpos
  obtain ⟨ss', hss', h0, -, hdrop⟩ :=
    LTS.OmegaExecution.append hu hss (by simpa [get_const] using hcum 0)
  refine ⟨ss', ⟨by simpa [h0] using h₀, hss'⟩, ?_⟩
  have hfreq : ∃ᶠ k in atTop, ss k ∈ na.accept := by
    rw [frequently_iff_strictMono]
    exact ⟨(const v).cumLen, cumLen_strictMono hpos, fun m => by
      simpa [hcum m, get_const] using hs⟩
  rw [← drop_frequently_iff_frequently u.length, hdrop]
  exact hfreq

/-- **An accepted word yields a lasso.** If a nondeterministic Büchi automaton with finitely many
states accepts some infinite word, then it has a lasso: some accepting state is visited twice
along an accepting run, and the run between the two visits is the cycle. -/
theorem hasLasso_of_mem [Finite State] {xs : ωSequence Symbol} (h : xs ∈ language na) :
    na.HasLasso := by
  obtain ⟨ss, hrun, hacc⟩ := h
  obtain ⟨s, hs, hfreq⟩ := frequently_in_finite_type.mp hacc
  obtain ⟨i, -, hi⟩ := frequently_atTop.mp hfreq 0
  obtain ⟨j, hj, hj'⟩ := frequently_atTop.mp hfreq (i + 1)
  refine ⟨ss 0, hrun.start, s, hs, ⟨xs.extract 0 i, ?_⟩, xs.extract i j, ?_, ?_⟩
  · simpa [hi] using hrun.trans.extract_mTr (Nat.zero_le i)
  · intro hnil
    have := congrArg List.length hnil
    simp only [length_extract, List.length_nil] at this
    omega
  · simpa [hi, hj'] using hrun.trans.extract_mTr (show i ≤ j by omega)

/-- **Lasso characterization of Büchi nonemptiness.** For finitely many states, the language
of a nondeterministic Büchi automaton is nonempty iff some accepting state is reachable from a
start state and lies on a nonempty cycle. -/
theorem language_nonempty_iff_hasLasso [Finite State] :
    (∃ xs, xs ∈ language na) ↔ na.HasLasso := by
  constructor
  · rintro ⟨xs, h⟩
    exact hasLasso_of_mem h
  · rintro ⟨s₀, h₀, s, hs, ⟨u, hu⟩, v, hv, hvs⟩
    have : Inhabited Symbol := ⟨v.head hv⟩
    exact ⟨_, lasso_mem_language h₀ hs hu hv hvs⟩

/-- **Nonempty Büchi languages contain ultimately periodic words.** Let $A$ be a
nondeterministic Büchi automaton with finitely many states over a nonempty alphabet. If $A$
accepts some infinite word, then there are finite words $u$ and $v$ with $v$ nonempty such that
$A$ accepts the ultimately periodic word $u v^\omega = u v v v \cdots$. -/
theorem exists_lasso_word_of_nonempty [Finite State] [Inhabited Symbol]
    (h : ∃ xs, xs ∈ language na) :
    ∃ u v : List Symbol, v ≠ [] ∧ u ++ω (const v).flatten ∈ language na := by
  obtain ⟨s₀, h₀, s, hs, ⟨u, hu⟩, v, hv, hvs⟩ := language_nonempty_iff_hasLasso.mp h
  exact ⟨u, v, hv, lasso_mem_language h₀ hs hu hv hvs⟩

/-! ## Reduction to graph reachability -/

/-- **Reachability by words is reachability in the transition graph.** For states $s$ and $t$ of
a nondeterministic Büchi automaton, the automaton can move from $s$ to $t$ by reading some finite
word (possibly empty) if and only if $t$ is reachable from $s$ in zero or more steps of the
transition graph, which has an edge from $p$ to $q$ when some symbol takes $p$ to $q$. -/
theorem exists_mTr_iff_reflTransGen {s t : State} :
    (∃ u, na.MTr s u t) ↔ ReflTransGen na.Step s t := by
  constructor
  · rintro ⟨u, hu⟩
    induction hu with
    | refl => exact ReflTransGen.refl
    | stepL htr _ ih => exact ReflTransGen.head ⟨_, htr⟩ ih
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨[], LTS.MTr.refl⟩
    | head hst _ ih =>
        obtain ⟨x, hx⟩ := hst
        obtain ⟨u, hu⟩ := ih
        exact ⟨x :: u, LTS.MTr.stepL hx hu⟩

/-- **Nonempty words and paths of positive length.** For states $s$ and $t$ of a
nondeterministic Büchi automaton, the automaton can move from $s$ to $t$ by reading some nonempty
finite word if and only if $t$ is reachable from $s$ in one or more steps of the transition
graph, which has an edge from $p$ to $q$ when some symbol takes $p$ to $q$. -/
theorem exists_ne_nil_mTr_iff_transGen {s t : State} :
    (∃ v, v ≠ [] ∧ na.MTr s v t) ↔ TransGen na.Step s t := by
  constructor
  · rintro ⟨v, hv, hvt⟩
    cases hvt with
    | refl => exact absurd rfl hv
    | stepL htr hrest =>
        exact TransGen.head' ⟨_, htr⟩ (exists_mTr_iff_reflTransGen.mp ⟨_, hrest⟩)
  · intro h
    obtain ⟨u, ⟨x, hx⟩, hu⟩ := TransGen.head'_iff.mp h
    obtain ⟨w, hw⟩ := exists_mTr_iff_reflTransGen.mpr hu
    exact ⟨x :: w, List.cons_ne_nil _ _, LTS.MTr.stepL hx hw⟩

/-- **The lasso condition in the transition graph.** A nondeterministic Büchi automaton has a
lasso if and only if there are a start state $s_0$ and an accepting state $s$ such that $s$ is
reachable from $s_0$ in zero or more steps of the transition graph and $s$ is reachable from
itself in one or more steps; the transition graph has an edge from $p$ to $q$ when some symbol
takes $p$ to $q$. -/
theorem hasLasso_iff_reachable :
    na.HasLasso ↔ ∃ s₀ ∈ na.start, ∃ s ∈ na.accept,
      ReflTransGen na.Step s₀ s ∧ TransGen na.Step s s := by
  simp only [HasLasso, exists_mTr_iff_reflTransGen, exists_ne_nil_mTr_iff_transGen]

/-! ## Decision procedure -/

section Decidable

variable [Fintype State] [DecidableEq State] [Fintype Symbol] [∀ s x t, Decidable (na.Tr s x t)]
  [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)]

instance : DecidableRel na.Step := fun s t =>
  inferInstanceAs (Decidable (∃ x, na.Tr s x t))

/-- **Finite set of start states.** For a nondeterministic Büchi automaton with finitely many
states and a decidable start set, this is the set of its start states, viewed as a finite set. -/
def startFin (na : Buchi State Symbol) [DecidablePred (· ∈ na.start)] : Finset State :=
  Finset.univ.filter (· ∈ na.start)

/-- **Lasso states of a finite Büchi automaton.** For a nondeterministic Büchi automaton with
finitely many states, decidable equality of states, a finite alphabet, and decidable transitions,
start set and accepting set, the lasso states form the finite set of accepting states $s$ that are
reachable from some start state in zero or more transitions and lie on a nonempty cycle, that is,
$s$ is reachable from itself in one or more transitions.

The set is computed by one reachability closure from all start states, then one cycle closure for
each reachable accepting state; each closure takes as many rounds as there are states. -/
def lassoStates (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)] : Finset State :=
  (na.startFin ∪ Relation.transGenFinFrom na.Step na.startFin).filter fun s =>
    s ∈ na.accept ∧ s ∈ Relation.transGenFin na.Step s

theorem mem_lassoStates {s : State} :
    s ∈ na.lassoStates ↔
      (∃ s₀ ∈ na.start, ReflTransGen na.Step s₀ s) ∧ s ∈ na.accept ∧ TransGen na.Step s s := by
  simp only [lassoStates, startFin, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
    true_and, Relation.mem_transGenFinFrom, Relation.mem_transGenFin]
  refine and_congr_left fun _ => ?_
  constructor
  · rintro (h | ⟨s₀, h₀, h⟩)
    · exact ⟨s, h, ReflTransGen.refl⟩
    · exact ⟨s₀, h₀, h.to_reflTransGen⟩
  · rintro ⟨s₀, h₀, h⟩
    rcases reflTransGen_iff_eq_or_transGen.mp h with rfl | h
    · exact Or.inl h₀
    · exact Or.inr ⟨s₀, h₀, h⟩

/-- **Lasso detection by finite reachability.** Let $A$ be a nondeterministic Büchi automaton
with finitely many states and finitely many symbols, with decidable equality of states, and whose
transitions, start states and accepting states are decidable. Then $A$ has a lasso if and only if
its set of lasso states, computed by finite reachability closures as the accepting states that are
reachable from a start state and lie on a nonempty cycle, is nonempty. -/
theorem hasLasso_iff_lassoStates_nonempty : na.HasLasso ↔ na.lassoStates.Nonempty := by
  rw [hasLasso_iff_reachable]
  constructor
  · rintro ⟨s₀, h₀, s, hs, hreach, hcyc⟩
    exact ⟨s, mem_lassoStates.mpr ⟨⟨s₀, h₀, hreach⟩, hs, hcyc⟩⟩
  · rintro ⟨s, hmem⟩
    obtain ⟨⟨s₀, h₀, hreach⟩, hs, hcyc⟩ := mem_lassoStates.mp hmem
    exact ⟨s₀, h₀, s, hs, hreach, hcyc⟩

/-- The lasso condition, hence Büchi emptiness, is decidable by finite reachability
(`lassoStates`). -/
instance instDecidableHasLasso : Decidable na.HasLasso :=
  decidable_of_iff _ hasLasso_iff_lassoStates_nonempty.symm

/-- **Büchi emptiness test.** For a nondeterministic Büchi automaton with finitely many states and
finitely many symbols, with decidable equality of states, and whose transitions, start states and
accepting states are decidable, the emptiness test returns true exactly when the automaton has no
lasso. It decides this by computing the set of lasso states; by the lasso characterization, it
returns true iff no infinite word is accepted.

With $n$ states, $f$ reachable accepting states and $k$ symbols, the computation performs at most
$f + 1$ reachability closures of $O(n^3 k)$ transition tests each. -/
def isEmptyB (na : Buchi State Symbol) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)] : Bool :=
  !decide na.HasLasso

/-- **Correctness of the Büchi emptiness test.** For a nondeterministic Büchi automaton with
finitely many states and finitely many symbols, with decidable equality of states, and whose
transitions, start states and accepting states are decidable, the emptiness test returns true if
and only if the automaton accepts no infinite word. -/
theorem isEmptyB_iff : na.isEmptyB = true ↔ language na = ⊥ := by
  rw [isEmptyB, Bool.not_eq_true', decide_eq_false_iff_not, ← language_nonempty_iff_hasLasso]
  constructor
  · intro h
    apply ωLanguage.mem_ext
    intro xs
    exact ⟨fun hx => absurd ⟨xs, hx⟩ h, fun hx => absurd hx (by simp)⟩
  · rintro h ⟨xs, hx⟩
    rw [h] at hx
    simp at hx

end Decidable

end Cslib.Automata.NA.Buchi
