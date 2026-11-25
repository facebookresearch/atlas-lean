/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generic separation-logic API lemmas
-/
module

public import CSLibExt.Languages.IMP.SeparationLogic

/-!
# Generic separation-logic API lemmas

Reusable infrastructure over the heap IMP separation logic: store
irrelevance of heap assertions and the resulting discharge of the frame
rule side condition, distribution of store facts over separating
conjunction, entailment combinators, local and framed read/write and
assignment rules, and transport of step validity over existential
witnesses. Worked examples live in
`CSLibExtTest/Languages/IMP/SeparationExamples.lean`.
-/

@[expose] public section

namespace Cslib.IMP

open HAssertion

open scoped HAssertion

/-! ## Generic bookkeeping lemmas -/

/-- **Store-irrelevant heap assertions.** A heap assertion $P$ is store-irrelevant when for all
stores $s, s'$ and every heap $h$, $P(s, h)$ implies $P(s', h)$; that is, whether $P$ holds
does not depend on the store.

The empty-heap and points-to assertions are store-irrelevant, and so is the separating
conjunction of two store-irrelevant assertions. -/
def StoreIrrel (P : HAssertion) : Prop :=
  ∀ (s s' : State) (h : Heap), P s h → P s' h

theorem pointsTo_storeIrrel {a v : Nat} : StoreIrrel (pointsTo a v) :=
  fun _s _s' _h hh => hh

theorem star_storeIrrel {P Q : HAssertion}
    (hP : StoreIrrel P) (hQ : StoreIrrel Q) : StoreIrrel (P ⋆ Q) := by
  intro s s' h hstar
  rw [HAssertion.star_def] at hstar ⊢
  obtain ⟨h₁, h₂, hd, heq, h1, h2⟩ := hstar
  exact ⟨h₁, h₂, hd, heq, hP s s' h₁ h1, hQ s s' h₂ h2⟩

/-- **Store-irrelevant frames satisfy the frame-rule side condition.** Let $R$ be a
store-irrelevant heap assertion and $c$ a heap command. For all stores $s, s'$ and every heap
$h$, if $R(s, h)$ holds and $s'(x) = s(x)$ for every variable $x$ outside the set of variables
that $c$ may assign to, then $R(s', h)$ holds.

This is the side condition on the frame in the frame rule. -/
theorem frame_of_storeIrrel {R : HAssertion} (hR : StoreIrrel R)
    (c : HeapCmd) :
    ∀ ⦃s : State⦄ ⦃h : Heap⦄ ⦃s' : State⦄, R s h →
      (∀ x, x ∉ c.modVars → s' x = s x) → R s' h := by
  intro s h s' hs _hagree
  exact hR s s' h hs

theorem entails_of_eq {P Q : HAssertion} (h : P = Q) : P.Entails Q := by
  intro s heap hh
  rw [← h]
  exact hh

/-- **Pulling a store fact out of a separating conjunction.** Let $p$ be a predicate on
stores and $P$, $R$ heap assertions. Write $A \star B$ for the separating conjunction of heap
assertions $A$ and $B$ (the heap splits into two disjoint parts satisfying $A$ and $B$,
respectively, at the same store), and $p \land P$ for the heap assertion that holds at store
$s$ and heap $h$ when $p(s)$ and $P(s, h)$ both hold. Then
$(p \land P) \star R = p \land (P \star R)$.

This lets framed local triples be stated with the store facts kept outside the separating
conjunction. -/
theorem star_and_left {p : State → Prop} {P R : HAssertion} :
    ((fun s h => p s ∧ P s h) ⋆ R) = (fun s h => p s ∧ (P ⋆ R) s h) := by
  funext s h
  apply propext
  simp only [HAssertion.star_def]
  constructor
  · rintro ⟨h₁, h₂, hd, heq, ⟨hp, hP⟩, hR⟩
    exact ⟨hp, h₁, h₂, hd, heq, hP, hR⟩
  · rintro ⟨hp, h₁, h₂, hd, heq, hP, hR⟩
    exact ⟨h₁, h₂, hd, heq, ⟨hp, hP⟩, hR⟩

theorem entails_and_right {p : State → Prop} {P Q : HAssertion}
    (hent : P.Entails Q) :
    HAssertion.Entails (fun s h => p s ∧ P s h)
      (fun s h => p s ∧ Q s h) := by
  intro s heap hPQ
  exact ⟨hPQ.1, hent hPQ.2⟩

/-- **Rearranging a separating conjunction.** For heap assertions $P$, $Q$ and $R$, write
$A \star B$ for the separating conjunction of heap assertions $A$ and $B$ (the heap splits into
two disjoint parts satisfying $A$ and $B$, respectively, at the same store). Then
$P \star (Q \star R)$ entails $(P \star R) \star Q$: every store and heap satisfying the first
assertion satisfy the second. -/
theorem star_swap_right {P Q R : HAssertion} :
    (P ⋆ (Q ⋆ R)).Entails ((P ⋆ R) ⋆ Q) :=
  (HAssertion.star_mono (HAssertion.entails_refl P)
    HAssertion.star_comm).trans
    (entails_of_eq HAssertion.star_assoc.symm)

/-! ## Framed one-cell steps

The library's `read`/`write` rules describe a heap consisting of a single
cell. The lemmas below frame them once and for all: the cell sits on the
left of a `⋆`, the (store-irrelevant) rest of the heap on the right, and
the store facts are carried as a plain conjunction `p s ∧ ·`. The
hypothesis `hpq` re-establishes the store facts after the step; computing
`Function.update` at the scratch variables is the caller's job. -/

/-- **Local rule for a heap read.** Let $x$ and $y$ be variables, let $a$ and $v$ be natural
numbers, and let $p$ and $q$ be predicates on stores. Write $s[x := n]$ for the store that agrees
with $s$ except that it maps $x$ to $n$, and $a \mapsto v$ for the heap assertion that holds when
the heap is the single cell at address $a$ holding $v$. If every store $s$ satisfying $p$ has
$s(y) = a$ and $q(s[x := v])$, then the separation-logic triple for the heap read $x := [y]$
(which loads into $x$ the value stored at the address held in $y$) is valid with precondition
"$p(s)$ and $a \mapsto v$ holds at $(s, h)$" and postcondition "$q(s)$ and $a \mapsto v$ holds at
$(s, h)$", where $s$ is the store and $h$ the heap. -/
theorem read_local {name addrName a v : Nat} {p q : State → Prop}
    (hpq : ∀ s, p s → s addrName = a ∧
      q (Function.update s name v)) :
    SepValid (fun s h => p s ∧ pointsTo a v s h)
      (.read name (.var addrName))
      (fun s h => q s ∧ pointsTo a v s h) := by
  refine SepValid.consequence ?_
    (SepValid.read (Q := fun s h => q s ∧ pointsTo a v s h)
      name (.var addrName)) (HAssertion.entails_refl _)
  intro s h hpre
  obtain ⟨hp, hpt⟩ := hpre
  obtain ⟨haddr, hq⟩ := hpq s hp
  simp only [AExp.eval_var]
  exact ⟨v, by rw [haddr]; exact hpt, hq, hpt⟩

theorem write_local {addrName valName a v w : Nat} {p q : State → Prop}
    (hpq : ∀ s, p s → q s ∧ s addrName = a ∧ s valName = v) :
    SepValid (fun s h => p s ∧ pointsTo a w s h)
      (.write (.var addrName) (.var valName))
      (fun s h => q s ∧ pointsTo a v s h) := by
  refine SepValid.consequence ?_
    (SepValid.write (Q := fun s h => q s ∧ pointsTo a v s h)
      (.var addrName) (.var valName)) (HAssertion.entails_refl _)
  intro s h hpre
  obtain ⟨hp, hpt⟩ := hpre
  obtain ⟨hq, haddr, hval⟩ := hpq s hp
  simp only [AExp.eval_var]
  refine ⟨w, by rw [haddr]; exact hpt, hq, ?_⟩
  rw [haddr, hval]
  rfl

theorem read_framed {name addrName a v : Nat} {p q : State → Prop}
    {R : HAssertion} (hR : StoreIrrel R)
    (hpq : ∀ s, p s → s addrName = a ∧
      q (Function.update s name v)) :
    SepValid (fun s h => p s ∧ (pointsTo a v ⋆ R) s h)
      (.read name (.var addrName))
      (fun s h => q s ∧ (pointsTo a v ⋆ R) s h) :=
  SepValid.consequence (entails_of_eq star_and_left.symm)
    (SepValid.frame (read_local hpq) (frame_of_storeIrrel hR _))
    (entails_of_eq star_and_left)

theorem write_framed {addrName valName a v w : Nat} {p q : State → Prop}
    {R : HAssertion} (hR : StoreIrrel R)
    (hpq : ∀ s, p s → q s ∧ s addrName = a ∧ s valName = v) :
    SepValid (fun s h => p s ∧ (pointsTo a w ⋆ R) s h)
      (.write (.var addrName) (.var valName))
      (fun s h => q s ∧ (pointsTo a v ⋆ R) s h) :=
  SepValid.consequence (entails_of_eq star_and_left.symm)
    (SepValid.frame (write_local hpq) (frame_of_storeIrrel hR _))
    (entails_of_eq star_and_left)

/-- **Assignment rule with a store-irrelevant heap assertion.** Let $x$ and $y$ be variables,
let $p$ and $q$ be predicates on stores, and let $H$ be a store-irrelevant heap assertion.
Write $s[x := n]$ for the store that agrees with $s$ except that it maps $x$ to $n$. If every
store $s$ satisfying $p$ has $q(s[x := s(y)])$, then the separation-logic triple for the
assignment $x := y$ is valid with precondition "$p(s)$ and $H(s, h)$" and postcondition
"$q(s)$ and $H(s, h)$", where $s$ is the store and $h$ the heap.

An assignment leaves the heap untouched, so no framing is needed. -/
theorem assign_step {name src : Nat} {p q : State → Prop}
    {H : HAssertion} (hH : StoreIrrel H)
    (hpq : ∀ s, p s → q (Function.update s name (s src))) :
    SepValid (fun s h => p s ∧ H s h) (.assign name (.var src))
      (fun s h => q s ∧ H s h) := by
  refine SepValid.consequence ?_
    (SepValid.assign (Q := fun s h => q s ∧ H s h) name (.var src))
    (HAssertion.entails_refl _)
  intro s h hpre
  obtain ⟨hp, hHh⟩ := hpre
  exact ⟨hpq s hp, hH s _ h hHh⟩

/-- **Existential rule for separation-logic triples.** Let $c$ be a heap command, let $\iota$ be
an arbitrary index (any type or proposition), and let $P_i$ and $Q_i$ be heap assertions for
each $i$ in $\iota$. If for every $i$ the triple with precondition $P_i$, command $c$ and
postcondition $Q_i$ is valid, then the triple with precondition "there is $i$ with $P_i$",
command $c$ and postcondition "there is $i$ with $Q_i$" is valid. -/
theorem SepValid.exists {ι : Sort*} {P Q : ι → HAssertion} {c : HeapCmd}
    (hstep : ∀ i, SepValid (P i) c (Q i)) :
    SepValid (fun s h => ∃ i, P i s h) c (fun s h => ∃ i, Q i s h) := by
  intro s h hex
  obtain ⟨i, hP⟩ := hex
  obtain ⟨hsafe, hterm⟩ := hstep i hP
  refine ⟨hsafe, ?_⟩
  intro s' h' hs
  exact ⟨i, hterm hs⟩

end Cslib.IMP
