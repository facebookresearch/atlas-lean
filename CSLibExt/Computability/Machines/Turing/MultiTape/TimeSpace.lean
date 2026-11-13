/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.MultiTape.Basic

/-!
# Time and space bounds and deterministic classes on CSLib's multi-tape model

Time and space are CSLib's own measures on computation paths of `Turing.MultiTapeTM`: a machine
runs in time `t` on an input when every computation path of at least `t` steps ends halted
(`MultiTapeNTM.RunsInTime`), and in space `s` when every computation path visits at most `s`
work-tape cells, counted per tape and summed over the tapes; the read-only input tape and the
write-only output tape are not counted (`MultiTapeNTM.RunsInSpace`). This file bounds these
uniformly in the input length (`TimeBoundedBy`, `SpaceBoundedBy`), proves that a deterministic
time bound `T` implies the space bound `k * (T + 1)` on a `k`-tape machine
(`runsInSpace_of_runsInTime`), and defines the deterministic classes on languages over `Bool`.

`DTIME t` and `DSPACE s` are the languages decided by some binary, finite-state multi-tape
machine within time, respectively space, `O(t n)` and `O(s n)`, written with explicit constants
`c₁ * t n + c₂`; `Classes.P` and `Classes.PSPACE` are their polynomial unions. The definitions
follow the shape of the classes in the open upstream PR leanprover/cslib#767 (`DTIME`, `DSPACE`,
`P`, `PSPACE`), stated against the pinned CSLib's `MultiTapeTM.DecidableInTimeAndSpace`, so that
they can be replaced by the upstream ones when CSLib provides them. They are not the repository's
canonical `P`, which is defined on Mathlib's `FinTM2` (`MetaMathlibExt.ComplexityTheory.P`); a
bridge between the two models is future work and is not built here.

`NP` and `NL` are not defined here: the pinned CSLib has no acceptance predicate for its
nondeterministic multi-tape machines, and the verifier characterization of `NP` on this model is
itself future work.

## Main definitions

- `Cslib.Turing.MultiTapeTM.TimeBoundedBy`, `Cslib.Turing.MultiTapeTM.SpaceBoundedBy`.
- `Cslib.Turing.MultiTapeTM.Decides`: a machine decides a language over `Bool`.
- `Cslib.Turing.MultiTapeTM.DTIME`, `Cslib.Turing.MultiTapeTM.DSPACE`.
- `Cslib.Turing.MultiTapeTM.Classes.P`, `Cslib.Turing.MultiTapeTM.Classes.PSPACE`.

## Main results

- `runsInSpace_of_runsInTime`, `TimeBoundedBy.spaceBoundedBy`: time bounds space.
- `decidableInTimeAndSpace_iff`, `mem_DTIME_iff`, `mem_DSPACE_iff`: the classes unfolded.
- `DTIME_mono`, `DSPACE_mono`: monotonicity up to linear changes of the bound.
- `DTIME_subset_DSPACE`, `Classes.P_subset_PSPACE`.

## References

- C. Papadimitriou, *Computational Complexity*, §§2.3–2.5, §7.1.
- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, §1.6, §4.1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Turing.MultiTapeTM

open _root_.Turing

variable {k : ℕ} {Symbol State : Type*}

/-! ### Uniform bounds -/

/-- **Time-bounded multi-tape machine.** A deterministic Turing machine $M$ with $k$ work tapes
is time bounded by $t : \mathbb{N} \to \mathbb{N}$ when, for every input word $w$, every
computation path of $M$ on $w$ with at least $t(|w|)$ steps ends in a halted configuration,
where $|w|$ is the length of $w$. -/
def TimeBoundedBy (tm : MultiTapeTM k Symbol State) (t : ℕ → ℕ) : Prop :=
  ∀ w, tm.RunsInTime w (t w.length)

/-- **Space-bounded multi-tape machine.** A deterministic Turing machine $M$ with $k$ work tapes
is space bounded by $s : \mathbb{N} \to \mathbb{N}$ when, for every input word $w$, every
computation path of $M$ on $w$ visits at most $s(|w|)$ work-tape cells, counting the cells
visited on each work tape and summing over the tapes, where $|w|$ is the length of $w$. -/
def SpaceBoundedBy (tm : MultiTapeTM k Symbol State) (s : ℕ → ℕ) : Prop :=
  ∀ w, tm.RunsInSpace w (s w.length)

theorem TimeBoundedBy.mono {tm : MultiTapeTM k Symbol State} {t t' : ℕ → ℕ}
    (h : TimeBoundedBy tm t) (ht : ∀ n, t n ≤ t' n) : TimeBoundedBy tm t' :=
  fun w ↦ (h w).mono (ht _)

theorem SpaceBoundedBy.mono {tm : MultiTapeTM k Symbol State} {s s' : ℕ → ℕ}
    (h : SpaceBoundedBy tm s) (hs : ∀ n, s n ≤ s' n) : SpaceBoundedBy tm s' :=
  fun w ↦ (h w).mono (hs _)

/-- **Time bounds space on one input.** Let $M$ be a deterministic Turing machine with $k$ work
tapes, let $w$ be an input word and let $T \in \mathbb{N}$. If $M$ runs in time $T$ on $w$, that
is, every computation path of $M$ on $w$ with at least $T$ steps ends in a halted configuration,
then $M$ runs in space $k(T + 1)$ on $w$: every computation path of $M$ on $w$ visits at most
$k(T + 1)$ work-tape cells, counting the cells visited on each work tape and summing over the
tapes. -/
theorem runsInSpace_of_runsInTime {tm : MultiTapeTM k Symbol State} {w : List Symbol} {T : ℕ}
    (h : tm.RunsInTime w T) : tm.RunsInSpace w (k * (T + 1)) := by
  have hhalt := halted_runFrom_of_runsInTime h
  intro p
  unfold MultiTapeNTM.ComputationPath.space MultiTapeNTM.RunPath.space
  calc ∑ i, MultiTapeNTM.RunPath.spaceUsedByTape p.toRunPath i ≤ ∑ _i : Fin k, (T + 1) :=
        Finset.sum_le_sum fun i _ ↦ ?_
    _ = k * (T + 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; rfl
  unfold MultiTapeNTM.RunPath.spaceUsedByTape MultiTapeNTM.RunPath.visitedByTapeHead
  have hsub : (Finset.univ.image fun n ↦ (p.toRunPath n).workTapePos i) ⊆
      Finset.univ.image fun n : Fin (T + 1) ↦
        (tm.runFrom (tm.initCfg w) n).workTapePos i := by
    intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨n, rfl⟩ := hz
    refine ⟨⟨min n T, by omega⟩, ?_⟩
    rw [MultiTapeTM.runPath_apply_eq_runFrom, p.head_eq]
    change (tm.runFrom (tm.initCfg w) (min (n : ℕ) T)).workTapePos i =
      (tm.runFrom (tm.initCfg w) n).workTapePos i
    rcases le_total (n : ℕ) T with hn | hn
    · simp [Nat.min_eq_left hn]
    · rw [Nat.min_eq_right hn, MultiTapeTM.runFrom_eq_of_halt tm _ hn hhalt]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

/-- **Uniform time bounds give uniform space bounds.** Let $M$ be a deterministic Turing machine
with $k$ work tapes and let $t : \mathbb{N} \to \mathbb{N}$. If $M$ is time bounded by $t$, then
$M$ is space bounded by the function $n \mapsto k(t(n) + 1)$. -/
theorem TimeBoundedBy.spaceBoundedBy {tm : MultiTapeTM k Symbol State} {t : ℕ → ℕ}
    (h : TimeBoundedBy tm t) : SpaceBoundedBy tm fun n ↦ k * (t n + 1) :=
  fun w ↦ runsInSpace_of_runsInTime (h w)

/-! ### Deciding languages -/

/-- **A multi-tape machine deciding a language.** A deterministic multi-tape Turing machine over
the Boolean alphabet decides a language $L$ of Boolean strings when, on every input $w$, it
eventually halts with output the one-bit string $[\mathrm{true}]$ if $w \in L$ and
$[\mathrm{false}]$ if $w \notin L$. -/
def Decides (tm : MultiTapeTM k Bool State) (L : Set (List Bool)) : Prop :=
  ∀ w, tm.Computes w [MultiTapeTM.indicator L w]

/-- **Decidability within time and space bounds, unfolded.** Let $L$ be a language of Boolean
strings and let $t$ and $s$ assign a natural number to every Boolean string. Then $L$ is decidable
within time $t$ and space $s$ in CSLib's sense, with the identity encoding of inputs, if and only
if there are a number $k$, a finite type of states and a deterministic Turing machine with $k$
work tapes over the Boolean alphabet that decides $L$ and, on every input $w$, runs in time $t(w)$
(every computation path of at least $t(w)$ steps ends in a halted configuration) and in space
$s(w)$ (every computation path visits at most $s(w)$ work-tape cells, summed over the work
tapes). -/
theorem decidableInTimeAndSpace_iff {L : Set (List Bool)} {t s : List Bool → ℕ} :
    MultiTapeTM.DecidableInTimeAndSpace L (Function.Embedding.refl _) t s ↔
      ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
        Decides tm L ∧ (∀ w, tm.RunsInTime w (t w)) ∧ ∀ w, tm.RunsInSpace w (s w) := by
  constructor
  · rintro ⟨k, State, hS, tm, h⟩
    exact ⟨k, State, hS, tm, fun w ↦ (h w).1, fun w ↦ (h w).2.1, fun w ↦ (h w).2.2⟩
  · rintro ⟨k, State, hS, tm, hd, ht, hs⟩
    exact ⟨k, State, hS, tm, fun w ↦ ⟨hd w, ht w, hs w⟩⟩

/-! ### Deterministic time and space classes -/

/-- **Deterministic time classes on multi-tape machines.** For $t : \mathbb{N} \to \mathbb{N}$,
$\mathrm{DTIME}(t)$ is the set of languages $L$ of Boolean strings for which there are constants
$c_1, c_2 \in \mathbb{N}$, a function $s : \mathbb{N} \to \mathbb{N}$ and a deterministic
multi-tape Turing machine with Boolean tape alphabet and finitely many states such that, on every
input $w$ of length $n$, the machine halts with the one-bit output $[\mathrm{true}]$ if $w \in L$
and $[\mathrm{false}]$ otherwise, runs in time $c_1 t(n) + c_2$ (every computation path of at
least $c_1 t(n) + c_2$ steps ends in a halted configuration) and runs in space $s(n)$ (every
computation path visits at most $s(n)$ work-tape cells, summed over the work tapes). -/
def DTIME (t : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c₁ c₂ : ℕ, ∃ s : ℕ → ℕ, MultiTapeTM.DecidableInTimeAndSpace L
    (Function.Embedding.refl _) (fun w ↦ c₁ * t w.length + c₂) (fun w ↦ s w.length)}

/-- **Deterministic space classes on multi-tape machines.** For $s : \mathbb{N} \to \mathbb{N}$,
$\mathrm{DSPACE}(s)$ is the set of languages $L$ of Boolean strings for which there are constants
$c_1, c_2 \in \mathbb{N}$, a function $t : \mathbb{N} \to \mathbb{N}$ and a deterministic
multi-tape Turing machine with Boolean tape alphabet and finitely many states such that, on every
input $w$ of length $n$, the machine halts with the one-bit output $[\mathrm{true}]$ if $w \in L$
and $[\mathrm{false}]$ otherwise, runs in time $t(n)$ (every computation path of at least $t(n)$
steps ends in a halted configuration) and runs in space $c_1 s(n) + c_2$ (every computation path
visits at most $c_1 s(n) + c_2$ work-tape cells, summed over the work tapes). -/
def DSPACE (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ c₁ c₂ : ℕ, ∃ t : ℕ → ℕ, MultiTapeTM.DecidableInTimeAndSpace L
    (Function.Embedding.refl _) (fun w ↦ t w.length) (fun w ↦ c₁ * s w.length + c₂)}

theorem mem_DTIME_iff {t : ℕ → ℕ} {L : Set (List Bool)} :
    L ∈ DTIME t ↔ ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM k Bool State), Decides tm L ∧
        TimeBoundedBy tm (fun n ↦ c₁ * t n + c₂) ∧ ∃ s, SpaceBoundedBy tm s := by
  constructor
  · rintro ⟨c₁, c₂, s, h⟩
    obtain ⟨k, State, hS, tm, hd, ht, hs⟩ := decidableInTimeAndSpace_iff.mp h
    exact ⟨c₁, c₂, k, State, hS, tm, hd, ht, s, hs⟩
  · rintro ⟨c₁, c₂, k, State, hS, tm, hd, ht, s, hs⟩
    exact ⟨c₁, c₂, s, decidableInTimeAndSpace_iff.mpr ⟨k, State, hS, tm, hd, ht, hs⟩⟩

theorem mem_DSPACE_iff {s : ℕ → ℕ} {L : Set (List Bool)} :
    L ∈ DSPACE s ↔ ∃ (c₁ c₂ k : ℕ) (State : Type) (_ : Finite State)
      (tm : MultiTapeTM k Bool State), Decides tm L ∧
        SpaceBoundedBy tm (fun n ↦ c₁ * s n + c₂) ∧ ∃ t, TimeBoundedBy tm t := by
  constructor
  · rintro ⟨c₁, c₂, t, h⟩
    obtain ⟨k, State, hS, tm, hd, ht, hs⟩ := decidableInTimeAndSpace_iff.mp h
    exact ⟨c₁, c₂, k, State, hS, tm, hd, hs, t, ht⟩
  · rintro ⟨c₁, c₂, k, State, hS, tm, hd, hs, t, ht⟩
    exact ⟨c₁, c₂, t, decidableInTimeAndSpace_iff.mpr ⟨k, State, hS, tm, hd, ht, hs⟩⟩

private theorem affine_le {f g : ℕ → ℕ} {a b : ℕ} (h : ∀ n, f n ≤ a * g n + b) (c₁ c₂ n : ℕ) :
    c₁ * f n + c₂ ≤ c₁ * a * g n + (c₁ * b + c₂) := by
  have := Nat.add_le_add_right (Nat.mul_le_mul_left c₁ (h n)) c₂
  rwa [Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc] at this

/-- **Deterministic time classes are monotone up to affine changes of the bound.** Let
$t_1, t_2 : \mathbb{N} \to \mathbb{N}$ and $a, b \in \mathbb{N}$ satisfy
$t_1(n) \le a \, t_2(n) + b$ for every $n \in \mathbb{N}$. Then
$\mathrm{DTIME}(t_1) \subseteq \mathrm{DTIME}(t_2)$. -/
theorem DTIME_mono {t₁ t₂ : ℕ → ℕ} (a b : ℕ) (h : ∀ n, t₁ n ≤ a * t₂ n + b) :
    DTIME t₁ ⊆ DTIME t₂ := by
  rintro L ⟨c₁, c₂, s, hL⟩
  exact ⟨c₁ * a, c₁ * b + c₂, s, MultiTapeTM.ComputableInTimeAndSpace.mono hL
    (fun w ↦ affine_le h c₁ c₂ w.length) fun _ ↦ le_rfl⟩

/-- **Deterministic space classes are monotone up to affine changes of the bound.** Let
$s_1, s_2 : \mathbb{N} \to \mathbb{N}$ and $a, b \in \mathbb{N}$ satisfy
$s_1(n) \le a \, s_2(n) + b$ for every $n \in \mathbb{N}$. Then
$\mathrm{DSPACE}(s_1) \subseteq \mathrm{DSPACE}(s_2)$. -/
theorem DSPACE_mono {s₁ s₂ : ℕ → ℕ} (a b : ℕ) (h : ∀ n, s₁ n ≤ a * s₂ n + b) :
    DSPACE s₁ ⊆ DSPACE s₂ := by
  rintro L ⟨c₁, c₂, t, hL⟩
  exact ⟨c₁ * a, c₁ * b + c₂, t, MultiTapeTM.ComputableInTimeAndSpace.mono hL
    (fun _ ↦ le_rfl) fun w ↦ affine_le h c₁ c₂ w.length⟩

/-- **Time classes are contained in space classes.** For every $t : \mathbb{N} \to \mathbb{N}$,
$\mathrm{DTIME}(t) \subseteq \mathrm{DSPACE}(t)$. -/
theorem DTIME_subset_DSPACE (t : ℕ → ℕ) : DTIME t ⊆ DSPACE t := by
  intro L hL
  obtain ⟨c₁, c₂, k, State, hS, tm, hd, ht, -⟩ := mem_DTIME_iff.mp hL
  refine mem_DSPACE_iff.mpr ⟨k * c₁, k * (c₂ + 1), k, State, hS, tm, hd, ?_, _, ht⟩
  refine ht.spaceBoundedBy.mono fun n ↦ le_of_eq ?_
  rw [Nat.add_assoc, Nat.mul_add, Nat.mul_assoc]

namespace Classes

/-- **Polynomial time on multi-tape machines.** $\mathrm{P}$ is the set of languages of Boolean
strings that lie in $\mathrm{DTIME}(n \mapsto n^d)$ for some $d \in \mathbb{N}$. -/
def P : Set (Set (List Bool)) := ⋃ d, DTIME (· ^ d)

/-- **Polynomial space on multi-tape machines.** $\mathrm{PSPACE}$ is the set of languages of
Boolean strings that lie in $\mathrm{DSPACE}(n \mapsto n^d)$ for some $d \in \mathbb{N}$. -/
def PSPACE : Set (Set (List Bool)) := ⋃ d, DSPACE (· ^ d)

/-- **P is contained in PSPACE.** On the deterministic multi-tape model,
$\mathrm{P} \subseteq \mathrm{PSPACE}$. -/
theorem P_subset_PSPACE : P ⊆ PSPACE :=
  Set.iUnion_mono fun d ↦ DTIME_subset_DSPACE (· ^ d)

end Classes

end Cslib.Turing.MultiTapeTM
