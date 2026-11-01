/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Pair hidden Markov models

A pair HMM (Durbin, Eddy, Krogh and Mitchison, *Biological Sequence Analysis*, 1998, chapter 4)
emits two sequences `xs`, `ys` at once: its emitting states are `M` (emit an aligned pair
`(a, b)`), `X` (emit `a` in `xs` only) and `Y` (emit `b` in `ys` only), between a silent begin
and end state. A state path emitting `xs` and `ys` is the same thing as an alignment of `xs`
and `ys` (`Cslib.Algorithms.Lean.Alignment`): the column `(some a, some b)` is a visit to `M`,
`(some a, none)` a visit to `X`, `(none, some b)` a visit to `Y`. So the joint weight
`P(xs, ys)` is a sum over alignments and the Viterbi value is a maximum over alignments.

Both are instances of one dynamic program. An `AlignmentAutomaton` reads an alignment column by
column, carrying a control state `q : Q` (for a pair HMM, the previous HMM state; for a profile
HMM, `ProfileHMM.lean`, the previous state and the current model node): each column has a
weight given the control state, and the alignment ends with a final weight. `sumDP` peels the
first column (three cases, like Needleman–Wunsch), and `maxDP` takes the largest of the three
products of a column weight with a recursively computed value. That is the largest alignment
weight only under nonnegative weights (see `alignWeight_le_maxDP`): with a negative column
weight, multiplying by the recursively chosen suffix maximum can reverse the order.

## Main results

* `mem_alignmentsOf`, `nodup_alignmentsOf`: `alignmentsOf xs ys` lists every alignment of a
  sequence over `α` with a sequence over `β` exactly once (`alignmentsOf_eq_alignments`: on one
  alphabet it is `Cslib.Algorithms.Lean.alignments`).
* `sumDP_eq_sum`: **the sum recursion is the sum over all alignments** of the alignment weights.
* `alignWeight_le_maxDP`, `exists_alignWeight_eq_maxDP`: under nonnegative weights in a
  linearly ordered semiring, the max recursion is the largest alignment weight
  (`alignWeight_le_maxDP`) and is attained (`exists_alignWeight_eq_maxDP`). Without
  nonnegativity the recursion is only the value of the recursively chosen alignment.
* `sumDP_cons_cons`, `maxDP_cons_cons` (and the boundary cases): the recursions in
  first-column form.
* `PairHMM.likelihood_eq_sum`, `PairHMM.alignProb_le_viterbi`,
  `PairHMM.exists_alignProb_eq_viterbi`: for a pair HMM, the full probability `P(xs, ys)` and
  the Viterbi value (Durbin et al., chapter 4). The recursion peels the first column, so it
  runs from the ends of the sequences towards the beginning: it is the backward recursion,
  whose value at the begin state is the full probability that the forward algorithm computes.
* `PairHMM.log_viterbi_div_background`: **log-odds Viterbi is Needleman–Wunsch**. For a pair
  HMM whose transition weights do not depend on the current state (`IsMemoryless`), against
  the independence model `R` with geometric lengths (Durbin et al., chapter 4), the
  log-odds Viterbi score `log (viterbi / P(xs, ys | R))` is the linear-gap Needleman–Wunsch
  score `nwScore σ gap xs ys` plus `log (τ / η²)`, when the per-column log-odds scores are the
  integers `σ a b` and `gap`.

## Gap model

The pair HMM's transition weights decide the gap model. With state-independent transitions the
log-odds score of a gap column does not depend on the previous column, so gaps are linear: a
run of `k` gap columns scores `k * gap`. Durbin's three-state model (`M → X` weight `δ`,
`X → X` weight `ε`, no `X → Y`) gives an affine-like gap model whose log-odds equal the Gotoh
score only after redistributing the `X → M` transition weight into the gap cost, and only up
to terms at the alignment ends; that correspondence is not claimed here.

## Cost model

The recursions `sumDP` and `maxDP` are specifications: they recompute shared subproblems, so
evaluating them directly takes exponential time. Tabulating them on prefix pairs (and control
states) gives the usual `O(|xs| |ys| |Q|)` algorithms; that is not done here.

## References

* R. Durbin, S. R. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis*, Cambridge
  University Press, 1998, chapter 4.
* S. B. Needleman and C. D. Wunsch, *A general method applicable to the search for similarities
  in the amino acid sequence of two proteins*, J. Mol. Biol. 48 (1970), 443–453.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.HMM

open Cslib.Algorithms.Lean

/-- All alignments of `xs : List α` with `ys : List β`, by fuel recursion on the first column
(the same recursion as `Cslib.Algorithms.Lean.alignmentsAux`, for two alphabets). Implementation
detail: use `alignmentsOf`, whose fuel `xs.length + ys.length + 1` is enough. -/
def alignmentsOfAux {α β : Type*} : ℕ → List α → List β → List (List (Option α × Option β))
  | 0, _, _ => []
  | _ + 1, [], [] => [[]]
  | n + 1, [], b :: ys => (alignmentsOfAux n [] ys).map fun A => (none, some b) :: A
  | n + 1, a :: xs, [] => (alignmentsOfAux n xs []).map fun A => (some a, none) :: A
  | n + 1, a :: xs, b :: ys =>
      (alignmentsOfAux n xs ys).map (fun A => (some a, some b) :: A) ++
        (alignmentsOfAux n xs (b :: ys)).map (fun A => (some a, none) :: A) ++
        (alignmentsOfAux n (a :: xs) ys).map (fun A => (none, some b) :: A)

/-- All alignments of a sequence over `α` with a sequence over `β`: lists of columns
`Option α × Option β` with no `(none, none)` column whose rows filter to `xs` and `ys`
(`mem_alignmentsOf`), each listed once (`nodup_alignmentsOf`). For `β = α` this is
`Cslib.Algorithms.Lean.alignments` (`alignmentsOf_eq_alignments`). -/
def alignmentsOf {α β : Type*} (xs : List α) (ys : List β) : List (List (Option α × Option β)) :=
  alignmentsOfAux (xs.length + ys.length + 1) xs ys

private theorem alignmentsOfAux_succ {α β : Type*} : ∀ (m : ℕ) (xs : List α) (ys : List β),
    xs.length + ys.length < m → alignmentsOfAux (m + 1) xs ys = alignmentsOfAux m xs ys
  | 0, xs, ys, h => by omega
  | m + 1, [], [], _ => by simp [alignmentsOfAux]
  | m + 1, [], b :: ys, h => by
      simp only [alignmentsOfAux]
      rw [alignmentsOfAux_succ m [] ys (by simp at h ⊢; omega)]
  | m + 1, a :: xs, [], h => by
      simp only [alignmentsOfAux]
      rw [alignmentsOfAux_succ m xs [] (by simp at h ⊢; omega)]
  | m + 1, a :: xs, b :: ys, h => by
      simp only [List.length_cons] at h
      simp only [alignmentsOfAux]
      rw [alignmentsOfAux_succ m xs ys (by omega), alignmentsOfAux_succ m xs (b :: ys)
        (by simp; omega), alignmentsOfAux_succ m (a :: xs) ys (by simp; omega)]

private theorem alignmentsOfAux_eq {α β : Type*} (m : ℕ) (xs : List α) (ys : List β)
    (h : xs.length + ys.length < m) :
    alignmentsOfAux m xs ys = alignmentsOf xs ys := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · rw [alignmentsOfAux_succ m xs ys h, ih h]
      · rw [alignmentsOf, h]

/-- The alignments of two nonempty sequences, by their first column. -/
theorem alignmentsOf_cons_cons {α β : Type*} (a : α) (b : β) (xs : List α) (ys : List β) :
    alignmentsOf (a :: xs) (b :: ys) =
      (alignmentsOf xs ys).map (fun A => (some a, some b) :: A) ++
        (alignmentsOf xs (b :: ys)).map (fun A => (some a, none) :: A) ++
        (alignmentsOf (a :: xs) ys).map (fun A => (none, some b) :: A) := by
  rw [alignmentsOf, show (a :: xs).length + (b :: ys).length + 1 =
    (xs.length + ys.length + 1 + 1) + 1 by simp; omega, alignmentsOfAux,
    alignmentsOfAux_eq _ xs ys (by omega), alignmentsOfAux_eq _ xs (b :: ys) (by simp; omega),
    alignmentsOfAux_eq _ (a :: xs) ys (by simp; omega)]

/-- The alignments of the empty sequence with a nonempty one. -/
theorem alignmentsOf_nil_cons {α β : Type*} (b : β) (ys : List β) :
    alignmentsOf ([] : List α) (b :: ys) =
      (alignmentsOf [] ys).map (fun A => (none, some b) :: A) := by
  rw [alignmentsOf, show ([] : List α).length + (b :: ys).length + 1 =
    (ys.length + 1) + 1 by simp, alignmentsOfAux, alignmentsOfAux_eq _ [] ys (by simp)]

/-- The alignments of a nonempty sequence with the empty one. -/
theorem alignmentsOf_cons_nil {α β : Type*} (a : α) (xs : List α) :
    alignmentsOf (a :: xs) ([] : List β) =
      (alignmentsOf xs []).map (fun A => (some a, none) :: A) := by
  rw [alignmentsOf, show (a :: xs).length + ([] : List β).length + 1 =
    (xs.length + 1) + 1 by simp, alignmentsOfAux, alignmentsOfAux_eq _ xs [] (by simp)]

private theorem valid_of_mem_aux {α β : Type*} : ∀ (n : ℕ) (xs : List α) (ys : List β)
    (A : List (Option α × Option β)), A ∈ alignmentsOfAux n xs ys →
    (∀ c ∈ A, c ≠ (none, none)) ∧ A.filterMap Prod.fst = xs ∧ A.filterMap Prod.snd = ys
  | 0, _, _, _, hA => by simp [alignmentsOfAux] at hA
  | n + 1, [], [], A, hA => by
      simp only [alignmentsOfAux, List.mem_singleton] at hA
      subst hA; simp
  | n + 1, [], b :: ys, A, hA => by
      simp only [alignmentsOfAux, List.mem_map] at hA
      obtain ⟨A, hA, rfl⟩ := hA
      obtain ⟨h1, h2, h3⟩ := valid_of_mem_aux n _ _ A hA
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  | n + 1, a :: xs, [], A, hA => by
      simp only [alignmentsOfAux, List.mem_map] at hA
      obtain ⟨A, hA, rfl⟩ := hA
      obtain ⟨h1, h2, h3⟩ := valid_of_mem_aux n _ _ A hA
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  | n + 1, a :: xs, b :: ys, A, hA => by
      simp only [alignmentsOfAux, List.mem_append, List.mem_map] at hA
      rcases hA with (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩) | ⟨A, hA, rfl⟩ <;>
      · obtain ⟨h1, h2, h3⟩ := valid_of_mem_aux n _ _ A hA
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

private theorem mem_of_valid {α β : Type*} : ∀ (A : List (Option α × Option β)) (xs : List α)
    (ys : List β), (∀ c ∈ A, c ≠ (none, none)) → A.filterMap Prod.fst = xs →
    A.filterMap Prod.snd = ys → A ∈ alignmentsOf xs ys
  | [], xs, ys, _, h2, h3 => by
      subst h2 h3; simp [alignmentsOf, alignmentsOfAux]
  | (none, none) :: A, _, _, h1, _, _ => absurd rfl (h1 _ List.mem_cons_self)
  | (some a, some b) :: A, xs, ys, h1, h2, h3 => by
      subst h2 h3
      change _ ∈ alignmentsOf (a :: A.filterMap Prod.fst) (b :: A.filterMap Prod.snd)
      rw [alignmentsOf_cons_cons]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
        (mem_of_valid A _ _ (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) rfl rfl)))
  | (some a, none) :: A, xs, ys, h1, h2, h3 => by
      subst h2 h3
      have ih := mem_of_valid A _ _ (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) rfl rfl
      change _ ∈ alignmentsOf (a :: A.filterMap Prod.fst) (A.filterMap Prod.snd)
      rcases hy : A.filterMap Prod.snd with _ | ⟨b, ys⟩
      · rw [hy] at ih; rw [alignmentsOf_cons_nil]; exact List.mem_map_of_mem ih
      · rw [hy] at ih; rw [alignmentsOf_cons_cons]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem ih))
  | (none, some b) :: A, xs, ys, h1, h2, h3 => by
      subst h2 h3
      have ih := mem_of_valid A _ _ (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) rfl rfl
      change _ ∈ alignmentsOf (A.filterMap Prod.fst) (b :: A.filterMap Prod.snd)
      rcases hx : A.filterMap Prod.fst with _ | ⟨a, xs⟩
      · rw [hx] at ih; rw [alignmentsOf_nil_cons]; exact List.mem_map_of_mem ih
      · rw [hx] at ih; rw [alignmentsOf_cons_cons]
        exact List.mem_append_right _ (List.mem_map_of_mem ih)

private theorem nodup_aux {α β : Type*} : ∀ (n : ℕ) (xs : List α) (ys : List β),
    (alignmentsOfAux n xs ys).Nodup
  | 0, _, _ => by simp [alignmentsOfAux]
  | n + 1, [], [] => List.nodup_singleton _
  | n + 1, [], b :: ys => by
      simp only [alignmentsOfAux]
      exact (nodup_aux n _ _).map (fun _ _ h => List.cons_injective h)
  | n + 1, a :: xs, [] => by
      simp only [alignmentsOfAux]
      exact (nodup_aux n _ _).map (fun _ _ h => List.cons_injective h)
  | n + 1, a :: xs, b :: ys => by
      simp only [alignmentsOfAux]
      refine List.Nodup.append (List.Nodup.append
        ((nodup_aux n _ _).map (fun _ _ h => List.cons_injective h))
        ((nodup_aux n _ _).map (fun _ _ h => List.cons_injective h)) ?_)
        ((nodup_aux n _ _).map (fun _ _ h => List.cons_injective h)) ?_
      · simp [List.disjoint_left]
      · simp only [List.disjoint_left, List.mem_append, List.mem_map]
        rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) ⟨_, _, h⟩ <;> simp at h

private theorem alignmentsOfAux_eq_alignmentsAux {α : Type*} : ∀ (n : ℕ) (xs ys : List α),
    alignmentsOfAux n xs ys = alignmentsAux n xs ys
  | 0, _, _ => rfl
  | n + 1, [], [] => rfl
  | n + 1, [], b :: ys => by
      simp only [alignmentsOfAux, alignmentsAux, alignmentsOfAux_eq_alignmentsAux n]
  | n + 1, a :: xs, [] => by
      simp only [alignmentsOfAux, alignmentsAux, alignmentsOfAux_eq_alignmentsAux n]
  | n + 1, a :: xs, b :: ys => by
      simp only [alignmentsOfAux, alignmentsAux, alignmentsOfAux_eq_alignmentsAux n]

/-- **Membership in `alignmentsOf` is validity**: no `(none, none)` column, and the rows filter
to the two sequences. -/
theorem mem_alignmentsOf {α β : Type*} (xs : List α) (ys : List β)
    (A : List (Option α × Option β)) :
    A ∈ alignmentsOf xs ys ↔
      (∀ c ∈ A, c ≠ (none, none)) ∧ A.filterMap Prod.fst = xs ∧ A.filterMap Prod.snd = ys :=
  ⟨valid_of_mem_aux _ xs ys A, fun ⟨h1, h2, h3⟩ => mem_of_valid A xs ys h1 h2 h3⟩

/-- **Each alignment is listed once.** -/
theorem nodup_alignmentsOf {α β : Type*} (xs : List α) (ys : List β) :
    (alignmentsOf xs ys).Nodup :=
  nodup_aux _ xs ys

/-- On one alphabet, `alignmentsOf` is `Cslib.Algorithms.Lean.alignments`. -/
theorem alignmentsOf_eq_alignments {α : Type*} (xs ys : List α) :
    alignmentsOf xs ys = alignments xs ys :=
  alignmentsOfAux_eq_alignmentsAux _ xs ys

/-- A weighted automaton reading an alignment of a sequence over `α` with a sequence over `β`
column by column with a control state in `Q`: the weight of reading a column in a control
state, the next control state, and the final weight of a control state. Weights are in `R`. -/
structure AlignmentAutomaton (Q α β R : Type*) where
  /-- The weight of reading a column in a control state. -/
  weight : Q → Option α × Option β → R
  /-- The control state after reading a column. -/
  next : Q → Option α × Option β → Q
  /-- The weight of ending in a control state. -/
  final : Q → R

namespace AlignmentAutomaton

variable {Q α β R : Type*}

section Semiring

variable [Semiring R] (M : AlignmentAutomaton Q α β R)

/-- The weight of an alignment read from control state `q`: the product of the column weights
along the alignment, then the final weight. -/
def alignWeight : Q → List (Option α × Option β) → R
  | q, [] => M.final q
  | q, c :: A => M.weight q c * alignWeight (M.next q c) A

/-- The sum recursion with fuel (the fuel bounds the recursion depth). Implementation detail:
use `sumDP`, whose fuel `xs.length + ys.length + 1` is enough. -/
def sumDPAux : ℕ → Q → List α → List β → R
  | 0, _, _, _ => 0
  | _ + 1, q, [], [] => M.final q
  | n + 1, q, [], b :: ys =>
      M.weight q (none, some b) * sumDPAux n (M.next q (none, some b)) [] ys
  | n + 1, q, a :: xs, [] =>
      M.weight q (some a, none) * sumDPAux n (M.next q (some a, none)) xs []
  | n + 1, q, a :: xs, b :: ys =>
      M.weight q (some a, some b) * sumDPAux n (M.next q (some a, some b)) xs ys +
        M.weight q (some a, none) * sumDPAux n (M.next q (some a, none)) xs (b :: ys) +
        M.weight q (none, some b) * sumDPAux n (M.next q (none, some b)) (a :: xs) ys

/-- The total weight of all alignments of `xs` and `ys` read from control state `q`, by the
first-column recursion (`sumDP_eq_sum`). -/
def sumDP (q : Q) (xs : List α) (ys : List β) : R :=
  sumDPAux M (xs.length + ys.length + 1) q xs ys

private theorem sumDPAux_eq_sum :
    ∀ (n : ℕ) (q : Q) (xs : List α) (ys : List β),
    sumDPAux M n q xs ys = ((alignmentsOfAux n xs ys).map (alignWeight M q)).sum
  | 0, q, xs, ys => by simp [sumDPAux, alignmentsOfAux]
  | n + 1, q, [], [] => by simp [sumDPAux, alignmentsOfAux, alignWeight]
  | n + 1, q, [], b :: ys => by
      simp [sumDPAux, alignmentsOfAux, alignWeight, sumDPAux_eq_sum n, Function.comp_def,
        List.sum_map_mul_left]
  | n + 1, q, a :: xs, [] => by
      simp [sumDPAux, alignmentsOfAux, alignWeight, sumDPAux_eq_sum n, Function.comp_def,
        List.sum_map_mul_left]
  | n + 1, q, a :: xs, b :: ys => by
      simp [sumDPAux, alignmentsOfAux, alignWeight, sumDPAux_eq_sum n, Function.comp_def,
        List.sum_map_mul_left, add_assoc]

/-- **The sum recursion is the sum over alignments.** -/
theorem sumDP_eq_sum (q : Q) (xs : List α) (ys : List β) :
    sumDP M q xs ys = ((alignmentsOf xs ys).map (alignWeight M q)).sum :=
  sumDPAux_eq_sum M _ q xs ys

/-- The sum recursion on two nonempty sequences. -/
theorem sumDP_cons_cons (q : Q) (a : α) (b : β) (xs : List α) (ys : List β) :
    sumDP M q (a :: xs) (b :: ys) =
      M.weight q (some a, some b) * sumDP M (M.next q (some a, some b)) xs ys +
        M.weight q (some a, none) * sumDP M (M.next q (some a, none)) xs (b :: ys) +
        M.weight q (none, some b) * sumDP M (M.next q (none, some b)) (a :: xs) ys := by
  simp only [sumDP_eq_sum, alignmentsOf_cons_cons, List.map_append, List.sum_append,
    List.map_map, Function.comp_def, alignWeight, List.sum_map_mul_left]

/-- The sum recursion when the first sequence is empty. -/
theorem sumDP_nil_cons (q : Q) (b : β) (ys : List β) :
    sumDP M q ([] : List α) (b :: ys) =
      M.weight q (none, some b) * sumDP M (M.next q (none, some b)) [] ys := by
  simp only [sumDP_eq_sum, alignmentsOf_nil_cons, List.map_map, Function.comp_def, alignWeight,
    List.sum_map_mul_left]

/-- The sum recursion when the second sequence is empty. -/
theorem sumDP_cons_nil (q : Q) (a : α) (xs : List α) :
    sumDP M q (a :: xs) ([] : List β) =
      M.weight q (some a, none) * sumDP M (M.next q (some a, none)) xs [] := by
  simp only [sumDP_eq_sum, alignmentsOf_cons_nil, List.map_map, Function.comp_def, alignWeight,
    List.sum_map_mul_left]

/-- The sum recursion on two empty sequences is the final weight. -/
theorem sumDP_nil_nil (q : Q) : sumDP M q ([] : List α) ([] : List β) = M.final q := rfl

end Semiring

section Max

variable [Semiring R] [LinearOrder R] (M : AlignmentAutomaton Q α β R)

/-- The max recursion with fuel. Implementation detail: use `maxDP`. -/
def maxDPAux : ℕ → Q → List α → List β → R
  | 0, _, _, _ => 0
  | _ + 1, q, [], [] => M.final q
  | n + 1, q, [], b :: ys =>
      M.weight q (none, some b) * maxDPAux n (M.next q (none, some b)) [] ys
  | n + 1, q, a :: xs, [] =>
      M.weight q (some a, none) * maxDPAux n (M.next q (some a, none)) xs []
  | n + 1, q, a :: xs, b :: ys =>
      max (max (M.weight q (some a, some b) * maxDPAux n (M.next q (some a, some b)) xs ys)
        (M.weight q (some a, none) * maxDPAux n (M.next q (some a, none)) xs (b :: ys)))
        (M.weight q (none, some b) * maxDPAux n (M.next q (none, some b)) (a :: xs) ys)

/-- The max-recursion value of an alignment of `xs` and `ys` read from control state `q`, by
the first-column recursion (`alignWeight_le_maxDP`, `exists_alignWeight_eq_maxDP`). It is the
largest alignment weight only when the weights are nonnegative; in general it is the value of
the recursively chosen alignment. -/
def maxDP (q : Q) (xs : List α) (ys : List β) : R :=
  maxDPAux M (xs.length + ys.length + 1) q xs ys

/-- Nonnegative column weights. The final weights may have any sign: the max recursion bounds
every alignment weight without that (`alignWeight_le_maxDP`). -/
def Nonneg : Prop := ∀ q c, 0 ≤ M.weight q c

private theorem maxDPAux_succ : ∀ (m : ℕ) (q : Q) (xs : List α) (ys : List β),
    xs.length + ys.length < m → maxDPAux M (m + 1) q xs ys = maxDPAux M m q xs ys
  | 0, _, xs, ys, h => by omega
  | m + 1, q, [], [], _ => by simp [maxDPAux]
  | m + 1, q, [], b :: ys, h => by
      simp only [maxDPAux]
      rw [maxDPAux_succ m _ [] ys (by simp at h ⊢; omega)]
  | m + 1, q, a :: xs, [], h => by
      simp only [maxDPAux]
      rw [maxDPAux_succ m _ xs [] (by simp at h ⊢; omega)]
  | m + 1, q, a :: xs, b :: ys, h => by
      simp only [List.length_cons] at h
      simp only [maxDPAux]
      rw [maxDPAux_succ m _ xs ys (by omega), maxDPAux_succ m _ xs (b :: ys)
        (by simp; omega), maxDPAux_succ m _ (a :: xs) ys (by simp; omega)]

private theorem maxDPAux_eq (m : ℕ) (q : Q) (xs : List α) (ys : List β)
    (h : xs.length + ys.length < m) : maxDPAux M m q xs ys = maxDP M q xs ys := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · rw [maxDPAux_succ M m q xs ys h, ih h]
      · rw [maxDP, h]

private theorem alignWeight_le_maxDPAux [IsOrderedRing R] {M : AlignmentAutomaton Q α β R}
    (hM : M.Nonneg) : ∀ (n : ℕ) (q : Q) (xs : List α) (ys : List β)
    (A : List (Option α × Option β)), A ∈ alignmentsOfAux n xs ys →
    alignWeight M q A ≤ maxDPAux M n q xs ys
  | 0, _, _, _, _, hA => by simp [alignmentsOfAux] at hA
  | n + 1, q, [], [], A, hA => by
      simp only [alignmentsOfAux, List.mem_singleton] at hA
      subst hA; simp [alignWeight, maxDPAux]
  | n + 1, q, [], b :: ys, A, hA => by
      simp only [alignmentsOfAux, List.mem_map] at hA
      obtain ⟨A, hA, rfl⟩ := hA
      exact mul_le_mul_of_nonneg_left (alignWeight_le_maxDPAux hM n _ _ _ A hA) (hM _ _)
  | n + 1, q, a :: xs, [], A, hA => by
      simp only [alignmentsOfAux, List.mem_map] at hA
      obtain ⟨A, hA, rfl⟩ := hA
      exact mul_le_mul_of_nonneg_left (alignWeight_le_maxDPAux hM n _ _ _ A hA) (hM _ _)
  | n + 1, q, a :: xs, b :: ys, A, hA => by
      simp only [alignmentsOfAux, List.mem_append, List.mem_map] at hA
      simp only [maxDPAux]
      rcases hA with (⟨A, hA, rfl⟩ | ⟨A, hA, rfl⟩) | ⟨A, hA, rfl⟩
      · exact le_max_of_le_left (le_max_of_le_left (mul_le_mul_of_nonneg_left
          (alignWeight_le_maxDPAux hM n _ _ _ A hA) (hM _ _)))
      · exact le_max_of_le_left (le_max_of_le_right (mul_le_mul_of_nonneg_left
          (alignWeight_le_maxDPAux hM n _ _ _ A hA) (hM _ _)))
      · exact le_max_of_le_right (mul_le_mul_of_nonneg_left
          (alignWeight_le_maxDPAux hM n _ _ _ A hA) (hM _ _))

private theorem exists_alignWeight_eq_maxDPAux : ∀ (n : ℕ) (q : Q) (xs : List α) (ys : List β),
    xs.length + ys.length < n →
    ∃ A ∈ alignmentsOfAux n xs ys, alignWeight M q A = maxDPAux M n q xs ys
  | 0, _, _, _, h => by omega
  | n + 1, q, [], [], _ => ⟨[], by simp [alignmentsOfAux], by simp [alignWeight, maxDPAux]⟩
  | n + 1, q, [], b :: ys, h => by
      obtain ⟨A, hA, hw⟩ := exists_alignWeight_eq_maxDPAux n (M.next q (none, some b)) [] ys
        (by simp at h ⊢; omega)
      exact ⟨_, List.mem_map_of_mem hA, by simp [alignWeight, maxDPAux, hw]⟩
  | n + 1, q, a :: xs, [], h => by
      obtain ⟨A, hA, hw⟩ := exists_alignWeight_eq_maxDPAux n (M.next q (some a, none)) xs []
        (by simp at h ⊢; omega)
      exact ⟨_, List.mem_map_of_mem hA, by simp [alignWeight, maxDPAux, hw]⟩
  | n + 1, q, a :: xs, b :: ys, h => by
      simp only [List.length_cons] at h
      obtain ⟨A1, h1, w1⟩ := exists_alignWeight_eq_maxDPAux n (M.next q (some a, some b)) xs ys
        (by omega)
      obtain ⟨A2, h2, w2⟩ := exists_alignWeight_eq_maxDPAux n (M.next q (some a, none)) xs
        (b :: ys) (by simp; omega)
      obtain ⟨A3, h3, w3⟩ := exists_alignWeight_eq_maxDPAux n (M.next q (none, some b))
        (a :: xs) ys (by simp; omega)
      simp only [maxDPAux, alignmentsOfAux, List.mem_append, List.mem_map]
      rcases max_choice (max (M.weight q (some a, some b) *
          maxDPAux M n (M.next q (some a, some b)) xs ys)
          (M.weight q (some a, none) * maxDPAux M n (M.next q (some a, none)) xs (b :: ys)))
          (M.weight q (none, some b) * maxDPAux M n (M.next q (none, some b)) (a :: xs) ys)
          with hm | hm <;> rw [hm]
      · rcases max_choice (M.weight q (some a, some b) *
            maxDPAux M n (M.next q (some a, some b)) xs ys)
            (M.weight q (some a, none) * maxDPAux M n (M.next q (some a, none)) xs (b :: ys))
            with hm' | hm' <;> rw [hm']
        · exact ⟨_, Or.inl (Or.inl ⟨A1, h1, rfl⟩), by simp [alignWeight, w1]⟩
        · exact ⟨_, Or.inl (Or.inr ⟨A2, h2, rfl⟩), by simp [alignWeight, w2]⟩
      · exact ⟨_, Or.inr ⟨A3, h3, rfl⟩, by simp [alignWeight, w3]⟩

/-- **Every alignment weighs at most the max recursion** (nonnegative weights). -/
theorem alignWeight_le_maxDP [IsOrderedRing R] {M : AlignmentAutomaton Q α β R}
    (hM : M.Nonneg) (q : Q) {xs : List α} {ys : List β} {A : List (Option α × Option β)}
    (hA : A ∈ alignmentsOf xs ys) :
    alignWeight M q A ≤ maxDP M q xs ys :=
  alignWeight_le_maxDPAux hM _ q xs ys A hA

/-- **The max recursion is attained** by an alignment. -/
theorem exists_alignWeight_eq_maxDP (q : Q) (xs : List α) (ys : List β) :
    ∃ A ∈ alignmentsOf xs ys, alignWeight M q A = maxDP M q xs ys :=
  exists_alignWeight_eq_maxDPAux M _ q xs ys (Nat.lt_succ_self _)

/-- The max recursion on two nonempty sequences. -/
theorem maxDP_cons_cons (q : Q) (a : α) (b : β) (xs : List α) (ys : List β) :
    maxDP M q (a :: xs) (b :: ys) =
      max (max (M.weight q (some a, some b) * maxDP M (M.next q (some a, some b)) xs ys)
        (M.weight q (some a, none) * maxDP M (M.next q (some a, none)) xs (b :: ys)))
        (M.weight q (none, some b) * maxDP M (M.next q (none, some b)) (a :: xs) ys) := by
  rw [maxDP, show (a :: xs).length + (b :: ys).length + 1 =
    (xs.length + ys.length + 1 + 1) + 1 by simp; omega, maxDPAux,
    maxDPAux_eq M _ _ xs ys (by omega), maxDPAux_eq M _ _ xs (b :: ys) (by simp; omega),
    maxDPAux_eq M _ _ (a :: xs) ys (by simp; omega)]

/-- The max recursion when the first sequence is empty. -/
theorem maxDP_nil_cons (q : Q) (b : β) (ys : List β) :
    maxDP M q ([] : List α) (b :: ys) =
      M.weight q (none, some b) * maxDP M (M.next q (none, some b)) [] ys := by
  rw [maxDP, show ([] : List α).length + (b :: ys).length + 1 = (ys.length + 1) + 1 by simp,
    maxDPAux, maxDPAux_eq M _ _ [] ys (by simp)]

/-- The max recursion when the second sequence is empty. -/
theorem maxDP_cons_nil (q : Q) (a : α) (xs : List α) :
    maxDP M q (a :: xs) ([] : List β) =
      M.weight q (some a, none) * maxDP M (M.next q (some a, none)) xs [] := by
  rw [maxDP, show (a :: xs).length + ([] : List β).length + 1 = (xs.length + 1) + 1 by simp,
    maxDPAux, maxDPAux_eq M _ _ xs [] (by simp)]

/-- The max recursion on two empty sequences is the final weight. -/
theorem maxDP_nil_nil (q : Q) : maxDP M q ([] : List α) ([] : List β) = M.final q := rfl

end Max

end AlignmentAutomaton

/-! ## Pair HMMs -/

/-- The emitting states of a pair HMM: `M` emits an aligned pair, `X` a letter of the first
sequence only, `Y` a letter of the second sequence only. -/
inductive PairState
  /-- Emit an aligned pair `(a, b)`. -/
  | M
  /-- Emit a letter of the first sequence against a gap. -/
  | X
  /-- Emit a letter of the second sequence against a gap. -/
  | Y
  deriving DecidableEq, Repr

/-- The state that emits an alignment column: `M` for `(some a, some b)`, `X` for
`(some a, none)`, `Y` for `(none, some b)` (and `M`, unused, for the invalid `(none, none)`). -/
def colState {α : Type*} : Option α × Option α → PairState
  | (some _, none) => .X
  | (none, some _) => .Y
  | _ => .M

/-- A pair HMM over the alphabet `α` with weights in `R` (Durbin et al., chapter 4): the
transition weights from the silent begin state (`start`) and between emitting states (`trans`),
to the silent end state (`stop` from an emitting state, `startStop` for the empty alignment),
and the emission weights of the three emitting states. -/
structure PairHMM (α R : Type*) where
  /-- The weight of the transition from the begin state to an emitting state. -/
  start : PairState → R
  /-- The weight of the transition from the begin state directly to the end state. -/
  startStop : R
  /-- The weight of a transition between emitting states (from the first to the second). -/
  trans : PairState → PairState → R
  /-- The weight of the transition from an emitting state to the end state. -/
  stop : PairState → R
  /-- The emission weight of an aligned pair from `M`. -/
  emitM : α → α → R
  /-- The emission weight of a letter of the first sequence from `X`. -/
  emitX : α → R
  /-- The emission weight of a letter of the second sequence from `Y`. -/
  emitY : α → R

namespace PairHMM

variable {α R : Type*}

section Semiring

variable [Semiring R] (h : PairHMM α R)

/-- The emission weight of an alignment column (`0` for the invalid `(none, none)`). -/
def emitCol : Option α × Option α → R
  | (some a, some b) => h.emitM a b
  | (some a, none) => h.emitX a
  | (none, some b) => h.emitY b
  | (none, none) => 0

/-- The pair HMM as an alignment automaton: the control state is the previous HMM state
(`none` for the begin state). -/
def toAutomaton : AlignmentAutomaton (Option PairState) α α R where
  weight q c := (match q with
    | none => h.start (colState c)
    | some s => h.trans s (colState c)) * h.emitCol c
  next _ c := some (colState c)
  final q := match q with
    | none => h.startStop
    | some s => h.stop s

/-- The joint weight of the sequences and the state path of an alignment `A` (the path visits
`colState c` for each column `c`): the product of the transition and emission weights along the
path, from the begin state to the end state. -/
def alignProb (A : Alignment α) : R := h.toAutomaton.alignWeight none A

/-- The full probability `P(xs, ys)` of a pair HMM: the total weight of all state paths that emit
`xs` and `ys` (`likelihood_eq_sum`), by the first-column recursion. -/
def likelihood (xs ys : List α) : R := h.toAutomaton.sumDP none xs ys

/-- **The pair-HMM recursion computes the full probability**: the sum over all alignments of
`xs` and `ys` of the joint weight of the sequences and the alignment. -/
theorem likelihood_eq_sum (xs ys : List α) :
    h.likelihood xs ys = ((alignments xs ys).map h.alignProb).sum := by
  rw [likelihood, AlignmentAutomaton.sumDP_eq_sum, alignmentsOf_eq_alignments]
  rfl

end Semiring

section Viterbi

variable [Semiring R] [LinearOrder R] (h : PairHMM α R)

/-- The Viterbi value of a pair HMM: the max-recursion value for `xs`, `ys`. It is the
largest joint weight over alignments when the HMM weights are nonnegative
(see `alignProb_le_viterbi`). -/
def viterbi (xs ys : List α) : R := h.toAutomaton.maxDP none xs ys

/-- Nonnegative transition weights into emitting states and nonnegative emission weights (the
transitions into the end state may have any sign: the Viterbi bound does not need them). -/
structure Nonneg : Prop where
  /-- Begin-state transitions are nonnegative. -/
  start : ∀ s, 0 ≤ h.start s
  /-- Transitions between emitting states are nonnegative. -/
  trans : ∀ s t, 0 ≤ h.trans s t
  /-- Match emissions are nonnegative. -/
  emitM : ∀ a b, 0 ≤ h.emitM a b
  /-- `X` emissions are nonnegative. -/
  emitX : ∀ a, 0 ≤ h.emitX a
  /-- `Y` emissions are nonnegative. -/
  emitY : ∀ b, 0 ≤ h.emitY b

variable {h}

/-- A pair HMM with nonnegative weights is a nonnegative alignment automaton. -/
theorem toAutomaton_nonneg [IsOrderedRing R] (hn : h.Nonneg) : h.toAutomaton.Nonneg := by
  intro q c
  refine mul_nonneg ?_ ?_
  · rcases q with _ | s
    exacts [hn.start _, hn.trans _ _]
  · rcases c with ⟨_ | a, _ | b⟩
    exacts [le_rfl, hn.emitY _, hn.emitX _, hn.emitM _ _]

/-- **Every alignment weighs at most the Viterbi value.** -/
theorem alignProb_le_viterbi [IsOrderedRing R] (hn : h.Nonneg) {xs ys : List α} {A : Alignment α}
    (hA : IsAlignment A xs ys) : h.alignProb A ≤ h.viterbi xs ys :=
  AlignmentAutomaton.alignWeight_le_maxDP (toAutomaton_nonneg hn) none
    (by rwa [alignmentsOf_eq_alignments, mem_alignments])

variable (h) in
/-- **The Viterbi value is attained** by an alignment: the Viterbi alignment. -/
theorem exists_alignProb_eq_viterbi (xs ys : List α) :
    ∃ A, IsAlignment A xs ys ∧ h.alignProb A = h.viterbi xs ys := by
  obtain ⟨A, hA, hw⟩ := h.toAutomaton.exists_alignWeight_eq_maxDP none xs ys
  rw [alignmentsOf_eq_alignments, mem_alignments] at hA
  exact ⟨A, hA, hw⟩

end Viterbi

/-! ## Log-odds scores and Needleman–Wunsch -/

section LogOdds

/-- The pair HMM's transition weights do not depend on the current state: every transition into
an emitting state `s` (from the begin state or from any emitting state) has weight `π s`, and
every transition into the end state has weight `τ`. -/
structure IsMemoryless (h : PairHMM α ℝ) (π : PairState → ℝ) (τ : ℝ) : Prop where
  /-- Begin-state transitions. -/
  start : ∀ s, h.start s = π s
  /-- Transitions between emitting states. -/
  trans : ∀ s t, h.trans s t = π t
  /-- Transitions to the end state from an emitting state. -/
  stop : ∀ s, h.stop s = τ
  /-- The begin-to-end transition. -/
  startStop : h.startStop = τ

/-- The probability of `xs` and `ys` under the independence (random) model of Durbin et al.,
chapter 4: each sequence has a geometric length with stopping probability `η` and independent
letters with background frequencies `q`, so
`P(xs, ys | R) = η² (1 - η)^(|xs| + |ys|) ∏ q xs ∏ q ys`. -/
noncomputable def background (q : α → ℝ) (η : ℝ) (xs ys : List α) : ℝ :=
  η ^ 2 * (1 - η) ^ (xs.length + ys.length) * (xs.map q).prod * (ys.map q).prod

/-- The hypotheses of the log-odds correspondence: a memoryless pair HMM with positive weights,
positive background frequencies and `0 < η < 1`, whose per-column log-odds scores against the
independence model are the integer scores `σ a b` (aligned pair) and `gap` (gap column). -/
structure LinearGapLogOdds (h : PairHMM α ℝ) (π : PairState → ℝ) (τ : ℝ) (q : α → ℝ) (η : ℝ)
    (σ : α → α → ℤ) (gap : ℤ) : Prop where
  /-- The transition weights do not depend on the current state. -/
  memoryless : h.IsMemoryless π τ
  /-- Positive transition weights. -/
  π_pos : ∀ s, 0 < π s
  /-- A positive end transition. -/
  τ_pos : 0 < τ
  /-- Positive background frequencies. -/
  q_pos : ∀ a, 0 < q a
  /-- The background stopping probability is in `(0, 1)`. -/
  η_pos : 0 < η
  /-- The background stopping probability is in `(0, 1)`. -/
  η_lt_one : η < 1
  /-- Positive match emissions. -/
  emitM_pos : ∀ a b, 0 < h.emitM a b
  /-- Positive `X` emissions. -/
  emitX_pos : ∀ a, 0 < h.emitX a
  /-- Positive `Y` emissions. -/
  emitY_pos : ∀ b, 0 < h.emitY b
  /-- The log-odds score of an aligned pair is `σ a b`. -/
  logOdds_M : ∀ a b,
    Real.log (π .M * h.emitM a b / ((1 - η) ^ 2 * q a * q b)) = σ a b
  /-- The log-odds score of a letter of the first sequence against a gap is `gap`. -/
  logOdds_X : ∀ a, Real.log (π .X * h.emitX a / ((1 - η) * q a)) = gap
  /-- The log-odds score of a letter of the second sequence against a gap is `gap`. -/
  logOdds_Y : ∀ b, Real.log (π .Y * h.emitY b / ((1 - η) * q b)) = gap

/-- The background factors of the letters of an alignment (without the `η²` end term). -/
private noncomputable def denom (q : α → ℝ) (η : ℝ) (A : Alignment α) : ℝ :=
  (1 - η) ^ ((A.filterMap Prod.fst).length + (A.filterMap Prod.snd).length) *
    ((A.filterMap Prod.fst).map q).prod * ((A.filterMap Prod.snd).map q).prod

private theorem log_alignWeight_div_denom {h : PairHMM α ℝ} {π : PairState → ℝ} {τ : ℝ}
    {q : α → ℝ} {η : ℝ} {σ : α → α → ℤ} {gap : ℤ} (H : LinearGapLogOdds h π τ q η σ gap) :
    ∀ (A : Alignment α), (∀ c ∈ A, c ≠ (none, none)) → ∀ r : Option PairState,
      0 < h.toAutomaton.alignWeight r A ∧ 0 < denom q η A ∧
      Real.log (h.toAutomaton.alignWeight r A / denom q η A) =
        alignmentScore σ gap A + Real.log τ
  | [], _, r => by
      have hf : h.toAutomaton.alignWeight r [] = τ := by
        rcases r with _ | s
        · exact H.memoryless.startStop
        · exact H.memoryless.stop s
      simp [hf, denom, alignmentScore, H.τ_pos]
  | (none, none) :: A, hA, _ => absurd rfl (hA _ List.mem_cons_self)
  | (some a, some b) :: A, hA, r => by
      obtain ⟨h1, h2, h3⟩ := log_alignWeight_div_denom H A
        (fun c hc => hA c (List.mem_cons_of_mem _ hc)) (some .M)
      have hw : h.toAutomaton.alignWeight r ((some a, some b) :: A) =
          π .M * h.emitM a b * h.toAutomaton.alignWeight (some .M) A := by
        rcases r with _ | s
        · simp [AlignmentAutomaton.alignWeight, toAutomaton, colState, emitCol,
            H.memoryless.start]
        · simp [AlignmentAutomaton.alignWeight, toAutomaton, colState, emitCol,
            H.memoryless.trans]
      have hd : denom q η ((some a, some b) :: A) =
          ((1 - η) ^ 2 * q a * q b) * denom q η A := by
        simp [denom, pow_succ]
        ring
      have hη : 0 < 1 - η := by linarith [H.η_lt_one]
      have hc : 0 < (1 - η) ^ 2 * q a * q b := by
        have := H.q_pos a; have := H.q_pos b; positivity
      have hm : 0 < π .M * h.emitM a b := mul_pos (H.π_pos _) (H.emitM_pos a b)
      refine ⟨by rw [hw]; exact mul_pos hm h1, by rw [hd]; exact mul_pos hc h2, ?_⟩
      rw [hw, hd, show π .M * h.emitM a b * h.toAutomaton.alignWeight (some .M) A /
          ((1 - η) ^ 2 * q a * q b * denom q η A) =
          (π .M * h.emitM a b / ((1 - η) ^ 2 * q a * q b)) *
            (h.toAutomaton.alignWeight (some .M) A / denom q η A) by
          field_simp,
        Real.log_mul (div_pos hm hc).ne' (div_pos h1 h2).ne', H.logOdds_M, h3]
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore]
      push_cast; ring
  | (some a, none) :: A, hA, r => by
      obtain ⟨h1, h2, h3⟩ := log_alignWeight_div_denom H A
        (fun c hc => hA c (List.mem_cons_of_mem _ hc)) (some .X)
      have hw : h.toAutomaton.alignWeight r ((some a, none) :: A) =
          π .X * h.emitX a * h.toAutomaton.alignWeight (some .X) A := by
        rcases r with _ | s
        · simp [AlignmentAutomaton.alignWeight, toAutomaton, colState, emitCol,
            H.memoryless.start]
        · simp [AlignmentAutomaton.alignWeight, toAutomaton, colState, emitCol,
            H.memoryless.trans]
      have hd : denom q η ((some a, none) :: A) = ((1 - η) * q a) * denom q η A := by
        simp [denom]
        ring
      have hη : 0 < 1 - η := by linarith [H.η_lt_one]
      have hc : 0 < (1 - η) * q a := mul_pos hη (H.q_pos a)
      have hm : 0 < π .X * h.emitX a := mul_pos (H.π_pos _) (H.emitX_pos a)
      refine ⟨by rw [hw]; exact mul_pos hm h1, by rw [hd]; exact mul_pos hc h2, ?_⟩
      rw [hw, hd, show π .X * h.emitX a * h.toAutomaton.alignWeight (some .X) A /
          ((1 - η) * q a * denom q η A) =
          (π .X * h.emitX a / ((1 - η) * q a)) *
            (h.toAutomaton.alignWeight (some .X) A / denom q η A) by
          field_simp,
        Real.log_mul (div_pos hm hc).ne' (div_pos h1 h2).ne', H.logOdds_X, h3]
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore]
      push_cast; ring
  | (none, some b) :: A, hA, r => by
      obtain ⟨h1, h2, h3⟩ := log_alignWeight_div_denom H A
        (fun c hc => hA c (List.mem_cons_of_mem _ hc)) (some .Y)
      have hw : h.toAutomaton.alignWeight r ((none, some b) :: A) =
          π .Y * h.emitY b * h.toAutomaton.alignWeight (some .Y) A := by
        rcases r with _ | s
        · simp [AlignmentAutomaton.alignWeight, toAutomaton, colState, emitCol,
            H.memoryless.start]
        · simp [AlignmentAutomaton.alignWeight, toAutomaton, colState, emitCol,
            H.memoryless.trans]
      have hd : denom q η ((none, some b) :: A) = ((1 - η) * q b) * denom q η A := by
        simp [denom]
        ring
      have hη : 0 < 1 - η := by linarith [H.η_lt_one]
      have hc : 0 < (1 - η) * q b := mul_pos hη (H.q_pos b)
      have hm : 0 < π .Y * h.emitY b := mul_pos (H.π_pos _) (H.emitY_pos b)
      refine ⟨by rw [hw]; exact mul_pos hm h1, by rw [hd]; exact mul_pos hc h2, ?_⟩
      rw [hw, hd, show π .Y * h.emitY b * h.toAutomaton.alignWeight (some .Y) A /
          ((1 - η) * q b * denom q η A) =
          (π .Y * h.emitY b / ((1 - η) * q b)) *
            (h.toAutomaton.alignWeight (some .Y) A / denom q η A) by
          field_simp,
        Real.log_mul (div_pos hm hc).ne' (div_pos h1 h2).ne', H.logOdds_Y, h3]
      simp only [alignmentScore, List.map_cons, List.sum_cons, columnScore]
      push_cast; ring


private theorem background_eq {q : α → ℝ} {η : ℝ} {xs ys : List α} {A : Alignment α}
    (hA : IsAlignment A xs ys) : background q η xs ys = η ^ 2 * denom q η A := by
  obtain ⟨-, rfl, rfl⟩ := hA
  simp only [background, denom]
  ring

/-- **Log-odds of one alignment**: for a memoryless pair HMM, the log-odds of an alignment
against the independence model is its linear-gap alignment score plus `log (τ / η²)`. -/
theorem log_alignProb_div_background {h : PairHMM α ℝ} {π : PairState → ℝ} {τ : ℝ}
    {q : α → ℝ} {η : ℝ} {σ : α → α → ℤ} {gap : ℤ} (H : LinearGapLogOdds h π τ q η σ gap)
    {xs ys : List α} {A : Alignment α} (hA : IsAlignment A xs ys) :
    Real.log (h.alignProb A / background q η xs ys) =
      alignmentScore σ gap A + Real.log (τ / η ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := log_alignWeight_div_denom H A hA.1 none
  have hη : 0 < η ^ 2 := pow_pos H.η_pos 2
  rw [background_eq hA, alignProb, show h.toAutomaton.alignWeight none A / (η ^ 2 * denom q η A) =
      (h.toAutomaton.alignWeight none A / denom q η A) / η ^ 2 by rw [div_div, mul_comm],
    Real.log_div (div_pos h1 h2).ne' hη.ne', h3, Real.log_div H.τ_pos.ne' hη.ne']
  ring

private theorem nonneg_of_linearGapLogOdds {h : PairHMM α ℝ} {π : PairState → ℝ} {τ : ℝ}
    {q : α → ℝ} {η : ℝ} {σ : α → α → ℤ} {gap : ℤ} (H : LinearGapLogOdds h π τ q η σ gap) :
    h.Nonneg where
  start s := (H.memoryless.start s).symm ▸ (H.π_pos s).le
  trans s t := (H.memoryless.trans s t).symm ▸ (H.π_pos t).le
  emitM a b := (H.emitM_pos a b).le
  emitX a := (H.emitX_pos a).le
  emitY b := (H.emitY_pos b).le

/-- **Log-odds Viterbi is linear-gap Needleman–Wunsch**: for a memoryless pair HMM whose
per-column log-odds scores are `σ a b` and `gap`, the log-odds Viterbi score against the
independence model is the Needleman–Wunsch score with substitution scores `σ` and linear gap
score `gap`, plus the length term `log (τ / η²)`. -/
theorem log_viterbi_div_background {h : PairHMM α ℝ} {π : PairState → ℝ} {τ : ℝ}
    {q : α → ℝ} {η : ℝ} {σ : α → α → ℤ} {gap : ℤ} (H : LinearGapLogOdds h π τ q η σ gap)
    (xs ys : List α) :
    Real.log (h.viterbi xs ys / background q η xs ys) =
      nwScore σ gap xs ys + Real.log (τ / η ^ 2) := by
  obtain ⟨A, hA, hAv⟩ := h.exists_alignProb_eq_viterbi xs ys
  obtain ⟨A₀, hA₀, hA₀s⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
  have hB : 0 < background q η xs ys := by
    rw [background_eq hA]
    exact mul_pos (pow_pos H.η_pos 2) (log_alignWeight_div_denom H A hA.1 none).2.1
  have hpos : ∀ {A : Alignment α}, IsAlignment A xs ys → 0 < h.alignProb A :=
    fun hA => (log_alignWeight_div_denom H _ hA.1 none).1
  refine le_antisymm ?_ ?_
  · rw [← hAv, log_alignProb_div_background H hA]
    have := alignmentScore_le_nwScore σ gap xs ys A hA
    have : (alignmentScore σ gap A : ℝ) ≤ nwScore σ gap xs ys := by exact_mod_cast this
    linarith
  · rw [← hA₀s, ← log_alignProb_div_background H hA₀]
    refine Real.log_le_log (div_pos (hpos hA₀) hB) ?_
    exact div_le_div_of_nonneg_right
      (alignProb_le_viterbi (nonneg_of_linearGapLogOdds H) hA₀) hB.le

end LogOdds

end PairHMM

end Cslib.Bioinformatics.HMM
