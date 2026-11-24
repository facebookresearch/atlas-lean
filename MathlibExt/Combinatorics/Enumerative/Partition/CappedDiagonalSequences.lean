/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
import all MathlibExt.Combinatorics.Enumerative.Partition.TruncateDiagonalSequences
import all MathlibExt.Combinatorics.Enumerative.Partition.ExtremalDiagonalSequences

/-!
# Capping multiplicities in a diagonal sequence

Capping each multiplicity after the initial staircase at two preserves the number of
partitions with the prescribed diagonal sequence.
-/

namespace MetaMathlibExt
namespace card_diagonalClassOf_min_two

open Finset card_diagonalClassOf_truncate
open diagonalSequence_max_eq_min_and_multiset (blocks blocks_succ)

private def tail {m a d} (x : Layers m (a :: d)) : Layers (m + 1) d where
  row t := x.row (t + 1)
  bound := fun h => by have := x.bound h; omega
  size t := x.size (t + 1)
  prev := fun h hj => x.prev h (by omega)

/-- Attach a new first diagonal, given the predecessor condition at the join. -/
private def cons {m a d} (r : Finset ℕ) (hb : ∀ i ∈ r, i ≤ m) (hs : r.card = a)
    (y : Layers (m + 1) d)
    (hp : ∀ i ∈ y.row 0, ∀ j ≤ m, j ≤ i → i ≤ j + 1 → j ∈ r) : Layers m (a :: d) where
  row t := Nat.casesOn t r y.row
  bound := by
    intro t i hi
    cases t with
    | zero => exact hb i hi
    | succ t => have := y.bound hi; omega
  size t := by
    cases t with
    | zero => exact hs
    | succ t => exact y.size t
  prev := by
    intro t i j hi hj hji hij
    cases t with
    | zero => exact hp i hi j hj hji hij
    | succ t => exact y.prev hi (by omega) hji hij

-- In two equally large consecutive diagonals, project the second towards the first
-- gap of the first diagonal. Every cell projects to a predecessor and the sizes agree,
-- so the second diagonal is determined by the first.
private theorem second_row {m k d} (hk : k ≤ m) (x : Layers m (k :: k :: d)) :
    x.row 1 = (x.row 0).image (skip (gap x)) := by
  apply eq_of_subset_of_card_le
  · intro i hi
    have ha : gap x ≤ k := gap_le_size x
    have hn : i ≠ gap x := fun e => missing_later x (by omega) (gap_missing x) 1 (e ▸ hi)
    refine mem_image.mpr ⟨unskip (gap x) i, ?_, skip_unskip hn⟩
    have hb := x.bound hi
    apply x.prev (t := 0) hi <;> unfold unskip <;> split <;> omega
  · rw [card_image_of_injective _ (skip_inj _), x.size, x.size]
    rfl

private theorem gap_tail {m k d} (hk : k ≤ m) (x : Layers m (k :: k :: d)) :
    gap (tail x) = gap x := by
  apply gap_eq
  · exact missing_later x (le_trans (gap_le_size x) hk) (gap_missing x) 1
  · intro i hi
    change i ∈ x.row 1
    rw [second_row hk]
    exact mem_image.mpr ⟨i, before_gap hi, ite_eq_left hi⟩

-- An equivalence preserving the first diagonal can be applied after any fixed prefix.
private structure FirstEquiv (m : ℕ) (d e : List ℕ) where
  equiv : Layers m d ≃ Layers m e
  first : ∀ x, (equiv x).row 0 = x.row 0

private def refl (m : ℕ) (d : List ℕ) : FirstEquiv m d d :=
  ⟨Equiv.refl _, fun _ => rfl⟩

private def trans {m d e f} (u : FirstEquiv m d e) (v : FirstEquiv m e f) : FirstEquiv m d f :=
  ⟨u.equiv.trans v.equiv, fun x => (v.first _).trans (u.first x)⟩

private def mapTail {m a d e} (f : Layers (m + 1) d → Layers (m + 1) e)
    (hf : ∀ x, (f x).row 0 = x.row 0) (x : Layers m (a :: d)) : Layers m (a :: e) :=
  cons (x.row 0) (fun _ h => x.bound h) (x.size 0) (f (tail x)) (by
    intro i hi j hj hji hij
    rw [hf] at hi
    exact x.prev (t := 0) hi hj hji hij)

private def consEquiv {m d e} (a : ℕ) (u : FirstEquiv (m + 1) d e) :
    FirstEquiv m (a :: d) (a :: e) where
  equiv := {
    toFun := mapTail u.equiv u.first
    invFun := mapTail u.equiv.symm fun x => by simpa using (u.first (u.equiv.symm x)).symm
    left_inv := by
      intro x
      apply layers_ext
      intro t
      cases t with
      | zero => rfl
      | succ t => exact congrArg (fun y => y.row t) (u.equiv.symm_apply_apply (tail x))
    right_inv := by
      intro x
      apply layers_ext
      intro t
      cases t with
      | zero => rfl
      | succ t => exact congrArg (fun y => y.row t) (u.equiv.apply_symm_apply (tail x)) }
  first _ := rfl

-- Deleting the first of three equal diagonals leaves two equal diagonals, on which
-- staircase truncation closes a gap. Its inverse widens the gap and restores the head.
private def eraseCopy {m k d} (hk : k ≤ m) : FirstEquiv m (k :: k :: k :: d) (k :: k :: d) := by
  let u := insertStep (d := d) hk
  have first (x : Layers m (k :: k :: k :: d)) : (u.symm (tail x)).row 0 = x.row 0 := by
    change ((x.row 1).image (unskip (gap (tail x)))) = x.row 0
    rw [gap_tail hk, second_row hk, image_image]
    simp [Function.comp_def, unskip_skip]
  let restore (y : Layers m (k :: k :: d)) : Layers m (k :: k :: k :: d) :=
    cons (y.row 0) (fun _ h => y.bound h) (y.size 0) (u y) (by
      intro i hi j hj hji hij
      change i ∈ (y.row 0).image (skip (gap y)) at hi
      rw [← second_row hk y] at hi
      exact y.prev (t := 0) hi hj hji hij)
  refine ⟨⟨fun x => u.symm (tail x), restore, ?_, ?_⟩, first⟩
  · intro x
    apply layers_ext
    intro t
    cases t with
    | zero => exact first x
    | succ t => exact congrArg (fun y => y.row t) (u.apply_symm_apply (tail x))
  · intro y
    exact u.symm_apply_apply y

private def capBlock {m k} (hk : k ≤ m) (r : ℕ) (d : List ℕ) :
    FirstEquiv m (List.replicate r k ++ d) (List.replicate (min r 2) k ++ d) := by
  induction r with
  | zero => exact refl _ _
  | succ r ih =>
    rcases r with _ | _ | r
    · exact refl _ _
    · exact refl _ _
    · rw [min_eq_right (by omega)]
      rw [min_eq_right (by omega)] at ih
      exact trans (eraseCopy hk) ih

private def prefixEquiv {m d e} (p : List ℕ) (u : FirstEquiv (m + p.length) d e) :
    FirstEquiv m (p ++ d) (p ++ e) := by
  induction p generalizing m with
  | nil => exact u
  | cons a p ih =>
    apply consEquiv a
    apply ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using u

private def capBlocks (k m : ℕ) (hk : k ≤ m) (s : ℕ → ℕ) :
    FirstEquiv m (blocks k s) (blocks k fun i => min (s i) 2) := by
  induction k generalizing m with
  | zero => exact refl _ _
  | succ k ih =>
    rw [blocks_succ, blocks_succ]
    exact trans (capBlock hk _ _) (prefixEquiv _ (ih _ (by omega)))

end card_diagonalClassOf_min_two

open card_diagonalClassOf_min_two card_diagonalClassOf_truncate in
set_option linter.unusedVariables false in
/-- **Capping the multiplicities of a diagonal sequence at two.** For $m \ge 0$ and a sequence
$s = (s_1, s_2, \dots)$ of natural numbers, let $d(m, s)$ be the sequence
$(1, 2, \dots, m, m^{(s_m)}, (m-1)^{(s_{m-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$, and let $n(m, s) = m(m+1)/2 + \sum_{j=1}^{m} j s_j$. Let
$q \ge 1$ and $\sigma_j = \min(s_j, 2)$ for all $j$. Then the number of partitions of $n(q, s)$
with diagonal sequence $d(q, s)$ equals the number of partitions of $n(q, \sigma)$ with diagonal
sequence $d(q, \sigma)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (5). -/
public theorem card_diagonalClassOf_min_two (q : ℕ) (hq : 1 ≤ q) (s : ℕ → ℕ) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * min (s j) 2)
        (diagonalOfList (diagonalNormalForm q fun j => min (s j) 2))).card := by
  rw [class_card, class_card]
  exact Nat.card_congr (capBlocks q q le_rfl s).equiv

end MetaMathlibExt
