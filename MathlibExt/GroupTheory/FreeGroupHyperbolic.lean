/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Group.WordMetric
public import MathlibExt.Topology.MetricSpace.GromovHyperbolic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Free groups are zero-hyperbolic

The word metric of a free basis is zero-hyperbolic. After translating the basepoint to the
identity, the Gromov product is the length of the common prefix of two reduced words.
-/

namespace MathlibExt.GroupTheory.HyperbolicGroupWanted

open FreeGroup

section

variable {ι : Type*}

private abbrev basis (ι : Type*) : Group.Generators (FreeGroup ι) ι :=
  ⟨FreeGroup.of, FreeGroup.closure_range_of ι⟩

private theorem wordLength_eq_norm [DecidableEq ι] (x : FreeGroup ι) :
    (basis ι).wordLength x = FreeGroup.norm x := by
  have eval (w : List (ι × Bool)) : (basis ι).wordProd w = mk w := lift_of_apply _
  apply le_antisymm
  · exact ((basis ι).wordLength_le_iff x).2 ⟨x.toWord, le_rfl, (eval _).trans mk_toWord⟩
  · obtain ⟨w, hw, rfl⟩ := (basis ι).exists_isGeodesic x
    rw [hw.eq, eval]
    exact norm_mk_le

private def commonLength {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | a :: u, b :: v => if a = b then commonLength u v + 1 else 0
  | _, _ => 0

private theorem min_commonLength_le {α : Type*} [DecidableEq α] (u v w : List α) :
    min (commonLength u v) (commonLength v w) ≤ commonLength u w := by
  induction u generalizing v w with
  | nil => simp [commonLength]
  | cons a u ih =>
    cases v with
    | nil => simp [commonLength]
    | cons b v =>
      cases w with
      | nil => simp [commonLength]
      | cons c w =>
        by_cases hab : a = b <;> by_cases hbc : b = c <;>
          simp_all [commonLength]

-- If the initial letters differ, the inverse of the first word and the second word
-- meet without cancelling.
private theorem reduced_join {a b : ι × Bool} {u v : List (ι × Bool)}
    (hu : IsReduced (a :: u)) (hv : IsReduced (b :: v)) (hab : a ≠ b) :
    IsReduced (invRev (a :: u) ++ b :: v) := by
  classical
  have hi : IsReduced (invRev (a :: u)) :=
    .of_reduce_eq (by rw [reduce_invRev, hu.reduce_eq])
  apply List.IsChain.append hi hv
  obtain ⟨i, s⟩ := a
  obtain ⟨j, t⟩ := b
  suffices i = j → (!s) = t by simpa [invRev] using this
  rintro rfl
  cases s <;> cases t <;> simp_all

private theorem norm_inv_mul_add_commonLength [DecidableEq ι] (u v : List (ι × Bool))
    (hu : IsReduced u) (hv : IsReduced v) :
    FreeGroup.norm ((mk u)⁻¹ * mk v) + 2 * commonLength u v = u.length + v.length := by
  induction u generalizing v with
  | nil => simp [commonLength, FreeGroup.norm, hv.reduce_eq]
  | cons a u ih =>
    cases v with
    | nil => simp [commonLength, FreeGroup.norm, reduce_invRev, hu.reduce_eq]
    | cons b v =>
      by_cases hab : a = b
      · subst b
        have cancel : (mk (a :: u))⁻¹ * mk (a :: v) = (mk u)⁻¹ * mk v := by
          change (mk [a] * mk u)⁻¹ * (mk [a] * mk v) = _
          simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
        rw [cancel]
        have h := ih v (List.IsChain.tail hu) (List.IsChain.tail hv)
        simp only [commonLength, ↓reduceIte, List.length_cons]
        omega
      · have h := reduced_join hu hv hab
        simp [commonLength, hab, FreeGroup.norm, inv_mk, h.reduce_eq]

end

/-- **Free groups are `0`-hyperbolic** (Gromov, *Hyperbolic groups*, 1987, §1.1.D and §1.4: the
Cayley graph of a free group on a free basis is a simplicial tree, and simplicial trees are
`0`-hyperbolic). The word metric of `FreeGroup ι` with respect to the free basis `FreeGroup.of` is
`0`-hyperbolic. -/
public theorem freeGroup_isDeltaHyperbolic_zero (ι : Type*) :
    @Metric.IsDeltaHyperbolic (FreeGroup ι)
      (⟨FreeGroup.of, FreeGroup.closure_range_of ι⟩ :
        Group.Generators (FreeGroup ι) ι).normedGroup.toPseudoMetricSpace 0 := by
  classical
  let _ := (basis ι).normedGroup
  have hdist (x y : FreeGroup ι) : dist x y = (FreeGroup.norm (x⁻¹ * y) : ℝ) := by
    rw [dist_eq_norm_inv_mul]
    exact congrArg Nat.cast (wordLength_eq_norm _)
  have product (w x y : FreeGroup ι) : Metric.gromovProduct w x y =
      (commonLength (w⁻¹ * x).toWord (w⁻¹ * y).toWord : ℝ) := by
    have h := norm_inv_mul_add_commonLength (w⁻¹ * x).toWord (w⁻¹ * y).toWord
      isReduced_toWord isReduced_toWord
    simp only [mk_toWord, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h
    rw [Metric.gromovProduct_eq, hdist, hdist, hdist]
    have he : (FreeGroup.norm (x⁻¹ * y) : ℝ) +
        2 * (commonLength (w⁻¹ * x).toWord (w⁻¹ * y).toWord : ℝ) =
        (FreeGroup.norm (w⁻¹ * x) : ℝ) + FreeGroup.norm (w⁻¹ * y) := by
      exact_mod_cast h
    linarith
  refine ⟨le_rfl, fun w x y z => ?_⟩
  simp only [product, sub_zero]
  exact_mod_cast min_commonLength_le _ _ _

end MathlibExt.GroupTheory.HyperbolicGroupWanted
