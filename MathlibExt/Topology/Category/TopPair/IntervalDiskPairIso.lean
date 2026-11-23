/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.IntervalDiskPair
public import MathlibExt.Topology.Category.TopPair.Range
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# The interval--disk pair as a classical disk pair

This file identifies the literal pair `(I × Dⁿ, (∂I × Dⁿ) ∪ (I × Sⁿ⁻¹))`
with the max-norm classical `(n+1)`-disk pair.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory Topology

universe u

namespace Topology.CWComplex

/-- The real interval `[-1,1]` as the one-dimensional max-norm closed ball. -/
noncomputable def realIccClassicalCellDiskOneHomeomorph :
    Set.Icc (-1 : ℝ) 1 ≃ₜ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
  let e : ℝ ≃ᵢ (Fin 1 → ℝ) := (IsometryEquiv.funUnique (Fin 1) ℝ).symm
  exact e.toHomeomorph.sets (by
    change Set.Icc (-1 : ℝ) 1 = (e : ℝ → (Fin 1 → ℝ)) ⁻¹'
      Metric.closedBall 0 1
    rw [e.preimage_closedBall]
    change Set.Icc (-1 : ℝ) 1 = Metric.closedBall (0 : ℝ) 1
    rw [Real.closedBall_zero_eq_Icc])

@[simp]
theorem realIccClassicalCellDiskOneHomeomorph_val_apply
    (x : Set.Icc (-1 : ℝ) 1) (i : Fin 1) :
    (realIccClassicalCellDiskOneHomeomorph x).val i = x.val := by
  change ((IsometryEquiv.funUnique (Fin 1) ℝ).symm x.val) i = x.val
  rw [Subsingleton.elim i (default : Fin 1)]
  exact (IsometryEquiv.funUnique (Fin 1) ℝ).apply_symm_apply x.val

/-- The unit interval, affinely rescaled to the one-dimensional max-norm disk. -/
noncomputable def topCatIntervalClassicalCellDiskOneHomeomorph :
    TopCat.I.{u} ≃ₜ (classicalCellDiskPair.{u} 1).fst :=
  TopCat.I.homeomorph |>.trans
    ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm |>.trans
      (realIccClassicalCellDiskOneHomeomorph.trans Homeomorph.ulift.symm))

@[simp]
theorem topCatIntervalClassicalCellDiskOneHomeomorph_down_val
    (t : TopCat.I.{u}) :
    (topCatIntervalClassicalCellDiskOneHomeomorph t).down.val =
      fun _ ↦ 2 * (TopCat.I.homeomorph t : ℝ) - 1 := by
  ext i
  change (realIccClassicalCellDiskOneHomeomorph
    ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm
      (TopCat.I.homeomorph t))).val i = _
  rw [realIccClassicalCellDiskOneHomeomorph_val_apply,
    iccHomeoI_symm_apply_coe]
  ring

/-- Concatenation identifies the product of max-norm closed balls with a
max-norm closed ball in the concatenated coordinates. -/
noncomputable def closedBallProductAppendHomeomorph (n : ℕ) :
    Metric.closedBall (0 : Fin 1 → ℝ) 1 ×
        Metric.closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
  let e : (Fin 1 → ℝ) × (Fin n → ℝ) ≃ᵢ (Fin (n + 1) → ℝ) :=
    Fin.appendIsometryOfEq (Nat.one_add n)
  let eBall : Metric.closedBall (0 : (Fin 1 → ℝ) × (Fin n → ℝ)) 1 ≃ₜ
      Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
    e.toHomeomorph.sets (by
      change Metric.closedBall (0 : (Fin 1 → ℝ) × (Fin n → ℝ)) 1 =
        (e : ((Fin 1 → ℝ) × (Fin n → ℝ)) → (Fin (n + 1) → ℝ)) ⁻¹'
          Metric.closedBall 0 1
      rw [e.preimage_closedBall]
      have hzero : e.symm 0 = 0 := by
        apply e.injective
        simp [e, Fin.appendIsometryOfEq]
        constructor <;> rfl
      rw [hzero])
  exact (Homeomorph.Set.prod
      (Metric.closedBall (0 : Fin 1 → ℝ) 1)
      (Metric.closedBall (0 : Fin n → ℝ) 1)).symm |>.trans
    ((Homeomorph.setCongr
      (closedBall_prod_same (0 : Fin 1 → ℝ) (0 : Fin n → ℝ) 1)) |>.trans
        eBall)

@[simp]
theorem closedBallProductAppendHomeomorph_val
    (n : ℕ)
    (x : Metric.closedBall (0 : Fin 1 → ℝ) 1)
    (y : Metric.closedBall (0 : Fin n → ℝ) 1) :
    (closedBallProductAppendHomeomorph n (x, y)).val =
      Fin.appendIsometryOfEq (Nat.one_add n) (x.val, y.val) := by
  rfl

/-- Lifted concatenation homeomorphism for the ambient spaces of classical
cell disk pairs. -/
noncomputable def classicalCellDiskPairProductHomeomorph (n : ℕ) :
    (classicalCellDiskPair.{u} 1).fst ×
        (classicalCellDiskPair.{u} n).fst ≃ₜ
      (classicalCellDiskPair.{u} (n + 1)).fst :=
  (Homeomorph.ulift.prodCongr Homeomorph.ulift) |>.trans
    ((closedBallProductAppendHomeomorph n).trans Homeomorph.ulift.symm)

@[simp]
theorem classicalCellDiskPairProductHomeomorph_down_val
    (n : ℕ)
    (x : (classicalCellDiskPair.{u} 1).fst)
    (y : (classicalCellDiskPair.{u} n).fst) :
    (classicalCellDiskPairProductHomeomorph n (x, y)).down.val =
      Fin.appendIsometryOfEq (Nat.one_add n) (x.down.val, y.down.val) := by
  change (closedBallProductAppendHomeomorph n (x.down, y.down)).val = _
  rw [closedBallProductAppendHomeomorph_val]

/-- Ambient homeomorphism from the interval product model to the classical
max-norm disk. -/
noncomputable def intervalDiskPairHomeomorph (n : ℕ) :
    (intervalDiskPair.{u} n).fst ≃ₜ
      (classicalCellDiskPair.{u} (n + 1)).fst :=
  (topCatIntervalClassicalCellDiskOneHomeomorph.prodCongr
      (Homeomorph.refl (classicalCellDiskPair.{u} n).fst)) |>.trans
    (classicalCellDiskPairProductHomeomorph n)

@[simp, nolint simpNF]
theorem intervalDiskPairHomeomorph_down_val
    (n : ℕ) (x : (intervalDiskPair.{u} n).fst) :
    (intervalDiskPairHomeomorph n x).down.val =
      Fin.appendIsometryOfEq (Nat.one_add n)
        ((topCatIntervalClassicalCellDiskOneHomeomorph x.1).down.val,
          x.2.down.val) := by
  change (classicalCellDiskPairProductHomeomorph n
    (topCatIntervalClassicalCellDiskOneHomeomorph x.1, x.2)).down.val = _
  rw [classicalCellDiskPairProductHomeomorph_down_val]

theorem norm_topCatIntervalClassicalCellDiskOneHomeomorph
    (t : TopCat.I.{u}) :
    ‖(topCatIntervalClassicalCellDiskOneHomeomorph t).down.val‖ =
      |2 * (TopCat.I.homeomorph t : ℝ) - 1| := by
  rw [topCatIntervalClassicalCellDiskOneHomeomorph_down_val]
  simp only [pi_norm_const, Real.norm_eq_abs]

theorem norm_topCatIntervalClassicalCellDiskOneHomeomorph_eq_one_iff
    (t : TopCat.I.{u}) :
    ‖(topCatIntervalClassicalCellDiskOneHomeomorph t).down.val‖ = 1 ↔
      t = 0 ∨ t = 1 := by
  rw [norm_topCatIntervalClassicalCellDiskOneHomeomorph]
  let s : ℝ := 2 * (TopCat.I.homeomorph t : ℝ) - 1
  constructor
  · intro hs
    have hsquare : s * s = (1 : ℝ) * 1 :=
      (abs_eq_iff_mul_self_eq).mp (by simpa [s] using hs)
    have hprod : (s - 1) * (s + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hprod with hpos | hneg
    · right
      apply TopCat.I.ext
      rw [TopCat.I.homeomorph_one]
      apply Subtype.ext
      change (TopCat.I.homeomorph t : ℝ) = 1
      dsimp [s] at hpos
      nlinarith
    · left
      apply TopCat.I.ext
      rw [TopCat.I.homeomorph_zero]
      apply Subtype.ext
      change (TopCat.I.homeomorph t : ℝ) = 0
      dsimp [s] at hneg
      nlinarith
  · rintro (rfl | rfl)
    · rw [TopCat.I.homeomorph_zero]
      norm_num
    · rw [TopCat.I.homeomorph_one]
      norm_num

theorem norm_topCatIntervalClassicalCellDiskOneHomeomorph_le_one
    (t : TopCat.I.{u}) :
    ‖(topCatIntervalClassicalCellDiskOneHomeomorph t).down.val‖ ≤ 1 := by
  have ht := (topCatIntervalClassicalCellDiskOneHomeomorph t).down.property
  change dist (topCatIntervalClassicalCellDiskOneHomeomorph t).down.val 0 ≤ 1 at ht
  simpa only [dist_zero_right] using ht

theorem norm_intervalDiskPairHomeomorph
    (n : ℕ) (x : (intervalDiskPair.{u} n).fst) :
    ‖(intervalDiskPairHomeomorph n x).down.val‖ =
      max ‖(topCatIntervalClassicalCellDiskOneHomeomorph x.1).down.val‖
        ‖x.2.down.val‖ := by
  rw [intervalDiskPairHomeomorph_down_val]
  let e : (Fin 1 → ℝ) × (Fin n → ℝ) ≃ᵢ (Fin (n + 1) → ℝ) :=
    Fin.appendIsometryOfEq (Nat.one_add n)
  let p : (Fin 1 → ℝ) × (Fin n → ℝ) :=
    ((topCatIntervalClassicalCellDiskOneHomeomorph x.1).down.val,
      x.2.down.val)
  have hzeroInv : e.symm 0 = 0 := by
    rw [Fin.appendIsometryOfEq_symm_apply]
    rfl
  have hzero : e 0 = 0 := by
    apply e.symm.injective
    simp only [e.symm_apply_apply, hzeroInv]
  calc
    ‖e p‖ = dist (e p) 0 := (dist_zero_right _).symm
    _ = dist (e p) (e 0) := by rw [hzero]
    _ = dist p 0 := e.dist_eq _ _
    _ = ‖p‖ := dist_zero_right _
    _ = max ‖(topCatIntervalClassicalCellDiskOneHomeomorph x.1).down.val‖
        ‖x.2.down.val‖ := rfl

theorem norm_intervalDiskPairHomeomorph_eq_one_iff
    (n : ℕ) (x : (intervalDiskPair.{u} n).fst) :
    ‖(intervalDiskPairHomeomorph n x).down.val‖ = 1 ↔
      ((x.1 : TopCat.I.{u}) = (0 : TopCat.I.{u}) ∨
        (x.1 : TopCat.I.{u}) = (1 : TopCat.I.{u})) ∨
        ‖x.2.down.val‖ = 1 := by
  rw [norm_intervalDiskPairHomeomorph]
  let a := ‖(topCatIntervalClassicalCellDiskOneHomeomorph x.1).down.val‖
  let b := ‖x.2.down.val‖
  have ha : a ≤ 1 := norm_topCatIntervalClassicalCellDiskOneHomeomorph_le_one x.1
  have hb : b ≤ 1 := by
    have hx := x.2.down.property
    change dist x.2.down.val 0 ≤ 1 at hx
    simpa only [dist_zero_right] using hx
  have hmax : max a b = 1 ↔ a = 1 ∨ b = 1 := by
    constructor
    · intro h
      by_cases hab : a ≤ b
      · right
        simpa [max_eq_right hab] using h
      · left
        have hba : b ≤ a := le_of_not_ge hab
        simpa [max_eq_left hba] using h
    · rintro (haeq | hbeq)
      · rw [haeq]
        exact max_eq_left hb
      · rw [hbeq]
        exact max_eq_right ha
  rw [hmax]
  exact or_congr
    (norm_topCatIntervalClassicalCellDiskOneHomeomorph_eq_one_iff x.1)
    Iff.rfl

/-- The boundary union of the interval--disk model is the inverse image of
the classical sphere under the ambient homeomorphism. -/
theorem intervalDiskPairHomeomorph_preimage_range (n : ℕ) :
    intervalDiskPairHomeomorph n ⁻¹'
        Set.range (classicalCellDiskPair.{u} (n + 1)).map =
      (Set.range (TopPair.intervalBoundaryPair.{u}).map).unionProd
        (Set.range (classicalCellDiskPair.{u} n).map) := by
  rw [← range_intervalDiskPair_map]
  ext x
  rw [Set.mem_preimage,
    TopPair.mem_range_closedUnitBallPair_map_iff,
    mem_range_intervalDiskPair_map_iff,
    TopPair.mem_range_closedUnitBallPair_map_iff,
    norm_intervalDiskPairHomeomorph_eq_one_iff]

/-- The interval--disk pair with its literal product boundary, first compared
to the range replacement of the classical disk pair. -/
noncomputable def intervalDiskPairRangeIso (n : ℕ) :
    intervalDiskPair.{u} n ≅
      TopPair.rangePair (classicalCellDiskPair.{u} (n + 1)) :=
  CategoryTheory.MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      ((intervalDiskPairHomeomorph n).sets
        (intervalDiskPairHomeomorph_preimage_range n).symm))
    (TopCat.isoOfHomeo (intervalDiskPairHomeomorph n))
    (by ext x; rfl)

/-- The literal interval--disk boundary pair is isomorphic to the classical
`(n+1)`-disk and sphere pair. -/
noncomputable def intervalDiskPairIso (n : ℕ) :
    intervalDiskPair.{u} n ≅ classicalCellDiskPair.{u} (n + 1) :=
  intervalDiskPairRangeIso n ≪≫
    (TopPair.rangeIso (classicalCellDiskPair.{u} (n + 1))).symm

end Topology.CWComplex

end
