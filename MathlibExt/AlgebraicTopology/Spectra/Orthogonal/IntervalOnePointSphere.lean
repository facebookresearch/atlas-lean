/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.MatrixIndex
public import MathlibExt.Topology.Category.TopCat.PointQuotientOnePoint
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.UnitInterval

/-!
# The interval endpoint quotient as a one-point real sphere

The actual open interval complement is homeomorphic to one-dimensional real
Euclidean space. Collapsing its two endpoints gives the original one-point
compactification through the existing point-quotient complement theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits Set Topology

namespace CategoryTheory.Spectra

/-- The affine map from `(-1,1)` to `(0,1)` with its literal inverse. -/
def openUnitIntervalAffine : Ioo (-1 : ℝ) 1 ≃ₜ Ioo (0 : ℝ) 1 where
  toFun x := ⟨(x.1 + 1) / 2, by constructor <;> linarith [x.2.1, x.2.2]⟩
  invFun x := ⟨2 * x.1 - 1, by constructor <;> linarith [x.2.1, x.2.2]⟩
  left_inv x := by apply Subtype.ext; dsimp; ring
  right_inv x := by apply Subtype.ext; dsimp; ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.add continuous_const).div_const 2
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_subtype_val).sub continuous_const

/-- A real coordinate parametrizes every point of the open unit interval. -/
def realOpenUnitIntervalHomeomorph : ℝ ≃ₜ Ioo (0 : ℝ) 1 :=
  (orderIsoIooNegOneOne ℝ).toHomeomorph.trans openUnitIntervalAffine

/-- The original one-dimensional Euclidean space has its literal scalar coordinate. -/
def euclideanOneRealHomeomorph : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans
    (Homeomorph.piUnique (fun _ : Fin 1 => ℝ))

/-- Interior interval points are exactly the complement of the two endpoints. -/
def unitIntervalInteriorHomeomorph : Ioo (0 : ℝ) 1 ≃ₜ
    ({(0 : unitInterval), (1 : unitInterval)}ᶜ : Set unitInterval) where
  toFun x := ⟨⟨x.1, x.2.1.le, x.2.2.le⟩, by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro h
    rcases h with h | h
    · have hval := congrArg Subtype.val h
      exact (ne_of_gt x.2.1) hval
    · have hval := congrArg Subtype.val h
      exact (ne_of_lt x.2.2) hval⟩
  invFun x := ⟨x.1.1, by
    have hz : x.1 ≠ (0 : unitInterval) := by
      intro hz
      apply x.2
      simp [hz]
    have ho : x.1 ≠ (1 : unitInterval) := by
      intro ho
      apply x.2
      simp [ho]
    constructor
    · exact lt_of_le_of_ne x.1.2.1 (fun h => hz (Subtype.ext h.symm))
    · exact lt_of_le_of_ne x.1.2.2 (fun h => ho (Subtype.ext h))⟩
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The actual lifted Euclidean coordinate parametrizes the lifted endpoint complement. -/
def liftedEuclideanIntervalComplement : ULift.{v, 0} (EuclideanSpace ℝ (Fin 1)) ≃ₜ
    ({(0 : TopCat.I.{v}), (1 : TopCat.I.{v})}ᶜ : Set TopCat.I.{v}) := by
  let e : EuclideanSpace ℝ (Fin 1) ≃ₜ
      ({(0 : unitInterval), (1 : unitInterval)}ᶜ : Set unitInterval) :=
    euclideanOneRealHomeomorph.trans
      (realOpenUnitIntervalHomeomorph.trans unitIntervalInteriorHomeomorph)
  let h := (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin 1))).trans e
  let i := TopCat.I.homeomorph.symm
  let r := i.image ({(0 : unitInterval), (1 : unitInterval)}ᶜ : Set unitInterval)
  have hr : i '' ({(0 : unitInterval), (1 : unitInterval)}ᶜ : Set unitInterval) =
      ({(0 : TopCat.I.{v}), (1 : TopCat.I.{v})}ᶜ : Set TopCat.I.{v}) := by
    have hzero : i (0 : unitInterval) = (0 : TopCat.I.{v}) := rfl
    have hone : i (1 : unitInterval) = (1 : TopCat.I.{v}) := rfl
    rw [i.image_compl]
    simp [hzero, hone]
  exact h.trans (r.trans (Homeomorph.setCongr hr))

end CategoryTheory.Spectra
