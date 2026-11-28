/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.PartialTotalSpectralObject

/-!
# Negative stages of the partial-total filtration

For a first-quadrant bicomplex `B` in an abelian category, the integer-indexed partial-total
cochain filtration is zero at every negative finite index. A map between two such stages has a
zero mapping cone, so its spectral-object homology vanishes in every integer degree.

The same vanishing holds for the interval from the bottom index to a negative finite stage,
since the bottom filtration object is zero.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- Negative finite partial-total cochain stage is zero.

For an integer `z < 0`, the filtration object `B.partialTotalCochainFiltration.obj z` is a
zero object. -/
theorem isZero_partialTotalCochainFiltration_obj_of_neg
    (z : ℤ) (hz : z < 0) :
    IsZero (B.partialTotalCochainFiltration.obj (z : EInt)) := by
  apply (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
  change IsZero (CategoryTheory.Functor.nonnegativeIntObj
    B.partialTotalFunctor z)
  exact CategoryTheory.Functor.isZero_nonnegativeIntObj_of_neg
    B.partialTotalFunctor z hz

/-- Spectral-object homology between negative finite stages vanishes.

Let `a ≤ b` be negative integers. For every integer degree `n`, the spectral-object homology
of the interval `a ⟶ b` is zero, because both partial-total filtration stages are zero. -/
theorem isZero_partialTotalSpectralObjectHObj_of_neg
    (n a b : ℤ) (hab : a ≤ b) (ha : a < 0) (hb : b < 0) :
    IsZero ((B.partialTotalSpectralObject.H n).obj
      (CategoryTheory.ComposableArrows.mk₁
        (homOfLE (show (a : EInt) ≤ (b : EInt) by simpa using hab)))) := by
  let hE : (a : EInt) ≤ (b : EInt) := by simpa using hab
  let f := B.partialTotalCochainFiltration.map (homOfLE hE)
  have hSource := B.isZero_partialTotalCochainFiltration_obj_of_neg a ha
  have hTarget := B.isZero_partialTotalCochainFiltration_obj_of_neg b hb
  have hConeX : IsZero ((CochainComplex.mappingCone f).X n) :=
    (CochainComplex.mappingCone.isZero_X_iff f n).2
      ⟨(HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)).map_isZero hSource,
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_isZero hTarget⟩
  have hConeHom : IsZero ((CochainComplex.mappingCone f).homology n) :=
    ((CochainComplex.mappingCone f).sc n).isZero_homology_of_isZero_X₂ hConeX
  exact IsZero.of_iso hConeHom
    (B.partialTotalSpectralObjectHObjIso n hE)
/-- Spectral-object homology from bottom to a negative stage vanishes.

For an integer `z < 0` and any integer degree `k`, the homology object of the interval `⊥ ⟶ z`
in the partial-total spectral object is zero. -/
theorem isZero_partialTotalSpectralObjectHObj_bot_to_neg
    (k z : ℤ) (hz : z < 0) :
    IsZero ((B.partialTotalSpectralObject.H k).obj
      (CategoryTheory.ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ (z : EInt) by simp)))) := by
  let hE : (⊥ : EInt) ≤ (z : EInt) := by simp
  let f := B.partialTotalCochainFiltration.map (homOfLE hE)
  have hSource : IsZero
      (B.partialTotalCochainFiltration.obj (⊥ : EInt)) := by
    apply (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
    rw [B.partialTotalEIntFiltration_obj_bot]
    exact isZero_zero _
  have hTarget := B.isZero_partialTotalCochainFiltration_obj_of_neg z hz
  have hConeX : IsZero ((CochainComplex.mappingCone f).X k) :=
    (CochainComplex.mappingCone.isZero_X_iff f k).2
      ⟨(HomologicalComplex.eval C (ComplexShape.up ℤ)
          (k + 1)).map_isZero hSource,
        (HomologicalComplex.eval C (ComplexShape.up ℤ) k).map_isZero hTarget⟩
  have hConeH : IsZero ((CochainComplex.mappingCone f).homology k) :=
    ((CochainComplex.mappingCone f).sc k)
      |>.isZero_homology_of_isZero_X₂ hConeX
  exact IsZero.of_iso hConeH
    (B.partialTotalSpectralObjectHObjIso k hE)


end HomologicalComplex₂

end
