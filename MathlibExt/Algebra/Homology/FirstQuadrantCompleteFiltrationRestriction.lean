/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison

/-!
# Restricting the complete filtration to natural indices

The natural numbers embed monotonically in the extended integers by
`n ↦ ((n : ℤ) : EInt)`.  Restricting the complete horizontal-filtration
diagram along this embedding recovers the original finite horizontal
filtration diagram, naturally in the filtration index.  The comparison also
intertwines the two natural transformations into the total complex.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- The monotone embedding of natural filtration indices into the extended
integers. -/
def horizontalFiltrationNatToEIntOrderHom : ℕ →o EInt where
  toFun n := ((n : ℤ) : EInt)
  monotone' _ _ h := WithBotTop.coe_monotone (Int.ofNat_le.mpr h)

@[simp]
theorem horizontalFiltrationNatToEIntOrderHom_apply (n : ℕ) :
    horizontalFiltrationNatToEIntOrderHom n = ((n : ℤ) : EInt) :=
  rfl

/-- The thin-category functor underlying the natural-index embedding. -/
abbrev horizontalFiltrationNatToEIntFunctor : ℕ ⥤ EInt :=
  horizontalFiltrationNatToEIntOrderHom.toFunctor

@[simp]
theorem horizontalFiltrationNatToEIntFunctor_obj (n : ℕ) :
    horizontalFiltrationNatToEIntFunctor.obj n = ((n : ℤ) : EInt) :=
  rfl

@[simp]
theorem horizontalFiltrationNatToEIntFunctor_map
    {n m : ℕ} (f : n ⟶ m) :
    horizontalFiltrationNatToEIntFunctor.map f =
      homOfLE (WithBotTop.coe_monotone (Int.ofNat_le.mpr f.le)) :=
  rfl

/-- Restriction of the complete horizontal-filtration diagram to natural
indices is naturally isomorphic to the original finite diagram. -/
noncomputable def horizontalCompleteTotalFiltrationNatRestrictionIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    horizontalFiltrationNatToEIntFunctor ⋙
        (horizontalCompleteTotalFiltration K).diagram ≅
      (horizontalTotalFiltration K).diagram :=
  NatIso.ofComponents
    (fun n => horizontalCompleteFilteredTotalComplexFiniteIso K
      (n : ℤ) (Int.natCast_nonneg n))
    (by
      intro n m f
      change horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone (Int.ofNat_le.mpr f.le)) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso K
            (m : ℤ) (Int.natCast_nonneg m)).hom =
        (horizontalCompleteFilteredTotalComplexFiniteIso K
            (n : ℤ) (Int.natCast_nonneg n)).hom ≫
          horizontalFilteredTotalComplexMap K f.le
      simpa only [Int.toNat_natCast] using
        (horizontalCompleteFilteredTotalComplexFiniteIso_transition K
          (n : ℤ) (m : ℤ) (Int.natCast_nonneg n)
          (Int.ofNat_le.mpr f.le)).symm)

@[simp]
theorem horizontalCompleteTotalFiltrationNatRestrictionIso_hom_app
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    (horizontalCompleteTotalFiltrationNatRestrictionIso K).hom.app n =
      (horizontalCompleteFilteredTotalComplexFiniteIso K
        (n : ℤ) (Int.natCast_nonneg n)).hom :=
  rfl

/-- The restriction isomorphism identifies the finite filtration inclusion
with the restriction of the complete filtration inclusion. -/
theorem horizontalCompleteTotalFiltrationNatRestrictionIso_hom_comp_ι
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    (horizontalCompleteTotalFiltrationNatRestrictionIso K).hom ≫
        (horizontalTotalFiltration K).ι =
      Functor.whiskerLeft horizontalFiltrationNatToEIntFunctor
        (horizontalCompleteTotalFiltration K).ι := by
  apply NatTrans.ext
  funext n
  change
    (horizontalCompleteFilteredTotalComplexFiniteIso K
          (n : ℤ) (Int.natCast_nonneg n)).hom ≫
        horizontalFilteredTotalComplexToTotal K n =
      horizontalCompleteFilteredTotalToTotal K ((n : ℤ) : EInt)
  exact horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K
    (n : ℤ) (Int.natCast_nonneg n)

end HomologicalComplex₂

end
