/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison

/-!
# Restriction of a complete horizontal filtration to natural cuts

The increasing inclusion e:ℕ→ℤ∪{⊥,⊤} sends n to the finite integer cut n and sends an inequality
n≤m to the same inequality between complete cuts. Let K be a first-quadrant bicomplex in a
preadditive category with a zero object and finite coproducts. Its complete horizontal diagram,
restricted along e, is naturally isomorphic to the finite horizontal filtration diagram.

At n∈ℕ, the comparison is the canonical isomorphism ε_{K,n}:G_{e(n)}(K)≅G^fin_n(K). It commutes
with all transitions n≤m and preserves inclusion into Tot K: ε_{K,n}.hom≫ι^fin_n=ι_{e(n)}. Thus
the diagrams agree as diagrams of subcomplexes of the same total complex, with arbitrary
category universes.
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

/-- The order-preserving map e:ℕ→ℤ∪{⊥,⊤} sends n to its finite integer cut n. For n≤m, the
corresponding finite cuts satisfy e(n)≤e(m). The image contains only nonnegative finite cuts and
contains neither endpoint ⊥ or ⊤. -/
def horizontalFiltrationNatToEIntOrderHom : ℕ →o EInt where
  toFun n := ((n : ℤ) : EInt)
  monotone' _ _ h := WithBotTop.coe_monotone (Int.ofNat_le.mpr h)

@[simp]
theorem horizontalFiltrationNatToEIntOrderHom_apply (n : ℕ) :
    horizontalFiltrationNatToEIntOrderHom n = ((n : ℤ) : EInt) :=
  rfl

/-- View ℕ and ℤ∪{⊥,⊤} as thin categories with a unique arrow a→b when a≤b. This functor e sends a
natural number n to its finite integer cut and sends the arrow n→m to the unique arrow e(n)→e(m)
given by the same inequality. -/
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

/-- Let C be preadditive with a zero object and finite coproducts. For a bicomplex K of shape (down
ℕ,down ℕ), let G(K) be its complete horizontal filtration diagram, G^fin(K) its finite
horizontal diagram, and e:ℕ→ℤ∪{⊥,⊤} the inclusion as nonnegative finite cuts. This natural
isomorphism e*G(K)≅G^fin(K) has component ε_{K,n}:G_{e(n)}(K)≅G^fin_n(K) at n∈ℕ. Its components
commute with the transition maps for every n≤m. -/
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

/-- Let C be preadditive with a zero object and finite coproducts. Let K be a first-quadrant
bicomplex, e:ℕ→ℤ∪{⊥,⊤} the finite-cut inclusion, and ε_K:e*G(K)≅G^fin(K) the complete-to-finite
diagram comparison. With ι^fin:G^fin(K)→const(Tot K) and ι:G(K)→const(Tot K) the stage-inclusion
transformations, ε_K.hom≫ι^fin=e*ι. Its component at n is ε_{K,n}.hom≫ι^fin_n=ι_{e(n)}. -/
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
