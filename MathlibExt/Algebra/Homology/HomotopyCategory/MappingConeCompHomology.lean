/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomotopyCategory.MappingConeCompShortComplex

/-!
# Homology boundary of a mapping-cone composition triangle

In an abelian category, let `S : K → L → M` be a short complex
of integer cochains and `g : L → X`. The boundary of the cone
composition triangle, followed by the homology map of `Cone(S.f) → M`,
equals the ordinary cone boundary for `g` followed by the map
induced by `S.g`, under the canonical homotopy-category homology
comparisons.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Let `C` be abelian, `S : K → L → M` a short complex of
integer cochains, and `g : L → X`. For `n+1=n′`, the homology
boundary of the cone composition triangle followed by
`H^n′(Cone(S.f) → M)` equals the ordinary boundary of `Cone(g)`
followed by `H^n′(S.g)`, using the canonical comparisons between
complex and homotopy-category homology. -/
theorem homologySequenceδ_mappingConeCompTriangleh_comp_descShortComplex
    (S : ShortComplex (CochainComplex C ℤ))
    {X : CochainComplex C ℤ} (g : S.X₂ ⟶ X)
    (n n' : ℤ) (h : n + 1 = n') :
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        (CochainComplex.mappingConeCompTriangleh S.f g) n n' h ≫
      (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n').hom.app (CochainComplex.mappingCone S.f) ≫
      HomologicalComplex.homologyMap (descShortComplex S) n' =
    (HomotopyCategory.homologyFunctorFactors
      C (ComplexShape.up ℤ) n).hom.app (CochainComplex.mappingCone g) ≫
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle g).mor₃ n n' (by omega) ≫
      HomologicalComplex.homologyMap S.g n' := by
  change
    (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).homologySequenceδ
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
          (CochainComplex.mappingConeCompTriangle S.f g)) n n' h ≫
      (HomotopyCategory.homologyFunctorFactors
        C (ComplexShape.up ℤ) n').hom.app (CochainComplex.mappingCone S.f) ≫
      HomologicalComplex.homologyMap (descShortComplex S) n' = _
  rw [homologySequenceδ_quotient_mapTriangle_obj]
  simp only [CochainComplex.mappingConeCompTriangle_obj₃,
    CochainComplex.mappingConeCompTriangle_obj₁, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [cancel_epi, CochainComplex.mappingConeCompTriangle_mor₃]
  change
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        ((triangle g).mor₃ ≫ (inr S.f)⟦(1 : ℤ)⟧') n n' (by omega) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shift n').map
        (descShortComplex S) =
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
        (triangle g).mor₃ n n' (by omega) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shift n').map S.g
  have hpackaged :
      ((triangle g).mor₃ ≫ (inr S.f)⟦(1 : ℤ)⟧') ≫
          (descShortComplex S)⟦(1 : ℤ)⟧' =
        (CochainComplex.mappingConeCompTriangle S.f g).mor₃ ≫
          (descShortComplex S)⟦(1 : ℤ)⟧' :=
    congrArg
      (fun k : CochainComplex.mappingCone g ⟶
          (CochainComplex.mappingCone S.f)⟦(1 : ℤ)⟧ ↦
        k ≫ (descShortComplex S)⟦(1 : ℤ)⟧')
      (CochainComplex.mappingConeCompTriangle_mor₃ S.f g).symm
  dsimp only [CochainComplex.mappingCone.triangle]
  dsimp only [CochainComplex.mappingCone.triangle] at hpackaged
  rw [← CategoryTheory.Functor.shiftMap_comp,
    hpackaged,
    mappingConeCompTriangle_mor₃_comp_descShortComplex_shift,
    CategoryTheory.Functor.shiftMap_comp]
  dsimp only [CochainComplex.mappingCone.triangle]

end CochainComplex.mappingCone

end
