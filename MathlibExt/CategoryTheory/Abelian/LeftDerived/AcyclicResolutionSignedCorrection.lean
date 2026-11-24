/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionNormalizationSign

/-!
## # Canonical natural scalar correction of the retained acyclic comparison
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- The triangular scalar correction is natural on any original degree functor. -/
def acyclicResolutionNormalizationIso (G : C ⥤ D) (n : ℕ) : G ≅ G :=
  NatIso.ofComponents (fun X =>
    ProjectiveResolution.acyclicResolutionNormalizationIso (G.obj X) n) (fun f => by
      dsimp only [ProjectiveResolution.acyclicResolutionNormalizationIso]
      rw [comp_zsmul, zsmul_comp, Category.comp_id, Category.id_comp])

/-- Every component is the exact original triangular scalar on the original functor object. -/
theorem acyclicResolutionNormalizationIso_hom_app (G : C ⥤ D) (n : ℕ) (X : C) :
    (G.acyclicResolutionNormalizationIso n).hom.app X =
      ProjectiveResolution.acyclicResolutionNormalizationSign n • 𝟙 (G.obj X) := rfl

/-- The correction commutes with every original coefficient natural transformation. -/
theorem acyclicResolutionNormalizationIso_naturality_transformation
    {G H : C ⥤ D} (α : G ⟶ H) (n : ℕ) :
    (G.acyclicResolutionNormalizationIso n).hom ≫ α =
      α ≫ (H.acyclicResolutionNormalizationIso n).hom := by
  ext X
  simp only [NatTrans.comp_app, acyclicResolutionNormalizationIso_hom_app,
    zsmul_comp, comp_zsmul, Category.id_comp, Category.comp_id]

end CategoryTheory.Functor

namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the SAME retained projective acyclic comparison has the SAME proved triangular
sign. -/
theorem normalizationAcyclicProjective_inv {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).inv =
      acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).inv := by
  let E := F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n
  change E.inv = acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).inv
  apply (cancel_mono E.hom).1
  rw [E.inv_hom_id]
  change 𝟙 _ = (acyclicResolutionNormalizationSign n • (P.isoLeftDerivedObj F n).inv) ≫
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).hom
  rw [normalizationAcyclicProjective_hom, zsmul_comp, comp_zsmul, smul_smul,
    Iso.inv_hom_id, acyclicResolutionNormalizationSign_mul_self, one_zsmul]

/-- Correct the retained projective acyclic iso by its canonical natural source scalar. -/
def normalizedAcyclicProjectiveComparison {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (F.leftDerived n).obj X ≅
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homology n :=
  ((F.leftDerived n).acyclicResolutionNormalizationIso n).app X ≪≫
    F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n

set_option backward.isDefEq.respectTransparency false in
/-- The canonical corrected comparison is literally the SAME projective comparison in every degree. -/
theorem normalizedAcyclicProjectiveComparison_hom {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q i : ℕ, IsZero ((F.leftDerived (i + 1)).obj (P.complex.X q))) (n : ℕ) :
    (normalizedAcyclicProjectiveComparison P F hP n).hom = (P.isoLeftDerivedObj F n).hom := by
  dsimp only [normalizedAcyclicProjectiveComparison, Iso.trans_hom]
  change (acyclicResolutionNormalizationSign n • 𝟙 ((F.leftDerived n).obj X)) ≫
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP n).hom =
      (P.isoLeftDerivedObj F n).hom
  rw [normalizationAcyclicProjective_hom, zsmul_comp, comp_zsmul, Category.id_comp,
    smul_smul, acyclicResolutionNormalizationSign_mul_self, one_zsmul]

set_option backward.isDefEq.respectTransparency false in
/-- The exact coefficient boundary has the forced adjacent-degree scalar compatibility. -/
theorem normalizationNativeLeftBoundary_scalar (F : C ⥤ D) [F.Additive]
    (S : ShortComplex.ShortExactSequences C) (n : ℕ) :
    (acyclicResolutionNormalizationIso ((F.leftDerived (n + 1)).obj S.obj.X₃) (n + 1)).hom ≫
      LeftDerivedDelta.LDdelta F n S.obj S.property =
    normalizationCrossSign n •
      (LeftDerivedDelta.LDdelta F n S.obj S.property ≫
        (acyclicResolutionNormalizationIso ((F.leftDerived n).obj S.obj.X₁) n).hom) := by
  dsimp only [acyclicResolutionNormalizationIso]
  rw [zsmul_comp, comp_zsmul, Category.id_comp, Category.comp_id, smul_smul]
  rfl

end CategoryTheory.ProjectiveResolution
