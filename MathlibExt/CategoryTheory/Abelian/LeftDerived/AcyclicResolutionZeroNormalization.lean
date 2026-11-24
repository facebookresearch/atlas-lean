/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolution

/-!
# The degree-zero projective normalization of the retained comparison
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

set_option backward.isDefEq.respectTransparency false in
/--
The augmentation homology iso on a projective resolution is the original quotient comparison used
by the derived-zero map.
-/
theorem normalizationHomologyZero_hom {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] :
    (ChainComplex.homologyZeroIsoOfPreservedAugmentation F P.π).hom =
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).homologyι 0 ≫
        P.fromLeftDerivedZero' F := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  apply (cancel_epi (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv)).1
  rw [Category.assoc, ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom]
  change F.map (P.π.f 0) =
    (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv) ≫ K.isoHomologyι₀.hom ≫ P.fromLeftDerivedZero' F
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (pOpcycles_comp_fromLeftDerivedZero' P F).symm

variable [HasProjectiveResolutions C]

set_option backward.isDefEq.respectTransparency false in
/-- In degree zero the retained acyclic comparison is the SAME projective comparison. -/
theorem normalizationAcyclicProjective_zero {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (hP : ∀ q n : ℕ, IsZero ((F.leftDerived (n + 1)).obj (P.complex.X q))) :
    (F.leftDerivedObjIsoHomologyOfAcyclicResolution P.complex P.π hP 0).hom =
      (P.isoLeftDerivedObj F 0).hom := by
  let K : ChainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let e := ChainComplex.homologyZeroIsoOfPreservedAugmentation F P.π
  unfold Functor.leftDerivedObjIsoHomologyOfAcyclicResolution
  change (F.leftDerivedZeroIsoSelf.app X).hom ≫ e.inv = (P.isoLeftDerivedObj F 0).hom
  apply (cancel_mono e.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [normalizationHomologyZero_hom]
  change F.fromLeftDerivedZero.app X = (P.isoLeftDerivedObj F 0).hom ≫
    K.isoHomologyι₀.hom ≫ P.fromLeftDerivedZero' F
  exact P.fromLeftDerivedZero_eq F

end CategoryTheory.ProjectiveResolution
