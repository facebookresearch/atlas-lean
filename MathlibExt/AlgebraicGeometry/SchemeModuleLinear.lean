/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/FunctorsAndMorphisms/IntegralTransformQcoh/Basic.lean`
(AxiomMath/Stacks at commit c496df0d9beea9deaeabcea8492605f9a0a2313b,
https://github.com/AxiomMath/Stacks): `baseRingToSections`, `baseScalar`,
`baseRingToCenter` and `modulesLinear`.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modification notice: only this base scalar and linearity section is copied, into
its own namespace and without Stacks imports, with documentation added.
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Canonical scalar action on actual module sheaves of a scheme over a ring

The action is fixed by the actual base-to-global-functions homomorphism
and restriction to each actual open. This complete port supplies the
canonical linear structure; it introduces no arbitrary coefficient action.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeModuleLinear

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

universe u

/-- The ring map from the base ring to the ring of functions on an open of an `R`-scheme. -/
@[simps!]
noncomputable def baseRingToSections (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (U : X.left.Opensᵒᵖ) :
    R →+* X.left.ringCatSheaf.obj.obj U :=
  ((forget₂ CommRingCat RingCat).map
      ((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop) ≫
    X.left.ringCatSheaf.obj.map U.unop.leTop.op).hom

/-- Multiplication by a base scalar, naturally on all module sheaves. -/
@[simps!]
noncomputable def baseScalar (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) (r : R) :
    CatCenter (SheafOfModules.{u} X.left.ringCatSheaf) where
  asHom := {
    app M := ⟨{
      app U := by
        letI : CommRing (X.left.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.left.presheaf.obj U))
        exact ModuleCat.ofHom ((baseRingToSections R X U r) •
          LinearMap.id (R := X.left.ringCatSheaf.obj.obj U) (M := M.val.obj U))
      naturality {U V} f := by
        ext x
        change baseRingToSections R X V r • (M.val.map f).hom x =
          (M.val.map f).hom (baseRingToSections R X U r • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun g => RingCat.Hom.hom g
          (((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop).hom r))
          (X.left.ringCatSheaf.obj.map_comp U.unop.leTop.op f) }⟩
    naturality {M N} f := by
      change f ≫ _ = _ ≫ f
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      ext x
      exact ((f.val.app U).hom.map_smul _ x).symm }

/-- The action of the base ring on the category of module sheaves. -/
@[simps]
noncomputable def baseRingToCenter (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) :
    R →+* CatCenter (SheafOfModules.{u} X.left.ringCatSheaf) where
  toFun := baseScalar R X
  map_one' := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U 1 • x = x
    simp
  map_mul' r s := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U (r * s) • x =
      baseRingToSections R X U r • (baseRingToSections R X U s • x)
    simp [mul_smul]
  map_zero' := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U 0 • x = 0
    simp
  map_add' r s := by
    apply CatCenter.ext
    intro M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    ext x
    change baseRingToSections R X U (r + s) • x =
      baseRingToSections R X U r • x + baseRingToSections R X U s • x
    simp [add_smul]

/-- The canonical linear structure on module sheaves over a scheme over `R`.

This is not an instance: the action depends on the structure morphism `X.hom`,
which `X.left.Modules` does not record, so two `R`-scheme structures on one
scheme give two linear structures. Install it locally, for instance with
`local instance : Linear R X.left.Modules := modulesLinear R X`. -/
@[instance_reducible]
noncomputable def modulesLinear (R : Type u) [CommRing R]
    (X : Over (Spec (.of R))) : Linear R X.left.Modules :=
  Linear.ofRingMorphism (baseRingToCenter R X)


end MathlibExt.AlgebraicGeometry.SchemeModuleLinear
