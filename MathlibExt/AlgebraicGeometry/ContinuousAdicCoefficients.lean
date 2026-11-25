/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean` (Mathlib, revision
56a005855ea17e0b0958f73ec801ae140b0a1679):
Copyright (c) 2026 Christian Merten. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Christian Merten

`StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b), for the sheafification of module-valued presheaves:
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: module-valued continuous coefficient sheaves, restriction of scalars and the
extension–restriction adjunction for sheaves.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Continuous coefficient sheaves on the pro-étale site

For a topological module `M` over a ring `R`, `continuousModuleSheaf R M X` is the sheaf of
`R`-modules `U ↦ C(U, M)` on the small pro-étale site of a scheme `X`, restricted from the big
pro-étale site, where it is a sheaf because continuous maps form an fpqc sheaf. For `M = ℤ_ℓ` or
`ℚ_ℓ` with their `ℓ`-adic topologies these are the coefficient sheaves of Bhatt–Scholze; no
coefficient module is given the discrete topology.

For an `R`-algebra `S`, a topological `S`-module `V` and an `R`-submodule `L` of `V` (for example
an integral lattice in a `ℚ_ℓ`-vector space), `latticeScalarComparison` is the map from the
sheafified extension of scalars of `C(-, L)` to `C(-, V)`, adjoint to the inclusion
`C(-, L) → C(-, V)`.

Reference: Bhatt--Scholze, The pro-étale topology for schemes,
Lemma 4.2.12 and Lemma 6.8.2.
-/

namespace MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

/-- Sheaves of `R`-modules on the small pro-étale site of `X`. -/
abbrev CoefficientSheaf (X : Scheme.{u}) (R : Type) [Ring R] :=
  Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)

/-- Sheafification of presheaves of modules on the small pro-étale site, in a universe containing
the site. -/
instance moduleSheafify (X : Scheme.{u}) (R : Type) [Ring R] :
    HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} R) := by
  let : HasLimits (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  let : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} R
  let : PreservesFilteredColimits (forget (ModuleCat.{u + 1} R)) :=
    comp_preservesFilteredColimits.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
      (forget AddCommGrpCat.{u + 1})
  let : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (forget (ModuleCat.{u + 1} R)) := inferInstance
  infer_instance

section ContinuousModules

variable (R : Type) [Ring R] (M : Type (u + 1))
  [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The presheaf of `R`-modules `U ↦ C(U, M)` on schemes. -/
def continuousModulePresheaf : Scheme.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj U := ModuleCat.of R C(U.unop, M)
  map {U V} f := ModuleCat.ofHom
    { toFun a := a.comp f.unop.base.hom
      map_add' a b := rfl
      map_smul' r a := rfl }
  map_id U := by ext a x; rfl
  map_comp f g := by ext a x; rfl

/-- The identity isomorphism between the presheaf of `R`-modules `U ↦ C(U, M)` on schemes,
composed with the forgetful functor to types, and the presheaf of continuous maps `U ↦ C(U, M)`
(`continuousMapPresheaf M`). -/
def continuousModuleForgetIso :
    continuousModulePresheaf R M ⋙ forget (ModuleCat.{u + 1} R) ≅
      continuousMapPresheaf.{u + 1, u} M := Iso.refl _

/-- The sheaf of `R`-modules `U ↦ C(U, M)` on the big pro-étale site. -/
def globalContinuousModule : Sheaf proetaleTopology (ModuleCat.{u + 1} R) :=
  ⟨continuousModulePresheaf R M, by
    let : HasLimits (ModuleCat.{u + 1} R) :=
      ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
    apply Presheaf.IsSheaf.of_le proetaleTopology_le_fpqcTopology
    exact (Presheaf.isSheaf_iff_isSheaf_forget fpqcTopology
      (continuousModulePresheaf R M) (forget (ModuleCat.{u + 1} R))).mpr
      (isSheaf_fpqcTopology_continuousMapPresheaf M)⟩

/-- The sheaf of `R`-modules `U ↦ C(U, M)` on the small pro-étale site of `X`. -/
def continuousModuleSheaf (X : Scheme.{u}) : CoefficientSheaf X R :=
  ((ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous
    (ModuleCat.{u + 1} R) (ProEt.topology X) proetaleTopology).obj
      (globalContinuousModule R M)

end ContinuousModules

section Lattices

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (V : Type (u + 1)) [TopologicalSpace V] [AddCommGroup V] [Module S V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul S V]

/-- The topological `S`-module `V` as an `R`-module, by restriction of scalars. -/
abbrev restrictedVector : ModuleCat.{u + 1} R :=
  (ModuleCat.restrictScalars.{u + 1, 0, 0} (algebraMap R S)).obj (ModuleCat.of S V)

instance restrictedVectorTopology : TopologicalSpace (restrictedVector R S V) :=
  inferInstanceAs (TopologicalSpace V)

instance restrictedVectorTopologicalAdd : IsTopologicalAddGroup (restrictedVector R S V) :=
  inferInstanceAs (IsTopologicalAddGroup V)

instance restrictedContinuousConstSMul : ContinuousConstSMul R (restrictedVector R S V) where
  continuous_const_smul r := continuous_const_smul (T := V) (algebraMap R S r)

variable (L : Submodule R (restrictedVector R S V))

/-- Extension of scalars from `R` to `S` for sheaves: sectionwise extension of scalars followed by
sheafification. -/
abbrev scalarExtension (X : Scheme.{u}) :
    CoefficientSheaf X R ⥤ CoefficientSheaf X S :=
  Sheaf.composeAndSheafify (ProEt.topology X)
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap R S))

/-- The inclusion `C(-, L) → C(-, V)` of continuous lattice-valued functions, as a morphism of
sheaves of `R`-modules. -/
def latticeInclusionSheaf (X : Scheme.{u}) :
    continuousModuleSheaf R L X ⟶
      (sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1, 0, 0} (algebraMap R S))).obj
        (continuousModuleSheaf S V X) :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        (Y := (ModuleCat.restrictScalars.{u + 1, 0, 0}
          (algebraMap R S)).obj ((continuousModuleSheaf S V X).obj.obj U))
        { toFun a := ⟨fun x ↦ (a x).val, continuous_subtype_val.comp a.continuous⟩
          map_add' a b := rfl
          map_smul' r a := rfl }
      naturality U W f := by rfl }

/-- The comparison map from the extension of scalars of `C(-, L)` to `C(-, V)`: the adjoint of the
inclusion `latticeInclusionSheaf` under the extension–restriction adjunction for sheaves. -/
def latticeScalarComparison (X : Scheme.{u}) :
    (scalarExtension R S X).obj (continuousModuleSheaf R L X) ⟶
      continuousModuleSheaf S V X :=
  ((Sheaf.adjunction (ProEt.topology X)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} (algebraMap R S))).homEquiv _ _).symm
      (latticeInclusionSheaf R S V L X)

end Lattices

end MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
