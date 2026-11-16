/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions are adapted from:
Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean at
56a005855ea17e0b0958f73ec801ae140b0a1679:
Copyright (c) 2026 Christian Merten. All rights reserved.
Authors: Christian Merten.
Licensed under Apache 2.0.

The module-sheafification proof is adapted from AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Spaces/ProetaleComparison.lean,
AlgebraicGeometry.hasSheafify_moduleCat, licensed under Apache 2.0.
That source has no individual author or copyright notice.
Modification notice: use module-valued continuous coefficient sheaves,
canonical restriction of scalars and the sheaf extension adjunction.
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
# Continuous adic coefficient models on the actual pro-étale site

The sheaf associated to a topological coefficient module has sections
C(U, M). The scalar extension comparison is fixed by inclusion of an
open integral lattice and the actual sheaf extension/restriction
adjunction. Its geometric isomorphism is a separate request.

For adic coefficients one specializes R to the ring of integers O,
S to its fraction field E, and the element inverted to ℓ or a
uniformizer. No sheaf is treated as carrying the discrete topology.

Reference: Bhatt--Scholze, The pro-étale topology for schemes,
Lemma 4.2.12 and Lemma 6.8.2.
-/

namespace MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme

universe u

/-- The actual module category of sheaves on the small pro-étale site. -/
abbrev CoefficientSheaf (X : Scheme.{u}) (R : Type) [Ring R] :=
  Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)

/-- Generic module sheafification, in a universe containing the site. -/
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

/-- Pointwise module-valued continuous functions on schemes. -/
def continuousModulePresheaf : Scheme.{u}ᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj U := ModuleCat.of R C(U.unop, M)
  map {U V} f := ModuleCat.ofHom
    { toFun a := a.comp f.unop.base.hom
      map_add' a b := rfl
      map_smul' r a := rfl }
  map_id U := by ext a x; rfl
  map_comp f g := by ext a x; rfl

/-- Forgetting the pointwise module gives the actual continuous-map
presheaf already proved to be an fpqc sheaf by Mathlib. -/
def continuousModuleForgetIso :
    continuousModulePresheaf R M ⋙ forget (ModuleCat.{u + 1} R) ≅
      continuousMapPresheaf.{u + 1, u} M := Iso.refl _

/-- The continuous coefficient module sheaf on the big pro-étale site. -/
def globalContinuousModule : Sheaf proetaleTopology (ModuleCat.{u + 1} R) :=
  ⟨continuousModulePresheaf R M, by
    let : HasLimits (ModuleCat.{u + 1} R) :=
      ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
    apply Presheaf.IsSheaf.of_le proetaleTopology_le_fpqcTopology
    exact (Presheaf.isSheaf_iff_isSheaf_forget fpqcTopology
      (continuousModulePresheaf R M) (forget (ModuleCat.{u + 1} R))).mpr
      (isSheaf_fpqcTopology_continuousMapPresheaf M)⟩

/-- The actual continuous coefficient model on the small pro-étale site. -/
def continuousModuleSheaf (X : Scheme.{u}) : CoefficientSheaf X R :=
  ((ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous
    (ModuleCat.{u + 1} R) (ProEt.topology X) proetaleTopology).obj
      (globalContinuousModule R M)

end ContinuousModules

section Lattices

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (V : Type (u + 1)) [TopologicalSpace V] [AddCommGroup V] [Module S V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul S V]

/-- The underlying R-module is canonical restriction of scalars, rather
than a separately selected scalar action on the coefficient module. -/
abbrev restrictedVector : ModuleCat.{u + 1} R :=
  (ModuleCat.restrictScalars.{u + 1, 0, 0} (algebraMap R S)).obj (ModuleCat.of S V)

instance restrictedVectorTopology : TopologicalSpace (restrictedVector R S V) :=
  inferInstanceAs (TopologicalSpace V)

instance restrictedVectorTopologicalAdd : IsTopologicalAddGroup (restrictedVector R S V) :=
  inferInstanceAs (IsTopologicalAddGroup V)

instance restrictedContinuousConstSMul : ContinuousConstSMul R (restrictedVector R S V) where
  continuous_const_smul r := continuous_const_smul (T := V) (algebraMap R S r)

variable (L : Submodule R (restrictedVector R S V))

/-- Extension of coefficients is the actual sectionwise tensor functor
followed by sheafification. -/
abbrev scalarExtension (X : Scheme.{u}) :
    CoefficientSheaf X R ⥤ CoefficientSheaf X S :=
  Sheaf.composeAndSheafify (ProEt.topology X)
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap R S))

/-- The pointwise inclusion of continuous lattice-valued functions,
viewed as a morphism to the canonical restriction of coefficients. -/
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

/-- The canonical scalar extension comparison, pinned by the actual
lattice inclusion and the sheaf extension adjunction. -/
def latticeScalarComparison (X : Scheme.{u}) :
    (scalarExtension R S X).obj (continuousModuleSheaf R L X) ⟶
      continuousModuleSheaf S V X :=
  ((Sheaf.adjunction (ProEt.topology X)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, 0} (algebraMap R S))).homEquiv _ _).symm
      (latticeInclusionSheaf R S V L X)

end Lattices

end MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
