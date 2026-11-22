/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.CentralAction
import MathlibExt.CategoryTheory.Monoidal.HomogeneousLocalization.AdjointTelescope
import MathlibExt.CategoryTheory.Monoidal.Mod.FreeRelativeTensor

/-!
# The actual coefficient tensor/internal-Hom adjunction and beta transition

The existing balanced free-relative tensor comparison identifies the actual
ambient tensor with `U` with relative tensor by the actual free R-module on U.
The existing module internal-Hom adjunction then supplies its right adjoint.
Both tensor comparison maps, the original equalizer/internal-Hom carrier,
and the original beta adjunct are retained.

No point-set tensor inverse is assumed.  Derived tensor invertibility,
Quillen/weak preservation and the beta-local reflection are separate
conditions and conclusions in the derived application.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.HomogeneousLocalization.CoefficientTensorHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (R : CommMon C) (U : C)

/-- Both original balanced free-relative tensor maps give the actual ambient tensor comparison. -/
def freeRelativeTensorIso (M : Mod C R.X) :
    ((Mod.relativeTensor R).obj ((Mod.free R.X).obj U)).obj M ≅
      Mod.AmbientTensor.tensorModule R.X U M :=
  Mod.FreeRelativeTensor.balancedIso R U M

omit [MonoidalClosed C] [HasEqualizers C] in
/-- The whole free-relative comparison keeps the same original balancing contraction. -/
theorem freeRelativeTensorIso_hom (M : Mod C R.X) :
    (freeRelativeTensorIso R U M).hom.hom = (Mod.FreeRelativeTensor.forward R U M).hom := rfl

/-- The complete ambient/free-relative comparison is natural on every original module arrow. -/
def freeRelativeTensorNatIso :
    (Mod.relativeTensor R).obj ((Mod.free R.X).obj U) ≅ Mod.AmbientTensor.functor R.X U :=
  NatIso.ofComponents (freeRelativeTensorIso R U) (fun {M N} f => by
    apply Mod.hom_ext
    simp only [Mod.comp_hom', freeRelativeTensorIso_hom, Mod.AmbientTensor.functor_map_hom]
    have h := Mod.FreeRelativeTensor.target_naturality R U f
    have he : Mod.relativeTensorMap R (𝟙 ((Mod.free R.X).obj U)) f =
        ((Mod.relativeTensor R).obj ((Mod.free R.X).obj U)).map f := by
      change ((Mod.relativeTensor R).map (𝟙 ((Mod.free R.X).obj U))).app M ≫
          ((Mod.relativeTensor R).obj ((Mod.free R.X).obj U)).map f = _
      rw [(Mod.relativeTensor R).map_id, NatTrans.id_app, Category.id_comp]
    rw [he] at h
    exact h)

/-- The actual right adjoint is the original module internal-Hom out of the unchanged free module. -/
def rightFunctor : Mod C R.X ⥤ Mod C R.X :=
  Mod.internalHom R ((Mod.free R.X).obj U)

/-- The full tensor/internal-Hom module adjunction comes from the original balanced adjunction. -/
def adjunction : Mod.AmbientTensor.functor R.X U ⊣ rightFunctor R U :=
  (Mod.relativeTensorInternalHomAdjunction R ((Mod.free R.X).obj U)).ofNatIsoLeft
    (freeRelativeTensorNatIso R U)

/-- The original internal-Hom equalizer is actually isomorphic to the original ambient internal Hom. -/
def underlyingRightIso (N : Mod C R.X) : ((rightFunctor R U).obj N).X ≅ (ihom U).obj N.X :=
  Mod.FreeInternalHom.iso R U N

variable (b : U ⟶ R.X)

/-- The actual multiplication action, with its full central coefficient producer. -/
def betaAction : Mod.AmbientTensor.functor R.X U ⟶ 𝟭 (Mod C R.X) :=
  centralActionNatTrans R.X b (isCentralClass_of_commutative R b)

/-- The genuine point-set beta transition is the original tensor/internal-Hom adjunct. -/
def coaugmentation : 𝟭 (Mod C R.X) ⟶ rightFunctor R U :=
  AdjointTelescope.coaugmentation (adjunction R U) (betaAction R U b)

theorem coaugmentation_app (M : Mod C R.X) :
    (coaugmentation R U b).app M =
      (adjunction R U).homEquiv M M (centralAction R.X b (isCentralClass_of_commutative R b) M) :=
  AdjointTelescope.coaugmentation_adjunct (adjunction R U) (betaAction R U b) M

/-- The whole current-stage beta diagram lives on the original module and internal-Hom carriers. -/
def betaDiagramFunctor : Mod C R.X ⥤ (ℕ ⥤ Mod C R.X) :=
  AdjointTelescope.diagramFunctor (coaugmentation R U b)

theorem betaDiagram_map_succ (M : Mod C R.X) (n : ℕ) :
    ((betaDiagramFunctor R U b).obj M).map (homOfLE (Nat.le_succ n)) =
      (coaugmentation R U b).app
        ((Functor.Iteration.iterate (rightFunctor R U) n).obj M) :=
  AdjointTelescope.diagram_map_succ (coaugmentation R U b) M n

end CategoryTheory.HomogeneousLocalization.CoefficientTensorHom
