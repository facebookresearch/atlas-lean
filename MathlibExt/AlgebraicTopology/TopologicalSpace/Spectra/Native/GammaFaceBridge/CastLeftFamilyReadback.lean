/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.LeftFamilyReadback
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Cast Left Family Readback

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uV vV uJ
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  [EnrichedCategory V ℕ]
  [MonoidalCategory (EnrichedFunctorCat V ℕ)] [SymmetricCategory (EnrichedFunctorCat V ℕ)]
  (S : EnrichedFunctorCat V ℕ) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V ℕ)]
  [∀ X : EnrichedFunctorCat V ℕ, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V ℕ, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {J : Type uJ} [EnrichedCategory V J]
  (E : RightModule S ≌ EnrichedFunctorCat V J)
  (a : ℕ → J)
  (h : ∀ n, E.functor ⋙ evaluation (a n) ≅
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.evaluation S n)

private local instance constructionMonoidal1 : MonoidalCategory (RightModule S) := RightModuleFree.tensorMonoidal S

/-- The native tensor obtained by transporting the right-module tensor along `E`. -/
@[instance_reducible]
def originalTargetMonoidal : MonoidalCategory (EnrichedFunctorCat V J) := Monoidal.transport E

/-- A transported target tensor retains the whole original source readback; the only unit
transport is the equality induced by that same complete target monoidal equality. -/
def CastLeftFamilyReadback (t : ℕ → ℕ → ℕ)
    (e : ∀ (n r : ℕ) (K L : V), Free.object n K ⊗ Free.object r L ≅ Free.object (t n r) (K ⊗ L))
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : originalTargetMonoidal S E = M)
    (p : Independent.PairFormula M (fun n K => Free.object (a n) K) t) : Prop :=
  letI := M
  ∀ (n r : ℕ) (K L : V) (N : EnrichedFunctorCat V J)
    (f : Free.object (a n) K ⟶ 𝟙_ (EnrichedFunctorCat V J))
    (g : Free.object (a r) L ⟶ N),
    Free.evaluate (a (t n r)) (K ⊗ L) N
      ((p n r K L).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    Free.evaluate (t n r) (K ⊗ L) (E.inverse.obj N).X
      ((e n r K L).inv ≫
        ((RightModuleFree.freeGenerator S (Free.object n K) ≫
          (sourcePreimage S E a h n K (E.functor.obj (𝟙_ (RightModule S)))
            (f ≫ eqToHom (congrArg (fun Z : MonoidalCategory (EnrichedFunctorCat V J) => Z.tensorUnit)
              hM.symm)) ≫ E.unitIso.inv.app (𝟙_ (RightModule S))).hom) ⊗ₘ
          (RightModuleFree.freeGenerator S (Free.object r L) ≫
            (sourcePreimage S E a h r L N g).hom)) ≫ leftAction S (E.inverse.obj N)) ≫
      (h (t n r)).inv.app (E.inverse.obj N) ≫
        component (E.counitIso.hom.app N) (a (t n r))

/-- Resolve the complete family and tensor casts abstractly, before any native source data is
specialized. Both pair maps and every original source and target comparison remain present. -/
theorem cast_family_left_readback (t : ℕ → ℕ → ℕ)
    (e : ∀ (n r : ℕ) (K L : V), Free.object n K ⊗ Free.object r L ≅ Free.object (t n r) (K ⊗ L))
    (M : MonoidalCategory (EnrichedFunctorCat V J))
    (hM : originalTargetMonoidal S E = M)
    (hType : ModuleStage.SymbolicPair.FamilyType S E a t =
      Independent.PairFormula M (fun n K => Free.object (a n) K) t) :
    CastLeftFamilyReadback S E a h t e M hM
      (cast hType (ModuleStage.SymbolicPair.pair S E a h t e)) := by
  cases hM
  simpa only [CastLeftFamilyReadback, LeftFamilyReadback, originalTargetMonoidal,
    sourcePreimage, cast_eq, eqToHom_refl, Category.comp_id] using
    left_family_readback S E a h t e

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeModuleEvaluation
