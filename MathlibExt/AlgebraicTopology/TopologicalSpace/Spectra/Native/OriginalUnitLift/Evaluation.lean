/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.NativeGammaGeneratorWeaknessCompletion

/-!
# Evaluation

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.Orthogonal.NativeGammaGeneratorWeaknessCompletion
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

/-- The full original lift family and the generic right lift are the same recipe before specialization. -/
theorem liftFamily_eq_rightLift (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (S : ℕ → V)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) (fun n r => n + r)) :
    letI := M
    ∀ (n r : ℕ) (K : V) (g : Free.object (a r) K ⟶ 𝟙_ (EnrichedFunctorCat V J)),
      UnitLiftFamily.liftFamily M (fun n X => Free.object (a n) X) S p n r K g =
        rightLift M a (fun n r => n + r) p n r (S n) K g := by
  let := M
  intro n r K g
  rfl

/-- The full original lift evaluated on the original free/evaluation counit supplies the typed target. -/
def liftFamilyTarget (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (S : ℕ → V)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) (fun n r => n + r))
    (n r : ℕ) :
    letI := M
    S n ⊗ (𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r) ⟶
      (Free.object (a n) (S n)).toEnrichedFunctor.obj (a (n + r)) := by
  letI := M
  exact Free.evaluate (a (n + r))
    (S n ⊗ (𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
    (Free.object (a n) (S n))
    (UnitLiftFamily.liftFamily M (fun n X => Free.object (a n) X) S p n r
      ((𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
      (Free.extend (a r) ((𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
        (𝟙_ (EnrichedFunctorCat V J)) (𝟙 _)))

/-- The complete counit target factorization holds for every map in the literal lift family. -/
theorem liftFamily_evaluate (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (S : ℕ → V)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) (fun n r => n + r))
    (h : CoefficientFamily M a (fun n r => n + r) p) (n r : ℕ) (K : V) :
    letI := M
    ∀ (g : Free.object (a r) K ⟶ 𝟙_ (EnrichedFunctorCat V J)),
      Free.evaluate (a (n + r)) (S n ⊗ K) (Free.object (a n) (S n))
        (UnitLiftFamily.liftFamily M (fun n X => Free.object (a n) X) S p n r K g) =
          (S n ◁ Free.evaluate (a r) K (𝟙_ (EnrichedFunctorCat V J)) g) ≫
            liftFamilyTarget M a S p n r := by
  let := M
  intro g
  simpa only [liftFamilyTarget, liftFamily_eq_rightLift] using
    rightLift_evaluate M a (fun n r => n + r) p h n r (S n) K g

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
