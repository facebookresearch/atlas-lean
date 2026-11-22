/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Evaluation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.EvaluationLabelCast

/-!
# Evaluation Readback

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

/-- The abstract target keeps the complete original lift and actual free/evaluation counit. -/
theorem liftFamilyTarget_original (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (S : ℕ → V)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) (fun n r => n + r))
    (n r : ℕ) :
    letI := M
    liftFamilyTarget M a S p n r =
      Free.evaluate (a (n + r))
        (S n ⊗ (𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
        (Free.object (a n) (S n))
        (UnitLiftFamily.liftFamily M (fun n X => Free.object (a n) X) S p n r
          ((𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
          (Free.extend (a r) ((𝟙_ (EnrichedFunctorCat V J)).toEnrichedFunctor.obj (a r))
            (𝟙_ (EnrichedFunctorCat V J)) (𝟙 _))) := by
  let := M
  rfl

/-- Every full source-label cast and target-label cast survives the abstract lift factorization. -/
theorem liftFamily_evaluate_label_cast (M : MonoidalCategory (EnrichedFunctorCat V J))
    (a : ℕ → J) (S : ℕ → V)
    (p : Independent.PairFormula M (fun n X => Free.object (a n) X) (fun n r => n + r))
    (h : CoefficientFamily M a (fun n r => n + r) p) (n r : ℕ) (K : V) :
    letI := M
    ∀ (g : Free.object (a r) K ⟶ 𝟙_ (EnrichedFunctorCat V J)),
      Free.evaluate (a (r + n)) (S n ⊗ K) (Free.object (a n) (S n))
        (eqToHom (congrArg (fun j => Free.object (a j) (S n ⊗ K)) (Nat.add_comm r n)) ≫
          UnitLiftFamily.liftFamily M (fun n X => Free.object (a n) X) S p n r K g) =
        (S n ◁ Free.evaluate (a r) K (𝟙_ (EnrichedFunctorCat V J)) g) ≫
          liftFamilyTarget M a S p n r ≫
            eqToHom (congrArg
              (fun j => (Free.object (a n) (S n)).toEnrichedFunctor.obj (a j))
              (Nat.add_comm r n).symm) := by
  let := M
  intro g
  have hc := evaluate_label_cast a (Nat.add_comm r n) (S n ⊗ K)
    (Free.object (a n) (S n))
    (UnitLiftFamily.liftFamily M (fun n X => Free.object (a n) X) S p n r K g)
  rw [liftFamily_evaluate M a S p h n r K g] at hc
  simpa only [Category.assoc] using hc

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
