/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalUnitLift.Generic

/-!
# Free Family Evaluation

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed
namespace PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
universe uV vV uJ
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]

/-- Coefficient-indexed operations taking free maps into `U` to free maps into `N` after tensoring
the coefficient with `X`. -/
def FreeMapFamily (r b : J) (X : V) (U N : EnrichedFunctorCat V J) : Type _ :=
  ∀ K : V, (Free.object r K ⟶ U) → (Free.object b (X ⊗ K) ⟶ N)

/-- A free-map family commutes with every coefficient map and its tensor with `X`. -/
def FreeMapFamilyNaturality (r b : J) (X : V) (U N : EnrichedFunctorCat V J)
    (L : FreeMapFamily r b X U N) : Prop :=
  ∀ {K K' : V} (f : K ⟶ K') (g : Free.object r K' ⟶ U),
    Free.coefficientMap b (X ◁ f) ≫ L K' g =
      L K (Free.coefficientMap r f ≫ g)

/-- The coefficient map of a free-map family, obtained by evaluating it on the free evaluation
counit of `U`. -/
def freeMapFamilyTarget (r b : J) (X : V) (U N : EnrichedFunctorCat V J)
    (L : FreeMapFamily r b X U N) :
    X ⊗ U.toEnrichedFunctor.obj r ⟶ N.toEnrichedFunctor.obj b :=
  Free.evaluate b (X ⊗ U.toEnrichedFunctor.obj r) N
    (L (U.toEnrichedFunctor.obj r)
      (Free.extend r (U.toEnrichedFunctor.obj r) U (𝟙 _)))

/-- Every coefficient-natural family keeps its explicit actual target and original evaluation counit. -/
theorem freeMapFamily_evaluate (r b : J) (X : V) (U N : EnrichedFunctorCat V J)
    (L : FreeMapFamily r b X U N) (h : FreeMapFamilyNaturality r b X U N L)
    (K : V) (g : Free.object r K ⟶ U) :
    Free.evaluate b (X ⊗ K) N (L K g) =
      (X ◁ Free.evaluate r K U g) ≫ freeMapFamilyTarget r b X U N L := by
  let A := U.toEnrichedFunctor.obj r
  let ev := Free.evaluate r K U g
  let c : Free.object r A ⟶ U := Free.extend r A U (𝟙 _)
  have hc : Free.coefficientMap r ev ≫ c = g := free_evaluation_counit r U g
  have hl := h ev c
  rw [hc] at hl
  have he := congrArg (Free.evaluate b (X ⊗ K) N) hl.symm
  have hn := (Free.adjunction b).homEquiv_naturality_left (X ◁ ev) (L A c)
  rw [Free.adjunction_homEquiv] at hn
  exact he.trans hn

end PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback
