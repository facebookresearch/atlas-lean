/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.ResolvedFiniteInverseImages

/-!
# Tests for the Milnor difference of resolved finite inverse images

After the `n`th product projection the Milnor difference is the `n`th projection minus the
`(n + 1)`st projection followed by the transition from level `n + 1` to level `n` (not the
reverse composition, and not an off-by-one index). Transitions compose to the resolved arrow over
two steps, and a compatible family is killed by the difference: its Milnor fibre detects exactly
the inverse limit.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.ResolvedFiniteInverseImages

namespace MathlibExtTest.ResolvedFiniteInverseImages

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {C : Type u₂} [Category.{v₂} C] [Abelian C]
  (ν : A ⥤ C) (T : ℕᵒᵖ ⥤ A) [EnoughInjectives (ℕᵒᵖ ⥤ C)] [HasLimitsOfShape (Discrete ℕ) C]

/-- The Milnor difference after the `n`th projection. -/
example (n : ℕ) :
    difference ν T ≫ Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) n =
      Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) n -
        Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) (n + 1) ≫ transition ν T n :=
  Pi.lift_comp_π _ _

/-- Two transitions compose to the resolved arrow from level `n + 2` to level `n`. -/
example (n : ℕ) :
    transition ν T (n + 1) ≫ transition ν T n =
      (resolved ν T).map (homOfLE (by omega : n ≤ n + 2)).op := by
  unfold transition
  rw [← Functor.map_comp]
  rfl

/-- A compatible family is killed by the Milnor difference. -/
example {K : CochainComplex C ℤ} (g : K ⟶ resolvedProduct ν T)
    (hg : ∀ n : ℕ, g ≫ Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) (n + 1) ≫ transition ν T n =
      g ≫ Pi.π (fun n : ℕ => (resolved ν T).obj (op n)) n) :
    g ≫ difference ν T = 0 := by
  refine Pi.hom_ext _ _ (fun n => ?_)
  rw [Category.assoc, difference, Pi.lift_comp_π, Preadditive.comp_sub, hg n, sub_self, zero_comp]

end MathlibExtTest.ResolvedFiniteInverseImages
