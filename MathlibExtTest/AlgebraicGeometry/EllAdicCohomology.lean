/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

/-! # Tests for coefficient maps, `ℤ_ℓ`-module structure and reductions in `ℓ`-adic cohomology

Scalar multiplication on `ℓ`-adic cohomology is induced by multiplication on the coefficient
sheaf; rational cohomology is a `ℚ_ℓ`-module; the canonical reduction maps exist for every prime
and are `PadicInt.toZModPow` and the quotient maps; reductions are compatible with the
transitions, giving the comparison with the inverse limit.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.EllAdicCohomology

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EllAdicCohomology
open MathlibExt.AlgebraicGeometry.EllAdicReductionComparison

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) (n : ℕ)

example (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n) : a • x = cohomologyScalar ℓ X n a x := rfl

example (x : X.EllAdicCohomology ℓ n) : (1 : ℤ_[ℓ]) • x = x := one_smul _ x

example (a b : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n) : (a * b) • x = a • b • x := mul_smul a b x

example : Module ℚ_[ℓ] (RationalCohomology ℓ X n) := inferInstance

/-- The coefficient map of a continuous additive map acts by composition on sections. -/
example {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [AddCommGroup A] [AddCommGroup B]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] (f : A →ₜ+ B) (U : Scheme.{u}ᵒᵖ)
    (g : C(U.unop, A)) :
    ((coefficientPresheafMap.{u} f).app U g : C(U.unop, B)) = f.toContinuousMap.comp g := rfl

/-- The canonical reduction maps are available for every prime. -/
example : ReductionMaps ℓ := inferInstance

/-- Reduction is continuous for Mathlib's discrete topology on `ℤ/ℓⁿ`. -/
example (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) := continuous_toZModPow ℓ n

example (r : ℕ) (x : ℤ_[ℓ]) :
    (canonicalReductionMaps ℓ).red r x = PadicInt.toZModPow (r + 1) x := rfl

example (r : ℕ) (x : ZMod (ℓ ^ (r + 2))) :
    (canonicalReductionMaps ℓ).step r x = ZMod.cast x := rfl

example (r : ℕ) (x : ℤ_[ℓ]) :
    (canonicalReductionMaps ℓ).step r ((canonicalReductionMaps ℓ).red (r + 1) x) =
      (canonicalReductionMaps ℓ).red r x :=
  (canonicalReductionMaps ℓ).comp r x

example (r : ℕ) (x : integralCohomology ℓ X n) :
    transition ℓ X n r (reduction ℓ X n (r + 1) x) = reduction ℓ X n r x :=
  reductions_commute ℓ X n r x

example (x : integralCohomology ℓ X n) (r : ℕ) :
    (comparison ℓ X n (reductions_commute ℓ X n) x).1 r = reduction ℓ X n r x := rfl

end MathlibExtTest.AlgebraicGeometry.EllAdicCohomology
