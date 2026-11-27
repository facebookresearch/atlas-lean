/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisibleGeometricTate

/-!
# Probes for finite-level torsion points

The finite-level comparison equivalence and its injectivity and surjectivity
consequences for `T`-points of a `p`-divisible group.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.PDivisibleGeometricTate

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels
open WantedExt.AlgebraicGeometry.PDivisibleGeometricTate

/-- The finite-level comparison equivalence. -/
def finiteTorsionEquiv (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ) :
    (finitePoints p S G n).obj (op T) ≃ TorsionLevel p S G T n :=
  Equiv.ofBijective _ (finite_to_torsion_bijective p S G T n)

/-- The comparison map is injective. -/
theorem finiteToTorsion_injective (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ) :
    Function.Injective (finiteToTorsion p S G T n) :=
  (finite_to_torsion_bijective p S G T n).1

/-- The comparison map is surjective. -/
theorem finiteToTorsion_surjective (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ) :
    Function.Surjective (finiteToTorsion p S G T n) :=
  (finite_to_torsion_bijective p S G T n).2

/-- Applying the equivalence coerces to the level inclusion. -/
example (p : ℕ) [Fact p.Prime] (S : Scheme.{0})
    (G : PDivisibleGroup S p) (T : Over S) (n : ℕ)
    (x : (finitePoints p S G n).obj (op T)) :
    (finiteTorsionEquiv p S G T n x).val =
      (((finiteInclusion p S G n).app (op T)).hom x) := rfl

end MathlibExtTest.AlgebraicGeometry.PDivisibleGeometricTate
