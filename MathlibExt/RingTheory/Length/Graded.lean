/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.Homogeneous.ModuleQuotient
public import MathlibExt.RingTheory.Length.Nat
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Length additivity for homogeneous submodule components

This file transports finite generation to the inherited and quotient degree
pieces of a homogeneous submodule.  Over an Artinian coefficient ring, the
fixed-degree short exact sequence then gives additivity of natural-valued
module length.

## Main declarations

* `HomogeneousSubmodule.gradeFinite`
* `HomogeneousSubmodule.quotientGradeFinite`
* `HomogeneousSubmodule.gradedPieceLength_eq_add`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HomogeneousSubmodule

universe u v w

variable {A : Type u} [CommRing A]
variable {S : Type v} [CommRing S] [Algebra A S]
variable {M : Type w} [AddCommGroup M]
  [Module A M] [Module S M] [IsScalarTower A S M]

variable (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
variable (Mgrade : ℕ → Submodule A M)
  [SetLike.GradedSMul Sgrade Mgrade]
  [DirectSum.Decomposition Mgrade]

variable (N : HomogeneousSubmodule Sgrade Mgrade)

/-- Let `A` be a Noetherian commutative ring, `S` a graded commutative
`A`-algebra, and `M` a graded `S`-module with compatible `A`-action. If every
ambient degree piece is finite over `A`, then each inherited degree piece of
a homogeneous submodule `N ⊆ M` is also finite over `A`. -/
instance gradeFinite [IsNoetherianRing A]
    [∀ n, Module.Finite A (Mgrade n)] (n : ℕ) :
    Module.Finite A (N.grade Sgrade Mgrade n) := by
  have : IsNoetherian A (Mgrade n) :=
    isNoetherian_of_isNoetherianRing_of_finite A (Mgrade n)
  exact Module.Finite.of_injective
    (N.gradeInclusion Sgrade Mgrade n)
    (N.gradeInclusion_injective Sgrade Mgrade n)

/-- Let `A` be a commutative ring, `S` a graded commutative `A`-algebra,
and `M` a graded `S`-module with compatible `A`-action and finite `A`-module
degree pieces. For a homogeneous submodule `N ⊆ M`, every degree piece of
`M/N` is finite over `A`. -/
instance quotientGradeFinite [∀ n, Module.Finite A (Mgrade n)] (n : ℕ) :
    Module.Finite A (N.quotientGrade Sgrade Mgrade n) :=
  Module.Finite.of_surjective
    (N.gradeQuotient Sgrade Mgrade n)
    (N.gradeQuotient_surjective Sgrade Mgrade n)

/-- Let `A` be an Artinian commutative ring, `S` a graded commutative
`A`-algebra, and `M` a graded `S`-module with compatible `A`-action and finite
`A`-module degree pieces. For a homogeneous submodule `N ⊆ M` and `n : ℕ`,
`lengthNat_A(M_n) = lengthNat_A(N_n) + lengthNat_A((M/N)_n)`. The scalar,
algebra and module universes retain their independent values. -/
theorem gradedPieceLength_eq_add [IsArtinianRing A]
    [∀ n, Module.Finite A (Mgrade n)] (n : ℕ) :
    HilbertSamuel.gradedPieceLength A Mgrade n =
      HilbertSamuel.moduleLengthNat A (N.grade Sgrade Mgrade n) +
      HilbertSamuel.moduleLengthNat A
        (N.quotientGrade Sgrade Mgrade n) :=
  HilbertSamuel.moduleLengthNat_eq_add_of_exact A
    (N.gradeInclusion Sgrade Mgrade n)
    (N.gradeQuotient Sgrade Mgrade n)
    (N.gradeInclusion_injective Sgrade Mgrade n)
    (N.gradeQuotient_surjective Sgrade Mgrade n)
    (N.grade_exact Sgrade Mgrade n)

end HomogeneousSubmodule
