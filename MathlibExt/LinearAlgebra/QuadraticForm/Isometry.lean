/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Isometries of quadratic maps

For quadratic maps over a commutative semiring, scaling an isometry by the same scalar on
both sides gives an isometry of the scaled maps. Equality gives an identity isometry, and
anisotropy is invariant under isometry. These constructions apply to module-valued quadratic
maps and do not require finite-dimensionality.
-/

@[expose] public section

set_option autoImplicit false

universe u v w v'

namespace QuadraticMap

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {M' : Type v'} [AddCommMonoid M'] [Module R M']
variable {N : Type w} [AddCommMonoid N] [Module R N]

namespace IsometryEquiv

/-- **Scaling a quadratic isometry.**

Let R be a commutative semiring, M,M′,N R-modules, and Q : M → N and Q′ : M′ → N quadratic
maps. For an R-linear isometry e : Q ≃ Q′ and any c ∈ R, the same linear equivalence gives an
isometry cQ ≃ cQ′.
-/
def smul {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N}
    (c : R) (e : Q.IsometryEquiv Q') :
    (c • Q).IsometryEquiv (c • Q') where
  toLinearEquiv := e.toLinearEquiv
  map_app' x := by simp [e.map_app]

/-- **The isometry associated to equality.**

Let R be a commutative semiring, M,N R-modules and Q,Q′ : M → N quadratic maps. If Q = Q′, the
identity linear equivalence on M gives an isometry Q ≃ Q′.
-/
def ofEq {Q Q' : QuadraticMap R M N} (h : Q = Q') :
    Q.IsometryEquiv Q' where
  toLinearEquiv := LinearEquiv.refl R M
  map_app' x := by cases h; rfl

/-- **Anisotropy is invariant under isometry.**

Let R be a commutative semiring, M,M′,N R-modules, and Q : M → N and Q′ : M′ → N quadratic
maps. If e : Q ≃ Q′ is an R-linear isometry, Q is anisotropic if and only if Q′ is
anisotropic, where anisotropy means Q(x) = 0 implies x = 0.
-/
theorem anisotropic_iff {Q : QuadraticMap R M N}
    {Q' : QuadraticMap R M' N} (e : Q.IsometryEquiv Q') :
    Q.Anisotropic ↔ Q'.Anisotropic := by
  constructor
  · intro hQ y hy
    have hx : Q (e.symm y) = 0 := by
      rw [← e.map_app]
      simpa
    have hzero := hQ _ hx
    simpa using congrArg e hzero
  · intro hQ x hx
    have he0 : Q' (e x) = 0 := by rw [e.map_app, hx]
    have hex : e x = 0 := hQ _ he0
    exact e.injective (by simpa using hex)

end IsometryEquiv

end QuadraticMap

end
