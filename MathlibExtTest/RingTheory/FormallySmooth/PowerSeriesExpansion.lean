/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.FormallySmooth.PowerSeriesExpansion

@[expose] public section

set_option autoImplicit false

universe u v

-- Exact-source consumer, with the original binders.
private theorem exactSource
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ RingHom.ker e.toRingHom ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) :=
  Algebra.FormallySmooth.exists_powerSeries_expansion_along_section e he

-- Boundary: at order zero the adic condition is vacuous, matching
-- membership in the zeroth power of the kernel.
example
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) (a : A) :
    a ∈ RingHom.ker e.toRingHom ^ 0 := by
  obtain ⟨θ, -, hθ, -⟩ := exactSource e he
  exact (hθ 0 a).mp fun k hk => (Nat.not_lt_zero k hk).elim
