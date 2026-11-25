/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.ArtinianLocalization

@[expose] public section

open scoped TensorProduct

-- Exact-source consumer, with the original binders.
private theorem exactSource
    (K : Type*) [Field K] {m r : ℕ} (g : Fin r → MvPolynomial (Fin m) K)
    (𝔫 : Ideal (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))) [𝔫.IsMaximal]
    (h𝔫 : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j) ∈ 𝔫)
    [Module.Finite K (Localization.AtPrime 𝔫)] :
    ∃ e : Localization.AtPrime 𝔫 ≃ₐ[K]
      (MvPowerSeries (Fin m) K ⧸
        Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))),
      ∀ p : MvPolynomial (Fin m) K,
        e (algebraMap (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
            (Localization.AtPrime 𝔫)
            (Ideal.Quotient.mk (Ideal.span (Set.range g)) p)) =
          Ideal.Quotient.mk
            (Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K)))
            (p : MvPowerSeries (Fin m) K) :=
  MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk K g 𝔫 h𝔫

-- Boundary use: finiteness transports across the equivalence, so the
-- power-series quotient is finite-dimensional over `K`.
example
    (K : Type*) [Field K] {m r : ℕ} (g : Fin r → MvPolynomial (Fin m) K)
    (𝔫 : Ideal (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))) [𝔫.IsMaximal]
    (h𝔫 : ∀ j, Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X j) ∈ 𝔫)
    [Module.Finite K (Localization.AtPrime 𝔫)] :
    Module.Finite K (MvPowerSeries (Fin m) K ⧸
      Ideal.span (Set.range fun i => (g i : MvPowerSeries (Fin m) K))) := by
  obtain ⟨e, -⟩ :=
    MvPolynomial.exists_algEquiv_localization_atPrime_mvPowerSeries_quotient_apply_mk
      K g 𝔫 h𝔫
  exact Module.Finite.equiv e.toLinearEquiv
