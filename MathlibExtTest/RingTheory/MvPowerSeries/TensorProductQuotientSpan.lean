/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.TensorProductQuotientSpan

@[expose] public section

set_option autoImplicit false

open scoped TensorProduct

/-- Exact-source consumer, using the original binders verbatim. -/
example {R : Type} [CommRing R] {S : Type} [CommRing S] [Algebra R S]
    {σ : Type} [Fintype σ] {ι : Type} (φ : ι → MvPowerSeries σ R)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈
      Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span
          (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk
            (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) :=
  MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem φ hN

/-- The same consumer in a higher universe. -/
example {R : Type 1} [CommRing R] {S : Type 1} [CommRing S] [Algebra R S]
    {σ : Type 1} [Fintype σ] {ι : Type 1} (φ : ι → MvPowerSeries σ R)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈
      Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸ Ideal.span
          (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk
            (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) :=
  MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem φ hN
