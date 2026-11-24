/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.TensorQuotientEquiv

@[expose] public section

open scoped TensorProduct

/-- `exactSource` consumer with the original binders. -/
example {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {σ : Type*} [Fintype σ] {ι : Type*} (φ : ι → MvPowerSeries σ R)
    (hN : ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈
      Ideal.span (Set.range φ)) :
    ∃ e : S ⊗[R] (MvPowerSeries σ R ⧸ Ideal.span (Set.range φ)) ≃ₐ[S]
        (MvPowerSeries σ S ⧸
          Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i))),
      ∀ (s : S) (q : MvPowerSeries σ R),
        e (s ⊗ₜ[R] Ideal.Quotient.mk (Ideal.span (Set.range φ)) q) =
          s • Ideal.Quotient.mk
            (Ideal.span (Set.range fun i => MvPowerSeries.map (algebraMap R S) (φ i)))
            (MvPowerSeries.map (algebraMap R S) q) :=
  MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem φ hN

/-- Boundary check: when every `φ i` is a variable power, the hypothesis holds
with exponent `1` for the span of the variables themselves. -/
example {R : Type*} [CommRing R] (σ : Type*) [Fintype σ] :
    ∃ N : ℕ, ∀ s : σ, (MvPowerSeries.X s : MvPowerSeries σ R) ^ N ∈
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
  ⟨1, fun s => by rw [pow_one]; exact Ideal.subset_span (Set.mem_range_self s)⟩
