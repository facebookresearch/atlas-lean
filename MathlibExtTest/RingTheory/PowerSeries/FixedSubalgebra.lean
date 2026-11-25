/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.FixedSubalgebra

@[expose] public section

-- Source statement, with the original `Type` binders.
example
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (G : Type) [Group G] [Finite G]
    (σ : G →* (PowerSeries W ≃ₐ[W] PowerSeries W))
    (S : Subalgebra W (PowerSeries W))
    (hS : ∀ f : PowerSeries W, f ∈ S ↔ ∀ g : G, σ g f = f) :
    Nonempty (PowerSeries W ≃ₐ[W] ↥S) :=
  PowerSeries.nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq W G σ S hS

-- Higher-universe consumer.
example
    (W : Type 1) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (G : Type 1) [Group G] [Finite G]
    (σ : G →* (PowerSeries W ≃ₐ[W] PowerSeries W))
    (S : Subalgebra W (PowerSeries W))
    (hS : ∀ f : PowerSeries W, f ∈ S ↔ ∀ g : G, σ g f = f) :
    Nonempty (PowerSeries W ≃ₐ[W] ↥S) :=
  PowerSeries.nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq W G σ S hS

-- Boundary case: for the trivial action, the fixed subalgebra is everything.
example
    (W : Type*) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (G : Type*) [Group G] [Finite G] :
    Nonempty (PowerSeries W ≃ₐ[W] ↥(⊤ : Subalgebra W (PowerSeries W))) :=
  PowerSeries.nonempty_algEquiv_of_forall_mem_iff_forall_apply_eq W G 1 ⊤
    (fun f => by simp)
