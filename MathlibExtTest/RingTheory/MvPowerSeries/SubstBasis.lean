/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.SubstBasis

@[expose] public section

open scoped TensorProduct

/-- Consumer of the uniqueness statement with the original binders. -/
example
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n d : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n,
      (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (b : Fin d → MvPowerSeries (Fin n) B)
    (β : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (TensorProduct B (IsLocalRing.ResidueField B)
        (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))))
    (hb : ∀ j, β j = TensorProduct.tmul B (1 : IsLocalRing.ResidueField B)
      (Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)))
    (f : MvPowerSeries (Fin n) B) :
    ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j :=
  MvPowerSeries.existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient
    ρ hρ0 hN hfin b β hb f

/-- Consumer of the existence statement with the original binders. -/
example
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n,
      (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    ∃ (d : ℕ) (b : Fin d → MvPowerSeries (Fin n) B),
      ∀ f : MvPowerSeries (Fin n) B,
        ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j :=
  MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing ρ hρ0 hN hfin

universe u in
/-- The existence statement in an arbitrary universe. -/
example
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n : ℕ}
    (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n,
      (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))) :
    ∃ (d : ℕ) (b : Fin d → MvPowerSeries (Fin n) B),
      ∀ f : MvPowerSeries (Fin n) B,
        ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j :=
  MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing ρ hρ0 hN hfin
