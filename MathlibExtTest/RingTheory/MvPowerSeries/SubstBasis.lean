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

open MvPowerSeries in
/-- In one variable, the quotient by `X ^ 2` is spanned over `B` by the classes of `1` and `X`. -/
private theorem finite_quotient_span_X_sq (B : Type*) [CommRing B] :
    Module.Finite B (MvPowerSeries (Fin 1) B ⧸
      Ideal.span (Set.range ![(X 0 : MvPowerSeries (Fin 1) B) ^ 2])) := by
  set I := Ideal.span (Set.range ![(X 0 : MvPowerSeries (Fin 1) B) ^ 2])
  refine Module.Finite.of_surjective
    (Fintype.linearCombination B ![Ideal.Quotient.mk I 1, Ideal.Quotient.mk I (X 0)]) ?_
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨![constantCoeff f, coeff (Finsupp.single 0 1) f], ?_⟩
  rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Ideal.Quotient.mkₐ_eq_mk B, ← map_smul, ← map_smul, ← map_add, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq]
  obtain ⟨g, hg⟩ : (X 0 : MvPowerSeries (Fin 1) B) ^ 2 ∣
      constantCoeff f • 1 + coeff (Finsupp.single 0 1) f • X 0 - f := by
    refine X_pow_dvd_iff.mpr fun m hm => ?_
    have hm' : m = Finsupp.single 0 (m 0) := Finsupp.ext fun i => by fin_cases i; simp
    obtain h | h : m 0 = 0 ∨ m 0 = 1 := by omega
    · rw [hm', h]
      simp [coeff_zero_eq_constantCoeff_apply]
    · rw [hm', h]
      simp [coeff_one, coeff_X]
  rw [hg]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)

/-- A concrete instance with a substitution that is not the identity: `X ↦ X ^ 2` in one
variable, over any Noetherian local ring, meets every hypothesis. -/
example (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    ∃ (d : ℕ) (b : Fin d → MvPowerSeries (Fin 1) B), ∀ f : MvPowerSeries (Fin 1) B,
      ∃! c : Fin d → MvPowerSeries (Fin 1) B,
        f = ∑ j, MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 1) B) ^ 2] (c j) *
          b j :=
  MvPowerSeries.exists_basis_subst_of_finite_quotient_of_isLocalRing _
    (fun i => by fin_cases i; simp)
    ⟨2, fun i => by fin_cases i; exact Ideal.subset_span ⟨0, rfl⟩⟩
    (finite_quotient_span_X_sq B)
