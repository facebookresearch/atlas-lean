/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C.lean`
and
`P2M/Sol/S_PowerSeries_exists_ringEquiv_adicCompletion_quotient_span_X_sub_C.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.LinearCombination
import MathlibExt.RingTheory.PowerSeries.DVRQuotient

/-!
# The completion of a discrete valuation ring as a power series quotient

For a discrete valuation ring `O` with uniformizer `ϖ`, the `𝔪`-adic
completion of `O` is ring-equivalent to `O⟦X⟧ / (X - ϖ)`, with the
equivalence sending every constant from `O` to the corresponding constant
power series.
-/

@[expose] public section

namespace PowerSeriesAdicCompletionQuotientAux

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private noncomputable def psum (ϖ : O) (n : ℕ) (F : PowerSeries O) : O :=
  ∑ i ∈ Finset.range n, coeff i F * ϖ ^ i

private theorem psum_eq_eval_trunc (ϖ : O) (n : ℕ) (F : PowerSeries O) :
    psum ϖ n F = Polynomial.eval₂ (RingHom.id O) ϖ (trunc n F) := by
  rw [eval₂_trunc_eq_sum_range]; rfl

private theorem psum_add (ϖ : O) (n : ℕ) (F G : PowerSeries O) :
    psum ϖ n (F + G) = psum ϖ n F + psum ϖ n G := by
  simp only [psum, map_add, add_mul, Finset.sum_add_distrib]

private theorem psum_succ (ϖ : O) (n : ℕ) (F : PowerSeries O) :
    psum ϖ (n + 1) F = psum ϖ n F + coeff n F * ϖ ^ n := by
  simp [psum, Finset.sum_range_succ]

private theorem psum_sub_psum_mem (ϖ : O) {m n : ℕ} (h : n ≤ m) (F : PowerSeries O) :
    psum ϖ m F - psum ϖ n F ∈ Ideal.span {ϖ ^ n} := by
  induction m, h using Nat.le_induction with
  | base => rw [sub_self]; exact zero_mem _
  | succ m hnm ih =>
      rw [psum_succ, add_sub_right_comm]
      refine add_mem ih (Ideal.mem_span_singleton.mpr ⟨coeff m F * ϖ ^ (m - n), ?_⟩)
      rw [mul_comm (ϖ ^ n), mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]

private theorem mk_pow_zero_eq (x y : O) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ 0) x =
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ 0) y := by
  rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

private theorem psum_C (ϖ : O) {n : ℕ} (hn : 1 ≤ n) (o : O) : psum ϖ n (C o) = o := by
  induction n, hn using Nat.le_induction with
  | base => simp [psum, coeff_C]
  | succ m hm ih => rw [psum_succ, ih, coeff_C, ite_eq_right (by omega), zero_mul, add_zero]

private theorem psum_X (ϖ : O) {n : ℕ} (hn : 2 ≤ n) :
    psum ϖ n (X : PowerSeries O) = ϖ := by
  induction n, hn using Nat.le_induction with
  | base => simp [psum, Finset.sum_range_succ, coeff_X]
  | succ m hm ih => rw [psum_succ, ih, coeff_X, ite_eq_right (by omega), zero_mul, add_zero]

private theorem psum_mul_sub_mem (ϖ : O) (n : ℕ) (F G : PowerSeries O) :
    psum ϖ n (F * G) - psum ϖ n F * psum ϖ n G ∈ Ideal.span {ϖ ^ n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set p : Polynomial O := trunc (k + 1) F * trunc (k + 1) G with hp
  have h1 : psum ϖ (k + 1) (F * G) = psum ϖ (k + 1) (p : PowerSeries O) := by
    rw [psum_eq_eval_trunc, psum_eq_eval_trunc, ← trunc_trunc_mul_trunc, hp,
      Polynomial.coe_mul]
  have h2 : psum ϖ (k + 1) F * psum ϖ (k + 1) G =
      Polynomial.eval₂ (RingHom.id O) ϖ p := by
    rw [psum_eq_eval_trunc, psum_eq_eval_trunc, hp, Polynomial.eval₂_mul]
  have hdeg : p.natDegree < (k + 1) + (k + 1) :=
    calc p.natDegree ≤ (trunc (k + 1) F).natDegree + (trunc (k + 1) G).natDegree :=
          Polynomial.natDegree_mul_le
      _ < (k + 1) + (k + 1) :=
          add_lt_add (natDegree_trunc_lt F k) (natDegree_trunc_lt G k)
  have h3 : Polynomial.eval₂ (RingHom.id O) ϖ p =
      psum ϖ ((k + 1) + (k + 1)) (p : PowerSeries O) := by
    rw [psum_eq_eval_trunc, trunc_coe_eq_self hdeg]
  rw [h1, h2, h3, ← neg_sub]
  exact neg_mem (psum_sub_psum_mem ϖ (by omega) _)

private noncomputable def psi (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    PowerSeries O →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ n where
  toFun F := Ideal.Quotient.mk _ (psum ϖ n F)
  map_one' := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [← map_one (Ideal.Quotient.mk _)]; exact mk_pow_zero_eq _ _
    · rw [show (1 : PowerSeries O) = C 1 from (map_one C).symm, psum_C ϖ hn, map_one]
  map_mul' F G := by
    rw [← map_mul, Ideal.Quotient.eq,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.span_singleton_pow]
    exact psum_mul_sub_mem ϖ n F G
  map_zero' := by simp [psum]
  map_add' F G := by rw [psum_add, map_add]

private theorem psi_apply (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (F : PowerSeries O) :
    psi ϖ hϖ n F = Ideal.Quotient.mk _ (psum ϖ n F) := rfl

private theorem psi_compat (ϖ : O) (hϖ : Irreducible ϖ) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp
      (psi ϖ hϖ n) = psi ϖ hϖ m := by
  ext F
  simp only [RingHom.comp_apply, psi_apply, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.span_singleton_pow]
  exact psum_sub_psum_mem ϖ hle F

private noncomputable def Phi (ϖ : O) (hϖ : Irreducible ϖ) :
    PowerSeries O →+* AdicCompletion (IsLocalRing.maximalIdeal O) O :=
  AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O) (psi ϖ hϖ)
    (psi_compat ϖ hϖ)

private theorem evalₐ_Phi (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (F : PowerSeries O) :
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal O) n (Phi ϖ hϖ F) =
      Ideal.Quotient.mk _ (psum ϖ n F) :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ n F

private theorem Phi_C (ϖ : O) (hϖ : Irreducible ϖ) (o : O) :
    Phi ϖ hϖ (C o) = algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_Phi, AdicCompletion.algebraMap_apply]
  change _ = AdicCompletion.evalₐ _ n (AdicCompletion.of _ O o)
  rw [AdicCompletion.evalₐ_of]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact mk_pow_zero_eq _ _
  · rw [psum_C ϖ hn]

private theorem Phi_X (ϖ : O) (hϖ : Irreducible ϖ) :
    Phi ϖ hϖ X = algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) ϖ := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_Phi, AdicCompletion.algebraMap_apply]
  change _ = AdicCompletion.evalₐ _ n (AdicCompletion.of _ O ϖ)
  rw [AdicCompletion.evalₐ_of]
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact mk_pow_zero_eq _ _
    · rw [Ideal.Quotient.eq, pow_one]
      have h0 : psum ϖ 1 (X : PowerSeries O) = 0 := by simp [psum, coeff_X]
      rw [h0, zero_sub]
      exact neg_mem ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ ▸
        Ideal.mem_span_singleton_self ϖ)
  · rw [psum_X ϖ hn]

private theorem Phi_X_sub_C (ϖ : O) (hϖ : Irreducible ϖ) : Phi ϖ hϖ (X - C ϖ) = 0 := by
  rw [map_sub, Phi_X, Phi_C, sub_self]

private noncomputable def Phibar (ϖ : O) (hϖ : Irreducible ϖ) :
    (PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) - C ϖ}) →+*
      AdicCompletion (IsLocalRing.maximalIdeal O) O :=
  Ideal.Quotient.lift _ (Phi ϖ hϖ) fun F hF => by
    obtain ⟨G, rfl⟩ := Ideal.mem_span_singleton'.mp hF
    rw [map_mul, Phi_X_sub_C, mul_zero]

private theorem Phibar_mk (ϖ : O) (hϖ : Irreducible ϖ) (F : PowerSeries O) :
    Phibar ϖ hϖ (Ideal.Quotient.mk _ F) = Phi ϖ hϖ F := rfl

private theorem Phibar_mk_C (ϖ : O) (hϖ : Irreducible ϖ) (o : O) :
    Phibar ϖ hϖ (Ideal.Quotient.mk _ (C o)) =
      algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o := by
  rw [Phibar_mk, Phi_C]

private theorem Phi_surjective (ϖ : O) (hϖ : Irreducible ϖ) :
    Function.Surjective (Phi ϖ hϖ) := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  intro x
  induction x using AdicCompletion.induction_on with
  | h b =>
    have hd : ∀ n : ℕ, ∃ d : O, (b : ℕ → O) (n + 1) - (b : ℕ → O) n = ϖ ^ n * d := by
      intro n
      have h := (AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ n) b)
      rw [Submodule.Quotient.eq] at h
      have h' : (b : ℕ → O) (n + 1) - (b : ℕ → O) n ∈
          (IsLocalRing.maximalIdeal O) ^ n := by
        simpa [smul_eq_mul, Ideal.mul_top] using h
      have h'' : (b : ℕ → O) (n + 1) - (b : ℕ → O) n ∈ Ideal.span {ϖ ^ n} := by
        rw [← Ideal.span_singleton_pow, ← hmax]; exact h'
      exact Ideal.mem_span_singleton'.mp h'' |>.imp fun d hd => by rw [← hd, mul_comm]
    choose d hd using hd
    refine ⟨C ((b : ℕ → O) 0) + PowerSeries.mk d, ?_⟩
    have htel : ∀ n, psum ϖ n (C ((b : ℕ → O) 0) + PowerSeries.mk d) =
        if n = 0 then 0 else (b : ℕ → O) n := by
      intro n
      induction n with
      | zero => simp [psum]
      | succ n ih =>
          rw [psum_succ, ih, map_add, coeff_mk, coeff_C]
          simp only [Nat.succ_ne_zero, ite_false]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp only [ite_true, zero_add]
            linear_combination -(hd 0)
          · simp only [hn.ne', ite_false, zero_add]
            linear_combination -(hd n)
    refine AdicCompletion.ext_evalₐ fun n => ?_
    rw [evalₐ_Phi, AdicCompletion.evalₐ_mk, htel]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact mk_pow_zero_eq _ _
    · rw [ite_eq_right hn.ne']

private theorem Phibar_surjective (ϖ : O) (hϖ : Irreducible ϖ) :
    Function.Surjective (Phibar ϖ hϖ) := by
  intro x
  obtain ⟨F, hF⟩ := Phi_surjective ϖ hϖ x
  exact ⟨Ideal.Quotient.mk _ F, hF⟩

private theorem algebraMap_adicCompletion_injective :
    Function.Injective
      (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O)) := by
  haveI : IsHausdorff (IsLocalRing.maximalIdeal O) O :=
    IsHausdorff.of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  exact AdicCompletion.of_injective (IsLocalRing.maximalIdeal O) O

private theorem injective_of_apply_mk_C (ϖ : O) (hϖ : Irreducible ϖ)
    (Φbar : (PowerSeries O ⧸
        Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) →+*
      AdicCompletion (IsLocalRing.maximalIdeal O) O)
    (h : ∀ o : O, Φbar (Ideal.Quotient.mk _ (PowerSeries.C o)) =
      algebraMap O _ o) :
    Function.Injective Φbar := by
  obtain ⟨hdom, hdvr, -, hirr⟩ :=
    PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible ϖ hϖ
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra hz0
  obtain ⟨kk, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hirr
  have hpow : Φbar ((Ideal.Quotient.mk _ (PowerSeries.C ϖ)) ^ kk) = 0 := by
    have hu : IsUnit (Φbar
        (u : PowerSeries O ⧸
          Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})) :=
      (Units.isUnit u).map Φbar
    rw [map_mul] at hz
    exact (hu.mul_right_eq_zero).mp hz
  rw [map_pow, h ϖ, ← map_pow] at hpow
  have hzero : (ϖ ^ kk : O) = 0 := by
    apply algebraMap_adicCompletion_injective
    rw [hpow, map_zero]
  exact hϖ.ne_zero (pow_eq_zero_iff'.mp hzero).1

end PowerSeriesAdicCompletionQuotientAux

/-- The `𝔪`-adic completion of a discrete valuation ring `O` is ring
equivalent to `O⟦X⟧ / (X - ϖ)` for a uniformizer `ϖ`, and the equivalence
preserves every constant from `O`. -/
public theorem PowerSeries.exists_ringEquiv_adicCompletion_quotient_span_X_sub_C
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal O) O ≃+*
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}),
      ∀ o : O, e (algebraMap O (AdicCompletion (IsLocalRing.maximalIdeal O) O) o) =
        Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})
          (PowerSeries.C o) := by
  set e₀ := RingEquiv.ofBijective
      (PowerSeriesAdicCompletionQuotientAux.Phibar ϖ hϖ)
    ⟨PowerSeriesAdicCompletionQuotientAux.injective_of_apply_mk_C ϖ hϖ
        (PowerSeriesAdicCompletionQuotientAux.Phibar ϖ hϖ)
        (PowerSeriesAdicCompletionQuotientAux.Phibar_mk_C ϖ hϖ),
      PowerSeriesAdicCompletionQuotientAux.Phibar_surjective ϖ hϖ⟩ with he₀
  refine ⟨e₀.symm, fun o => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  exact (PowerSeriesAdicCompletionQuotientAux.Phibar_mk_C ϖ hϖ o).symm
