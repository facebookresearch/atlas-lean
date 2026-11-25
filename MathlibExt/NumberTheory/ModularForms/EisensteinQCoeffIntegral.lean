/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularForm_eisenstein_qCoeff_p_integral_dvd.lean`
and
`P2M/Sol/S_ModularForm_eisenstein_qCoeff_p_integral_dvd.lean`
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

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

@[expose] public section

open scoped ArithmeticFunction.sigma

/-- For a prime `p` with `p - 1 ∣ k`, the positive `q`-expansion coefficients of the
normalised Eisenstein series of even weight `k ≥ 3` are `p`-integral in the sense that,
after clearing a denominator prime to `p`, the resulting integer is divisible by `p`. -/
public theorem ModularForm.eisenstein_qCoeff_p_integral_dvd (p : ℕ) [Fact p.Prime] {k : ℕ}
    (hk : 3 ≤ k) (hk2 : Even k) (hpk : p - 1 ∣ k) (m : ℕ) (hm : 0 < m) :
    ∃ (x : ℤ) (s : ℕ), ¬ p ∣ s ∧
      (x : ℂ) = s * (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 ⇑(ModularForm.E hk)) ∧
      (p : ℤ) ∣ x := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨k', hk'⟩ : ∃ k', k = 2 * k' := ⟨k / 2, (Nat.two_mul_div_two_of_even hk2).symm⟩
  obtain ⟨A, hA⟩ := Bernoulli.vonStaudt_clausen k'
  set P : Finset ℕ :=
    Finset.filter (fun ℓ => ℓ.Prime ∧ (ℓ - 1) ∣ 2 * k') (Finset.range (2 * k' + 2)) with hPdef
  have hPprime : ∀ ℓ ∈ P, ℓ.Prime := fun ℓ hℓ => ((Finset.mem_filter.mp hℓ).2).1
  have hpP : p ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp, hk' ▸ hpk⟩
    have h1 : p - 1 ≤ 2 * k' := Nat.le_of_dvd (by omega) (hk' ▸ hpk)
    omega
  set D : ℤ := ∏ ℓ ∈ P, (ℓ : ℤ) with hDdef
  let E : ℕ → ℤ := fun ℓ => ∏ ℓ' ∈ P.erase ℓ, (ℓ' : ℤ)
  have hDE : ∀ ℓ ∈ P, D = (ℓ : ℤ) * E ℓ :=
    fun ℓ hℓ => (Finset.mul_prod_erase P (fun x : ℕ => (x : ℤ)) hℓ).symm
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ℓ hℓ => by
    exact_mod_cast (hPprime ℓ hℓ).ne_zero
  have hpD : (p : ℤ) ∣ D := Finset.dvd_prod_of_mem (fun x : ℕ => (x : ℤ)) hpP
  set Nb : ℤ := A * D - ∑ ℓ ∈ P, E ℓ with hNbdef
  have hB : bernoulli k = (Nb : ℚ) / (D : ℚ) := by
    have hsum : (∑ ℓ ∈ P, (1 : ℚ) / ℓ) = (∑ ℓ ∈ P, (E ℓ : ℚ)) / (D : ℚ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast (hPprime ℓ hℓ).ne_zero
      rw [eq_div_iff (by exact_mod_cast hD0), hDE ℓ hℓ]
      push_cast
      field_simp
    have hA' : bernoulli (2 * k') = (A : ℚ) - ∑ ℓ ∈ P, (1 : ℚ) / ℓ := by rw [hA]; ring
    rw [hk', hA', hsum, hNbdef]
    push_cast
    field_simp
  have hpE : ¬ (p : ℤ) ∣ E p := by
    intro h
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨ℓ, hℓ, hdvd⟩ := (hpr.dvd_finsetProd_iff _).mp h
    have hℓP : ℓ ∈ P := Finset.mem_of_mem_erase hℓ
    have hne : ℓ ≠ p := Finset.ne_of_mem_erase hℓ
    have : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp (hPprime ℓ hℓP)).mp (by exact_mod_cast hdvd)
    exact hne this.symm
  have hpNb : ¬ (p : ℤ) ∣ Nb := by
    intro h
    apply hpE
    have hrest : (p : ℤ) ∣ ∑ ℓ ∈ P.erase p, E ℓ := by
      refine Finset.dvd_sum fun ℓ hℓ => Finset.dvd_prod_of_mem (fun x : ℕ => (x : ℤ)) ?_
      exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hℓ).symm, hpP⟩
    have hsplit : ∑ ℓ ∈ P, E ℓ = E p + ∑ ℓ ∈ P.erase p, E ℓ := (Finset.add_sum_erase P E hpP).symm
    have hEp : E p = A * D - ∑ ℓ ∈ P.erase p, E ℓ - Nb := by rw [hNbdef, hsplit]; ring
    rw [hEp]
    exact ((hpD.mul_left A).sub hrest).sub h
  have hNb0 : Nb ≠ 0 := fun h => hpNb (h ▸ dvd_zero _)
  refine ⟨-(2 * k * D * (σ (k - 1) m : ℤ)) * Nb.sign, Nb.natAbs, ?_, ?_, ?_⟩
  · intro h
    exact hpNb (Int.natCast_dvd.mpr h)
  · rw [EisensteinSeries.E_qExpansion_coeff hk hk2 m, ite_eq_right hm.ne']
    have hs : ((Nb.natAbs : ℕ) : ℚ) = (Nb.sign : ℚ) * Nb := by
      have hz : ((Nb.natAbs : ℕ) : ℤ) = Nb.sign * Nb := by
        rcases lt_or_gt_of_ne hNb0 with hneg | hpos
        · rw [Int.ofNat_natAbs_of_nonpos hneg.le, Int.sign_eq_neg_one_of_neg hneg]; ring
        · rw [Int.natAbs_of_nonneg hpos.le, Int.sign_eq_one_of_pos hpos]; ring
      rw [← Int.cast_natCast (R := ℚ), hz]
      push_cast
      ring
    have key : ((-(2 * k * D * (σ (k - 1) m : ℤ)) * Nb.sign : ℤ) : ℚ)
        = ((Nb.natAbs : ℕ) : ℚ) * (-(2 * k / bernoulli k) * (σ (k - 1) m : ℚ)) := by
      rw [hs, hB]
      have hNbQ : (Nb : ℚ) ≠ 0 := by exact_mod_cast hNb0
      have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD0
      push_cast
      field_simp
    have keyC := congrArg (fun r : ℚ => (r : ℂ)) key
    push_cast at keyC ⊢
    exact keyC
  · exact Dvd.dvd.mul_right (Dvd.dvd.neg_right ((hpD.mul_left (2 * (k : ℤ))).mul_right _)) _
