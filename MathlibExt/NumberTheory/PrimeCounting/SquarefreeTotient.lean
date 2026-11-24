/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

namespace MathlibExt.NumberTheory.PrimeCounting


private theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := Real.log - fun y ↦ (y - y⁻¹) / 2
  have hf : AntitoneOn f (Set.Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · intro y hy
      have hypos : 0 < y := zero_lt_one.trans_le hy
      have hderiv : HasDerivAt f
          (y⁻¹ - (1 - -(y ^ 2)⁻¹) / 2) y := by
        exact (Real.hasDerivAt_log hypos.ne').sub
          (((hasDerivAt_id y).sub (hasDerivAt_inv hypos.ne')).div_const 2)
      exact hderiv.continuousAt.continuousWithinAt
    · intro y hy
      have hy' := interior_subset hy
      have hypos : 0 < y := zero_lt_one.trans_le hy'
      have hderiv := (Real.hasDerivAt_log hypos.ne').sub
        (((hasDerivAt_id y).sub (hasDerivAt_inv hypos.ne')).div_const 2)
      exact hderiv.differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' := interior_subset hy
      have hypos : 0 < y := zero_lt_one.trans_le hy'
      have hderiv : HasDerivAt f
          (y⁻¹ - (1 - -(y ^ 2)⁻¹) / 2) y := by
        exact (Real.hasDerivAt_log hypos.ne').sub
          (((hasDerivAt_id y).sub (hasDerivAt_inv hypos.ne')).div_const 2)
      rw [hderiv.deriv]
      have hy1 : 1 ≤ y := hy'
      field_simp
      nlinarith [sq_nonneg (y - 1)]
  have hfx := hf (by simp) (show x ∈ Set.Ici 1 from hx) hx
  dsimp only [f] at hfx
  norm_num at hfx
  linarith

private noncomputable def harmonicLowerApprox (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ))

private theorem harmonicLowerApprox_mono : Monotone harmonicLowerApprox := by
  apply monotone_nat_of_le_succ
  intro n
  have hlog := log_le_half_sub_inv
    (show (1 : ℝ) ≤ (n + 2 : ℝ) / (n + 1 : ℝ) by
      rw [le_div_iff₀ (by positivity)]
      norm_num)
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have hharm : (harmonic (n + 2) : ℝ) =
      harmonic (n + 1) + 1 / (n + 2 : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ]
    push_cast
    ring
  rw [harmonicLowerApprox, harmonicLowerApprox, hharm]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hid :
      (((n + 2 : ℝ) / (n + 1 : ℝ) -
        ((n + 2 : ℝ) / (n + 1 : ℝ))⁻¹) / 2) =
        1 / (2 * (n + 1 : ℝ)) + 1 / (2 * (n + 2 : ℝ)) := by
    field_simp
    ring
  rw [hid] at hlog
  have hhalf :
      1 / (n + 2 : ℝ) - 1 / (2 * (n + 2 : ℝ)) = 1 / (2 * (n + 2 : ℝ)) := by
    field_simp
    ring
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  linarith

private theorem tendsto_harmonicLowerApprox :
    Filter.Tendsto harmonicLowerApprox Filter.atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hmain := Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv : Filter.Tendsto (fun n : ℕ ↦ (1 / (2 * (n + 1 : ℝ)) : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [one_div, mul_inv, mul_comm] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ))
  change Filter.Tendsto (fun n : ℕ ↦
    (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ)))
      Filter.atTop (nhds Real.eulerMascheroniConstant)
  convert hmain.sub hinv using 1
  · funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  · simp

private theorem harmonic_le_log_add_gamma_add_half (n : ℕ) (hn : 0 < n) :
    (harmonic n : ℝ) ≤ Real.log n + Real.eulerMascheroniConstant + 1 / (2 * n) := by
  have hle : harmonicLowerApprox (n - 1) ≤ Real.eulerMascheroniConstant :=
    harmonicLowerApprox_mono.ge_of_tendsto tendsto_harmonicLowerApprox (n - 1)
  dsimp only [harmonicLowerApprox] at hle
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hnEq] at hle
  have hnEqR := congrArg (fun k : ℕ ↦ (k : ℝ)) hnEq
  norm_num at hnEqR
  rw [hnEqR] at hle
  linarith

private noncomputable def harmonicLowerError (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ) + 1)

private theorem harmonicLowerError_antitone : Antitone harmonicLowerError := by
  apply antitone_nat_of_succ_le
  intro n
  have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  have hlog := Real.lt_log_one_add_of_pos hpos
  have hharm : (harmonic (n + 2) : ℝ) =
      harmonic (n + 1) + 1 / (n + 2 : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, harmonic_succ]
    push_cast
    ring
  rw [harmonicLowerError, harmonicLowerError, hharm]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring]
  have hlog' : Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) =
      Real.log (1 + 1 / ((n : ℝ) + 1)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  rw [← hlog'] at hlog
  have hrat : 1 / ((n : ℝ) + 2) + 1 / (2 * ((n : ℝ) + 1) + 1) -
      1 / (2 * ((n : ℝ) + 2) + 1) ≤ 2 / (2 * ((n : ℝ) + 1) + 1) := by
    field_simp
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlog'' : 2 / (2 * ((n : ℝ) + 1) + 1) <
      Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) := by
    calc
      2 / (2 * ((n : ℝ) + 1) + 1) =
          2 * (1 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 1) + 2) := by
        field_simp
        ring
      _ < _ := hlog
  linarith

private theorem tendsto_harmonicLowerError :
    Filter.Tendsto harmonicLowerError Filter.atTop
      (nhds Real.eulerMascheroniConstant) := by
  have hmain := Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1)
  have hinv : Filter.Tendsto
      (fun n : ℕ ↦ (1 / (2 * (n + 1 : ℝ) + 1) : ℝ)) Filter.atTop (nhds 0) := by
    apply squeeze_zero (g := fun n : ℕ ↦ (1 / (n + 1 : ℝ)))
    · intro n
      positivity
    · intro n
      apply one_div_le_one_div_of_le (by positivity)
      norm_num
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  change Filter.Tendsto (fun n : ℕ ↦
    (harmonic (n + 1) : ℝ) - Real.log (n + 1) - 1 / (2 * (n + 1 : ℝ) + 1))
      Filter.atTop (nhds Real.eulerMascheroniConstant)
  convert hmain.sub hinv using 1
  · funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  · simp

private theorem harmonic_ge_log_add_gamma_add_lower (n : ℕ) (hn : 0 < n) :
    Real.log n + Real.eulerMascheroniConstant + 1 / (2 * (n : ℝ) + 1) ≤
      (harmonic n : ℝ) := by
  have hle : Real.eulerMascheroniConstant ≤ harmonicLowerError (n - 1) :=
    harmonicLowerError_antitone.le_of_tendsto tendsto_harmonicLowerError (n - 1)
  dsimp only [harmonicLowerError] at hle
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hnCast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnEq
  rw [hnEq, hnCast] at hle
  linarith

private theorem harmonic_sub_lower (a b k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hab : k * a ≤ b) :
    Real.log k + 1 / (2 * (b : ℝ) + 1) - 1 / (2 * (a : ℝ)) ≤
      (harmonic b : ℝ) - harmonic a := by
  have hb : 0 < b := lt_of_lt_of_le (Nat.mul_pos hk ha) hab
  have hlower := harmonic_ge_log_add_gamma_add_lower b hb
  have hupper := harmonic_le_log_add_gamma_add_half a ha
  have hlog : Real.log k + Real.log a ≤ Real.log b := by
    calc
      Real.log k + Real.log a = Real.log ((k : ℝ) * a) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ Real.log b := Real.log_le_log (by positivity) (by exact_mod_cast hab)
  linarith

private theorem harmonic_sub_upper_two (t w : ℕ) (ht : 0 < t) (hw : 0 < w)
    (hwt : w ≤ 2 * t + 1) :
    (harmonic w : ℝ) - harmonic t ≤
      Real.log 2 + 1 / (2 * (t : ℝ)) + 1 / (2 * (w : ℝ)) -
        1 / (2 * (t : ℝ) + 1) := by
  have hupper := harmonic_le_log_add_gamma_add_half w hw
  have hlower := harmonic_ge_log_add_gamma_add_lower t ht
  have hratio : (w : ℝ) / t ≤ 2 + 1 / (t : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    calc
      (w : ℝ) ≤ 2 * t + 1 := by exact_mod_cast hwt
      _ = (2 + 1 / (t : ℝ)) * t := by
        field_simp
  have hlog : Real.log w - Real.log t ≤ Real.log 2 + 1 / (2 * (t : ℝ)) := by
    calc
      Real.log w - Real.log t = Real.log ((w : ℝ) / t) := by
        rw [Real.log_div (by positivity) (by positivity)]
      _ ≤ Real.log (2 + 1 / (t : ℝ)) :=
        Real.log_le_log (by positivity) hratio
      _ = Real.log 2 + Real.log (1 + 1 / (2 * (t : ℝ))) := by
        rw [show 2 + 1 / (t : ℝ) = 2 * (1 + 1 / (2 * (t : ℝ))) by
          field_simp]
        rw [Real.log_mul (by norm_num) (by positivity)]
      _ ≤ Real.log 2 + 1 / (2 * (t : ℝ)) := by
        gcongr
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 1 + 1 / (2 * (t : ℝ)) by positivity)
        linarith
  linarith

private theorem gamma_gt_fiftySeven :
    (57 / 100 : ℝ) < Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 127
  rw [Real.eulerMascheroniSeq] at h
  norm_num [harmonic] at h
  rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow] at h
  have h2 := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

open scoped BigOperators

private noncomputable def invNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by push_cast; rw [mul_inv]

private theorem invNatHom_prime_lt_one {p : ℕ} (hp : p.Prime) :
    ‖invNatHom p‖ < 1 := by
  rw [show invNatHom p = (p : ℝ)⁻¹ by rfl, norm_inv, Real.norm_natCast]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

private theorem radical_squarefree (n : ℕ) :
    Squarefree (∏ p ∈ n.primeFactors, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).squarefree

private theorem factored_inv_sum (r : ℕ) :
    HasSum (fun m : Nat.factoredNumbers r.primeFactors ↦
      ((r : ℝ) * (m : ℕ))⁻¹) (Nat.totient r : ℝ)⁻¹ := by
  have hsum := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    invNatHom_prime_lt_one r.primeFactors).2
  have hprime : r.primeFactors.filter Nat.Prime = r.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  rw [hprime] at hsum
  have hscaled := hsum.mul_left (r : ℝ)⁻¹
  simp only [invNatHom, MonoidHom.coe_mk, OneHom.coe_mk] at hscaled
  have hvalue :
      (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ =
        (Nat.totient r : ℝ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    have htot := congrArg (fun x : ℚ ↦ (x : ℝ))
      (Nat.totient_eq_mul_prod_factors r)
    norm_num at htot
    rw [htot]
    rw [mul_inv]
  rw [hvalue] at hscaled
  simpa only [mul_inv] using hscaled

private def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

private theorem radical_dvd (n : ℕ) : radical n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

private theorem radical_primeFactors (n : ℕ) : (radical n).primeFactors = n.primeFactors := by
  exact Nat.primeFactors_prod_primeFactors n

private theorem radical_pos {n : ℕ} (hn : 0 < n) : 0 < radical n := by
  exact Nat.pos_of_dvd_of_pos (radical_dvd n) hn

private theorem radical_fiber_le (y r : ℕ) (hr : 0 < r) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n ↦ radical n = r), (n : ℝ)⁻¹) ≤
      (Nat.totient r : ℝ)⁻¹ := by
  let A := (Finset.Icc 1 y).filter (fun n ↦ radical n = r)
  have hmem (n : ℕ) (hn : n ∈ A) : n / r ∈ Nat.factoredNumbers r.primeFactors := by
    have hnData := Finset.mem_filter.mp hn
    have hnRange := Finset.mem_Icc.mp hnData.1
    have hnpos : 0 < n := by omega
    have hdiv : r ∣ n := hnData.2 ▸ radical_dvd n
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpm
    have hpmn : p ∣ n := by
      rw [← Nat.mul_div_cancel' hdiv]
      exact dvd_mul_of_dvd_right hpm r
    have hpFact : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpmn, hnpos.ne'⟩
    rw [← hnData.2, radical_primeFactors]
    exact hpFact
  let e : {n // n ∈ A} → Nat.factoredNumbers r.primeFactors := fun n ↦
    ⟨n / r, hmem n n.2⟩
  have he : Function.Injective e := by
    intro m n hmn
    apply Subtype.ext
    have hmData := Finset.mem_filter.mp m.2
    have hnData := Finset.mem_filter.mp n.2
    have hdm : r ∣ m := hmData.2 ▸ radical_dvd m
    have hdn : r ∣ n := hnData.2 ▸ radical_dvd n
    have hquot : (m : ℕ) / r = (n : ℕ) / r :=
      congrArg (fun x : Nat.factoredNumbers r.primeFactors ↦ (x : ℕ)) hmn
    calc
      (m : ℕ) = r * (m / r) := (Nat.mul_div_cancel' hdm).symm
      _ = r * (n / r) := by rw [hquot]
      _ = (n : ℕ) := Nat.mul_div_cancel' hdn
  have hsum := factored_inv_sum r
  calc
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n ↦ radical n = r), (n : ℝ)⁻¹) =
        ∑ m ∈ Finset.image e A.attach, ((r : ℝ) * (m : ℕ))⁻¹ := by
      rw [show (Finset.Icc 1 y).filter (fun n ↦ radical n = r) = A by rfl]
      rw [Finset.sum_image he.injOn]
      calc
        (∑ n ∈ A, (n : ℝ)⁻¹) = ∑ n ∈ A.attach, ((n : ℕ) : ℝ)⁻¹ := by
          exact (Finset.sum_attach A (fun n ↦ (n : ℝ)⁻¹)).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnData := Finset.mem_filter.mp n.2
          have hdiv : r ∣ n := hnData.2 ▸ radical_dvd n
          congr 1
          change ((n : ℕ) : ℝ) = (r : ℝ) * (((n : ℕ) / r : ℕ) : ℝ)
          exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    _ ≤ ∑' m : Nat.factoredNumbers r.primeFactors,
        ((r : ℝ) * (m : ℕ))⁻¹ := by
      exact hsum.summable.sum_le_tsum _ (fun _ _ ↦ by positivity)
    _ = (Nat.totient r : ℝ)⁻¹ := hsum.tsum_eq

private theorem coprimeSixHarmonic_le_squarefreeTotient (y : ℕ) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n ↦ Nat.Coprime n 6), (n : ℝ)⁻¹) ≤
      ∑ r ∈ (Finset.Icc 1 y).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r),
        (Nat.totient r : ℝ)⁻¹ := by
  let C := (Finset.Icc 1 y).filter (fun n ↦ Nat.Coprime n 6)
  let I := Finset.image radical C
  let R := (Finset.Icc 1 y).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r)
  let F : ℕ → ℝ := fun r ↦
    ∑ n ∈ C.filter (fun n ↦ radical n = r), (n : ℝ)⁻¹
  have hpartition : (∑ n ∈ C, (n : ℝ)⁻¹) = ∑ r ∈ I, F r := by
    symm
    apply Finset.sum_image'
    intro n hn
    rfl
  have hIR : I ⊆ R := by
    intro r hrI
    rcases Finset.mem_image.mp hrI with ⟨n, hnC, rfl⟩
    have hnData := Finset.mem_filter.mp hnC
    have hnRange := Finset.mem_Icc.mp hnData.1
    have hnpos : 0 < n := by omega
    have hradpos := radical_pos hnpos
    have hradle := Nat.le_of_dvd hnpos (radical_dvd n)
    have hcop : Nat.Coprime (radical n) 6 :=
      hnData.2.of_dvd_left (radical_dvd n)
    simp only [R, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hradle.trans hnRange.2⟩, hcop, radical_squarefree n⟩
  rw [show (Finset.Icc 1 y).filter (fun n ↦ Nat.Coprime n 6) = C by rfl,
    show (Finset.Icc 1 y).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r) = R by rfl,
    hpartition]
  calc
    (∑ r ∈ I, F r) ≤ ∑ r ∈ I, (Nat.totient r : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hrI
      have hrR := Finset.mem_of_subset hIR hrI
      have hrpos : 0 < r := by
        exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hrR).1).1
      calc
        F r ≤ ∑ n ∈ (Finset.Icc 1 y).filter (fun n ↦ radical n = r),
            (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            have hnData := Finset.mem_filter.mp hn
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnData.1).1, hnData.2⟩
          · intro n _ _
            positivity
        _ ≤ (Nat.totient r : ℝ)⁻¹ := radical_fiber_le y r hrpos
    _ ≤ ∑ r ∈ R, (Nat.totient r : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hIR
      intro r _ _
      positivity

private def sixMultipliers : Finset ℕ := {1, 2, 3, 6}

private theorem mem_sixMultipliers {m : ℕ} (hm : m ∈ sixMultipliers) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
  simpa only [sixMultipliers, Finset.mem_insert, Finset.mem_singleton] using hm

private theorem sixMultiplier_dvd {m : ℕ} (hm : m ∈ sixMultipliers) : m ∣ 6 := by
  rcases mem_sixMultipliers hm with rfl | rfl | rfl | rfl <;> norm_num

private theorem sixMultiplier_squarefree {m : ℕ} (hm : m ∈ sixMultipliers) :
    Squarefree m := by
  rcases mem_sixMultipliers hm with rfl | rfl | rfl | rfl
  · exact squarefree_one
  · exact Nat.prime_two.squarefree
  · exact Nat.prime_three.squarefree
  · exact (Nat.squarefree_mul (by norm_num)).mpr
      ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩

private theorem gcd_mul_six {m r : ℕ} (hm : m ∈ sixMultipliers)
    (hr : Nat.Coprime r 6) : Nat.gcd (m * r) 6 = m := by
  rcases mem_sixMultipliers hm with rfl | rfl | rfl | rfl
  · simpa using hr.gcd_eq_one
  · have hr3 : Nat.Coprime r 3 := hr.of_dvd_right (by norm_num)
    calc
      Nat.gcd (2 * r) 6 = Nat.gcd (2 * r) (2 * 3) := by norm_num
      _ = 2 * Nat.gcd r 3 := Nat.gcd_mul_left 2 r 3
      _ = 2 := by rw [hr3.gcd_eq_one]
  · have hr2 : Nat.Coprime r 2 := hr.of_dvd_right (by norm_num)
    calc
      Nat.gcd (3 * r) 6 = Nat.gcd (3 * r) (3 * 2) := by norm_num
      _ = 3 * Nat.gcd r 2 := Nat.gcd_mul_left 3 r 2
      _ = 3 := by rw [hr2.gcd_eq_one]
  · calc
      Nat.gcd (6 * r) 6 = Nat.gcd (6 * r) (6 * 1) := by norm_num
      _ = 6 * Nat.gcd r 1 := Nat.gcd_mul_left 6 r 1
      _ = 6 := by simp

private noncomputable def squarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter Squarefree, (Nat.totient r : ℝ)⁻¹

private noncomputable def coprimeSquarefreeTotientSum (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r),
    (Nat.totient r : ℝ)⁻¹

private noncomputable def coprimeSixHarmonic (z : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r 6), (r : ℝ)⁻¹

private theorem squarefreeTotientSum_ge_multiplierSum (z : ℕ) :
    (∑ m ∈ sixMultipliers, (Nat.totient m : ℝ)⁻¹ *
      coprimeSquarefreeTotientSum (z / m)) ≤ squarefreeTotientSum z := by
  let P := (sixMultipliers ×ˢ Finset.Icc 1 z).filter (fun p ↦
    p.2 ≤ z / p.1 ∧ Nat.Coprime p.2 6 ∧ Squarefree p.2)
  let A := (Finset.Icc 1 z).filter Squarefree
  let e : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  let f : ℕ × ℕ → ℝ := fun p ↦
    (Nat.totient p.1 : ℝ)⁻¹ * (Nat.totient p.2 : ℝ)⁻¹
  let g : ℕ → ℝ := fun n ↦ (Nat.totient n : ℝ)⁻¹
  have he : Set.InjOn e (P : Set (ℕ × ℕ)) := by
    intro p hp q hq hpq
    have hpData := Finset.mem_filter.mp hp
    have hqData := Finset.mem_filter.mp hq
    have hpProd := Finset.mem_product.mp hpData.1
    have hqProd := Finset.mem_product.mp hqData.1
    have hgcd := congrArg (fun n ↦ Nat.gcd n 6) hpq
    have hm : p.1 = q.1 := by
      simpa only [e, gcd_mul_six hpProd.1 hpData.2.2.1,
        gcd_mul_six hqProd.1 hqData.2.2.1] using hgcd
    apply Prod.ext hm
    have hmpos : 0 < p.1 := by
      rcases mem_sixMultipliers hpProd.1 with h | h | h | h <;> omega
    apply Nat.eq_of_mul_eq_mul_left hmpos
    simpa only [e, hm] using hpq
  have heA : Finset.image e P ⊆ A := by
    rw [Finset.image_subset_iff]
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hpData.1
    have hmpos : 0 < p.1 := by
      rcases mem_sixMultipliers hpProd.1 with h | h | h | h <;> omega
    have hrpos : 0 < p.2 := (Finset.mem_Icc.mp hpProd.2).1
    have hmr : Nat.Coprime p.1 p.2 :=
      Nat.Coprime.of_dvd_left (sixMultiplier_dvd hpProd.1) hpData.2.2.1.symm
    have hsq : Squarefree (p.1 * p.2) :=
      (Nat.squarefree_mul hmr).mpr ⟨sixMultiplier_squarefree hpProd.1, hpData.2.2.2⟩
    simp only [A, e, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.mul_pos hmpos hrpos, ?_⟩, hsq⟩
    simpa only [mul_comm] using (Nat.le_div_iff_mul_le hmpos).mp hpData.2.1
  have hterm : ∀ p ∈ P, f p = g (e p) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hpData.1
    have hmr : Nat.Coprime p.1 p.2 :=
      Nat.Coprime.of_dvd_left (sixMultiplier_dvd hpProd.1) hpData.2.2.1.symm
    simp only [f, g, e]
    rw [Nat.totient_mul hmr]
    push_cast
    rw [mul_inv]
  have hinj : (∑ p ∈ P, f p) ≤ ∑ n ∈ A, g n := by
    exact Finset.sum_le_sum_of_injOn e he heA (fun p hp ↦ (hterm p hp).le)
      (fun n hnA hn ↦ by positivity)
  change (∑ m ∈ sixMultipliers, (Nat.totient m : ℝ)⁻¹ *
    coprimeSquarefreeTotientSum (z / m)) ≤ squarefreeTotientSum z
  rw [squarefreeTotientSum]
  change _ ≤ ∑ n ∈ A, g n
  refine (le_of_eq ?_).trans hinj
  change (∑ m ∈ sixMultipliers, (Nat.totient m : ℝ)⁻¹ *
    coprimeSquarefreeTotientSum (z / m)) =
      ∑ p ∈ (sixMultipliers ×ˢ Finset.Icc 1 z).filter (fun p ↦
        p.2 ≤ z / p.1 ∧ Nat.Coprime p.2 6 ∧ Squarefree p.2), f p
  rw [Finset.sum_filter, Finset.sum_product]
  simp only [f, coprimeSquarefreeTotientSum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  have hmpos : 0 < m := by
    rcases mem_sixMultipliers hm with h | h | h | h <;> omega
  have hsets :
      (Finset.Icc 1 (z / m)).filter (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r) =
        (Finset.Icc 1 z).filter (fun r ↦
          r ≤ z / m ∧ Nat.Coprime r 6 ∧ Squarefree r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨⟨h.1.1, h.1.2.trans (Nat.div_le_self z m)⟩, h.1.2, h.2.1, h.2.2⟩
    · intro h
      exact ⟨⟨h.1.1, h.2.1⟩, h.2.2.1, h.2.2.2⟩
  calc
    (∑ r ∈ (Finset.Icc 1 (z / m)).filter
        (fun r ↦ Nat.Coprime r 6 ∧ Squarefree r),
        (Nat.totient m : ℝ)⁻¹ * (Nat.totient r : ℝ)⁻¹) =
      ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦
        r ≤ z / m ∧ Nat.Coprime r 6 ∧ Squarefree r),
        (Nat.totient m : ℝ)⁻¹ * (Nat.totient r : ℝ)⁻¹ := by rw [hsets]
    _ = _ := Finset.sum_filter _ _

private theorem squarefreeTotientSum_ge_harmonicCombination (z : ℕ) :
    coprimeSixHarmonic z + coprimeSixHarmonic (z / 2) +
        (1 / 2 : ℝ) * coprimeSixHarmonic (z / 3) +
        (1 / 2 : ℝ) * coprimeSixHarmonic (z / 6) ≤
      squarefreeTotientSum z := by
  apply le_trans ?_ (squarefreeTotientSum_ge_multiplierSum z)
  have hsum :
      (∑ m ∈ sixMultipliers, (Nat.totient m : ℝ)⁻¹ *
        coprimeSixHarmonic (z / m)) ≤
      ∑ m ∈ sixMultipliers, (Nat.totient m : ℝ)⁻¹ *
        coprimeSquarefreeTotientSum (z / m) := by
    apply Finset.sum_le_sum
    intro m hm
    exact mul_le_mul_of_nonneg_left
      (coprimeSixHarmonic_le_squarefreeTotient (z / m)) (by positivity)
  apply le_trans ?_ hsum
  have hphi2 : Nat.totient 2 = 1 := by
    rw [Nat.totient_prime Nat.prime_two]
  have hphi3 : Nat.totient 3 = 2 := by
    rw [Nat.totient_prime Nat.prime_three]
  have hphi6 : Nat.totient 6 = 2 := by
    rw [show 6 = 2 * 3 by norm_num, Nat.totient_mul (by norm_num), hphi2, hphi3]
  rw [sixMultipliers]
  norm_num [hphi2, hphi3, hphi6]
  ring_nf
  rfl

private theorem multiplesInvSum (n d : ℕ) (hd : 0 < d) :
    (∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ d ∣ k), (k : ℝ)⁻¹) =
      (d : ℝ)⁻¹ * (harmonic (n / d) : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun k _ ↦ k / d) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    simp only [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hk.2) hd,
      (Nat.le_div_iff_mul_le hd).mpr (by
        rw [mul_comm, Nat.mul_div_cancel' hk.2]
        exact hk.1.2)⟩
  · intro k hk l hl hkl
    simp only [Finset.mem_filter] at hk hl
    rw [← Nat.mul_div_cancel' hk.2, ← Nat.mul_div_cancel' hl.2, hkl]
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨d * j, ?_, Nat.mul_div_cancel_left j hd⟩
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.dvd_mul_right]
    constructor
    · exact ⟨Nat.mul_pos hd (by omega), by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd).mp hj.2⟩
    · simp
  · intro k hk
    simp only [Finset.mem_filter] at hk
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk.1).1
    have hdivpos : 0 < k / d := Nat.div_pos (Nat.le_of_dvd hkpos hk.2) hd
    calc
      (k : ℝ)⁻¹ = ((d * (k / d) : ℕ) : ℝ)⁻¹ := by
        rw [Nat.mul_div_cancel' hk.2]
      _ = (d : ℝ)⁻¹ * ((k / d : ℕ) : ℝ)⁻¹ := by
        push_cast
        rw [mul_inv]

private theorem coprimeSix_iff (n : ℕ) :
    Nat.Coprime n 6 ↔ ¬2 ∣ n ∧ ¬3 ∣ n := by
  rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_right]
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two,
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]

private noncomputable def C (n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 n).filter (fun k ↦ Nat.Coprime k 6), (k : ℝ)⁻¹

private theorem coprimeSixHarmonic_eq (n : ℕ) : coprimeSixHarmonic n =
    (harmonic n : ℝ) - (1 / 2 : ℝ) * harmonic (n / 2) -
      (1 / 3 : ℝ) * harmonic (n / 3) + (1 / 6 : ℝ) * harmonic (n / 6) := by
  rw [coprimeSixHarmonic, Finset.sum_filter]
  have hpoint (k : ℕ) :
      (if Nat.Coprime k 6 then (k : ℝ)⁻¹ else 0) =
        (k : ℝ)⁻¹ - (if 2 ∣ k then (k : ℝ)⁻¹ else 0) -
          (if 3 ∣ k then (k : ℝ)⁻¹ else 0) +
            (if 6 ∣ k then (k : ℝ)⁻¹ else 0) := by
    simp only [coprimeSix_iff]
    by_cases h2 : 2 ∣ k <;> by_cases h3 : 3 ∣ k <;>
      simp only [h2, h3, not_true_eq_false, not_false_eq_true, and_self,
        false_and, ite_false, ite_true]
    · have h6 : 6 ∣ k := by
        rw [show 6 = 2 * 3 by norm_num]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      simp [h6]
    all_goals
      have h6 : ¬6 ∣ k := by
        intro h
        first | exact h2 (dvd_trans (by norm_num) h) |
          exact h3 (dvd_trans (by norm_num) h)
      simp [h6]
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [multiplesInvSum n 2 (by norm_num), multiplesInvSum n 3 (by norm_num),
    multiplesInvSum n 6 (by norm_num)]
  norm_num

private noncomputable def btHarmonicCombination (z : ℕ) : ℝ :=
  coprimeSixHarmonic z + coprimeSixHarmonic (z / 2) +
    (1 / 2 : ℝ) * coprimeSixHarmonic (z / 3) +
    (1 / 2 : ℝ) * coprimeSixHarmonic (z / 6)

private theorem btHarmonicCombination_sub (z : ℕ) :
    btHarmonicCombination z - (harmonic z : ℝ) =
      (1 / 2 : ℝ) * ((harmonic (z / 2) : ℝ) - harmonic (z / 4)) +
      (1 / 6 : ℝ) * ((harmonic (z / 3) : ℝ) - harmonic (z / 9)) +
      (1 / 12 : ℝ) * ((harmonic (z / 6) : ℝ) - harmonic (z / 12) -
        harmonic (z / 18) + harmonic (z / 36)) := by
  rw [btHarmonicCombination, coprimeSixHarmonic_eq, coprimeSixHarmonic_eq,
    coprimeSixHarmonic_eq, coprimeSixHarmonic_eq]
  simp only [Nat.div_div_eq_div_mul]
  norm_num
  ring

private theorem btHarmonicCombination_sub_gt_half (z : ℕ) (hz : 100 ≤ z) :
    (1 / 2 : ℝ) < btHarmonicCombination z - harmonic z := by
  let A := z / 4
  let B := z / 2
  let C := z / 9
  let D := z / 3
  let U := z / 6
  let V := z / 12
  let W := z / 18
  let T := z / 36
  have hA : 25 ≤ A := by simp only [A]; omega
  have hC : 11 ≤ C := by simp only [C]; omega
  have hV : 8 ≤ V := by simp only [V]; omega
  have hT : 2 ≤ T := by simp only [T]; omega
  have hAB₁ : 2 * A ≤ B := by simp only [A, B]; omega
  have hAB₂ : B ≤ 2 * A + 1 := by simp only [A, B]; omega
  have hCD₁ : 3 * C ≤ D := by simp only [C, D]; omega
  have hCD₂ : D ≤ 3 * C + 2 := by simp only [C, D]; omega
  have hVU₁ : 2 * V ≤ U := by simp only [U, V]; omega
  have hVU₂ : U ≤ 2 * V + 1 := by simp only [U, V]; omega
  have hTW₁ : 2 * T ≤ W := by simp only [T, W]; omega
  have hTW₂ : W ≤ 2 * T + 1 := by simp only [T, W]; omega
  have hBA := harmonic_sub_lower A B 2 (by omega) (by norm_num) hAB₁
  have hDC := harmonic_sub_lower C D 3 (by omega) (by norm_num) hCD₁
  have hUV := harmonic_sub_lower V U 2 (by omega) (by norm_num) hVU₁
  have hWT := harmonic_sub_upper_two T W (by omega) (by omega) hTW₂
  have hBAcorr : (-21 / 4000 : ℝ) ≤
      (1 / 2 : ℝ) * (1 / (2 * (B : ℝ) + 1) - 1 / (2 * (A : ℝ))) := by
    have hinv : 1 / (4 * (A : ℝ) + 3) ≤ 1 / (2 * (B : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (show 2 * B + 1 ≤ 4 * A + 3 by omega)
    calc
      (-21 / 4000 : ℝ) ≤
          (1 / 2 : ℝ) * (1 / (4 * A + 3) - 1 / (2 * A)) := by
        field_simp
        nlinarith [show (25 : ℝ) ≤ A by exact_mod_cast hA]
      _ ≤ _ := by gcongr
  have hDCcorr : (-21 / 4000 : ℝ) ≤
      (1 / 6 : ℝ) * (1 / (2 * (D : ℝ) + 1) - 1 / (2 * (C : ℝ))) := by
    have hinv : 1 / (6 * (C : ℝ) + 5) ≤ 1 / (2 * (D : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (show 2 * D + 1 ≤ 6 * C + 5 by omega)
    calc
      (-21 / 4000 : ℝ) ≤
          (1 / 6 : ℝ) * (1 / (6 * C + 5) - 1 / (2 * C)) := by
        field_simp
        nlinarith [show (11 : ℝ) ≤ C by exact_mod_cast hC]
      _ ≤ _ := by gcongr
  have hUVcorr : (-3 / 1000 : ℝ) ≤
      (1 / 12 : ℝ) * (1 / (2 * (U : ℝ) + 1) - 1 / (2 * (V : ℝ))) := by
    have hinv : 1 / (4 * (V : ℝ) + 3) ≤ 1 / (2 * (U : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast (show 2 * U + 1 ≤ 4 * V + 3 by omega)
    calc
      (-3 / 1000 : ℝ) ≤
          (1 / 12 : ℝ) * (1 / (4 * V + 3) - 1 / (2 * V)) := by
        field_simp
        nlinarith [show (8 : ℝ) ≤ V by exact_mod_cast hV]
      _ ≤ _ := by gcongr
  have hTcorr : (-7 / 480 : ℝ) ≤ (1 / 12 : ℝ) *
      (-1 / (2 * (T : ℝ)) - 1 / (2 * (W : ℝ)) + 1 / (2 * T + 1)) := by
    have hinv : 1 / (2 * (W : ℝ)) ≤ 1 / (4 * (T : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have h : 4 * T ≤ 2 * W := by omega
      exact_mod_cast h
    calc
      (-7 / 480 : ℝ) ≤ (1 / 12 : ℝ) *
          (-1 / (2 * T) - 1 / (4 * T) + 1 / (2 * T + 1)) := by
        field_simp
        nlinarith [show (2 : ℝ) ≤ T by exact_mod_cast hT]
      _ ≤ _ := by gcongr
  have hBA' := mul_le_mul_of_nonneg_left hBA (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hDC' := mul_le_mul_of_nonneg_left hDC (show (0 : ℝ) ≤ 1 / 6 by norm_num)
  have hUV' := mul_le_mul_of_nonneg_left hUV (show (0 : ℝ) ≤ 1 / 12 by norm_num)
  have hWT' := mul_le_mul_of_nonneg_left hWT (show (0 : ℝ) ≤ 1 / 12 by norm_num)
  norm_num only [Nat.cast_ofNat] at hBA' hDC' hUV'
  have hBAfinal : (1 / 2 : ℝ) * Real.log 2 - 21 / 4000 ≤
      (1 / 2 : ℝ) * ((harmonic B : ℝ) - harmonic A) := by
    linarith
  have hDCfinal : (1 / 6 : ℝ) * Real.log 3 - 21 / 4000 ≤
      (1 / 6 : ℝ) * ((harmonic D : ℝ) - harmonic C) := by
    linarith
  have hlast : (-3 / 1000 - 7 / 480 : ℝ) ≤
      (1 / 12 : ℝ) *
        ((harmonic U : ℝ) - harmonic V - harmonic W + harmonic T) := by
    calc
      (-3 / 1000 - 7 / 480 : ℝ) ≤
          (1 / 12 : ℝ) * (1 / (2 * (U : ℝ) + 1) - 1 / (2 * (V : ℝ))) +
          (1 / 12 : ℝ) *
            (-1 / (2 * (T : ℝ)) - 1 / (2 * (W : ℝ)) + 1 / (2 * T + 1)) :=
        by linarith [hUVcorr, hTcorr]
      _ = (1 / 12 : ℝ) *
            (Real.log 2 + 1 / (2 * (U : ℝ) + 1) - 1 / (2 * (V : ℝ))) -
          (1 / 12 : ℝ) *
            (Real.log 2 + 1 / (2 * (T : ℝ)) + 1 / (2 * (W : ℝ)) -
              1 / (2 * T + 1)) := by ring
      _ ≤ (1 / 12 : ℝ) * ((harmonic U : ℝ) - harmonic V) -
          (1 / 12 : ℝ) * ((harmonic W : ℝ) - harmonic T) :=
        sub_le_sub hUV' hWT'
      _ = _ := by ring
  rw [btHarmonicCombination_sub]
  change (1 / 2 : ℝ) <
    (1 / 2 : ℝ) * ((harmonic B : ℝ) - harmonic A) +
    (1 / 6 : ℝ) * ((harmonic D : ℝ) - harmonic C) +
    (1 / 12 : ℝ) * ((harmonic U : ℝ) - harmonic V - harmonic W + harmonic T)
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  norm_num at h2 h3
  have hconst : (1 / 2 : ℝ) <
      (1 / 2 : ℝ) * Real.log 2 + (1 / 6 : ℝ) * Real.log 3 -
        21 / 4000 - 21 / 4000 - 3 / 1000 - 7 / 480 := by
    nlinarith
  apply hconst.trans_le
  linarith [hBAfinal, hDCfinal, hlast]

private def btSmallSquarefree (n : ℕ) : Prop :=
  ¬4 ∣ n ∧ ¬9 ∣ n ∧ ¬25 ∣ n ∧ ¬49 ∣ n

private instance (n : ℕ) : Decidable (btSmallSquarefree n) := by
  unfold btSmallSquarefree
  infer_instance

private def btSmallTotient (n : ℕ) : ℕ :=
  match n / 10 with
  | 0 => #[0, 1, 1, 2, 2, 4, 2, 6, 4, 6].getD (n % 10) 0
  | 1 => #[4, 10, 4, 12, 6, 8, 8, 16, 6, 18].getD (n % 10) 0
  | 2 => #[8, 12, 10, 22, 8, 20, 12, 18, 12, 28].getD (n % 10) 0
  | 3 => #[8, 30, 16, 20, 16, 24, 12, 36, 18, 24].getD (n % 10) 0
  | 4 => #[16, 40, 12, 42, 20, 24, 22, 46, 16, 42].getD (n % 10) 0
  | 5 => #[20, 32, 24, 52, 18, 40, 24, 36, 28, 58].getD (n % 10) 0
  | 6 => #[16, 60, 30, 36, 32, 48, 20, 66, 32, 44].getD (n % 10) 0
  | 7 => #[24, 70, 24, 72, 36, 40, 36, 60, 24, 78].getD (n % 10) 0
  | 8 => #[32, 54, 40, 82, 24, 64, 42, 56, 40, 88].getD (n % 10) 0
  | 9 => #[24, 72, 44, 60, 46, 72, 32, 96, 42, 60].getD (n % 10) 0
  | _ => 0

private theorem btSquarefree_iff_small (n : ℕ) (hn : n < 100) :
    Squarefree n ↔ btSmallSquarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  constructor
  · intro h
    exact ⟨h 2 Nat.prime_two, h 3 Nat.prime_three, h 5 (by norm_num),
      h 7 (by norm_num)⟩
  · intro h p hp hsq
    have hnpos : 0 < n := by
      by_contra hnzero
      simp only [Nat.not_lt, Nat.le_zero] at hnzero
      exact h.1 (hnzero ▸ dvd_zero 4)
    have hpp : p * p ≤ n := Nat.le_of_dvd hnpos hsq
    have hp10 : p < 10 := by nlinarith
    have hpCases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      have hp2 : 2 ≤ p := hp.two_le
      have hp4 : p ≠ 4 := by intro heq; subst p; norm_num at hp
      have hp6 : p ≠ 6 := by intro heq; subst p; norm_num at hp
      have hp8 : p ≠ 8 := by intro heq; subst p; norm_num at hp
      have hp9 : p ≠ 9 := by intro heq; subst p; norm_num at hp
      omega
    rcases hpCases with rfl | rfl | rfl | rfl
    · norm_num at hsq
      exact h.1 hsq
    · norm_num at hsq
      exact h.2.1 hsq
    · norm_num at hsq
      exact h.2.2.1 hsq
    · norm_num at hsq
      exact h.2.2.2 hsq

private theorem btTotient_eq_small (n : ℕ) (hn : n < 100) :
    Nat.totient n = btSmallTotient n := by
  interval_cases n <;> decide

private theorem squarefreeTotientSum_succ (n : ℕ) :
    squarefreeTotientSum (n + 1) = squarefreeTotientSum n +
      if Squarefree (n + 1) then (Nat.totient (n + 1) : ℝ)⁻¹ else 0 := by
  have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnmem : n + 1 ∉ Finset.Icc 1 n := by simp
  rw [squarefreeTotientSum, squarefreeTotientSum, hI]
  rw [Finset.filter_insert]
  by_cases hs : Squarefree (n + 1)
  · simp [hs, hnmem, add_comm]
  · simp [hs]

private noncomputable def btSmallSquarefreeTotientSum : ℕ → ℝ
  | 0 => 0
  | n + 1 => btSmallSquarefreeTotientSum n +
      if btSmallSquarefree (n + 1) then (btSmallTotient (n + 1) : ℝ)⁻¹ else 0

private theorem squarefreeTotientSum_eq_small (z : ℕ) (hz : z < 100) :
    squarefreeTotientSum z = btSmallSquarefreeTotientSum z := by
  induction z with
  | zero => simp [squarefreeTotientSum, btSmallSquarefreeTotientSum]
  | succ n ih =>
      rw [squarefreeTotientSum_succ, btSmallSquarefreeTotientSum, ih (by omega)]
      simp only [btSquarefree_iff_small (n + 1) (by omega)]
      rw [btTotient_eq_small (n + 1) (by omega)]

private theorem squarefreeTotientSum_mono : Monotone squarefreeTotientSum := by
  apply monotone_nat_of_le_succ
  intro n
  rw [squarefreeTotientSum_succ]
  by_cases hs : Squarefree (n + 1)
  · have hnonneg : (0 : ℝ) ≤ (Nat.totient (n + 1) : ℝ)⁻¹ := by positivity
    simp only [hs, ite_true]
    exact le_add_of_nonneg_right hnonneg
  · simp [hs]

private theorem btHarmonicMonotone : Monotone (fun n : ℕ ↦ (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  have hsucc : (harmonic (n + 1) : ℝ) =
      (harmonic n : ℝ) + ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (harmonic_succ n)
    norm_num at h ⊢
  rw [hsucc]
  exact le_add_of_nonneg_right (by positivity)

set_option maxHeartbeats 2000000 in
-- The sixteen rational checks cover every integer from six through ninety-nine.
private theorem squarefreeTotientSum_gt_harmonic_small (z : ℕ) (hz : 6 ≤ z)
    (hz' : z < 100) :
    (harmonic z : ℝ) + 57 / 100 < squarefreeTotientSum z := by
  have hblock (L U : ℕ) (hL : L ≤ z) (hU : z ≤ U) (hL100 : L < 100)
      (hnum : (harmonic U : ℝ) + 57 / 100 < btSmallSquarefreeTotientSum L) :
      (harmonic z : ℝ) + 57 / 100 < squarefreeTotientSum z := by
    calc
      (harmonic z : ℝ) + 57 / 100 ≤ (harmonic U : ℝ) + 57 / 100 := by
        linarith [btHarmonicMonotone hU]
      _ < btSmallSquarefreeTotientSum L := hnum
      _ = squarefreeTotientSum L := (squarefreeTotientSum_eq_small L hL100).symm
      _ ≤ squarefreeTotientSum z := squarefreeTotientSum_mono hL
  by_cases h7 : z ≤ 7
  · exact hblock 6 7 hz h7 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h9 : z ≤ 9
  · exact hblock 8 9 (by omega) h9 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h11 : z ≤ 11
  · exact hblock 10 11 (by omega) h11 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h13 : z ≤ 13
  · exact hblock 12 13 (by omega) h13 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h17 : z ≤ 17
  · exact hblock 14 17 (by omega) h17 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h20 : z ≤ 20
  · exact hblock 18 20 (by omega) h20 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h23 : z ≤ 23
  · exact hblock 21 23 (by omega) h23 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h27 : z ≤ 27
  · exact hblock 24 27 (by omega) h27 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h30 : z ≤ 30
  · exact hblock 28 30 (by omega) h30 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h36 : z ≤ 36
  · exact hblock 31 36 (by omega) h36 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h44 : z ≤ 44
  · exact hblock 37 44 (by omega) h44 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h55 : z ≤ 55
  · exact hblock 45 55 (by omega) h55 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h64 : z ≤ 64
  · exact hblock 56 64 (by omega) h64 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h75 : z ≤ 75
  · exact hblock 65 75 (by omega) h75 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  by_cases h90 : z ≤ 90
  · exact hblock 76 90 (by omega) h90 (by norm_num)
      (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])
  exact hblock 91 99 (by omega) (by omega) (by norm_num)
    (by norm_num [btSmallSquarefreeTotientSum, btSmallSquarefree, btSmallTotient, harmonic])

private theorem eulerMascheroniSeq_hundred_gt_fiftySeven :
    (57 / 100 : ℝ) < Real.eulerMascheroniSeq 100 := by
  have hlog100 : Real.log 100 = 2 * Real.log 2 + 2 * Real.log 5 := by
    rw [show (100 : ℝ) = 2 ^ 2 * 5 ^ 2 by norm_num, Real.log_mul
      (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    ring
  have hlog101 : Real.log 101 = Real.log 100 + Real.log (101 / 100 : ℝ) := by
    calc
      Real.log 101 = Real.log (100 * (101 / 100 : ℝ)) := by norm_num
      _ = _ := Real.log_mul (by norm_num) (by norm_num)
  have hratio := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 101 / 100 by norm_num) (by norm_num : (101 / 100 : ℝ) ≠ 1)
  have h2 := Real.log_two_lt_d9
  have h5 := Real.log_five_lt_d9
  rw [Real.eulerMascheroniSeq]
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  rw [hlog101, hlog100]
  norm_num [harmonic] at ⊢
  linarith

private theorem eulerMascheroniSeq_gt_fiftySeven (z : ℕ) (hz : 100 ≤ z) :
    (57 / 100 : ℝ) < (harmonic z : ℝ) - Real.log (z + 1) := by
  rw [← Real.eulerMascheroniSeq]
  exact eulerMascheroniSeq_hundred_gt_fiftySeven.trans_le
    (Real.strictMono_eulerMascheroniSeq.monotone hz)

private theorem eulerMascheroniSeq_gt_half (z : ℕ) (hz : 6 ≤ z) :
    (1 / 2 : ℝ) < (harmonic z : ℝ) - Real.log (z + 1) := by
  rw [← Real.eulerMascheroniSeq]
  exact Real.one_half_lt_eulerMascheroniSeq_six.trans_le
    (Real.strictMono_eulerMascheroniSeq.monotone hz)

private theorem squarefreeTotientSum_gt_log_succ (z : ℕ) (hz : 6 ≤ z) :
    Real.log (z + 1) + 107 / 100 < squarefreeTotientSum z := by
  by_cases hz100 : 100 ≤ z
  · have hcomb := squarefreeTotientSum_ge_harmonicCombination z
    change btHarmonicCombination z ≤ squarefreeTotientSum z at hcomb
    have hhalf := btHarmonicCombination_sub_gt_half z hz100
    have heuler := eulerMascheroniSeq_gt_fiftySeven z hz100
    linarith
  · have hzlt : z < 100 := by omega
    have hfinite := squarefreeTotientSum_gt_harmonic_small z hz hzlt
    have heuler := eulerMascheroniSeq_gt_half z hz
    linarith

private theorem moebiusTotientSum_eq_squarefree (z : ℕ) :
    (∑ r ∈ Finset.Icc 1 z,
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) =
      squarefreeTotientSum z := by
  calc
    (∑ r ∈ Finset.Icc 1 z,
        (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) =
        ∑ r ∈ Finset.Icc 1 z,
          if Squarefree r then (Nat.totient r : ℝ)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hsq : Squarefree r
      · rw [ite_eq_left hsq]
        have hmu := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
        have hmuReal : (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2) = 1 := by
          have hcast := congrArg (fun n : ℤ ↦ (n : ℝ)) hmu
          norm_num at hcast
          rcases hcast with hcast | hcast
          · rw [hcast]
            norm_num
          · rw [hcast]
            norm_num
        rw [hmuReal]
        simp only [one_div]
      · rw [ite_eq_right hsq,
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        norm_num
    _ = squarefreeTotientSum z := by
      rw [squarefreeTotientSum]
      exact (Finset.sum_filter (s := Finset.Icc 1 z) Squarefree
        (fun r : ℕ ↦ (Nat.totient r : ℝ)⁻¹)).symm

/--
**Lower bound for the squarefree totient sum.** For every natural number $z \ge 6$,
$\log(z + 1) + 107/100 < \sum_{r=1}^{z} \mu(r)^2 / \varphi(r)$, where $\mu$ is the Möbius
function and $\varphi$ is Euler's totient function.

Source: Montgomery–Vaughan, *The large sieve* (1973), Lemmas 4–7 and equation
(4.3), lines 462–657. The bound here uses `log (z + 1)`, which is slightly
stronger than the paper's `log z`.
-/
public theorem moebiusSq_div_totient_sum_gt_log (z : ℕ) (hz : 6 ≤ z) :
    Real.log (z + 1) + 107 / 100 <
      ∑ r ∈ Finset.Icc 1 z,
        (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r) := by
  rw [moebiusTotientSum_eq_squarefree]
  exact squarefreeTotientSum_gt_log_succ z hz

end MathlibExt.NumberTheory.PrimeCounting
