/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.Exponential

@[expose] public section

open scoped unitInterval

section
namespace MathlibExt.Analysis.FunctionalAnalysis.MuntzSzaszWanted

/-- The Golitschek operator: a linear operator on polynomials used in von Golitschek's
elementary proof of the sufficiency half of the Müntz–Szász theorem. -/
private noncomputable def mszGol (lam : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P.sum fun j a =>
    Polynomial.C (a / ((lam : ℝ) - (j : ℝ))) * (Polynomial.X ^ j - Polynomial.X ^ lam)

private lemma mszGol_add (lam : ℕ) (P Q : Polynomial ℝ) :
    mszGol lam (P + Q) = mszGol lam P + mszGol lam Q := by
  unfold mszGol
  refine Polynomial.sum_add_index P Q _ (fun i => by simp) ?_
  intro a b₁ b₂
  rw [add_div, Polynomial.C_add, add_mul]

private lemma mszGol_monomial (lam j : ℕ) (a : ℝ) :
    mszGol lam (Polynomial.monomial j a) =
      Polynomial.C (a / ((lam : ℝ) - (j : ℝ))) * (Polynomial.X ^ j - Polynomial.X ^ lam) := by
  unfold mszGol
  exact Polynomial.sum_monomial_index a _ (by simp)

private lemma mszGol_C_mul (lam : ℕ) (c : ℝ) (P : Polynomial ℝ) :
    mszGol lam (Polynomial.C c * P) = Polynomial.C c * mszGol lam P := by
  refine Polynomial.induction_on' P ?_ ?_
  · intro P Q hP hQ
    rw [mul_add, mszGol_add, mszGol_add, hP, hQ, mul_add]
  · intro j a
    rw [Polynomial.C_mul_monomial, mszGol_monomial, mszGol_monomial, mul_div_assoc,
      ← mul_assoc, Polynomial.C_mul]

private lemma mszGol_coeff (lam : ℕ) (P : Polynomial ℝ) (j : ℕ) (hj : j ≠ lam) :
    (mszGol lam P).coeff j = P.coeff j / ((lam : ℝ) - (j : ℝ)) := by
  refine Polynomial.induction_on' P ?_ ?_
  · intro P Q hP hQ
    rw [mszGol_add, Polynomial.coeff_add, Polynomial.coeff_add, hP, hQ, add_div]
  · intro j' a
    rw [mszGol_monomial]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_monomial]
    by_cases hjj : j = j'
    · subst hjj
      simp [hj]
    · simp [hjj, hj, Ne.symm hjj]

private lemma msz_X_mul_deriv_X_pow (n : ℕ) :
    (Polynomial.X : Polynomial ℝ) * Polynomial.derivative (Polynomial.X ^ n) =
      Polynomial.C (n : ℝ) * Polynomial.X ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Polynomial.derivative_X_pow, Nat.add_sub_cancel]
    push_cast
    ring

private lemma msz_ode_monomial (lam j : ℕ) (c : ℝ) :
    (Polynomial.X : Polynomial ℝ) * Polynomial.derivative
        (Polynomial.C c * (Polynomial.X ^ j - Polynomial.X ^ lam)) -
        Polynomial.C (lam : ℝ) * (Polynomial.C c * (Polynomial.X ^ j - Polynomial.X ^ lam)) =
      Polynomial.C (c * ((j : ℝ) - (lam : ℝ))) * Polynomial.X ^ j := by
  have e : ∀ (a : ℝ) (n : ℕ), (Polynomial.X : Polynomial ℝ) *
      (Polynomial.C a * Polynomial.derivative (Polynomial.X ^ n)) =
      Polynomial.C a * (Polynomial.C (n : ℝ) * Polynomial.X ^ n) := by
    intro a n
    rw [mul_left_comm, msz_X_mul_deriv_X_pow n]
  have h1 := e c j
  have h2 := e c lam
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_sub, Polynomial.C_mul,
    Polynomial.C_sub]
  linear_combination h1 - h2

private lemma mszGol_ode (lam : ℕ) (P : Polynomial ℝ) :
    (Polynomial.X : Polynomial ℝ) * Polynomial.derivative (mszGol lam P) -
        Polynomial.C (lam : ℝ) * mszGol lam P =
      Polynomial.monomial lam (P.coeff lam) - P := by
  refine Polynomial.induction_on' P ?_ ?_
  · intro P Q hP hQ
    rw [mszGol_add, Polynomial.derivative_add, mul_add, mul_add, Polynomial.coeff_add,
      map_add (Polynomial.monomial lam)]
    linear_combination hP + hQ
  · intro j a
    rw [mszGol_monomial, msz_ode_monomial, Polynomial.coeff_monomial]
    by_cases hjl : j = lam
    · rw [hjl, sub_self, div_zero, zero_mul, Polynomial.C_0, zero_mul]
      simp
    · have hif : (if j = lam then a else 0) = (0 : ℝ) := by simp [hjl]
      rw [hif, Polynomial.monomial_zero_right, zero_sub]
      have hlamj : lam ≠ j := Ne.symm hjl
      have hcoe : (lam : ℝ) ≠ (j : ℝ) := by exact_mod_cast hlamj
      have hne : (lam : ℝ) - (j : ℝ) ≠ 0 := sub_ne_zero.mpr hcoe
      have hcc : a / ((lam : ℝ) - (j : ℝ)) * ((j : ℝ) - (lam : ℝ)) = -a := by
        field_simp
        ring
      rw [hcc, Polynomial.C_neg, neg_mul, Polynomial.C_mul_X_pow_eq_monomial]

private lemma mszGol_eval_one (lam : ℕ) (P : Polynomial ℝ) :
    (mszGol lam P).eval 1 = 0 := by
  refine Polynomial.induction_on' P ?_ ?_
  · intro P Q hP hQ
    rw [mszGol_add, Polynomial.eval_add, hP, hQ, add_zero]
  · intro j a
    rw [mszGol_monomial, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_pow, Polynomial.eval_X, one_pow, one_pow, sub_self, mul_zero]

/-- Derivative of the barrier function used in the Euler-operator bound. -/
private lemma mszPhiDeriv (R : Polynomial ℝ) (lam : ℕ) (M s t : ℝ) (ht : t ≠ 0)
    (hne : (lam : ℝ) ≠ 0) :
    HasDerivAt
      (fun u => M / (lam : ℝ) * (u ^ (-(lam : ℤ)) - 1) - s * (R.eval u * u ^ (-(lam : ℤ))))
      (t ^ (-(lam : ℤ) - 1) * (-M - s * (t * R.derivative.eval t - (lam : ℝ) * R.eval t)))
      t := by
  have hR : HasDerivAt (fun u => R.eval u) (R.derivative.eval t) t := R.hasDerivAt t
  have hu := hasDerivAt_zpow (-(lam : ℤ)) t (Or.inl ht)
  have h1 := (hu.sub_const 1).const_mul (M / (lam : ℝ))
  have h2 := (hR.mul hu).const_mul s
  refine (h1.sub h2).congr_deriv ?_
  rw [Int.cast_neg, Int.cast_natCast]
  have hpow : t ^ (-(lam : ℤ)) = t * t ^ (-(lam : ℤ) - 1) := by
    conv_lhs => rw [show (-(lam : ℤ)) = 1 + (-(lam : ℤ) - 1) from by omega]
    rw [zpow_add₀ ht, zpow_one]
  rw [hpow]
  field_simp
  ring

/-- Barrier inequality from the antitone argument. -/
private lemma mszPhiNonneg (R : Polynomial ℝ) (lam : ℕ) (M : ℝ) (hlam : 1 ≤ lam)
    (hR1 : R.eval 1 = 0)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |x * R.derivative.eval x - (lam : ℝ) * R.eval x| ≤ M)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    0 ≤ M / (lam : ℝ) * (x ^ (-(lam : ℤ)) - 1) - s * (R.eval x * x ^ (-(lam : ℤ))) := by
  have hlamR : (0 : ℝ) < (lam : ℝ) := by
    have hpos : 0 < lam := by omega
    exact_mod_cast hpos
  have hlam0 : (lam : ℝ) ≠ 0 := ne_of_gt hlamR
  have hxD : x ∈ Set.Icc x 1 := ⟨le_rfl, hx1⟩
  have h1D : (1 : ℝ) ∈ Set.Icc x 1 := ⟨hx1, le_rfl⟩
  have hanti : AntitoneOn
      (fun t => M / (lam : ℝ) * (t ^ (-(lam : ℤ)) - 1) - s * (R.eval t * t ^ (-(lam : ℤ))))
      (Set.Icc x 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc x 1) ?_ ?_ ?_
    · have hzc : ContinuousOn (fun t : ℝ => t ^ (-(lam : ℤ))) (Set.Icc x 1) := by
        intro t ht
        have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx0 (Set.mem_Icc.mp ht).1)
        exact ((hasDerivAt_zpow (-(lam : ℤ)) t
        (Or.inl ht0)).continuousAt).continuousWithinAt
      exact ContinuousOn.sub ((ContinuousOn.sub hzc continuousOn_const).const_mul _)
        (continuousOn_const.mul ((R.continuous).continuousOn.mul hzc))
    · rw [interior_Icc]
      intro t ht
      have ht0 : t ≠ 0 :=
        ne_of_gt (lt_of_le_of_lt (le_of_lt hx0) (Set.mem_Ioo.mp ht).1)
      exact ((mszPhiDeriv R lam M s t ht0 hlam0).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have htpos : (0 : ℝ) < t :=
        lt_of_le_of_lt (le_of_lt hx0) (Set.mem_Ioo.mp ht).1
      have ht0 : t ≠ 0 := ne_of_gt htpos
      have hmem : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_of_lt htpos, le_of_lt (Set.mem_Ioo.mp ht).2⟩
      have hb := hbound t hmem
      rw [(mszPhiDeriv R lam M s t ht0 hlam0).deriv]
      have h2 : -M - s * (t * R.derivative.eval t - (lam : ℝ) * R.eval t) ≤ 0 := by
        have hsw : -(s * (t * R.derivative.eval t - (lam : ℝ) * R.eval t)) ≤ M := by
          rcases hs with rfl | rfl
          · simpa using (neg_le_abs _).trans hb
          · simpa using (le_abs_self _).trans hb
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (zpow_nonneg (le_of_lt htpos) _) h2
  have hφ1 : (fun t => M / (lam : ℝ) * (t ^ (-(lam : ℤ)) - 1) -
      s * (R.eval t * t ^ (-(lam : ℤ)))) 1 = 0 := by
    change M / (lam : ℝ) * ((1 : ℝ) ^ (-(lam : ℤ)) - 1) -
      s * (R.eval 1 * (1 : ℝ) ^ (-(lam : ℤ))) = 0
    rw [hR1]
    simp
  have h := hanti hxD h1D hx1
  rw [hφ1] at h
  exact h

/-- Grönwall-type bound for the Euler operator `x d/dx - lam`. -/
private lemma mszAbsEval (R : Polynomial ℝ) (lam : ℕ) (hlam : 1 ≤ lam) (M : ℝ)
    (hR1 : R.eval 1 = 0)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |x * R.derivative.eval x - (lam : ℝ) * R.eval x| ≤ M) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, |R.eval x| ≤ M / (lam : ℝ) := by
  have hlamR : (0 : ℝ) < (lam : ℝ) := by
    have hpos : 0 < lam := by omega
    exact_mod_cast hpos
  have hM : 0 ≤ M := by
    have h1 := hbound 1 ⟨zero_le_one, le_rfl⟩
    rw [hR1, mul_zero, sub_zero] at h1
    exact (abs_nonneg _).trans h1
  intro x hx
  have hx0 : 0 ≤ x := (Set.mem_Icc.mp hx).1
  have hx1 : x ≤ 1 := (Set.mem_Icc.mp hx).2
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · have h0 := hbound 0 ⟨le_rfl, zero_le_one⟩
    rw [zero_mul, zero_sub, abs_neg, abs_mul, abs_of_pos hlamR] at h0
    rw [le_div_iff₀ hlamR, mul_comm]
    exact h0
  · have hzx : x ^ (-(lam : ℤ)) * x ^ lam = 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero lam (ne_of_gt hxpos))
    have e1 : ∀ s : ℝ, (M / (lam : ℝ) * (x ^ (-(lam : ℤ)) - 1) -
        s * (R.eval x * x ^ (-(lam : ℤ)))) * x ^ lam =
        M / (lam : ℝ) * (1 - x ^ lam) - s * R.eval x := by
      intro s
      linear_combination (M / (lam : ℝ) - s * R.eval x) * hzx
    have bound : ∀ s : ℝ, s = 1 ∨ s = -1 → s * R.eval x ≤ M / (lam : ℝ) := by
      intro s hs
      have hnn := mszPhiNonneg R lam M hlam hR1 hbound x hxpos hx1 s hs
      have hpos : (0 : ℝ) ≤ (M / (lam : ℝ) * (x ^ (-(lam : ℤ)) - 1) -
          s * (R.eval x * x ^ (-(lam : ℤ)))) * x ^ lam :=
        mul_nonneg hnn (le_of_lt (pow_pos hxpos lam))
      rw [e1 s] at hpos
      have hle : M / (lam : ℝ) * (1 - x ^ lam) ≤ M / (lam : ℝ) := by
        have hnn2 : (0 : ℝ) ≤ M / (lam : ℝ) * x ^ lam :=
          mul_nonneg (div_nonneg hM (le_of_lt hlamR)) (le_of_lt (pow_pos hxpos lam))
        have hexpand : M / (lam : ℝ) * (1 - x ^ lam) =
            M / (lam : ℝ) - M / (lam : ℝ) * x ^ lam := by ring
        linarith
      linarith
    have b1 := bound 1 (Or.inl rfl)
    have b2 := bound (-1) (Or.inr rfl)
    rw [one_mul] at b1
    have b2' : -(R.eval x) ≤ M / (lam : ℝ) := by simpa using b2
    rw [abs_le]
    constructor <;> linarith

/-- Finite von Golitschek estimate. -/
private lemma mszGolApprox (m : ℕ) (S : Finset ℕ) (hmS : m ∉ S) (h0S : 0 ∉ S) :
    ∃ Q : Polynomial ℝ, Q.coeff m = 1 ∧ (∀ j, j ≠ m → j ∉ S → Q.coeff j = 0) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |Q.eval x| ≤ ∏ s ∈ S, |1 - (m : ℝ) / (s : ℝ)| := by
  revert hmS h0S
  refine Finset.induction_on S ?_ ?_
  · intro _ _
    refine ⟨Polynomial.X ^ m, Polynomial.coeff_X_pow_self m, ?_, ?_⟩
    · intro j hjm _
      rw [Polynomial.coeff_X_pow]
      simp [hjm]
    · intro x hx
      rw [Finset.prod_empty]
      have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [(Set.mem_Icc.mp hx).1], (Set.mem_Icc.mp hx).2⟩
      calc |Polynomial.eval x (Polynomial.X ^ m)| = |x| ^ m := by
            rw [Polynomial.eval_pow, Polynomial.eval_X, abs_pow]
        _ ≤ 1 := by
            calc |x| ^ m ≤ 1 ^ m := pow_le_pow_left₀ (abs_nonneg x) hx1 m
              _ = 1 := one_pow m
  · intro lam T hlam ih hmS h0S
    have hlamm : lam ≠ m := fun h => hmS (by rw [h]; exact Finset.mem_insert_self m T)
    have hlam0 : lam ≠ 0 := fun h => h0S (by rw [h]; exact Finset.mem_insert_self 0 T)
    have hmT : m ∉ T := fun h => hmS (Finset.mem_insert_of_mem h)
    have h0T : 0 ∉ T := fun h => h0S (Finset.mem_insert_of_mem h)
    obtain ⟨Q, hQm, hQsupp, hQbnd⟩ := ih hmT h0T
    have hQlam : Q.coeff lam = 0 := hQsupp lam hlamm hlam
    have hlamR : (lam : ℝ) ≠ (m : ℝ) := by exact_mod_cast hlamm
    have hsub : (lam : ℝ) - (m : ℝ) ≠ 0 := sub_ne_zero.mpr hlamR
    have hlampos : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hlam0
    have hlam1 : 1 ≤ lam := Nat.one_le_iff_ne_zero.mpr hlam0
    refine ⟨Polynomial.C ((lam : ℝ) - m) * mszGol lam Q, ?_, ?_, ?_⟩
    · rw [Polynomial.coeff_C_mul, mszGol_coeff lam Q m (Ne.symm hlamm), hQm, one_div,
        mul_inv_cancel₀ hsub]
    · intro j hjm hjT
      have hjlam : j ≠ lam := fun h => hjT (by rw [h]; exact Finset.mem_insert_self lam T)
      have hjT' : j ∉ T := fun h => hjT (Finset.mem_insert_of_mem h)
      rw [Polynomial.coeff_C_mul, mszGol_coeff lam Q j hjlam, hQsupp j hjm hjT', zero_div,
        mul_zero]
    · intro x hx
      have hR1 : (mszGol lam Q).eval 1 = 0 := mszGol_eval_one lam Q
      have hodeY : ∀ y : ℝ, y * (mszGol lam Q).derivative.eval y -
          (lam : ℝ) * (mszGol lam Q).eval y = -(Q.eval y) := by
        intro y
        have h := congrArg (fun P : Polynomial ℝ => P.eval y) (mszGol_ode lam Q)
        rw [hQlam, Polynomial.monomial_zero_right] at h
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_C, Polynomial.eval_neg, zero_sub] at h
        exact h
      have hRx := mszAbsEval (mszGol lam Q) lam hlam1 _ hR1
        (fun y hy => by rw [hodeY y, abs_neg]; exact hQbnd y hy) x hx
      have hfin : |(Polynomial.C ((lam : ℝ) - m) * mszGol lam Q).eval x| ≤
          |1 - (m : ℝ) / (lam : ℝ)| * ∏ s ∈ T, |1 - (m : ℝ) / (s : ℝ)| := by
        rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul]
        have e : |1 - (m : ℝ) / (lam : ℝ)| = |(lam : ℝ) - m| / (lam : ℝ) := by
          have ediv : (1 : ℝ) - m / lam = ((lam : ℝ) - m) / lam := by
            rw [sub_div, div_self hlampos.ne']
          rw [ediv, abs_div, abs_of_pos hlampos]
        calc |(lam : ℝ) - m| * |(mszGol lam Q).eval x|
            ≤ |(lam : ℝ) - m| * ((∏ s ∈ T, |1 - (m : ℝ) / (s : ℝ)|) / (lam : ℝ)) :=
              mul_le_mul_of_nonneg_left hRx (abs_nonneg _)
          _ = |1 - (m : ℝ) / (lam : ℝ)| * (∏ s ∈ T, |1 - (m : ℝ) / (s : ℝ)|) := by
              rw [e]
              ring
      rw [Finset.prod_insert hlam]
      exact hfin

private lemma mszProdSmall (Λ : ℕ → ℕ) (hΛ : StrictMono Λ)
    (hdiv : ¬Summable (fun n => ((Λ (n + 1) : ℝ))⁻¹)) (m : ℕ) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∏ k ∈ Finset.Ico (m + 1) N, |1 - (m : ℝ) / (Λ k : ℝ)| < ε := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hshift : ¬Summable (fun i => ((Λ (i + (m + 1)) : ℝ))⁻¹) := by
    have h := summable_nat_add_iff (f := fun n => ((Λ n : ℝ))⁻¹) (m + 1)
    have h' := summable_nat_add_iff (f := fun n => ((Λ n : ℝ))⁻¹) 1
    exact fun hs => hdiv (h'.mpr (h.mp hs))
  have hnn : ∀ i, 0 ≤ ((Λ (i + (m + 1)) : ℝ))⁻¹ :=
    fun i => inv_nonneg.mpr (Nat.cast_nonneg _)
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp hshift
  obtain ⟨K, hK⟩ := (htend.eventually_gt_atTop (Real.log ε⁻¹ / (m : ℝ))).exists
  refine ⟨m + 1 + K, ?_⟩
  have hsub : m + 1 + K - (m + 1) = K := by omega
  have hsum : ∑ k ∈ Finset.Ico (m + 1) (m + 1 + K), ((Λ k : ℝ))⁻¹ =
      ∑ i ∈ Finset.range K, ((Λ (i + (m + 1)) : ℝ))⁻¹ := by
    rw [Finset.sum_Ico_eq_sum_range _ _ _, hsub]
    apply Finset.sum_congr rfl
    intro i _
    have hii : m + 1 + i = i + (m + 1) := by omega
    rw [hii]
  have hfactor : ∀ k ∈ Finset.Ico (m + 1) (m + 1 + K),
      (0 : ℝ) ≤ 1 - (m : ℝ) / (Λ k : ℝ) ∧
        1 - (m : ℝ) / (Λ k : ℝ) ≤ Real.exp (-((m : ℝ) / (Λ k : ℝ))) := by
    intro k hk
    have hk1 : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hlt : (m : ℝ) < (Λ k : ℝ) := by
      have hkk : m < Λ k := by
        have h1 : m ≤ Λ m := hΛ.id_le m
        exact lt_of_le_of_lt h1 (hΛ (by omega))
      exact_mod_cast hkk
    have hpos : (0 : ℝ) < (Λ k : ℝ) := hmR.trans hlt
    have hle : (m : ℝ) / (Λ k : ℝ) ≤ 1 := (div_le_one hpos).mpr (le_of_lt hlt)
    exact ⟨sub_nonneg.mpr hle, Real.one_sub_le_exp_neg _⟩
  have hexp : (∑ k ∈ Finset.Ico (m + 1) (m + 1 + K), (-((m : ℝ) * ((Λ k : ℝ))⁻¹))) =
      -((m : ℝ) * ∑ k ∈ Finset.Ico (m + 1) (m + 1 + K), ((Λ k : ℝ))⁻¹) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  have hprod : ∏ k ∈ Finset.Ico (m + 1) (m + 1 + K), |1 - (m : ℝ) / (Λ k : ℝ)|
      ≤ Real.exp (-((m : ℝ) *
        ∑ k ∈ Finset.Ico (m + 1) (m + 1 + K), ((Λ k : ℝ))⁻¹)) := by
    rw [← hexp, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun k hk => abs_nonneg _) ?_
    intro k hk
    rw [abs_of_nonneg (hfactor k hk).1, div_eq_mul_inv]
    exact (hfactor k hk).2
  refine lt_of_le_of_lt hprod ?_
  rw [hsum]
  have hm0 := ne_of_gt hmR
  have hloginv : Real.log ε⁻¹ = -Real.log ε := Real.log_inv ε
  have harg : -((m : ℝ) * ∑ i ∈ Finset.range K, ((Λ (i + (m + 1)) : ℝ))⁻¹) <
      Real.log ε := by
    have hmul : Real.log ε⁻¹ < (m : ℝ) *
        ∑ i ∈ Finset.range K, ((Λ (i + (m + 1)) : ℝ))⁻¹ := by
      calc Real.log ε⁻¹ = (m : ℝ) * (Real.log ε⁻¹ / (m : ℝ)) := by
            rw [mul_div_cancel₀ _ hm0]
        _ < (m : ℝ) * ∑ i ∈ Finset.range K, ((Λ (i + (m + 1)) : ℝ))⁻¹ :=
            mul_lt_mul_of_pos_left hK hmR
    linarith
  calc Real.exp (-((m : ℝ) * ∑ i ∈ Finset.range K, ((Λ (i + (m + 1)) : ℝ))⁻¹))
      < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr harg
    _ = ε := Real.exp_log hε

private lemma mszMemSpan (Λ : ℕ → ℕ) (P : Polynomial ℝ)
    (hP : ∀ j, P.coeff j ≠ 0 → j ∈ Set.range Λ) :
    P.toContinuousMapOn I ∈
      Submodule.span ℝ (Set.range fun n : ℕ =>
        ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I) := by
  have hchoice : ∀ j, ∃ n, P.coeff j ≠ 0 → Λ n = j := by
    intro j
    by_cases hj : P.coeff j ≠ 0
    · obtain ⟨n, hn⟩ := hP j hj
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose n hn using hchoice
  have e : Polynomial.toContinuousMapOnAlgHom I P =
      ∑ j ∈ P.support,
        P.coeff j • Polynomial.toContinuousMapOnAlgHom I (Polynomial.X ^ Λ (n j)) := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow P, map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul, Polynomial.C_eq_algebraMap, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      hn j (Polynomial.mem_support_iff.mp hj)]
  rw [← Polynomial.toContinuousMapOnAlgHom_apply, e]
  exact Submodule.sum_mem _ (fun j hj => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n j, rfl⟩))

private lemma mszExistsPoly (Λ : ℕ → ℕ) (f : C(↥I, ℝ))
    (hf : f ∈ Submodule.span ℝ (Set.range fun n : ℕ =>
      ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I)) :
    ∃ P : Polynomial ℝ, P.toContinuousMapOn I = f ∧
      ∀ j, j ∉ Set.range Λ → P.coeff j = 0 := by
  refine Submodule.span_induction (fun x hx => ?_) ?_ ?_ ?_ hf
  · obtain ⟨n, rfl⟩ := hx
    refine ⟨Polynomial.X ^ Λ n, rfl, fun j hj => ?_⟩
    have hne : j ≠ Λ n := fun h => hj ⟨n, h.symm⟩
    rw [Polynomial.coeff_X_pow]
    simp [hne]
  · exact ⟨0, by simp [← Polynomial.toContinuousMapOnAlgHom_apply], fun j _ => by simp⟩
  · rintro x y _ _ ⟨Px, hPx, hPxsupp⟩ ⟨Py, hPy, hPysupp⟩
    refine ⟨Px + Py, ?_, fun j hj => by
      rw [Polynomial.coeff_add, hPxsupp j hj, hPysupp j hj, add_zero]⟩
    have e : (Px + Py).toContinuousMapOn I =
        Px.toContinuousMapOn I + Py.toContinuousMapOn I := by
      simp only [← Polynomial.toContinuousMapOnAlgHom_apply, map_add]
    rw [e, hPx, hPy]
  · rintro r x _ ⟨P, hP, hPsupp⟩
    refine ⟨Polynomial.C r * P, ?_, fun j hj => by
      rw [Polynomial.coeff_C_mul, hPsupp j hj, mul_zero]⟩
    have e : (Polynomial.C r * P).toContinuousMapOn I = r • P.toContinuousMapOn I := by
      rw [← Polynomial.smul_eq_C_mul, ← Polynomial.toContinuousMapOnAlgHom_apply,
        ← Polynomial.toContinuousMapOnAlgHom_apply, map_smul]
    rw [e, hP]

private lemma mszClosureTop (B : Submodule ℝ C(↥I, ℝ))
    (h : ∀ m : ℕ,
      ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I ∈ B.topologicalClosure) :
    B.topologicalClosure = ⊤ := by
  have hmem : ∀ p : Polynomial ℝ,
      p.toContinuousMapOn I ∈ B.topologicalClosure := by
    intro p
    have e : Polynomial.toContinuousMapOnAlgHom I p =
        ∑ j ∈ p.support,
          p.coeff j • Polynomial.toContinuousMapOnAlgHom I (Polynomial.X ^ j) := by
      conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow p, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, Polynomial.C_eq_algebraMap, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [← Polynomial.toContinuousMapOnAlgHom_apply, e]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (h j))
  have hsub : (polynomialFunctions I : Set C(↥I, ℝ)) ⊆ ↑B.topologicalClosure := by
    rw [polynomialFunctions_coe]
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hclosed : (polynomialFunctions I).topologicalClosure = ⊤ :=
    polynomialFunctions_closure_eq_top'
  have h1 : closure (polynomialFunctions I : Set C(↥I, ℝ)) = Set.univ := by
    rw [← Subalgebra.topologicalClosure_coe, hclosed]
    rfl
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x ∈ closure (polynomialFunctions I : Set C(↥I, ℝ)) :=
    h1.symm ▸ Set.mem_univ x
  exact closure_minimal hsub (Submodule.isClosed_topologicalClosure B) hx

private lemma mszMonomialMem (Λ : ℕ → ℕ) (hΛ : StrictMono Λ) (h0 : Λ 0 = 0)
    (hdiv : ¬Summable (fun n => ((Λ (n + 1) : ℝ))⁻¹)) (m : ℕ) :
    ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I ∈
      (Submodule.span ℝ (Set.range fun n : ℕ =>
        ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I)).topologicalClosure := by
  by_cases hm : m ∈ Set.range Λ
  · obtain ⟨n, hn⟩ := hm
    have hmem : ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I ∈
        Submodule.span ℝ (Set.range fun n : ℕ =>
          ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I) := by
      apply Submodule.subset_span
      exact ⟨n, by simp only [hn]⟩
    exact Submodule.le_topologicalClosure _ hmem
  · have hm0 : 1 ≤ m := by
      by_contra hcon
      rw [not_le] at hcon
      interval_cases m
      exact hm ⟨0, h0⟩
    have hmemclose : ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I ∈
        closure (↑(Submodule.span ℝ (Set.range fun n : ℕ =>
          ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I))) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := mszProdSmall Λ hΛ hdiv m hm0 hε
      set S := (Finset.Ico (m + 1) N).image Λ with hS
      have hmS : m ∉ S := by
        rw [hS]
        intro hcon
        apply hm
        obtain ⟨k, _, hkk⟩ := Finset.mem_image.mp hcon
        exact ⟨k, hkk⟩
      have h0S : 0 ∉ S := by
        rw [hS]
        intro hcon
        obtain ⟨k, hk, hkk⟩ := Finset.mem_image.mp hcon
        have hk1 : m + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hlam : k ≤ Λ k := hΛ.id_le k
        omega
      obtain ⟨Q, hQm, hQsupp, hQbnd⟩ := mszGolApprox m S hmS h0S
      have hprod : ∏ s ∈ S, |1 - (m : ℝ) / (s : ℝ)| =
          ∏ k ∈ Finset.Ico (m + 1) N, |1 - (m : ℝ) / (Λ k : ℝ)| := by
        rw [hS]
        exact Finset.prod_image hΛ.injective.injOn
      have hp : (Polynomial.X ^ m - Q).toContinuousMapOn I ∈
          Submodule.span ℝ (Set.range fun n : ℕ =>
            ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I) := by
        apply mszMemSpan
        intro j hj
        by_cases hjm : j = m
        · subst hjm
          exfalso
          apply hj
          rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self j, hQm, sub_self]
        · have hjS : j ∈ S := by
            by_contra hcon
            apply hj
            rw [Polynomial.coeff_sub]
            have hX : ((Polynomial.X : Polynomial ℝ) ^ m).coeff j = 0 := by
              rw [Polynomial.coeff_X_pow]
              simp [hjm]
            rw [hX, hQsupp j hjm hcon, sub_zero]
          rw [hS] at hjS
          obtain ⟨k, _, hkk⟩ := Finset.mem_image.mp hjS
          exact ⟨k, hkk⟩
      refine ⟨(Polynomial.X ^ m - Q).toContinuousMapOn I, hp, ?_⟩
      have e : ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I -
          (Polynomial.X ^ m - Q).toContinuousMapOn I = Q.toContinuousMapOn I := by
        simp only [← Polynomial.toContinuousMapOnAlgHom_apply, map_sub, sub_sub_cancel]
      have hnorm : ‖Q.toContinuousMapOn I‖ ≤
          ∏ k ∈ Finset.Ico (m + 1) N, |1 - (m : ℝ) / (Λ k : ℝ)| := by
        rw [← hprod]
        apply (ContinuousMap.norm_le _ (Finset.prod_nonneg
          (fun s _ => abs_nonneg _))).mpr
        intro x
        rw [Real.norm_eq_abs, Polynomial.toContinuousMapOn_apply,
          Polynomial.toContinuousMap_apply]
        exact hQbnd _ x.property
      rw [dist_eq_norm, e]
      exact lt_of_le_of_lt hnorm hN
    exact hmemclose

/-- Partial-fraction decomposition with simple poles from Lagrange interpolation. -/
private lemma mszPartialFrac (s : Finset ℕ) (v : ℕ → ℝ)
    (hvs : Set.InjOn v s) (N : Polynomial ℝ) (hdeg : N.degree < s.card) (x : ℝ)
    (hx : ∀ i ∈ s, x ≠ v i) :
    N.eval x / ∏ i ∈ s, (x - v i) =
      ∑ i ∈ s, N.eval (v i) * Lagrange.nodalWeight s v i / (x - v i) := by
  have hprod : ∏ i ∈ s, (x - v i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact sub_ne_zero.mpr (hx i hi)
  have hN : N = Lagrange.interpolate s v (fun i => N.eval (v i)) :=
    Lagrange.eq_interpolate hvs hdeg
  have heval : N.eval x = (∏ i ∈ s, (x - v i)) *
      ∑ i ∈ s, Lagrange.nodalWeight s v i * (x - v i)⁻¹ * N.eval (v i) := by
    conv_lhs => rw [hN]
    rw [Lagrange.eval_interpolate_not_at_node _ hx, Lagrange.eval_nodal]
  rw [heval, mul_div_cancel_left₀ _ hprod]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]
  ring

/-- Hilbert-matrix moments on `[0, 1]`. -/
private lemma mszMoment (E : Finset ℕ) (r : ℕ → ℝ) (a : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ a * (∑ e ∈ E, r e * x ^ e)) =
      ∑ e ∈ E, r e / ((a : ℝ) + (e : ℝ) + 1) := by
  have hfun : ∀ x : ℝ, x ^ a * (∑ e ∈ E, r e * x ^ e)
      = ∑ e ∈ E, r e * x ^ (a + e) := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp_rw [hfun]
  have hint : ∀ e ∈ E, IntervalIntegrable (fun x : ℝ => r e * x ^ (a + e))
      MeasureTheory.volume 0 1 := fun e _ =>
    (continuous_const.mul (continuous_pow _)).intervalIntegrable 0 1
  have key : (∫ x in (0 : ℝ)..1, ∑ e ∈ E, r e * x ^ (a + e))
      = ∑ e ∈ E, ∫ x in (0 : ℝ)..1, r e * x ^ (a + e) :=
    intervalIntegral.integral_finsetSum hint
  rw [key]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow, one_pow,
    zero_pow (by omega : a + e + 1 ≠ 0), sub_zero]
  push_cast
  ring

/-- The Müntz dual element. -/
private lemma mszDual (m : ℕ) (F : Finset ℕ) (hmF : m ∉ F) :
    ∃ w : Polynomial ℝ,
      (∀ a ∈ F, (∫ x in (0 : ℝ)..1, x ^ a * w.eval x) = 0) ∧
      (∫ x in (0 : ℝ)..1, x ^ m * w.eval x) =
        (∏ e ∈ F, ((m : ℝ) - (e : ℝ))) /
          ((2 * (m : ℝ) + 1) * ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1)) ∧
      (∫ x in (0 : ℝ)..1, (w.eval x) ^ 2) = 1 / (2 * (m : ℝ) + 1) := by
  set v : ℕ → ℝ := fun e => -((e : ℝ) + 1) with hv
  set E : Finset ℕ := insert m F with hE
  set N : Polynomial ℝ := Lagrange.nodal F (fun e => (e : ℝ)) with hN
  set r : ℕ → ℝ := fun e => N.eval (v e) * Lagrange.nodalWeight E v e with hr
  set w : Polynomial ℝ := ∑ e ∈ E, Polynomial.C (r e) * Polynomial.X ^ e with hw
  have hvInj : Set.InjOn v ↑E := by
    intro e1 _ e2 _ h
    simp only [hv] at h
    have h2 : (e1 : ℝ) = (e2 : ℝ) := by linarith
    exact_mod_cast h2
  have hnpos : ∀ i : ℕ, v i < 0 := by
    intro i
    simp only [hv]
    have hpos : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    linarith
  have hne : ∀ (a : ℕ) (i : ℕ), i ∈ E → (a : ℝ) ≠ v i := by
    intro a i _ h
    have h1 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg _
    have h2 := hnpos i
    linarith
  have hdeg : N.degree < E.card := by
    rw [hN, Lagrange.degree_nodal, hE, Finset.card_insert_of_notMem hmF]
    exact_mod_cast Nat.lt_succ_self _
  have hN0 : ∀ a ∈ F, N.eval (a : ℝ) = 0 := by
    intro a ha
    rw [hN]
    exact Lagrange.eval_nodal_at_node ha
  have hμ : ∀ a : ℕ, (∫ x in (0 : ℝ)..1, x ^ a * w.eval x)
      = N.eval (a : ℝ) / ∏ e ∈ E, ((a : ℝ) + (e : ℝ) + 1) := by
    intro a
    have hwe : ∀ x : ℝ, w.eval x = ∑ e ∈ E, r e * x ^ e := by
      intro x
      rw [hw, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have h1 : (∫ x in (0 : ℝ)..1, x ^ a * w.eval x)
        = ∑ e ∈ E, r e / ((a : ℝ) + (e : ℝ) + 1) := by
      simp_rw [hwe]
      exact mszMoment E r a
    have h2 := mszPartialFrac E v hvInj N hdeg (a : ℝ) (fun i hi => hne a i hi)
    have hden : ∀ i ∈ E, (a : ℝ) - v i = (a : ℝ) + (i : ℝ) + 1 := by
      intro i _
      simp only [hv]
      ring
    have hprod : ∏ i ∈ E, ((a : ℝ) - v i) = ∏ e ∈ E, ((a : ℝ) + (e : ℝ) + 1) :=
      Finset.prod_congr rfl fun i hi => hden i hi
    have hsum : (∑ i ∈ E, N.eval (v i) * Lagrange.nodalWeight E v i / ((a : ℝ) - v i))
        = ∑ e ∈ E, r e / ((a : ℝ) + (e : ℝ) + 1) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hri : r i = N.eval (v i) * Lagrange.nodalWeight E v i := by simp only [hr]
      rw [hden i hi, hri]
    rw [hprod, hsum] at h2
    rw [h1]
    exact h2.symm
  refine ⟨w, ?_, ?_, ?_⟩
  · intro a ha
    rw [hμ a, hN0 a ha, zero_div]
  · have hNm : N.eval (m : ℝ) = ∏ e ∈ F, ((m : ℝ) - (e : ℝ)) := by
      rw [hN, Lagrange.eval_nodal]
    have hEprod : ∏ e ∈ E, ((m : ℝ) + (e : ℝ) + 1)
        = (2 * (m : ℝ) + 1) * ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1) := by
      rw [hE, Finset.prod_insert hmF]
      congr 1
      ring
    rw [hμ m, hNm, hEprod]
  · have hNv : N.eval (v m) = ∏ e ∈ F, (-((m : ℝ) + 1) - (e : ℝ)) := by
      rw [hN, Lagrange.eval_nodal]
    have hnw : Lagrange.nodalWeight E v m
        = ∏ e ∈ F, (((e : ℝ) - (m : ℝ))⁻¹) := by
      have hdef : Lagrange.nodalWeight E v m
          = ∏ j ∈ E.erase m, ((v m - v j)⁻¹) := rfl
      rw [hdef, hE, Finset.erase_insert hmF]
      refine Finset.prod_congr rfl fun e _ => ?_
      congr 1
      simp only [hv]
      ring
    have hfactor : ∀ e ∈ F, (-((m : ℝ) + 1) - (e : ℝ)) * (((e : ℝ) - (m : ℝ))⁻¹)
        * ((m : ℝ) - (e : ℝ)) = (m : ℝ) + (e : ℝ) + 1 := by
      intro e he
      have hme : m ≠ e := fun h => hmF (h ▸ he)
      have h1 : (((e : ℝ) - (m : ℝ))⁻¹) * ((m : ℝ) - (e : ℝ)) = -1 := by
        have h2 : (m : ℝ) - (e : ℝ) = -((e : ℝ) - (m : ℝ)) := by ring
        have h3 : (e : ℝ) - (m : ℝ) ≠ 0 :=
          sub_ne_zero.mpr (by exact_mod_cast Ne.symm hme)
        rw [h2, mul_neg, inv_mul_cancel₀ h3]
      linear_combination (-((m : ℝ) + 1) - (e : ℝ)) * h1
    have hrmβ : r m * ((∏ e ∈ F, ((m : ℝ) - (e : ℝ))) /
        ((2 * (m : ℝ) + 1) * ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1)))
        = 1 / (2 * (m : ℝ) + 1) := by
      have hrm : r m = (∏ e ∈ F, (-((m : ℝ) + 1) - (e : ℝ)))
          * (∏ e ∈ F, (((e : ℝ) - (m : ℝ))⁻¹)) := by
        have h0 : r m = N.eval (v m) * Lagrange.nodalWeight E v m := by
          simp only [hr]
        rw [h0, hNv, hnw]
      have hDpos : (0 : ℝ) < ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1) := by
        apply Finset.prod_pos
        intro e _
        have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
        linarith
      have h2m1 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by
        have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        linarith
      have hprod : (∏ e ∈ F, (-((m : ℝ) + 1) - (e : ℝ)))
          * (∏ e ∈ F, (((e : ℝ) - (m : ℝ))⁻¹)) * (∏ e ∈ F, ((m : ℝ) - (e : ℝ)))
          = ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun e he => hfactor e he
      have hX : (2 * (m : ℝ) + 1) * ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1) ≠ 0 :=
        mul_ne_zero h2m1.ne' hDpos.ne'
      rw [hrm, ← mul_div_assoc, hprod, div_eq_iff hX, div_mul_eq_mul_div, one_mul,
        mul_div_cancel_left₀ _ h2m1.ne']
    have hsq : ∀ x : ℝ, (w.eval x) ^ 2 = ∑ e ∈ E, r e * (x ^ e * w.eval x) := by
      intro x
      have hwe : w.eval x = ∑ e ∈ E, r e * x ^ e := by
        rw [hw, Polynomial.eval_finsetSum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
      rw [sq, hwe, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    have hint2 : ∀ e ∈ E, IntervalIntegrable (fun x : ℝ => r e * (x ^ e * w.eval x))
        MeasureTheory.volume 0 1 := fun e _ =>
      (continuous_const.mul ((continuous_pow _).mul w.continuous)).intervalIntegrable 0 1
    have key2 : (∫ x in (0 : ℝ)..1, ∑ e ∈ E, r e * (x ^ e * w.eval x))
        = ∑ e ∈ E, ∫ x in (0 : ℝ)..1, r e * (x ^ e * w.eval x) :=
      intervalIntegral.integral_finsetSum hint2
    have hsplit : (∑ e ∈ E, r e * (N.eval (e : ℝ) / ∏ j ∈ E, ((e : ℝ) + (j : ℝ) + 1)))
        = r m * (N.eval (m : ℝ) / ∏ j ∈ E, ((m : ℝ) + (j : ℝ) + 1)) := by
      apply Finset.sum_eq_single m
      · intro e heE hem
        have heF : e ∈ F := (Finset.mem_insert.mp (hE ▸ heE)).resolve_left hem
        rw [hN0 e heF, zero_div, mul_zero]
      · intro hcon
        have hmE : m ∈ E := hE ▸ Finset.mem_insert_self m F
        exact absurd hmE hcon
    have hEprod2 : ∏ j ∈ E, ((m : ℝ) + (j : ℝ) + 1)
        = (2 * (m : ℝ) + 1) * ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1) := by
      rw [hE, Finset.prod_insert hmF]
      congr 1
      ring
    have hNm2 : N.eval (m : ℝ) = ∏ e ∈ F, ((m : ℝ) - (e : ℝ)) := by
      rw [hN, Lagrange.eval_nodal]
    simp_rw [hsq]
    rw [key2]
    rw [show (∑ e ∈ E, ∫ x in (0 : ℝ)..1, r e * (x ^ e * w.eval x))
        = ∑ e ∈ E, r e * (N.eval (e : ℝ) / ∏ j ∈ E, ((e : ℝ) + (j : ℝ) + 1)) from
      Finset.sum_congr rfl fun e _ => by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        exact hμ e]
    rw [hsplit, hNm2, hEprod2]
    exact hrmβ

/-- L² Müntz distance lower bound and its sup-norm corollary. -/
private lemma mszL2 (m : ℕ) (F : Finset ℕ) (hmF : m ∉ F) (q : Polynomial ℝ)
    (hqm : q.coeff m = 1) (hqF : ∀ j, j ≠ m → j ∉ F → q.coeff j = 0) :
    (1 / (2 * (m : ℝ) + 1)) *
        ∏ e ∈ F, (((m : ℝ) - (e : ℝ)) / ((m : ℝ) + (e : ℝ) + 1)) ^ 2 ≤
      ∫ x in (0 : ℝ)..1, (q.eval x) ^ 2 := by
  obtain ⟨w, hw0, hwβ, hwγ⟩ := mszDual m F hmF
  set β : ℝ := (∏ e ∈ F, ((m : ℝ) - (e : ℝ))) /
    ((2 * (m : ℝ) + 1) * ∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1)) with hβ
  set c : ℝ := (2 * (m : ℝ) + 1) * β with hc
  have hsupp : q.support ⊆ insert m F := by
    intro j hj
    have hne : q.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    by_cases hjm : j = m
    · rw [hjm]
      exact Finset.mem_insert_self m F
    · by_cases hjF : j ∈ F
      · exact Finset.mem_insert_of_mem hjF
      · exact absurd (hqF j hjm hjF) hne
  have hqeval : ∀ x : ℝ, q.eval x = ∑ j ∈ insert m F, q.coeff j * x ^ j := by
    intro x
    conv_lhs => rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    exact Finset.sum_subset hsupp fun j _ hj => by
      rw [Polynomial.notMem_support_iff.mp hj, zero_mul]
  have hqw : (∫ x in (0 : ℝ)..1, q.eval x * w.eval x) = β := by
    have hfun : ∀ x : ℝ, q.eval x * w.eval x
        = ∑ j ∈ insert m F, q.coeff j * (x ^ j * w.eval x) := by
      intro x
      rw [hqeval x, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ j ∈ insert m F, IntervalIntegrable
        (fun x : ℝ => q.coeff j * (x ^ j * w.eval x)) MeasureTheory.volume 0 1 := by
      intro j _
      exact (continuous_const.mul
        ((continuous_pow _).mul w.continuous)).intervalIntegrable 0 1
    have key : (∫ x in (0 : ℝ)..1, ∑ j ∈ insert m F, q.coeff j * (x ^ j * w.eval x))
        = ∑ j ∈ insert m F, ∫ x in (0 : ℝ)..1, q.coeff j * (x ^ j * w.eval x) :=
      intervalIntegral.integral_finsetSum hint
    have hmterm : (∫ x in (0 : ℝ)..1, q.coeff m * (x ^ m * w.eval x)) = β := by
      rw [intervalIntegral.integral_const_mul _ _, hqm, one_mul]
      exact hwβ
    have hFterm : (∑ j ∈ F, ∫ x in (0 : ℝ)..1, q.coeff j * (x ^ j * w.eval x)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [intervalIntegral.integral_const_mul _ _, hw0 e he, mul_zero]
    simp_rw [hfun]
    rw [key, Finset.sum_insert hmF, hmterm, hFterm, add_zero]
  have hintQ : IntervalIntegrable (fun x : ℝ => (q.eval x) ^ 2)
      MeasureTheory.volume 0 1 :=
    (q.continuous.pow 2).intervalIntegrable 0 1
  have hintQW : IntervalIntegrable (fun x : ℝ => q.eval x * w.eval x)
      MeasureTheory.volume 0 1 :=
    (q.continuous.mul w.continuous).intervalIntegrable 0 1
  have hintW : IntervalIntegrable (fun x : ℝ => (w.eval x) ^ 2)
      MeasureTheory.volume 0 1 :=
    (w.continuous.pow 2).intervalIntegrable 0 1
  have e1 : (∫ x in (0 : ℝ)..1,
      ((q.eval x) ^ 2 - 2 * c * (q.eval x * w.eval x) + c ^ 2 * (w.eval x) ^ 2))
      = (∫ x in (0 : ℝ)..1, ((q.eval x) ^ 2 - 2 * c * (q.eval x * w.eval x)))
        + (∫ x in (0 : ℝ)..1, (c ^ 2 * (w.eval x) ^ 2)) :=
    intervalIntegral.integral_add
      (hintQ.sub (hintQW.const_mul (2 * c))) (hintW.const_mul (c ^ 2))
  have e2 : (∫ x in (0 : ℝ)..1, ((q.eval x) ^ 2 - 2 * c * (q.eval x * w.eval x)))
      = (∫ x in (0 : ℝ)..1, (q.eval x) ^ 2)
        - (∫ x in (0 : ℝ)..1, (2 * c * (q.eval x * w.eval x))) :=
    intervalIntegral.integral_sub hintQ (hintQW.const_mul (2 * c))
  have e3 : (∫ x in (0 : ℝ)..1, (2 * c * (q.eval x * w.eval x)))
      = 2 * c * (∫ x in (0 : ℝ)..1, q.eval x * w.eval x) :=
    intervalIntegral.integral_const_mul _ _
  have e4 : (∫ x in (0 : ℝ)..1, (c ^ 2 * (w.eval x) ^ 2))
      = c ^ 2 * (∫ x in (0 : ℝ)..1, (w.eval x) ^ 2) :=
    intervalIntegral.integral_const_mul _ _
  have hexpand : (∫ x in (0 : ℝ)..1, (q.eval x - c * w.eval x) ^ 2)
      = (∫ x in (0 : ℝ)..1, (q.eval x) ^ 2)
        - 2 * c * β + c ^ 2 * (1 / (2 * (m : ℝ) + 1)) := by
    have hfun : ∀ x : ℝ, (q.eval x - c * w.eval x) ^ 2
        = (q.eval x) ^ 2 - 2 * c * (q.eval x * w.eval x) + c ^ 2 * (w.eval x) ^ 2 := by
      intro x
      ring
    simp_rw [hfun]
    rw [e1, e2, e3, e4, hqw, hwγ]
  have hnonneg : (0 : ℝ) ≤ ∫ x in (0 : ℝ)..1, (q.eval x - c * w.eval x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have h2m1 : (2 * (m : ℝ) + 1) ≠ 0 := by
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hlt : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
    exact ne_of_gt hlt
  have hval : 2 * c * β - c ^ 2 * (1 / (2 * (m : ℝ) + 1))
      = (2 * (m : ℝ) + 1) * β ^ 2 := by
    rw [hc]
    field_simp
    ring
  have hQ : (2 * (m : ℝ) + 1) * β ^ 2 ≤ ∫ x in (0 : ℝ)..1, (q.eval x) ^ 2 := by
    rw [hexpand] at hnonneg
    linarith [hval, hnonneg]
  have hDne : (∏ e ∈ F, ((m : ℝ) + (e : ℝ) + 1)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro e _
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
    linarith
  have hbeta : (1 / (2 * (m : ℝ) + 1)) *
      ∏ e ∈ F, (((m : ℝ) - (e : ℝ)) / ((m : ℝ) + (e : ℝ) + 1)) ^ 2
      = (2 * (m : ℝ) + 1) * β ^ 2 := by
    rw [hβ, Finset.prod_pow, Finset.prod_div_distrib]
    field_simp
  rw [hbeta]
  exact hQ

private lemma mszSup (m : ℕ) (F : Finset ℕ) (hmF : m ∉ F) (q : Polynomial ℝ)
    (hqm : q.coeff m = 1) (hqF : ∀ j, j ≠ m → j ∉ F → q.coeff j = 0) (ε : ℝ)
    (hε : ∀ x ∈ Set.Icc (0 : ℝ) 1, |q.eval x| ≤ ε) :
    (1 / (2 * (m : ℝ) + 1)) *
        ∏ e ∈ F, (((m : ℝ) - (e : ℝ)) / ((m : ℝ) + (e : ℝ) + 1)) ^ 2 ≤ ε ^ 2 := by
  have hL2 := mszL2 m F hmF q hqm hqF
  refine le_trans hL2 ?_
  have hint : IntervalIntegrable (fun x : ℝ => (q.eval x) ^ 2)
      MeasureTheory.volume 0 1 :=
    (q.continuous.pow 2).intervalIntegrable 0 1
  have hintc : IntervalIntegrable (fun _ : ℝ => ε ^ 2)
      MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hle : (∫ x in (0 : ℝ)..1, (q.eval x) ^ 2) ≤ ∫ x in (0 : ℝ)..1, ε ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num) hint hintc (fun x hx => by
      have h := hε x hx
      have h2 := abs_le.mp h
      exact sq_le_sq' h2.1 h2.2)
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at hle
  exact hle

/-- Weierstrass product inequality. -/
private lemma mszProdIneq {ι : Type*} (G : Finset ι) (t : ι → ℝ)
    (ht : ∀ i ∈ G, 0 ≤ t i ∧ t i ≤ 1) :
    1 - ∑ i ∈ G, t i ≤ ∏ i ∈ G, (1 - t i) := by
  classical
  revert ht
  refine Finset.induction_on G ?_ ?_
  · intro _
    simp
  · intro a s has ih ht
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have htG : ∀ i ∈ s, 0 ≤ t i ∧ t i ≤ 1 :=
      fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have ha := ht a (Finset.mem_insert_self a s)
    have hnn : (0 : ℝ) ≤ ∑ i ∈ s, t i :=
      Finset.sum_nonneg fun i hi => (htG i hi).1
    have h1ta : (0 : ℝ) ≤ 1 - t a := by linarith [ha.2]
    have hP := ih htG
    nlinarith [mul_nonneg h1ta (sub_nonneg.mpr hP), mul_nonneg ha.1 hnn]

private lemma mszProdLower (Λ : ℕ → ℕ) (hΛ : StrictMono Λ)
    (hs : Summable (fun n => ((Λ (n + 1) : ℝ))⁻¹)) (m : ℕ) (hm : m ∉ Set.range Λ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : Finset ℕ,
      δ ≤ ∏ k ∈ G, (((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1)) ^ 2 := by
  classical
  set f : ℕ → ℝ := fun k =>
    (((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1)) ^ 2 with hf
  set u : ℕ → ℝ := fun k =>
    (2 * (m : ℝ) + 1) / ((m : ℝ) + (Λ k : ℝ) + 1) with hu
  have hΛne : ∀ k, Λ k ≠ m := fun k hk => hm ⟨k, hk⟩
  have hposD : ∀ k, (0 : ℝ) < (m : ℝ) + (Λ k : ℝ) + 1 := by
    intro k
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ ((Λ k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hfpos : ∀ k, 0 < f k := by
    intro k
    have hne : ((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1) ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr (by exact_mod_cast Ne.symm (hΛne k)))
        (ne_of_gt (hposD k))
    simp only [hf]
    rw [pow_two]
    exact mul_self_pos.mpr hne
  have hfle1 : ∀ k, f k ≤ 1 := by
    intro k
    have h1 : |((m : ℝ) - (Λ k : ℝ))| < (m : ℝ) + (Λ k : ℝ) + 1 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      have hk0 : (0 : ℝ) ≤ ((Λ k : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_lt]
      constructor <;> linarith
    have h2 : |((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1)| ≤ 1 := by
      rw [abs_div, abs_of_pos (hposD k)]
      exact le_of_lt ((div_lt_one (hposD k)).mpr h1)
    have hfk : f k
        = (((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1)) ^ 2 := rfl
    rw [hfk, ← sq_abs]
    simpa using pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hfu : ∀ k, f k = (1 - u k) ^ 2 := by
    intro k
    have hDk : ((m : ℝ) + (Λ k : ℝ) + 1) ≠ 0 := ne_of_gt (hposD k)
    have e : (1 : ℝ) - u k
        = (((Λ k : ℕ) : ℝ) - (m : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1) := by
      simp only [hu]
      field_simp
      ring
    have e2 : (((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1))
        = -((((Λ k : ℕ) : ℝ) - (m : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1)) := by
      rw [← neg_div]
      congr 1
      ring
    simp only [hf, e, e2, neg_sq]
  have h2u_nn : ∀ n, 0 ≤ 2 * u n := by
    intro n
    have h1 : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    simp only [hu]
    exact mul_nonneg (by norm_num) (div_nonneg h1 (le_of_lt (hposD n)))
  have hbound : ∀ n, 2 * u (n + 1)
      ≤ (2 * (2 * (m : ℝ) + 1)) * ((Λ (n + 1) : ℝ))⁻¹ := by
    intro n
    have hΛpos : (0 : ℝ) < ((Λ (n + 1) : ℕ) : ℝ) := by
      have h1 : 1 ≤ Λ (n + 1) := by
        have hle : n + 1 ≤ Λ (n + 1) := hΛ.id_le (n + 1)
        omega
      have h1r : (1 : ℝ) ≤ ((Λ (n + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hle : ((Λ (n + 1) : ℕ) : ℝ) ≤ (m : ℝ) + (Λ (n + 1) : ℝ) + 1 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    have h2 : (1 : ℝ) / ((m : ℝ) + (Λ (n + 1) : ℝ) + 1)
        ≤ 1 / ((Λ (n + 1) : ℝ)) :=
      one_div_le_one_div_of_le hΛpos hle
    have h3 : (0 : ℝ) ≤ 2 * (2 * (m : ℝ) + 1) := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    have e : 2 * u (n + 1)
        = (2 * (2 * (m : ℝ) + 1)) * (1 / ((m : ℝ) + (Λ (n + 1) : ℝ) + 1)) := by
      simp only [hu]
      ring
    have e2 : (2 * (2 * (m : ℝ) + 1)) * ((Λ (n + 1) : ℝ))⁻¹
        = (2 * (2 * (m : ℝ) + 1)) * (1 / ((Λ (n + 1) : ℝ))) := by
      rw [inv_eq_one_div]
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left h2 h3
  have hCsum : Summable
      (fun n => (2 * (2 * (m : ℝ) + 1)) * ((Λ (n + 1) : ℝ))⁻¹) :=
    hs.mul_left _
  have hshift : Summable (fun n => 2 * u (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => h2u_nn (n + 1)) hbound hCsum
  have hsumU : Summable (fun k => 2 * u k) :=
    (summable_nat_add_iff (f := fun k => 2 * u k) 1).mp hshift
  have hvan := summable_iff_vanishing_norm.mp hsumU (1 / 2 : ℝ) (by norm_num)
  obtain ⟨s₀, hs₀⟩ := hvan
  have htail : ∀ t : Finset ℕ, Disjoint t s₀ → ∑ i ∈ t, 2 * u i < 1 / 2 := by
    intro t hdt
    have h := hs₀ t hdt
    have hnn : (0 : ℝ) ≤ ∑ i ∈ t, 2 * u i :=
      Finset.sum_nonneg fun i _ => h2u_nn i
    rwa [Real.norm_eq_abs, abs_of_nonneg hnn] at h
  have hcpos : 0 < ∏ k ∈ s₀, f k := Finset.prod_pos fun k _ => hfpos k
  refine ⟨(∏ k ∈ s₀, f k) / 2, half_pos hcpos, fun G => ?_⟩
  have hsplit := Finset.prod_filter_mul_prod_filter_not G (fun k => k ∈ s₀) f
  have hsub : G.filter (fun k => k ∈ s₀) ⊆ s₀ := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hfirst : ∏ k ∈ s₀, f k ≤ ∏ k ∈ G.filter (fun k => k ∈ s₀), f k :=
    Finset.prod_le_prod_of_subset_of_le_one₀ hsub
      (fun k _ => le_of_lt (hfpos k)) (fun k _ _ => hfle1 k)
  have hdis : Disjoint (G.filter (fun k => k ∉ s₀)) s₀ := by
    rw [Finset.disjoint_left]
    intro a ha hs
    exact (Finset.mem_filter.mp ha).2 hs
  have htailG := htail _ hdis
  have hfac : ∀ k ∈ G.filter (fun k => k ∉ s₀), (1 : ℝ) - 2 * u k ≤ f k := by
    intro k _
    rw [hfu k]
    nlinarith [sq_nonneg (u k)]
  have hnn1 : ∀ k ∈ G.filter (fun k => k ∉ s₀), (0 : ℝ) ≤ 1 - 2 * u k := by
    intro k hk
    have hle1 : 2 * u k ≤ ∑ i ∈ G.filter (fun k => k ∉ s₀), 2 * u i :=
      Finset.single_le_sum (fun i _ => h2u_nn i) hk
    linarith [htailG]
  have hIneq : 1 - ∑ i ∈ G.filter (fun k => k ∉ s₀), 2 * u i
      ≤ ∏ k ∈ G.filter (fun k => k ∉ s₀), (1 - 2 * u k) :=
    mszProdIneq _ _ fun k hk => by
      have hle1 : 2 * u k ≤ ∑ i ∈ G.filter (fun k => k ∉ s₀), 2 * u i :=
        Finset.single_le_sum (fun i _ => h2u_nn i) hk
      exact ⟨h2u_nn k, by linarith [htailG]⟩
  have hprod1 : ∏ k ∈ G.filter (fun k => k ∉ s₀), (1 - 2 * u k)
      ≤ ∏ k ∈ G.filter (fun k => k ∉ s₀), f k :=
    Finset.prod_le_prod₀ hnn1 hfac
  have hsecond : (1 / 2 : ℝ) ≤ ∏ k ∈ G.filter (fun k => k ∉ s₀), f k := by
    linarith [hIneq, hprod1, htailG]
  have hA0 : (0 : ℝ) ≤ ∏ k ∈ G.filter (fun k => k ∈ s₀), f k :=
    Finset.prod_nonneg fun k _ => le_of_lt (hfpos k)
  calc (∏ k ∈ s₀, f k) / 2 = (∏ k ∈ s₀, f k) * (1 / 2) := by ring
    _ ≤ (∏ k ∈ G.filter (fun k => k ∈ s₀), f k)
        * (∏ k ∈ G.filter (fun k => k ∉ s₀), f k) :=
        mul_le_mul hfirst hsecond (by norm_num) hA0
    _ = ∏ k ∈ G, f k := hsplit

private lemma mszMissing (Λ : ℕ → ℕ) (hΛ : StrictMono Λ)
    (hs : Summable (fun n => ((Λ (n + 1) : ℝ))⁻¹)) : ∃ m : ℕ, m ∉ Set.range Λ := by
  by_contra hcon
  have hall : ∀ m, m ∈ Set.range Λ := fun m => by
    by_contra hm
    exact hcon ⟨m, hm⟩
  have hrange : Set.range Λ = Set.univ := Set.eq_univ_of_forall hall
  have hΛid : Λ = id :=
    (hΛ.range_inj_of_wellFoundedLT strictMono_id).mp (by rw [hrange, Set.range_id])
  have h2 : (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ))⁻¹)
      = (fun n => ((Λ (n + 1) : ℝ))⁻¹) := by
    funext n
    simp only [hΛid, id_eq]
  have hs1 : Summable (fun n : ℕ => ((((n + 1 : ℕ)) : ℝ))⁻¹) := h2 ▸ hs
  exact Real.not_summable_natCast_inv
    ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ))⁻¹) 1).mp hs1)

private lemma mszNec (Λ : ℕ → ℕ) (hΛ : StrictMono Λ)
    (h : (Submodule.span ℝ (Set.range fun n : ℕ =>
      ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I)).topologicalClosure = ⊤) :
    ¬Summable (fun n => ((Λ (n + 1) : ℝ))⁻¹) := by
  classical
  intro hs
  obtain ⟨m, hm⟩ := mszMissing Λ hΛ hs
  obtain ⟨δ, hδpos, hδ⟩ := mszProdLower Λ hΛ hs m hm
  have h2m1 : (0 : ℝ) < 2 * (m : ℝ) + 1 := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  set t : ℝ := δ / (2 * (2 * (m : ℝ) + 1)) with ht
  set ε : ℝ := min 1 t with hε
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos hδpos (by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith)
  have hεpos : 0 < ε := lt_min_iff.mpr ⟨by norm_num, htpos⟩
  have hεsq : ε ^ 2 < δ / (2 * (m : ℝ) + 1) := by
    have hε1 : ε ≤ 1 := min_le_left 1 t
    have hεt : ε ≤ t := min_le_right 1 t
    have hεnn : 0 ≤ ε := le_of_lt hεpos
    have h1 : ε ^ 2 ≤ ε := by
      calc ε ^ 2 = ε * ε := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hε1 hεnn
        _ = ε := mul_one ε
    have h2 : t = (δ / (2 * (m : ℝ) + 1)) / 2 := by
      rw [ht, div_div]
      congr 1
      ring
    have h3 : (δ / (2 * (m : ℝ) + 1)) / 2 < δ / (2 * (m : ℝ) + 1) :=
      half_lt_self (div_pos hδpos h2m1)
    linarith
  have hmem : ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I
      ∈ (Submodule.span ℝ (Set.range fun n : ℕ =>
        ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I)).topologicalClosure := by
    rw [h]
    exact Submodule.mem_top
  have hmemclose : ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I
      ∈ closure (↑(Submodule.span ℝ (Set.range fun n : ℕ =>
        ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I))) := hmem
  rw [Metric.mem_closure_iff] at hmemclose
  obtain ⟨f, hfmem, hdist⟩ := hmemclose ε hεpos
  have hfspan : f ∈ Submodule.span ℝ (Set.range fun n : ℕ =>
      ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I) := hfmem
  obtain ⟨P, hP, hPsupp⟩ := mszExistsPoly Λ f hfspan
  have hmP : P.coeff m = 0 := hPsupp m hm
  have hmF : m ∉ P.support := fun h => (Polynomial.mem_support_iff.mp h) hmP
  have hqm : (Polynomial.X ^ m - P).coeff m = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, hmP, sub_zero]
  have hqF : ∀ j, j ≠ m → j ∉ P.support
      → (Polynomial.X ^ m - P).coeff j = 0 := by
    intro j hjm hjF
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ite_eq_right hjm,
      Polynomial.notMem_support_iff.mp hjF, sub_zero]
  have hqε : ∀ x ∈ Set.Icc (0 : ℝ) 1, |(Polynomial.X ^ m - P).eval x| ≤ ε := by
    intro x hx
    have hxI : x ∈ I := hx
    have e : |(Polynomial.X ^ m - P).eval x|
        = ‖(((Polynomial.X ^ m - P).toContinuousMapOn I) ⟨x, hxI⟩ : ℝ)‖ := by
      rw [Real.norm_eq_abs, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply]
    have hqfun : (Polynomial.X ^ m - P).toContinuousMapOn I
        = ((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I - f := by
      rw [← hP]
      simp only [← Polynomial.toContinuousMapOnAlgHom_apply, map_sub]
    rw [e, hqfun]
    calc ‖((((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I - f) ⟨x, hxI⟩ :
        ℝ)‖
        ≤ ‖((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I - f‖ :=
          ContinuousMap.norm_coe_le_norm _ _
      _ = dist (((Polynomial.X : Polynomial ℝ) ^ m).toContinuousMapOn I) f := by
          rw [dist_eq_norm]
      _ ≤ ε := le_of_lt hdist
  have hbound := mszSup m P.support hmF _ hqm hqF ε hqε
  have hsuppR : ∀ e ∈ P.support, e ∈ Set.range Λ := by
    intro e he
    by_contra hcon
    exact (Polynomial.mem_support_iff.mp he) (hPsupp e hcon)
  have hG : P.support.filter (fun e => e ∈ Set.range Λ) = P.support :=
    Finset.filter_true_of_mem (fun e he => hsuppR e he)
  have hInj : Set.InjOn Λ (Λ ⁻¹' ↑P.support) := hΛ.injective.injOn
  set G : Finset ℕ := P.support.preimage Λ hInj with hGdef
  have hreidx : ∏ e ∈ P.support, (((m : ℝ) - (e : ℝ)) / ((m : ℝ) + (e : ℝ) + 1)) ^ 2
      = ∏ k ∈ G, (((m : ℝ) - (Λ k : ℝ)) / ((m : ℝ) + (Λ k : ℝ) + 1)) ^ 2 := by
    have hpp := Finset.prod_preimage' Λ P.support hInj
      (fun e => (((m : ℝ) - (e : ℝ)) / ((m : ℝ) + (e : ℝ) + 1)) ^ 2)
    rw [hG] at hpp
    exact hpp.symm
  rw [hreidx] at hbound
  have hδG := hδ G
  have hpos : (0 : ℝ) < 1 / (2 * (m : ℝ) + 1) :=
    div_pos one_pos h2m1
  have hmul := mul_le_mul_of_nonneg_left hδG (le_of_lt hpos)
  have heq : (1 / (2 * (m : ℝ) + 1)) * δ = δ / (2 * (m : ℝ) + 1) := by ring
  linarith [hbound, hmul, heq, hεsq]

/--
**Müntz–Szász theorem for integer exponents.** Let $\Lambda : \mathbb{N} \to \mathbb{N}$ be
strictly increasing with $\Lambda(0) = 0$. The real linear span of the monomials
$x \mapsto x^{\Lambda(n)}$, $n \in \mathbb{N}$, restricted to $[0, 1]$, is dense in
$C([0, 1], \mathbb{R})$ with the uniform norm if and only if the series
$\sum_{n \ge 0} 1/\Lambda(n+1)$ diverges, that is, the sequence
$(1/\Lambda(n+1))_{n \in \mathbb{N}}$ is not summable.

Proves `Wanted` entry `muntz_szasz_nat`.

Source: C. Müntz, Festschrift H. A. Schwarz
1914 303-312 and O. Szász, Math. Ann. 77 (1916) 482-496, Müntz-Szász theorem; Rudin Real &
Complex; Lean states integer-exponent `ℕ→ℕ` `StrictMono` with `0∈range` case as closure `= ⊤` iff
non-summable reciprocals.
-/
public theorem muntz_szasz_nat
    (Λ : ℕ → ℕ)
    (hΛ_strict : StrictMono Λ)
    (hΛ_zero : Λ 0 = 0) :
    (Submodule.span ℝ (Set.range (fun n : ℕ =>
        ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn I))).topologicalClosure = ⊤
    ↔ ¬Summable (fun n : ℕ => ((Λ (n + 1) : ℝ)⁻¹)) := by
  constructor
  · exact mszNec Λ hΛ_strict
  · intro hdiv
    exact mszClosureTop _
      (fun m => mszMonomialMem Λ hΛ_strict hΛ_zero hdiv m)

end MathlibExt.Analysis.FunctionalAnalysis.MuntzSzaszWanted
