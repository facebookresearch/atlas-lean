/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MathlibExt.Analysis.Normed.Algebra.LieTrotterError

open scoped Matrix.Norms.L2Operator

/-- One Lie–Trotter step for Hermitian `A` and `B` at time `t`, in the
order of Childs, Su, Tran, Wiebe and Zhu, *A Theory of Trotter Error*,
arXiv:1912.08854v3, Section 5.1: `S₁(t) = e^{-itB} e^{-itA}`. -/
noncomputable def trotterStep {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • B) *
    NormedSpace.exp (-(Complex.I * (t : ℂ)) • A)

/-- If `A` and `B` commute, one Lie–Trotter step is exact. -/
theorem trotterStep_of_commute {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hAB : Commute A B) (t : ℝ) :
    trotterStep A B t =
      NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B)) := by
  letI := NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  unfold trotterStep
  have hcomm : Commute (-(Complex.I * (t : ℂ)) • B)
      (-(Complex.I * (t : ℂ)) • A) := by
    show (-(Complex.I * (t : ℂ)) • B) * (-(Complex.I * (t : ℂ)) • A) =
      (-(Complex.I * (t : ℂ)) • A) * (-(Complex.I * (t : ℂ)) • B)
    simp only [smul_mul_assoc, mul_smul_comm]
    rw [hAB.symm.eq]
  have hexp := NormedSpace.exp_add_of_commute hcomm
  have hadd : (-(Complex.I * (t : ℂ)) • B) + (-(Complex.I * (t : ℂ)) • A) =
      (-(Complex.I * (t : ℂ))) • (A + B) := by
    rw [← smul_add, add_comm B A]
  rw [hadd] at hexp
  first | exact hexp.symm | exact hexp

/-- The exponential of a skew-Hermitian scalar multiple is unitary, hence
has L2 operator norm at most one (the L2 operator norm is a C-star norm;
the bound `≤ 1` also covers the trivial `n = 0` case). -/
private theorem norm_exp_unitary_le_one {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (s : ℝ) :
    ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • H)‖ ≤ 1 := by
  letI := NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  have hmem : (-(Complex.I * (s : ℂ)) • H) ∈
      skewAdjoint (Matrix (Fin n) (Fin n) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp only [star_smul, hH.star_eq]
    have hscalar : star (-(Complex.I * (s : ℂ))) =
        -(-(Complex.I * (s : ℂ))) := by
      simp
    rw [hscalar, neg_smul]
  have hU := NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hmem
  by_cases hnt : Nontrivial (Matrix (Fin n) (Fin n) ℂ)
  · have hnorm := CStarRing.norm_of_mem_unitary hU
    rw [hnorm]
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have heq : NormedSpace.exp (-(Complex.I * (s : ℂ)) • H) = 0 :=
      hnt.elim _ _
    rw [heq, norm_zero]
    exact zero_le_one

/-- Telescoping estimate for powers with factors of norm at most one,
assuming nontriviality (so the C-star norm provides `NormOneClass`). -/
private theorem norm_pow_sub_pow_le_aux_of_nontrivial {n : ℕ}
    [Nontrivial (Matrix (Fin n) (Fin n) ℂ)]
    (U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (r : ℕ) :
    ‖U ^ r - V ^ r‖ ≤ (r : ℝ) * ‖U - V‖ := by
  induction r with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    have hid : U ^ k * U - V ^ k * V =
        U ^ k * (U - V) + (U ^ k - V ^ k) * V := by
      simp only [mul_sub, sub_mul]
      abel
    rw [hid]
    have hUk : ‖U ^ k‖ ≤ 1 := by
      have h1 : ‖U ^ k‖ ≤ ‖U‖ ^ k := by apply norm_pow_le
      have h0 : 0 ≤ ‖U‖ := by positivity
      have h2 : ‖U‖ ^ k ≤ 1 := by apply pow_le_one₀ h0 hU
      exact h1.trans h2
    have e1 : ‖U ^ k * (U - V)‖ ≤ 1 * ‖U - V‖ := by
      have h : ‖U ^ k * (U - V)‖ ≤ ‖U ^ k‖ * ‖U - V‖ := by
        apply norm_mul_le
      have h' : ‖U ^ k‖ * ‖U - V‖ ≤ 1 * ‖U - V‖ :=
        mul_le_mul_of_nonneg_right hUk (by positivity)
      exact h.trans h'
    have e2 : ‖(U ^ k - V ^ k) * V‖ ≤ ((k : ℝ) * ‖U - V‖) * 1 := by
      have h : ‖(U ^ k - V ^ k) * V‖ ≤ ‖U ^ k - V ^ k‖ * ‖V‖ := by
        apply norm_mul_le
      have h1 : ‖U ^ k - V ^ k‖ * ‖V‖ ≤ ((k : ℝ) * ‖U - V‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      have hVk_nonneg : 0 ≤ (k : ℝ) * ‖U - V‖ := by positivity
      have h2 : ((k : ℝ) * ‖U - V‖) * ‖V‖ ≤ ((k : ℝ) * ‖U - V‖) * 1 :=
        mul_le_mul_of_nonneg_left hV hVk_nonneg
      have h' : ‖U ^ k - V ^ k‖ * ‖V‖ ≤ ((k : ℝ) * ‖U - V‖) * 1 :=
        h1.trans h2
      exact h.trans h'
    have h_add : ‖U ^ k * (U - V) + (U ^ k - V ^ k) * V‖ ≤
        ‖U ^ k * (U - V)‖ + ‖(U ^ k - V ^ k) * V‖ := by
      apply norm_add_le
    have h_sum : ‖U ^ k * (U - V)‖ + ‖(U ^ k - V ^ k) * V‖ ≤
        1 * ‖U - V‖ + ((k : ℝ) * ‖U - V‖) * 1 :=
      add_le_add e1 e2
    have h_le : ‖U ^ k * (U - V) + (U ^ k - V ^ k) * V‖ ≤
        1 * ‖U - V‖ + ((k : ℝ) * ‖U - V‖) * 1 :=
      h_add.trans h_sum
    have h_eq : (1 : ℝ) * ‖U - V‖ + ((k : ℝ) * ‖U - V‖) * 1 =
        (((k + 1 : ℕ)) : ℝ) * ‖U - V‖ := by
      push_cast
      ring
    rw [h_eq] at h_le
    exact h_le

/-- Telescoping estimate for powers with factors of norm at most one. -/
private theorem norm_pow_sub_pow_le_aux {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (r : ℕ) :
    ‖U ^ r - V ^ r‖ ≤ (r : ℝ) * ‖U - V‖ := by
  by_cases hnt : Nontrivial (Matrix (Fin n) (Fin n) ℂ)
  · exact norm_pow_sub_pow_le_aux_of_nontrivial U V hU hV r
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have hUV : U = V := hnt.elim U V
    have hUVr : U ^ r = V ^ r := by rw [hUV]
    rw [hUVr, sub_self, norm_zero]
    have hnn : 0 ≤ (r : ℝ) * ‖U - V‖ := by positivity
    exact hnn

/-- Powers of an exponential are exponentials of scalar multiples. -/
private theorem exp_pow_eq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) :
    (NormedSpace.exp X) ^ k =
      NormedSpace.exp (((k : ℕ) : ℂ) • X) := by
  letI := NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  induction k with
  | zero =>
    simp [pow_zero, NormedSpace.exp_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    have hcast : (((k + 1 : ℕ) : ℂ)) = (((k : ℕ) : ℂ)) + 1 := by
      push_cast
      ring
    rw [hcast, add_smul, one_smul]
    have hcomm : Commute ((((k : ℕ) : ℂ)) • X) X := by
      show ((((k : ℕ) : ℂ)) • X) * X = X * ((((k : ℕ) : ℂ)) • X)
      simp only [smul_mul_assoc, mul_smul_comm]
    have hexp := NormedSpace.exp_add_of_commute hcomm
    first | exact hexp.symm | exact hexp

/-- The `r`-th power of a small exact step is the full evolution. -/
private theorem exp_pow_small_step {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (r : ℕ) (hr : 0 < r) :
    (NormedSpace.exp (-(Complex.I * (((t / (r : ℝ)) : ℂ))) • H)) ^ r =
      NormedSpace.exp (-(Complex.I * (t : ℂ)) • H) := by
  letI := NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  have hpow := exp_pow_eq (-(Complex.I * (((t / (r : ℝ)) : ℂ))) • H) r
  rw [hpow]
  congr 1
  rw [← mul_smul]
  congr 1
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrR : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hrN : r ≠ 0 := ne_of_gt hr
  have hrC : (((r : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hrR
  have hrCN : (((r : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast hrN
  push_cast
  field_simp

/-- The one-step Lie–Trotter error bound with commutator scaling
(Childs–Su–Tran–Wiebe–Zhu, arXiv:1912.08854v3, eq. (143)): for Hermitian
`A` and `B` and `t ≥ 0`, `‖S₁(t) − e^{-it(A+B)}‖ ≤ (t²/2) ‖[B, A]‖` in the
L2 operator norm. -/
theorem norm_trotterStep_sub_exp_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    ‖trotterStep A B t -
        NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B))‖ ≤
      t ^ 2 / 2 * ‖B * A - A * B‖ := by
  by_cases hcomm : B * A - A * B = 0
  · have hEq : B * A = A * B := sub_eq_zero.mp hcomm
    have hComm : Commute A B := by
      show A * B = B * A
      exact hEq.symm
    rw [trotterStep_of_commute hComm t, sub_self, norm_zero, hcomm,
      norm_zero, mul_zero]
  · -- Interaction-picture bound via the double-integral representation.
    letI := NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
    set X₁ : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • B) with hX₁
    set Y₁ : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • A) with hY₁
    set Z₁ : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • (A + B)) with hZ₁
    have hZ : Z₁ = X₁ + Y₁ := by
      rw [hX₁, hY₁, hZ₁, smul_add, neg_add]
      abel
    have hsmul_neg : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ),
        s • (-(Complex.I • M)) = (-(Complex.I * (s : ℂ))) • M := by
      intro M s
      rw [smul_neg, ← smul_assoc, Complex.real_smul, ← neg_smul]
      congr 1
      ring
    have hsmul_pos : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ),
        s • (Complex.I • M) = (-(Complex.I * ((-s : ℝ) : ℂ))) • M := by
      intro M s
      rw [← smul_assoc, Complex.real_smul]
      congr 1
      push_cast
      ring
    have hE1 : ∀ s : ℝ, s • X₁ = (-(Complex.I * (s : ℂ))) • B := by
      intro s
      rw [hX₁]
      exact hsmul_neg B s
    have hE2 : ∀ s : ℝ, s • Y₁ = (-(Complex.I * (s : ℂ))) • A := by
      intro s
      rw [hY₁]
      exact hsmul_neg A s
    have hE3 : ∀ s : ℝ,
        s • (-Z₁) = (-(Complex.I * ((-s : ℝ) : ℂ))) • (A + B) := by
      intro s
      rw [hZ₁]
      simp only [neg_neg]
      exact hsmul_pos (A + B) s
    have hE2m : ∀ u : ℝ, u • (-Y₁) = (-(Complex.I * ((-u : ℝ) : ℂ))) • A := by
      intro u
      rw [hY₁]
      simp only [neg_neg]
      exact hsmul_pos A u
    have hN1 : ∀ s : ℝ, ‖NormedSpace.exp (s • X₁)‖ ≤ 1 := by
      intro s
      rw [hE1 s]
      exact norm_exp_unitary_le_one B hB s
    have hN2 : ∀ s : ℝ, ‖NormedSpace.exp (s • Y₁)‖ ≤ 1 := by
      intro s
      rw [hE2 s]
      exact norm_exp_unitary_le_one A hA s
    have hABh : (A + B).IsHermitian := hA.add hB
    have hN3 : ∀ s : ℝ, ‖NormedSpace.exp (s • (-Z₁))‖ ≤ 1 := by
      intro s
      rw [hE3 s]
      exact norm_exp_unitary_le_one (A + B) hABh (-s)
    have hN2m : ∀ u : ℝ, ‖NormedSpace.exp (u • (-Y₁))‖ ≤ 1 := by
      intro u
      rw [hE2m u]
      exact norm_exp_unitary_le_one A hA (-u)
    have e1 : ∀ s : ℝ, NormedSpace.exp (s • Y₁) * Y₁ =
        Y₁ * NormedSpace.exp (s • Y₁) :=
      fun s => (((Commute.refl Y₁).smul_right s).exp_right).eq.symm
    have hYX : Y₁ * X₁ - X₁ * Y₁ = B * A - A * B := by
      rw [hX₁, hY₁, neg_mul_neg, neg_mul_neg, smul_mul_smul, smul_mul_smul,
        Complex.I_mul_I, ← smul_sub, neg_smul, one_smul, neg_sub]
    have hvalInner : ∀ x : ℝ,
        ((NormedSpace.exp (x • Y₁) * Y₁) * X₁) *
            NormedSpace.exp (x • (-Y₁)) +
            (NormedSpace.exp (x • Y₁) * X₁) *
            ((-Y₁) * NormedSpace.exp (x • (-Y₁))) =
          NormedSpace.exp (x • Y₁) * (Y₁ * X₁ - X₁ * Y₁) *
            NormedSpace.exp (x • (-Y₁)) := by
      intro x
      simp only [mul_assoc, mul_add, add_mul, mul_neg, neg_mul,
        sub_eq_add_neg]
    have hEmbed : ∀ s : ℝ, 0 ≤ s →
        ‖NormedSpace.exp (s • Y₁) * X₁ - X₁ * NormedSpace.exp (s • Y₁)‖ ≤
          s * ‖Y₁ * X₁ - X₁ * Y₁‖ := by
      intro s hs
      set g : ℝ → Matrix (Fin n) (Fin n) ℂ := fun u =>
        NormedSpace.exp (u • Y₁) * X₁ * NormedSpace.exp (u • (-Y₁)) with hg
      set g' : ℝ → Matrix (Fin n) (Fin n) ℂ := fun u =>
        NormedSpace.exp (u • Y₁) * (Y₁ * X₁ - X₁ * Y₁) *
          NormedSpace.exp (u • (-Y₁)) with hg'
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt g (g' x) x := by
        intro x _
        have h1 := hasDerivAt_exp_smul_const Y₁ x
        have h2 := hasDerivAt_exp_smul_const' (-Y₁) x
        have hmul := (h1.mul_const X₁).mul h2
        rw [hg, hg']
        beta_reduce at hmul ⊢
        rw [hvalInner x] at hmul
        exact hmul.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => rfl)
      have hcont : Continuous g' := by
        rw [hg']
        have eA : Continuous fun u : ℝ => NormedSpace.exp (u • Y₁) :=
          NormedSpace.exp_continuous.comp
            (continuous_id.smul continuous_const)
        have eB : Continuous fun u : ℝ => NormedSpace.exp (u • (-Y₁)) :=
          NormedSpace.exp_continuous.comp
            (continuous_id.smul continuous_const)
        exact ((eA.mul continuous_const).mul eB)
      have hint : IntervalIntegrable g' MeasureTheory.volume 0 s :=
        hcont.intervalIntegrable 0 s
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      have hpt : ∀ y ∈ Set.uIoc (0 : ℝ) s,
          ‖g' y‖ ≤ ‖Y₁ * X₁ - X₁ * Y₁‖ := by
        intro y _
        rw [hg']
        beta_reduce
        calc ‖NormedSpace.exp (y • Y₁) * (Y₁ * X₁ - X₁ * Y₁) *
              NormedSpace.exp (y • (-Y₁))‖
            ≤ ‖NormedSpace.exp (y • Y₁) * (Y₁ * X₁ - X₁ * Y₁)‖ *
              ‖NormedSpace.exp (y • (-Y₁))‖ := norm_mul_le _ _
          _ ≤ (‖NormedSpace.exp (y • Y₁)‖ * ‖Y₁ * X₁ - X₁ * Y₁‖) *
              ‖NormedSpace.exp (y • (-Y₁))‖ :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (1 * ‖Y₁ * X₁ - X₁ * Y₁‖) *
              ‖NormedSpace.exp (y • (-Y₁))‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hN2 y) (norm_nonneg _))
                (norm_nonneg _)
          _ ≤ (1 * ‖Y₁ * X₁ - X₁ * Y₁‖) * 1 :=
              mul_le_mul_of_nonneg_left (hN2m y) (by positivity)
          _ = ‖Y₁ * X₁ - X₁ * Y₁‖ := by rw [one_mul, mul_one]
      have hle : ‖g s - g 0‖ ≤ ‖Y₁ * X₁ - X₁ * Y₁‖ * |s - 0| := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := g')
          (C := ‖Y₁ * X₁ - X₁ * Y₁‖) hpt
        rw [hftc] at h
        exact h
      simp only [hg, zero_smul, NormedSpace.exp_zero, one_mul,
        mul_one] at hle
      have hEE : NormedSpace.exp (s • (-Y₁)) * NormedSpace.exp (s • Y₁)
          = 1 := by
        have hcomm : Commute (s • (-Y₁)) (s • Y₁) :=
          (((Commute.refl Y₁).neg_left).smul_left s).smul_right s
        have hadd : (s • (-Y₁)) + (s • Y₁) = 0 := by
          rw [← smul_add, neg_add_cancel, smul_zero]
        have h := NormedSpace.exp_add_of_commute hcomm
        rw [hadd, NormedSpace.exp_zero] at h
        exact h.symm
      have htarget : NormedSpace.exp (s • Y₁) * X₁ -
          X₁ * NormedSpace.exp (s • Y₁)
          = (NormedSpace.exp (s • Y₁) * X₁ *
            NormedSpace.exp (s • (-Y₁)) - X₁) *
            NormedSpace.exp (s • Y₁) := by
        have hassoc := mul_assoc (NormedSpace.exp (s • Y₁) * X₁)
          (NormedSpace.exp (s • (-Y₁))) (NormedSpace.exp (s • Y₁))
        rw [sub_mul, hassoc, hEE, mul_one]
      rw [htarget]
      calc ‖(NormedSpace.exp (s • Y₁) * X₁ *
            NormedSpace.exp (s • (-Y₁)) - X₁) *
            NormedSpace.exp (s • Y₁)‖
          ≤ ‖NormedSpace.exp (s • Y₁) * X₁ *
              NormedSpace.exp (s • (-Y₁)) - X₁‖ *
              ‖NormedSpace.exp (s • Y₁)‖ := norm_mul_le _ _
        _ ≤ (‖Y₁ * X₁ - X₁ * Y₁‖ * |s - 0|) * 1 :=
            mul_le_mul hle (hN2 s) (norm_nonneg _) (by positivity)
        _ = s * ‖Y₁ * X₁ - X₁ * Y₁‖ := by
            rw [sub_zero, abs_of_nonneg hs]; ring
    have hvalOuter : ∀ x : ℝ,
        (NormedSpace.exp (x • X₁) * X₁) *
            (NormedSpace.exp (x • Y₁) * NormedSpace.exp (x • (-Z₁))) +
            NormedSpace.exp (x • X₁) *
            ((NormedSpace.exp (x • Y₁) * Y₁) *
              NormedSpace.exp (x • (-Z₁)) +
              NormedSpace.exp (x • Y₁) *
              ((-Z₁) * NormedSpace.exp (x • (-Z₁)))) =
          NormedSpace.exp (x • X₁) * (X₁ * NormedSpace.exp (x • Y₁) -
            NormedSpace.exp (x • Y₁) * X₁) *
            NormedSpace.exp (x • (-Z₁)) := by
      intro x
      rw [hZ]
      simp only [neg_add, mul_add, add_mul, mul_assoc, mul_neg, neg_mul,
        sub_eq_add_neg]
      abel
    set f : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s =>
      NormedSpace.exp (s • X₁) *
        (NormedSpace.exp (s • Y₁) * NormedSpace.exp (s • (-Z₁))) with hf
    set f' : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s =>
      NormedSpace.exp (s • X₁) * (X₁ * NormedSpace.exp (s • Y₁) -
        NormedSpace.exp (s • Y₁) * X₁) *
        NormedSpace.exp (s • (-Z₁)) with hf'
    have hderivF : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt f (f' x) x := by
      intro x _
      have h1 := hasDerivAt_exp_smul_const X₁ x
      have h2 := hasDerivAt_exp_smul_const Y₁ x
      have h3 := hasDerivAt_exp_smul_const' (-Z₁) x
      have hmul := h1.mul (h2.mul h3)
      simp only [Pi.mul_apply] at hmul
      rw [hf, hf']
      beta_reduce at hmul ⊢
      rw [hvalOuter x] at hmul
      exact hmul.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    have hcontF : Continuous f' := by
      rw [hf']
      have eA : Continuous fun s : ℝ => NormedSpace.exp (s • X₁) :=
        NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
      have eB : Continuous fun s : ℝ => NormedSpace.exp (s • Y₁) :=
        NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
      have eC : Continuous fun s : ℝ => NormedSpace.exp (s • (-Z₁)) :=
        NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
      have eMid : Continuous fun s : ℝ =>
          X₁ * NormedSpace.exp (s • Y₁) - NormedSpace.exp (s • Y₁) * X₁ :=
        (continuous_const.mul eB).sub (eB.mul continuous_const)
      exact ((eA.mul eMid).mul eC)
    have hintF : IntervalIntegrable f' MeasureTheory.volume 0 t :=
      hcontF.intervalIntegrable 0 t
    have hftcF :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hintF
    have hptF : ∀ s : ℝ, 0 ≤ s →
        ‖f' s‖ ≤ s * ‖Y₁ * X₁ - X₁ * Y₁‖ := by
      intro s hs0
      have h2 : ‖X₁ * NormedSpace.exp (s • Y₁) -
          NormedSpace.exp (s • Y₁) * X₁‖ ≤ s * ‖Y₁ * X₁ - X₁ * Y₁‖ := by
        rw [norm_sub_rev]
        exact hEmbed s hs0
      rw [hf']
      beta_reduce
      calc ‖NormedSpace.exp (s • X₁) * (X₁ * NormedSpace.exp (s • Y₁) -
            NormedSpace.exp (s • Y₁) * X₁) *
            NormedSpace.exp (s • (-Z₁))‖
          ≤ ‖NormedSpace.exp (s • X₁) *
              (X₁ * NormedSpace.exp (s • Y₁) -
                NormedSpace.exp (s • Y₁) * X₁)‖ *
              ‖NormedSpace.exp (s • (-Z₁))‖ := norm_mul_le _ _
        _ ≤ (‖NormedSpace.exp (s • X₁)‖ *
              ‖X₁ * NormedSpace.exp (s • Y₁) -
                NormedSpace.exp (s • Y₁) * X₁‖) *
              ‖NormedSpace.exp (s • (-Z₁))‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (1 * (s * ‖Y₁ * X₁ - X₁ * Y₁‖)) *
              ‖NormedSpace.exp (s • (-Z₁))‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hN1 s) h2 (norm_nonneg _) zero_le_one)
              (norm_nonneg _)
        _ ≤ (1 * (s * ‖Y₁ * X₁ - X₁ * Y₁‖)) * 1 :=
            mul_le_mul_of_nonneg_left (hN3 s) (by positivity)
        _ = s * ‖Y₁ * X₁ - X₁ * Y₁‖ := by rw [one_mul, mul_one]
    have hbound : IntervalIntegrable
        (fun s : ℝ => s * ‖Y₁ * X₁ - X₁ * Y₁‖) MeasureTheory.volume 0 t :=
      (continuous_id.mul continuous_const).intervalIntegrable 0 t
    have hae : ∀ᵐ s ∂MeasureTheory.volume,
        s ∈ Set.Ioc (0 : ℝ) t → ‖f' s‖ ≤ s * ‖Y₁ * X₁ - X₁ * Y₁‖ :=
      Filter.Eventually.of_forall fun s hs => hptF s (le_of_lt hs.1)
    have hleF : ‖f t - f 0‖ ≤ ‖Y₁ * X₁ - X₁ * Y₁‖ * t ^ 2 / 2 := by
      have h := intervalIntegral.norm_integral_le_of_norm_le ht hae hbound
      rw [hftcF] at h
      have hInt : (∫ s in (0 : ℝ)..t, s * ‖Y₁ * X₁ - X₁ * Y₁‖)
          = ‖Y₁ * X₁ - X₁ * Y₁‖ * t ^ 2 / 2 := by
        rw [intervalIntegral.integral_mul_const]
        have hId : (∫ s in (0 : ℝ)..t, s) = t ^ 2 / 2 := by
          have hderivId : ∀ x ∈ Set.uIcc (0 : ℝ) t,
              HasDerivAt (fun s : ℝ => s ^ 2 / 2) x x := by
            intro x _
            have hh := (hasDerivAt_id x).pow 2
            simpa using hh.div_const 2
          have hintId : IntervalIntegrable (fun s : ℝ => s)
              MeasureTheory.volume 0 t :=
            continuous_id.intervalIntegrable 0 t
          have hh :=
            intervalIntegral.integral_eq_sub_of_hasDerivAt hderivId hintId
          simpa using hh
        rw [hId]
        ring
      rw [hInt] at h
      exact h
    simp only [hf, zero_smul, NormedSpace.exp_zero, mul_one] at hleF
    have hFt : NormedSpace.exp (t • X₁) *
          (NormedSpace.exp (t • Y₁) * NormedSpace.exp (t • (-Z₁))) =
          trotterStep A B t * NormedSpace.exp (t • (-Z₁)) := by
      rw [← mul_assoc, hE1 t, hE2 t]
      rfl
    have hexpZ : NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B)) *
          NormedSpace.exp (t • (-Z₁)) = 1 := by
      have harg : (-(Complex.I * ((-t : ℝ) : ℂ))) • (A + B)
          = -((-(Complex.I * (t : ℂ))) • (A + B)) := by
        rw [← neg_smul]
        congr 1
        push_cast
        ring
      rw [hE3 t, harg]
      have hcomm : Commute ((-(Complex.I * (t : ℂ))) • (A + B))
          (-((-(Complex.I * (t : ℂ))) • (A + B))) := (Commute.refl _).neg_right
      have h := NormedSpace.exp_add_of_commute hcomm
      rw [add_neg_cancel, NormedSpace.exp_zero] at h
      exact h.symm
    have hEq : NormedSpace.exp (t • X₁) *
          (NormedSpace.exp (t • Y₁) * NormedSpace.exp (t • (-Z₁))) - 1
          = (trotterStep A B t -
            NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
            NormedSpace.exp (t • (-Z₁)) := by
      rw [hFt, ← hexpZ, ← sub_mul]
    have hU : NormedSpace.exp (t • (-Z₁)) ∈
        unitary (Matrix (Fin n) (Fin n) ℂ) := by
      rw [hE3 t]
      apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      rw [skewAdjoint.mem_iff]
      simp only [star_smul, hABh.star_eq]
      have hscalar : star (-(Complex.I * ((-t : ℝ) : ℂ))) =
          -(-(Complex.I * ((-t : ℝ) : ℂ))) := by
        simp
      rw [hscalar, neg_smul]
    have hpres : ‖trotterStep A B t -
          NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))‖ ≤
          ‖(trotterStep A B t -
            NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
            NormedSpace.exp (t • (-Z₁))‖ := by
      by_cases hnt : Nontrivial (Matrix (Fin n) (Fin n) ℂ)
      · have hUs : star (NormedSpace.exp (t • (-Z₁))) ∈
            unitary (Matrix (Fin n) (Fin n) ℂ) := Unitary.star_mem hU
        have hnUs : ‖star (NormedSpace.exp (t • (-Z₁)))‖ = 1 :=
          CStarRing.norm_of_mem_unitary hUs
        have hback : (trotterStep A B t -
              NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
              NormedSpace.exp (t • (-Z₁)) *
              star (NormedSpace.exp (t • (-Z₁))) =
              (trotterStep A B t -
                NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) := by
          rw [mul_assoc, Unitary.mul_star_self_of_mem hU, mul_one]
        calc ‖trotterStep A B t -
              NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))‖
              = ‖(trotterStep A B t -
                NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
                NormedSpace.exp (t • (-Z₁)) *
                star (NormedSpace.exp (t • (-Z₁)))‖ := by rw [hback]
            _ ≤ ‖(trotterStep A B t -
                  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
                  NormedSpace.exp (t • (-Z₁))‖ *
                  ‖star (NormedSpace.exp (t • (-Z₁)))‖ := norm_mul_le _ _
            _ = ‖(trotterStep A B t -
                  NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
                  NormedSpace.exp (t • (-Z₁))‖ := by rw [hnUs, mul_one]
      · rw [not_nontrivial_iff_subsingleton] at hnt
        have h2 : (trotterStep A B t -
              NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) *
              NormedSpace.exp (t • (-Z₁)) =
              (trotterStep A B t -
                NormedSpace.exp ((-(Complex.I * (t : ℂ))) • (A + B))) :=
          hnt.elim _ _
        rw [h2]
    rw [hEq, hYX] at hleF
    calc ‖trotterStep A B t -
          NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B))‖
        ≤ ‖(trotterStep A B t -
            NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B))) *
            NormedSpace.exp (t • (-Z₁))‖ := hpres
      _ ≤ ‖B * A - A * B‖ * t ^ 2 / 2 := hleF
      _ = t ^ 2 / 2 * ‖B * A - A * B‖ := by ring

/-- One Lie–Trotter step has L2 operator norm at most one. -/
private theorem norm_trotterStep_le_one {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (s : ℝ) :
    ‖trotterStep A B s‖ ≤ 1 := by
  have hB' := norm_exp_unitary_le_one B hB s
  have hA' := norm_exp_unitary_le_one A hA s
  unfold trotterStep
  have g1 : ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • B)‖ *
      ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • A)‖ ≤
      1 * ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • A)‖ :=
    mul_le_mul_of_nonneg_right hB' (by positivity)
  have g2 : (1 : ℝ) * ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • A)‖ ≤
      1 * 1 :=
    mul_le_mul_of_nonneg_left hA' zero_le_one
  calc ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • B) *
        NormedSpace.exp (-(Complex.I * (s : ℂ)) • A)‖ ≤
      ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • B)‖ *
        ‖NormedSpace.exp (-(Complex.I * (s : ℂ)) • A)‖ := by
        apply norm_mul_le
    _ ≤ 1 * 1 := g1.trans g2
    _ = 1 := by simp

/-- The `r`-step Lie–Trotter error bound: splitting the evolution into
`r` steps of length `t / r` gives error at most `(t²/(2r)) ‖[B, A]‖`. -/
theorem norm_trotterStep_pow_sub_exp_le {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {t : ℝ} (ht : 0 ≤ t)
    {r : ℕ} (hr : 0 < r) :
    ‖trotterStep A B (t / r) ^ r -
        NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B))‖ ≤
      t ^ 2 / (2 * r) * ‖B * A - A * B‖ := by
  letI := NormedAlgebra.restrictScalars ℚ ℂ (Matrix (Fin n) (Fin n) ℂ)
  have ht_div : 0 ≤ t / (r : ℝ) := div_nonneg ht (by positivity)
  have h_one := norm_trotterStep_sub_exp_le hA hB ht_div
  have hU : ‖trotterStep A B (t / (r : ℝ))‖ ≤ 1 :=
    norm_trotterStep_le_one hA hB (t / (r : ℝ))
  have hABh : (A + B).IsHermitian := hA.add hB
  have hV := norm_exp_unitary_le_one (A + B) hABh (t / (r : ℝ))
  push_cast at h_one hV
  have h_tel := norm_pow_sub_pow_le_aux (trotterStep A B (t / (r : ℝ)))
    (NormedSpace.exp (-(Complex.I * (((t / (r : ℝ)) : ℂ))) • (A + B)))
    hU hV r
  have heq := exp_pow_small_step (A + B) t r hr
  rw [heq] at h_tel
  have hr_pos : 0 < (r : ℝ) := by positivity
  have hrR : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  calc ‖trotterStep A B (t / (r : ℝ)) ^ r -
        NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B))‖ ≤
      (r : ℝ) * ‖trotterStep A B (t / (r : ℝ)) -
        NormedSpace.exp (-(Complex.I * (((t / (r : ℝ)) : ℂ))) • (A + B))‖ :=
      h_tel
    _ ≤ (r : ℝ) * ((t / (r : ℝ)) ^ 2 / 2 * ‖B * A - A * B‖) :=
      mul_le_mul_of_nonneg_left h_one (by positivity)
    _ = t ^ 2 / (2 * (r : ℝ)) * ‖B * A - A * B‖ := by
      field_simp

/-- Step count form: `r ≥ t² ‖[B, A]‖ / (2ε)` steps give error at most
`ε`. -/
theorem norm_trotterStep_pow_sub_exp_le_of_steps {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {t ε : ℝ} (ht : 0 ≤ t)
    (hε : 0 < ε) {r : ℕ} (hr0 : 0 < r)
    (hr : t ^ 2 * ‖B * A - A * B‖ / (2 * ε) ≤ r) :
    ‖trotterStep A B (t / r) ^ r -
        NormedSpace.exp (-(Complex.I * (t : ℂ)) • (A + B))‖ ≤ ε := by
  have hstep := norm_trotterStep_pow_sub_exp_le hA hB ht hr0
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have h2ε : (0 : ℝ) < 2 * ε := by positivity
  have h2r : (0 : ℝ) < 2 * (r : ℝ) := by positivity
  have hmul : t ^ 2 * ‖B * A - A * B‖ ≤ (r : ℝ) * (2 * ε) :=
    (div_le_iff₀ h2ε).mp hr
  have hfin : t ^ 2 / (2 * (r : ℝ)) * ‖B * A - A * B‖ ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ h2r]
    calc t ^ 2 * ‖B * A - A * B‖ ≤ (r : ℝ) * (2 * ε) := hmul
      _ = ε * (2 * (r : ℝ)) := by ring
  exact hstep.trans hfin

end MathlibExt.Analysis.Normed.Algebra.LieTrotterError
