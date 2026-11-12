/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-! # Le Cam's bound in KL form

For two distributions on a finite type, any test's error
probabilities sum to at least `1 - √(KL / 2)`: Le Cam's two-point
bound composed with Pinsker's inequality. This is the KL
corollary of roadmap package ML-44 of the Atlas TCS canon
roadmap, built on `MathlibExt/Probability/LearningTheory/LeCam.lean`.

Source: Tsybakov, Introduction to Nonparametric Estimation
(2009), Section 2.2.
-/

open Finset

/-- Kullback-Leibler divergence between two PMFs on a finite type
(in nats, with `0 log 0 = 0` through the real conventions). -/
noncomputable def klSum {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)

private theorem pmf_toReal_sum_one {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have hsum : ∑ a, p a = (1 : ENNReal) := by
    have h := PMF.tsum_coe p
    rwa [tsum_fintype] at h
  have hfin : ∀ a ∈ Finset.univ, p a ≠ ⊤ := fun a _ => PMF.apply_ne_top p a
  calc ∑ a, (p a).toReal = (∑ a, p a).toReal := (ENNReal.toReal_sum hfin).symm
    _ = (1 : ENNReal).toReal := by rw [hsum]
    _ = 1 := ENNReal.toReal_one

private theorem pmf_toReal_support {α : Type*} [Fintype α] (p q : PMF α)
    (hsupp : ∀ a, (q a) = 0 → (p a) = 0) (a : α)
    (h : (q a).toReal = 0) : (p a).toReal = 0 := by
  rw [ENNReal.toReal_eq_zero_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl (hsupp a h)
  · exact absurd h (PMF.apply_ne_top q a)

private theorem log_sum_ineq {ι : Type*} (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ a ∈ s, 0 ≤ u a) (hv : ∀ a ∈ s, 0 ≤ v a)
    (hsupp : ∀ a ∈ s, v a = 0 → u a = 0) :
    (∑ a ∈ s, u a) * Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) ≤
      ∑ a ∈ s, u a * Real.log (u a / v a) := by
  have hU0_of : ∑ a ∈ s, v a = 0 → ∑ a ∈ s, u a = 0 := by
    intro hV0
    apply Finset.sum_eq_zero
    intro a ha
    apply hsupp a ha
    exact (Finset.sum_eq_zero_iff_of_nonneg hv).mp hV0 a ha
  by_cases hU0 : ∑ a ∈ s, u a = 0
  · have hUa : ∀ a ∈ s, u a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hu).mp hU0
    have hRHS : ∑ a ∈ s, u a * Real.log (u a / v a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [hUa a ha, zero_mul]
    simp [hU0, hRHS]
  · by_cases hV0 : ∑ a ∈ s, v a = 0
    · exact absurd (hU0_of hV0) hU0
    · have hUpos : 0 < ∑ a ∈ s, u a :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun a ha => hu a ha))
          (fun h => hU0 h.symm)
      have hVpos : 0 < ∑ a ∈ s, v a :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun a ha => hv a ha))
          (fun h => hV0 h.symm)
      have hpoint : ∀ a ∈ s, u a * Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) +
          (u a - ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) * v a) ≤
          u a * Real.log (u a / v a) := by
        intro a ha
        by_cases hu0 : u a = 0
        · have hWv : (0:ℝ) ≤ ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) * v a :=
            mul_nonneg (le_of_lt (div_pos hUpos hVpos)) (hv a ha)
          simp only [hu0, zero_mul, zero_add]
          linarith [hWv]
        · have hu' : 0 < u a := lt_of_le_of_ne (hu a ha) (fun h => hu0 h.symm)
          have hv' : 0 < v a := by
            apply lt_of_le_of_ne (hv a ha)
            intro h
            exact hu0 (hsupp a ha h.symm)
          set t : ℝ := (v a * (∑ a ∈ s, u a)) / (u a * (∑ a ∈ s, v a)) with ht
          have htpos : 0 < t := by
            rw [ht]
            exact div_pos (mul_pos hv' hUpos) (mul_pos hu' hVpos)
          have hlog := Real.log_le_sub_one_of_pos htpos
          have e1 : Real.log t =
              Real.log (v a * (∑ a ∈ s, u a)) - Real.log (u a * (∑ a ∈ s, v a)) := by
            rw [ht]
            exact Real.log_div (mul_ne_zero hv'.ne' hUpos.ne')
              (mul_ne_zero hu'.ne' hVpos.ne')
          have e2 : Real.log (v a * (∑ a ∈ s, u a)) =
              Real.log (v a) + Real.log (∑ a ∈ s, u a) :=
            Real.log_mul hv'.ne' hUpos.ne'
          have e3 : Real.log (u a * (∑ a ∈ s, v a)) =
              Real.log (u a) + Real.log (∑ a ∈ s, v a) :=
            Real.log_mul hu'.ne' hVpos.ne'
          have e4 : Real.log (u a / v a) = Real.log (u a) - Real.log (v a) :=
            Real.log_div hu'.ne' hv'.ne'
          have e5 : Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) =
              Real.log (∑ a ∈ s, u a) - Real.log (∑ a ∈ s, v a) :=
            Real.log_div hUpos.ne' hVpos.ne'
          have ekey : Real.log (u a / v a) =
              Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) - Real.log t := by
            linarith [e1, e2, e3, e4, e5]
          have hut : u a * t = ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) * v a := by
            rw [ht]
            have h1 : u a * (∑ a ∈ s, v a) ≠ 0 :=
              mul_ne_zero hu'.ne' hVpos.ne'
            have h2 : (∑ a ∈ s, v a) ≠ 0 := hVpos.ne'
            have h3 : u a ≠ 0 := hu'.ne'
            field_simp
          have hmul : u a * Real.log t ≤ u a * (t - 1) :=
            mul_le_mul_of_nonneg_left hlog (le_of_lt hu')
          have hmul2 : u a * Real.log t ≤
              ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) * v a - u a := by
            calc u a * Real.log t ≤ u a * (t - 1) := hmul
              _ = u a * t - u a := by ring
              _ = ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) * v a - u a := by rw [hut]
          rw [ekey]
          have hexpand : u a * (Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) -
              Real.log t) = u a * Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) -
              u a * Real.log t := by ring
          rw [hexpand]
          linarith [hmul2]
      have hsum := Finset.sum_le_sum hpoint
      rw [Finset.sum_add_distrib] at hsum
      have hUC : ∑ a ∈ s, u a * Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) =
          (∑ a ∈ s, u a) * Real.log ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) :=
        (Finset.sum_mul s u _).symm
      have hWV : ∑ a ∈ s, (u a - ((∑ a ∈ s, u a) / (∑ a ∈ s, v a)) * v a) = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
          div_mul_cancel₀ (∑ a ∈ s, u a) hVpos.ne', sub_self]
      rw [hUC, hWV, add_zero] at hsum
      exact hsum

private theorem binary_pinsker_r0 (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    2 * (0 - s) ^ 2 ≤
      0 * Real.log (0 / s) + (1 - 0) * Real.log ((1 - 0) / (1 - s)) := by
  have hRHS : 0 * Real.log (0 / s) + (1 - 0) * Real.log ((1 - 0) / (1 - s)) =
      Real.log (1 / (1 - s)) := by simp
  have hLHS : 2 * (0 - s) ^ 2 = 2 * s ^ 2 := by ring
  rw [hLHS, hRHS]
  have hHD : ∀ q : ℝ, q < 1 →
      HasDerivAt (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2)
        (1 / (1 - q) - 4 * q) q := by
    intro q hq
    have hne : (1:ℝ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
    have hne2 : (1:ℝ) / (1 - q) ≠ 0 := div_ne_zero one_ne_zero hne
    have hsub : HasDerivAt (fun q : ℝ => 1 - q) (0 - 1) q :=
      (hasDerivAt_const q 1).sub (hasDerivAt_id q)
    have hdiv : HasDerivAt (fun q : ℝ => 1 / (1 - q))
        ((0 * (1 - q) - 1 * (0 - 1)) / (1 - q) ^ 2) q :=
      (hasDerivAt_const q (1:ℝ)).div hsub hne
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 / (1 - y)))
        (((0 * (1 - q) - 1 * (0 - 1)) / (1 - q) ^ 2) / (1 / (1 - q))) q :=
      hdiv.log hne2
    have hsq : HasDerivAt (fun q : ℝ => q ^ 2) (2 * q ^ (2 - 1) * 1) q :=
      (hasDerivAt_id q).pow 2
    have h2sq : HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * q ^ (2 - 1) * 1)) q :=
      HasDerivAt.const_mul 2 hsq
    have hG : HasDerivAt (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2)
        ((((0 * (1 - q) - 1 * (0 - 1)) / (1 - q) ^ 2) / (1 / (1 - q))) -
          2 * (2 * q ^ (2 - 1) * 1)) q :=
      hlog.sub h2sq
    have hval : ((((0 * (1 - q) - 1 * (0 - 1)) / (1 - q) ^ 2) / (1 / (1 - q))) -
        2 * (2 * q ^ (2 - 1) * 1)) = 1 / (1 - q) - 4 * q := by
      field_simp
      ring
    rwa [hval] at hG
  have hdiff : DifferentiableOn ℝ
      (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2) (Set.Icc 0 s) :=
    fun x hx => (hHD x (lt_of_le_of_lt hx.2 hs1)).differentiableAt.differentiableWithinAt
  have hcont := hdiff.continuousOn
  have hdiff_int : DifferentiableOn ℝ
      (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2)
      (interior (Set.Icc 0 s)) := by
    rw [interior_Icc]
    intro x hx
    exact (hHD x (lt_trans hx.2 hs1)).differentiableAt.differentiableWithinAt
  have hsign : ∀ x ∈ interior (Set.Icc (0:ℝ) s),
      0 ≤ deriv (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x < 1 := lt_trans hx.2 hs1
    rw [(hHD x hx1).deriv]
    have hpos : (0:ℝ) < 1 - x := sub_pos.mpr hx1
    have hne : (1:ℝ) - x ≠ 0 := ne_of_gt hpos
    have heq : 1 / (1 - x) - 4 * x = (1 - 2 * x) ^ 2 / (1 - x) := by
      field_simp
      ring
    rw [heq]
    exact div_nonneg (sq_nonneg _) (le_of_lt hpos)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 s) hcont hdiff_int hsign
  have hmem0 : (0:ℝ) ∈ Set.Icc 0 s := ⟨le_rfl, le_of_lt hs0⟩
  have hmems : s ∈ Set.Icc 0 s := ⟨le_of_lt hs0, le_rfl⟩
  have hle := hmono hmem0 hmems (le_of_lt hs0)
  have hG0 : (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2) 0 = 0 := by simp
  have hGs : (fun q : ℝ => Real.log (1 / (1 - q)) - 2 * q ^ 2) s =
      Real.log (1 / (1 - s)) - 2 * s ^ 2 := rfl
  rw [hG0, hGs] at hle
  linarith [hle]

private theorem binary_pinsker_r1 (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    2 * (1 - s) ^ 2 ≤
      1 * Real.log (1 / s) + (1 - 1) * Real.log ((1 - 1) / (1 - s)) := by
  have hRHS : 1 * Real.log (1 / s) + (1 - 1) * Real.log ((1 - 1) / (1 - s)) =
      Real.log (1 / s) := by simp
  rw [hRHS]
  have hHD : ∀ q : ℝ, 0 < q →
      HasDerivAt (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2)
        (4 * (1 - q) - 1 / q) q := by
    intro q hq
    have hne : q ≠ 0 := hq.ne'
    have hne2 : (1:ℝ) / q ≠ 0 := div_ne_zero one_ne_zero hne
    have hdiv : HasDerivAt (fun q : ℝ => 1 / q) ((0 * q - 1 * 1) / q ^ 2) q :=
      (hasDerivAt_const q (1:ℝ)).div (hasDerivAt_id q) hne
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 / y))
        (((0 * q - 1 * 1) / q ^ 2) / (1 / q)) q :=
      hdiv.log hne2
    have hsub : HasDerivAt (fun q : ℝ => 1 - q) (0 - 1) q :=
      (hasDerivAt_const q 1).sub (hasDerivAt_id q)
    have hpow : HasDerivAt (fun q : ℝ => (1 - q) ^ 2)
        (2 * (1 - q) ^ (2 - 1) * (0 - 1)) q :=
      hsub.pow 2
    have h2 : HasDerivAt (fun y : ℝ => 2 * (1 - y) ^ 2)
        (2 * (2 * (1 - q) ^ (2 - 1) * (0 - 1))) q :=
      HasDerivAt.const_mul 2 hpow
    have hH : HasDerivAt (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2)
        ((((0 * q - 1 * 1) / q ^ 2) / (1 / q)) -
          2 * (2 * (1 - q) ^ (2 - 1) * (0 - 1))) q :=
      hlog.sub h2
    have hval : ((((0 * q - 1 * 1) / q ^ 2) / (1 / q)) -
        2 * (2 * (1 - q) ^ (2 - 1) * (0 - 1))) = 4 * (1 - q) - 1 / q := by
      field_simp
      ring
    rwa [hval] at hH
  have hdiff : DifferentiableOn ℝ
      (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2) (Set.Icc s 1) :=
    fun x hx => (hHD x (lt_of_lt_of_le hs0 hx.1)).differentiableAt.differentiableWithinAt
  have hcont := hdiff.continuousOn
  have hdiff_int : DifferentiableOn ℝ
      (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2)
      (interior (Set.Icc s 1)) := by
    rw [interior_Icc]
    intro x hx
    exact (hHD x (lt_trans hs0 hx.1)).differentiableAt.differentiableWithinAt
  have hsign : ∀ x ∈ interior (Set.Icc s (1:ℝ)),
      deriv (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2) x ≤ 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := lt_trans hs0 hx.1
    rw [(hHD x hx0).deriv]
    have hne : x ≠ 0 := hx0.ne'
    have heq : 4 * (1 - x) - 1 / x = -(((1 - 2 * x) ^ 2) / x) := by
      field_simp
      ring
    rw [heq]
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (le_of_lt hx0))
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc s 1) hcont hdiff_int hsign
  have hmems : s ∈ Set.Icc s (1:ℝ) := ⟨le_rfl, le_of_lt hs1⟩
  have hmem1 : (1:ℝ) ∈ Set.Icc s 1 := ⟨le_of_lt hs1, le_rfl⟩
  have hle := hanti hmems hmem1 (le_of_lt hs1)
  have hH1 : (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2) 1 = 0 := by simp
  have hHs : (fun q : ℝ => Real.log (1 / q) - 2 * (1 - q) ^ 2) s =
      Real.log (1 / s) - 2 * (1 - s) ^ 2 := rfl
  rw [hH1, hHs] at hle
  linarith [hle]

private theorem binary_pinsker_main (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    2 * (r - s) ^ 2 ≤
      r * Real.log (r / s) + (1 - r) * Real.log ((1 - r) / (1 - s)) := by
  have hr0' : r ≠ 0 := hr0.ne'
  have hr1' : (1:ℝ) - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  have hHD : ∀ q : ℝ, 0 < q → q < 1 →
      HasDerivAt (fun q : ℝ => r * Real.log (r / q) +
        (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2)
        (-r / q + (1 - r) / (1 - q) + 4 * (r - q)) q := by
    intro q hq0 hq1
    have hne_q : q ≠ 0 := hq0.ne'
    have hne_1q : (1:ℝ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
    have hne_rq : r / q ≠ 0 := div_ne_zero hr0' hne_q
    have hne_1r1q : (1 - r) / (1 - q) ≠ 0 := div_ne_zero hr1' hne_1q
    have hdiv1 : HasDerivAt (fun q : ℝ => r / q) ((0 * q - r * 1) / q ^ 2) q :=
      (hasDerivAt_const q r).div (hasDerivAt_id q) hne_q
    have hlog1 : HasDerivAt (fun y : ℝ => Real.log (r / y))
        (((0 * q - r * 1) / q ^ 2) / (r / q)) q :=
      hdiv1.log hne_rq
    have hm1 : HasDerivAt (fun y : ℝ => r * Real.log (r / y))
        (r * (((0 * q - r * 1) / q ^ 2) / (r / q))) q :=
      HasDerivAt.const_mul r hlog1
    have hsub1 : HasDerivAt (fun q : ℝ => 1 - q) (0 - 1) q :=
      (hasDerivAt_const q 1).sub (hasDerivAt_id q)
    have hdiv2 : HasDerivAt (fun q : ℝ => (1 - r) / (1 - q))
        ((0 * (1 - q) - (1 - r) * (0 - 1)) / (1 - q) ^ 2) q :=
      (hasDerivAt_const q (1 - r)).div hsub1 hne_1q
    have hlog2 : HasDerivAt (fun y : ℝ => Real.log ((1 - r) / (1 - y)))
        (((0 * (1 - q) - (1 - r) * (0 - 1)) / (1 - q) ^ 2) /
          ((1 - r) / (1 - q))) q :=
      hdiv2.log hne_1r1q
    have hm2 : HasDerivAt (fun y : ℝ => (1 - r) * Real.log ((1 - r) / (1 - y)))
        ((1 - r) * (((0 * (1 - q) - (1 - r) * (0 - 1)) / (1 - q) ^ 2) /
          ((1 - r) / (1 - q)))) q :=
      HasDerivAt.const_mul (1 - r) hlog2
    have hadd : HasDerivAt (fun y : ℝ => r * Real.log (r / y) +
        (1 - r) * Real.log ((1 - r) / (1 - y)))
        (r * (((0 * q - r * 1) / q ^ 2) / (r / q)) +
          (1 - r) * (((0 * (1 - q) - (1 - r) * (0 - 1)) / (1 - q) ^ 2) /
            ((1 - r) / (1 - q)))) q :=
      hm1.add hm2
    have hsub2 : HasDerivAt (fun q : ℝ => r - q) (0 - 1) q :=
      (hasDerivAt_const q r).sub (hasDerivAt_id q)
    have hpow : HasDerivAt (fun q : ℝ => (r - q) ^ 2)
        (2 * (r - q) ^ (2 - 1) * (0 - 1)) q :=
      hsub2.pow 2
    have hm3 : HasDerivAt (fun y : ℝ => 2 * (r - y) ^ 2)
        (2 * (2 * (r - q) ^ (2 - 1) * (0 - 1))) q :=
      HasDerivAt.const_mul 2 hpow
    have hF : HasDerivAt (fun q : ℝ => r * Real.log (r / q) +
        (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2)
        ((r * (((0 * q - r * 1) / q ^ 2) / (r / q)) +
          (1 - r) * (((0 * (1 - q) - (1 - r) * (0 - 1)) / (1 - q) ^ 2) /
            ((1 - r) / (1 - q)))) - 2 * (2 * (r - q) ^ (2 - 1) * (0 - 1))) q :=
      hadd.sub hm3
    have hval : ((r * (((0 * q - r * 1) / q ^ 2) / (r / q)) +
        (1 - r) * (((0 * (1 - q) - (1 - r) * (0 - 1)) / (1 - q) ^ 2) /
          ((1 - r) / (1 - q)))) - 2 * (2 * (r - q) ^ (2 - 1) * (0 - 1))) =
        -r / q + (1 - r) / (1 - q) + 4 * (r - q) := by
      field_simp
      ring
    rwa [hval] at hF
  have hfactor : ∀ q : ℝ, 0 < q → q < 1 →
      -r / q + (1 - r) / (1 - q) + 4 * (r - q) =
        (q - r) * (1 / (q * (1 - q)) - 4) := by
    intro q hq0 hq1
    have hne_q : q ≠ 0 := hq0.ne'
    have hne_1q : (1:ℝ) - q ≠ 0 := ne_of_gt (sub_pos.mpr hq1)
    have hne_q1q : q * (1 - q) ≠ 0 := mul_ne_zero hne_q hne_1q
    field_simp
    ring
  have hbig : ∀ q : ℝ, 0 < q → q < 1 → (4:ℝ) ≤ 1 / (q * (1 - q)) := by
    intro q hq0 hq1
    have hq1q : (0:ℝ) < q * (1 - q) := mul_pos hq0 (sub_pos.mpr hq1)
    have hsq : (0:ℝ) ≤ (1 - 2 * q) ^ 2 := sq_nonneg _
    rw [le_div_iff₀ hq1q]
    linarith [hsq]
  have hFr : (fun q : ℝ => r * Real.log (r / q) +
      (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2) r = 0 := by
    have e1 : r / r = (1:ℝ) := div_self hr0'
    have e2 : (1 - r) / (1 - r) = (1:ℝ) := div_self hr1'
    simp [e1, e2, Real.log_one]
  have hFs : (fun q : ℝ => r * Real.log (r / q) +
      (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2) s =
      r * Real.log (r / s) + (1 - r) * Real.log ((1 - r) / (1 - s)) -
        2 * (r - s) ^ 2 := rfl
  rcases lt_trichotomy s r with hsr | hsr | hsr
  · have hdiff : DifferentiableOn ℝ (fun q : ℝ => r * Real.log (r / q) +
        (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2)
        (Set.Icc s r) :=
      fun x hx => (hHD x (lt_of_lt_of_le hs0 hx.1)
        (lt_of_le_of_lt hx.2 hr1)).differentiableAt.differentiableWithinAt
    have hcont := hdiff.continuousOn
    have hdiff_int : DifferentiableOn ℝ (fun q : ℝ => r * Real.log (r / q) +
        (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2)
        (interior (Set.Icc s r)) := by
      rw [interior_Icc]
      intro x hx
      exact (hHD x (lt_trans hs0 hx.1)
        (lt_trans hx.2 hr1)).differentiableAt.differentiableWithinAt
    have hsign : ∀ x ∈ interior (Set.Icc s r), deriv (fun q : ℝ =>
        r * Real.log (r / q) + (1 - r) * Real.log ((1 - r) / (1 - q)) -
        2 * (r - q) ^ 2) x ≤ 0 := by
      intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_trans hs0 hx.1
      have hx1 : x < 1 := lt_trans hx.2 hr1
      rw [(hHD x hx0 hx1).deriv, hfactor x hx0 hx1]
      have h4 := hbig x hx0 hx1
      have hqr : x - r ≤ 0 := sub_nonpos.mpr (le_of_lt hx.2)
      have hnn : (0:ℝ) ≤ 1 / (x * (1 - x)) - 4 := sub_nonneg.mpr h4
      exact mul_nonpos_of_nonpos_of_nonneg hqr hnn
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc s r) hcont
      hdiff_int hsign
    have hmems : s ∈ Set.Icc s r := ⟨le_rfl, le_of_lt hsr⟩
    have hmemr : r ∈ Set.Icc s r := ⟨le_of_lt hsr, le_rfl⟩
    have hle := hanti hmems hmemr (le_of_lt hsr)
    rw [hFr, hFs] at hle
    linarith [hle]
  · rw [hsr]
    have e1 : r / r = (1:ℝ) := div_self hr0'
    have e2 : (1 - r) / (1 - r) = (1:ℝ) := div_self hr1'
    simp [e1, e2, Real.log_one]
  · have hdiff : DifferentiableOn ℝ (fun q : ℝ => r * Real.log (r / q) +
        (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2)
        (Set.Icc r s) :=
      fun x hx => (hHD x (lt_of_lt_of_le hr0 hx.1)
        (lt_of_le_of_lt hx.2 hs1)).differentiableAt.differentiableWithinAt
    have hcont := hdiff.continuousOn
    have hdiff_int : DifferentiableOn ℝ (fun q : ℝ => r * Real.log (r / q) +
        (1 - r) * Real.log ((1 - r) / (1 - q)) - 2 * (r - q) ^ 2)
        (interior (Set.Icc r s)) := by
      rw [interior_Icc]
      intro x hx
      exact (hHD x (lt_trans hr0 hx.1)
        (lt_trans hx.2 hs1)).differentiableAt.differentiableWithinAt
    have hsign : ∀ x ∈ interior (Set.Icc r s), 0 ≤ deriv (fun q : ℝ =>
        r * Real.log (r / q) + (1 - r) * Real.log ((1 - r) / (1 - q)) -
        2 * (r - q) ^ 2) x := by
      intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := lt_trans hr0 hx.1
      have hx1 : x < 1 := lt_trans hx.2 hs1
      rw [(hHD x hx0 hx1).deriv, hfactor x hx0 hx1]
      have h4 := hbig x hx0 hx1
      have hqr : (0:ℝ) ≤ x - r := sub_nonneg.mpr (le_of_lt hx.1)
      have hnn : (0:ℝ) ≤ 1 / (x * (1 - x)) - 4 := sub_nonneg.mpr h4
      exact mul_nonneg hqr hnn
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc r s) hcont
      hdiff_int hsign
    have hmemr : r ∈ Set.Icc r s := ⟨le_rfl, le_of_lt hsr⟩
    have hmems : s ∈ Set.Icc r s := ⟨le_of_lt hsr, le_rfl⟩
    have hle := hmono hmemr hmems (le_of_lt hsr)
    rw [hFr, hFs] at hle
    linarith [hle]

private theorem binary_pinsker (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (h0 : s = 0 → r = 0) (h1 : s = 1 → r = 1) :
    2 * (r - s) ^ 2 ≤
      r * Real.log (r / s) + (1 - r) * Real.log ((1 - r) / (1 - s)) := by
  by_cases hs0' : s = 0
  · subst hs0'
    have hr : r = 0 := h0 rfl
    subst hr
    simp [Real.log_one]
  · by_cases hs1' : s = 1
    · subst hs1'
      have hr : r = 1 := h1 rfl
      subst hr
      simp [Real.log_one]
    · have hs0pos : 0 < s := lt_of_le_of_ne hs0 (fun h => hs0' h.symm)
      have hs1pos : s < 1 := lt_of_le_of_ne hs1 hs1'
      by_cases hr0' : r = 0
      · subst hr0'
        exact binary_pinsker_r0 s hs0pos hs1pos
      · by_cases hr1' : r = 1
        · subst hr1'
          exact binary_pinsker_r1 s hs0pos hs1pos
        · exact binary_pinsker_main r
            (lt_of_le_of_ne hr0 (fun h => hr0' h.symm))
            (lt_of_le_of_ne hr1 hr1') s hs0pos hs1pos

/-- Le Cam's bound in KL form: for two distributions on a finite
type, any test's two error probabilities sum to at least
`1 - √(KL / 2)` (Pinsker applied to Le Cam's two-point bound).
Assumes `q` dominates `p` pointwise so the KL sum is the true
divergence. -/
theorem lecam_kl {α : Type*} [Fintype α] (p q : PMF α) (δ : α → Bool)
    (hsupp : ∀ a, (q a) = 0 → (p a) = 0) :
    1 - Real.sqrt (klSum p q / 2) ≤
      (∑ a ∈ Finset.univ.filter (fun a => δ a = true), (p a).toReal) +
        (∑ a ∈ Finset.univ.filter (fun a => δ a = false), (q a).toReal) := by
  set A : Finset α := Finset.univ.filter (fun a => δ a = true) with hA
  set B : Finset α := Finset.univ.filter (fun a => δ a = false) with hB
  have hBA : Finset.univ.filter (fun a => ¬ δ a = true) = B := by
    rw [hB]
    apply Finset.filter_congr
    intro a _
    cases δ a <;> simp
  have hsuppR : ∀ a : α, (q a).toReal = 0 → (p a).toReal = 0 :=
    fun a h => pmf_toReal_support p q hsupp a h
  have hsplit_kl : (∑ a ∈ A, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) +
      (∑ a ∈ B, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)) = klSum p q := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => δ a = true)
      (fun a => (p a).toReal * Real.log ((p a).toReal / (q a).toReal))
    rw [hBA, ← hA] at h
    have hkl : klSum p q = ∑ a ∈ Finset.univ,
        (p a).toReal * Real.log ((p a).toReal / (q a).toReal) := rfl
    rw [hkl]
    exact h
  have hp_split : (∑ a ∈ A, (p a).toReal) + (∑ a ∈ B, (p a).toReal) = 1 := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => δ a = true)
      (fun a => (p a).toReal)
    rw [hBA, ← hA, pmf_toReal_sum_one p] at h
    exact h
  have hq_split : (∑ a ∈ A, (q a).toReal) + (∑ a ∈ B, (q a).toReal) = 1 := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => δ a = true)
      (fun a => (q a).toReal)
    rw [hBA, ← hA, pmf_toReal_sum_one q] at h
    exact h
  have hrC_eq : (∑ a ∈ B, (p a).toReal) = 1 - (∑ a ∈ A, (p a).toReal) := by
    linarith [hp_split]
  have hsC_eq : (∑ a ∈ B, (q a).toReal) = 1 - (∑ a ∈ A, (q a).toReal) := by
    linarith [hq_split]
  have hr0 : (0:ℝ) ≤ ∑ a ∈ A, (p a).toReal :=
    Finset.sum_nonneg (fun a _ => ENNReal.toReal_nonneg)
  have hs0 : (0:ℝ) ≤ ∑ a ∈ A, (q a).toReal :=
    Finset.sum_nonneg (fun a _ => ENNReal.toReal_nonneg)
  have hr1 : (∑ a ∈ A, (p a).toReal) ≤ 1 := by
    have hsub : A ⊆ Finset.univ := by rw [hA]; exact Finset.filter_subset _ _
    have hle : (∑ a ∈ A, (p a).toReal) ≤ ∑ a ∈ Finset.univ, (p a).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => ENNReal.toReal_nonneg)
    rwa [pmf_toReal_sum_one p] at hle
  have hs1 : (∑ a ∈ A, (q a).toReal) ≤ 1 := by
    have hsub : A ⊆ Finset.univ := by rw [hA]; exact Finset.filter_subset _ _
    have hle : (∑ a ∈ A, (q a).toReal) ≤ ∑ a ∈ Finset.univ, (q a).toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => ENNReal.toReal_nonneg)
    rwa [pmf_toReal_sum_one q] at hle
  have hsupp0 : (∑ a ∈ A, (q a).toReal) = 0 → (∑ a ∈ A, (p a).toReal) = 0 := by
    intro hs
    apply Finset.sum_eq_zero
    intro a ha
    apply hsuppR a
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => ENNReal.toReal_nonneg)).mp hs a ha
  have hsupp1 : (∑ a ∈ A, (q a).toReal) = 1 → (∑ a ∈ A, (p a).toReal) = 1 := by
    intro hs
    have hsC : (∑ a ∈ B, (q a).toReal) = 0 := by linarith [hq_split, hs]
    have hrC : (∑ a ∈ B, (p a).toReal) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply hsuppR a
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => ENNReal.toReal_nonneg)).mp hsC a ha
    linarith [hp_split, hrC]
  have hlogA := log_sum_ineq A (fun a => (p a).toReal) (fun a => (q a).toReal)
    (fun a _ => ENNReal.toReal_nonneg) (fun a _ => ENNReal.toReal_nonneg)
    (fun a _ h => hsuppR a h)
  have hlogB := log_sum_ineq B (fun a => (p a).toReal) (fun a => (q a).toReal)
    (fun a _ => ENNReal.toReal_nonneg) (fun a _ => ENNReal.toReal_nonneg)
    (fun a _ h => hsuppR a h)
  rw [hrC_eq, hsC_eq] at hlogB
  have hdp : (∑ a ∈ A, (p a).toReal) *
      Real.log ((∑ a ∈ A, (p a).toReal) / (∑ a ∈ A, (q a).toReal)) +
      (1 - (∑ a ∈ A, (p a).toReal)) *
      Real.log ((1 - (∑ a ∈ A, (p a).toReal)) / (1 - (∑ a ∈ A, (q a).toReal))) ≤
      klSum p q := by
    have hadd := add_le_add hlogA hlogB
    rwa [hsplit_kl] at hadd
  have hpin := binary_pinsker (∑ a ∈ A, (p a).toReal) (∑ a ∈ A, (q a).toReal)
    hr0 hr1 hs0 hs1 hsupp0 hsupp1
  have h2 : 2 * ((∑ a ∈ A, (p a).toReal) - (∑ a ∈ A, (q a).toReal)) ^ 2 ≤
      klSum p q := le_trans hpin hdp
  have hsq : ((∑ a ∈ A, (p a).toReal) - (∑ a ∈ A, (q a).toReal)) ^ 2 ≤
      klSum p q / 2 := by linarith [h2]
  have habs : |(∑ a ∈ A, (p a).toReal) - (∑ a ∈ A, (q a).toReal)| ≤
      Real.sqrt (klSum p q / 2) := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs] at h
  have hneg : -((∑ a ∈ A, (p a).toReal) - (∑ a ∈ A, (q a).toReal)) ≤
      Real.sqrt (klSum p q / 2) :=
    le_trans (neg_le_abs _) habs
  rw [hsC_eq]
  linarith [hneg]
