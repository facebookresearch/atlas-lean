/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import MathlibExt.InformationTheory.LogSum

/-!
# Csiszar-Kullback-Pinsker inequality

For strictly positive probability vectors `p` and `q` on a finite type,
`(∑ |p a - q a|)² ≤ 2 * ∑ p a * log (p a / q a)`. The proof splits the type by the sign of
`p a - q a`, applies the log-sum inequality on each part, and reduces to the two-point case, which
is proved by calculus.
-/

@[expose] public section

open Finset BigOperators

namespace MathlibExt.InformationTheory.Pinsker

/-- The gap in the binary Pinsker inequality at `q`, for the reference point `v`. -/
private noncomputable def pinskerGap (v q : ℝ) : ℝ :=
  q * Real.log (q / v) + (1 - q) * Real.log ((1 - q) / (1 - v)) - 2 * (q - v) ^ 2

/-- The derivative of `pinskerGap v`. -/
private noncomputable def pinskerGapDeriv (v q : ℝ) : ℝ :=
  Real.log (q / v) - Real.log ((1 - q) / (1 - v)) - 4 * (q - v)

private lemma binary_pinsker {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    2 * (u - v)^2 ≤ u * Real.log (u / v) + (1 - u) * Real.log ((1-u)/(1-v)) := by
  by_cases huv : u = v
  · subst huv
    have hune : u ≠ 0 := ne_of_gt hu0
    have h1une : (1:ℝ) - u ≠ 0 := ne_of_gt (by linarith)
    simp [sub_self, div_self hune, div_self h1une, Real.log_one]
  · -- calculus
    have hv1' : (0:ℝ) < 1 - v := by linarith
    have h1v : (1:ℝ) - v ≠ 0 := ne_of_gt hv1'
    have hvne : v ≠ 0 := ne_of_gt hv0
    -- auxiliary derivative facts
    have hsub1 : ∀ p : ℝ, HasDerivAt (fun x : ℝ => (1:ℝ) - x) (-1) p := by
      intro p
      have h := ((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p))
      have hfun : ((fun _ : ℝ => (1:ℝ)) - id) = (fun x => (1:ℝ) - x) := by
        ext x; simp [Pi.sub_apply, id_eq]
      have hder : (0:ℝ) - (1:ℝ) = -1 := by ring
      rw [hfun, hder] at h
      exact h
    have hdiv1 : ∀ p : ℝ, HasDerivAt (fun x : ℝ => x / v) (1 / v) p := by
      intro p
      have h := ((hasDerivAt_id p).div_const v)
      have hfun : (fun x : ℝ => id x / v) = (fun x : ℝ => x / v) := by
        ext x; simp [id_eq]
      rwa [hfun] at h
    have hdiv2 : ∀ p : ℝ, HasDerivAt (fun x : ℝ => ((1:ℝ) - x) / (1 - v)) ((-1) / (1 - v)) p := by
      intro p
      exact ((hsub1 p).div_const (1 - v))
    have hlog1 : ∀ p : ℝ, 0 < p → HasDerivAt (fun x : ℝ => Real.log (x / v)) (p⁻¹) p := by
      intro p hp0
      have hne : p / v ≠ 0 := div_ne_zero (ne_of_gt hp0) hvne
      have h := ((hdiv1 p).log hne)
      have heq : (1 / v) / (p / v) = p⁻¹ := by field_simp
      rwa [heq] at h
    have hlog2 : ∀ p : ℝ, p < 1 →
        HasDerivAt (fun x : ℝ => Real.log (((1:ℝ) - x) / (1 - v))) (-((1 - p)⁻¹)) p := by
      intro p hp1
      have hp1' : (0:ℝ) < 1 - p := by linarith
      have hne : ((1:ℝ) - p) / (1 - v) ≠ 0 := div_ne_zero (ne_of_gt hp1') h1v
      have h := ((hdiv2 p).log hne)
      have heq : ((-1) / (1 - v)) / (((1:ℝ) - p) / (1 - v)) = -((1 - p)⁻¹) := by
        field_simp
      rwa [heq] at h
    have hbase : ∀ p : ℝ, HasDerivAt (fun x : ℝ => x - v) 1 p := by
      intro p
      have h := ((hasDerivAt_id p).sub (hasDerivAt_const p v))
      have hfun : (id - (fun _ : ℝ => v)) = (fun x : ℝ => x - v) := by
        ext x; simp [Pi.sub_apply, id_eq]
      have hder : (1:ℝ) - 0 = 1 := by ring
      rw [hfun, hder] at h
      exact h
    have hF : ∀ p : ℝ, 0 < p → p < 1 →
        HasDerivAt (pinskerGap v)
        (Real.log (p / v) - Real.log ((1 - p) / (1 - v)) - 4 * (p - v)) p := by
      intro p hp0 hp1
      have hp1' : (0:ℝ) < 1 - p := by linarith
      have e1' : HasDerivAt (fun x : ℝ => x * Real.log (x / v))
          (1 * Real.log (p / v) + p * p⁻¹) p := by
        have h := (hasDerivAt_id p).mul (hlog1 p hp0)
        have hfun : (id * (fun x : ℝ => Real.log (x / v))) =
            (fun x : ℝ => x * Real.log (x / v)) := by
          ext x; simp [Pi.mul_apply, id_eq]
        rwa [hfun] at h
      have e2 : HasDerivAt (fun x : ℝ => ((1:ℝ) - x) * Real.log (((1:ℝ) - x) / (1 - v)))
          ((-1) * Real.log (((1:ℝ) - p) / (1 - v)) + (1 - p) * (-((1 - p)⁻¹))) p := by
        have h := (hsub1 p).mul (hlog2 p hp1)
        have hfun : ((fun x : ℝ => (1:ℝ) - x) * (fun x : ℝ => Real.log (((1:ℝ) - x) / (1 - v))))
            = (fun x : ℝ => ((1:ℝ) - x) * Real.log (((1:ℝ) - x) / (1 - v))) := by
          ext x; simp [Pi.mul_apply]
        rwa [hfun] at h
      have hpow : HasDerivAt (fun x : ℝ => (x - v)^2) ((2:ℝ) * (p - v)) p := by
        have h := (hbase p).mul (hbase p)
        have hfun : ((fun x : ℝ => x - v) * (fun x : ℝ => x - v)) = (fun x : ℝ => (x - v)^2) := by
          ext x; simp [Pi.mul_apply, pow_two]
        have hder : (1:ℝ) * (p - v) + (p - v) * 1 = 2 * (p - v) := by ring
        rw [hfun, hder] at h
        exact h
      have e3 : HasDerivAt (fun x : ℝ => (2:ℝ) * (x - v)^2) (4 * (p - v)) p := by
        have hcm := hpow.const_mul (2:ℝ)
        have hfun : (fun y : ℝ => (2:ℝ) * ((fun x : ℝ => (x - v)^2) y)) =
            (fun x : ℝ => (2:ℝ) * (x - v)^2) := rfl
        have hder : (2:ℝ) * (2 * (p - v)) = 4 * (p - v) := by ring
        rw [hfun, hder] at hcm
        exact hcm
      have hcomb := (e1'.add e2).sub e3
      have hfun : ((fun x : ℝ => x * Real.log (x / v)) +
          (fun x : ℝ => ((1:ℝ) - x) * Real.log (((1:ℝ) - x) / (1 - v))) -
          (fun x : ℝ => (2:ℝ) * (x - v)^2)) = pinskerGap v := by
        ext x; simp [pinskerGap, Pi.add_apply, Pi.sub_apply]
      rw [hfun] at hcomb
      have hsimp : 1 * Real.log (p / v) + p * p⁻¹ +
            ((-1) * Real.log (((1:ℝ) - p) / (1 - v)) + (1 - p) * (-((1 - p)⁻¹))) - 4 * (p - v)
          = Real.log (p / v) - Real.log ((1 - p) / (1 - v)) - 4 * (p - v) := by
        field_simp
        ring
      rwa [hsimp] at hcomb
    have hFp : ∀ p : ℝ, 0 < p → p < 1 →
        HasDerivAt (pinskerGapDeriv v)
        (p⁻¹ + (1 - p)⁻¹ - 4) p := by
      intro p hp0 hp1
      have e4 : HasDerivAt (fun x : ℝ => 4 * (x - v)) 4 p := by
        have hcm := (hbase p).const_mul (4:ℝ)
        have hfun : (fun y : ℝ => (4:ℝ) * ((fun x : ℝ => x - v) y)) =
            (fun x : ℝ => 4 * (x - v)) := rfl
        have hder : (4:ℝ) * 1 = 4 := by ring
        rw [hfun, hder] at hcm
        exact hcm
      have hcomb := ((hlog1 p hp0).sub (hlog2 p hp1)).sub e4
      have hfun : ((fun x : ℝ => Real.log (x / v)) -
          (fun x : ℝ => Real.log (((1:ℝ) - x) / (1 - v))) - (fun x : ℝ => 4 * (x - v))) =
          pinskerGapDeriv v := by
        ext x; simp [pinskerGapDeriv, Pi.sub_apply]
      rw [hfun] at hcomb
      have hsimp : p⁻¹ - -((1 - p)⁻¹) - 4 = p⁻¹ + (1 - p)⁻¹ - 4 := by ring
      rwa [hsimp] at hcomb
    have hFpp_nonneg : ∀ p : ℝ, 0 < p → p < 1 → 0 ≤ p⁻¹ + (1 - p)⁻¹ - 4 := by
      intro p hp0 hp1
      have hp1' : (0:ℝ) < 1 - p := by linarith
      have hpp : (0:ℝ) < p * (1 - p) := mul_pos hp0 hp1'
      have heq : p⁻¹ + (1 - p)⁻¹ - 4 = ((2 * p - 1)^2) / (p * (1 - p)) := by
        field_simp
        ring
      rw [heq]
      exact div_nonneg (sq_nonneg _) (le_of_lt hpp)
    -- Monotonicity of Fp on Ioo 0 1
    have hFpDiff : DifferentiableOn ℝ (pinskerGapDeriv v) (Set.Ioo 0 1) := by
      intro x hx
      exact ((hFp x hx.1 hx.2).differentiableAt.differentiableWithinAt)
    have hFpCont : ContinuousOn (pinskerGapDeriv v) (Set.Ioo 0 1) :=
      hFpDiff.continuousOn
    have hMonoFp : MonotoneOn (pinskerGapDeriv v) (Set.Ioo 0 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1) hFpCont
      · -- differentiable on interior
        rw [IsOpen.interior_eq isOpen_Ioo]
        exact hFpDiff
      · intro x hx
        rw [IsOpen.interior_eq isOpen_Ioo] at hx
        have hder : deriv (pinskerGapDeriv v) x
            = x⁻¹ + (1 - x)⁻¹ - 4 := (hFp x hx.1 hx.2).deriv
        rw [hder]
        exact hFpp_nonneg x hx.1 hx.2
    have hFpv : pinskerGapDeriv v v = 0 := by
      simp [pinskerGapDeriv, div_self hvne, div_self h1v, Real.log_one]
    have hvIoo : v ∈ Set.Ioo (0:ℝ) 1 := ⟨hv0, hv1⟩
    have huIoo : u ∈ Set.Ioo (0:ℝ) 1 := ⟨hu0, hu1⟩
    have hsign_le : ∀ x : ℝ, x ∈ Set.Ioo (0:ℝ) 1 → x ≤ v →
        pinskerGapDeriv v x ≤ 0 := by
      intro x hx hxle
      have h := hMonoFp hx hvIoo hxle
      rwa [hFpv] at h
    have hsign_ge : ∀ x : ℝ, x ∈ Set.Ioo (0:ℝ) 1 → v ≤ x →
        0 ≤ pinskerGapDeriv v x := by
      intro x hx hxle
      have h := hMonoFp hvIoo hx hxle
      rwa [hFpv] at h
    have hFv : pinskerGap v v = 0 := by
      simp [pinskerGap, div_self hvne, div_self h1v, Real.log_one, sub_self]
    -- split on order
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · -- u < v: F antitone on Icc u v
      have hsub : Set.Icc u v ⊆ Set.Ioo (0:ℝ) 1 := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        constructor <;> linarith
      have hFdiff : DifferentiableOn ℝ (pinskerGap v) (Set.Icc u v) := by
        intro x hx
        have hxIoo := hsub hx
        exact ((hF x hxIoo.1 hxIoo.2).differentiableAt.differentiableWithinAt)
      have hFcont : ContinuousOn (pinskerGap v) (Set.Icc u v) :=
        hFdiff.continuousOn
      have hAnti : AntitoneOn (pinskerGap v) (Set.Icc u v) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc u v) hFcont
        · -- differentiable on interior
          rw [interior_Icc]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
          exact ((hF x hxIoo.1 hxIoo.2).differentiableAt.differentiableWithinAt)
        · intro x hx
          rw [interior_Icc] at hx
          obtain ⟨hx1, hx2⟩ := hx
          have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
          have hxle : x ≤ v := le_of_lt hx2
          have hder : deriv (pinskerGap v) x
              = pinskerGapDeriv v x :=
            (hF x hxIoo.1 hxIoo.2).deriv
          rw [hder]
          exact hsign_le x hxIoo hxle
      have hle : pinskerGap v v
          ≤ pinskerGap v u :=
        hAnti (Set.left_mem_Icc.mpr hlt.le) (Set.right_mem_Icc.mpr hlt.le) hlt.le
      rw [hFv] at hle
      -- hle : 0 ≤ F u, unfold to goal
      have hFu : pinskerGap v u
          = u * Real.log (u / v) + (1 - u) * Real.log ((1-u)/(1-v)) - 2 * (u - v)^2 := rfl
      rw [hFu] at hle
      linarith
    · -- v < u: F monotone on Icc v u
      have hsub : Set.Icc v u ⊆ Set.Ioo (0:ℝ) 1 := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        constructor <;> linarith
      have hFdiff : DifferentiableOn ℝ (pinskerGap v) (Set.Icc v u) := by
        intro x hx
        have hxIoo := hsub hx
        exact ((hF x hxIoo.1 hxIoo.2).differentiableAt.differentiableWithinAt)
      have hFcont : ContinuousOn (pinskerGap v) (Set.Icc v u) :=
        hFdiff.continuousOn
      have hMono : MonotoneOn (pinskerGap v) (Set.Icc v u) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc v u) hFcont
        · rw [interior_Icc]
          intro x hx
          obtain ⟨hx1, hx2⟩ := hx
          have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
          exact ((hF x hxIoo.1 hxIoo.2).differentiableAt.differentiableWithinAt)
        · intro x hx
          rw [interior_Icc] at hx
          obtain ⟨hx1, hx2⟩ := hx
          have hxIoo : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
          have hxge : v ≤ x := le_of_lt hx1
          have hder : deriv (pinskerGap v) x
              = pinskerGapDeriv v x :=
            (hF x hxIoo.1 hxIoo.2).deriv
          rw [hder]
          exact hsign_ge x hxIoo hxge
      have hle : pinskerGap v v
          ≤ pinskerGap v u :=
        hMono (Set.left_mem_Icc.mpr hgt.le) (Set.right_mem_Icc.mpr hgt.le) hgt.le
      rw [hFv] at hle
      have hFu : pinskerGap v u
          = u * Real.log (u / v) + (1 - u) * Real.log ((1-u)/(1-v)) - 2 * (u - v)^2 := rfl
      rw [hFu] at hle
      linarith

/--
**Csiszár–Kullback–Pinsker inequality for strictly positive distributions.** Let $\alpha$ be a
finite nonempty set and let $p, q : \alpha \to \mathbb{R}$ satisfy $p(a) > 0$ and $q(a) > 0$
for every $a \in \alpha$ and $\sum_a p(a) = \sum_a q(a) = 1$. Then, with the natural logarithm,
$$
\Bigl(\sum_{a \in \alpha} |p(a) - q(a)|\Bigr)^2
\le 2 \sum_{a \in \alpha} p(a) \log \frac{p(a)}{q(a)}.
$$

Equivalently, the total variation distance $\frac12 \sum_a |p(a) - q(a)|$ is at most
$\sqrt{D/2}$, where $D = \sum_a p(a) \log (p(a)/q(a))$ is the Kullback–Leibler divergence.

Source: M. S. Pinsker, Information and Information Stability of Random Variables and Processes
(1960; English translation 1964), with I. Csiszar, Information-type measures of difference of
probability distributions and indirect observations, Studia Sci. Math. Hungar. 2 (1967), 299-318.
Proves `Wanted` entry `csiszar_kullback_pinsker`, without its `[DecidableEq α]`, which the statement
does not use.
-/
theorem csiszar_kullback_pinsker
    {α : Type*} [Fintype α] [Nonempty α]
    (p q : α → ℝ)
    (hp_pos : ∀ a, 0 < p a)
    (hq_pos : ∀ a, 0 < q a)
    (hp_sum : ∑ a : α, p a = 1)
    (hq_sum : ∑ a : α, q a = 1) :
    (∑ a : α, |p a - q a|) ^ 2 ≤ 2 * ∑ a : α, p a * Real.log (p a / q a) := by
  classical
  set s : Finset α := Finset.univ.filter (fun a => q a ≤ p a) with hs_def
  set sc : Finset α := Finset.univ.filter (fun a => ¬ q a ≤ p a) with hsc_def
  have hs_nonempty : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hall : ∀ a : α, p a < q a := by
      intro a
      have hmem : a ∉ s := by rw [h]; exact Finset.notMem_empty a
      simpa [hs_def, Finset.mem_filter] using hmem
    obtain ⟨a0⟩ : Nonempty α := inferInstance
    have hlt : ∑ a : α, p a < ∑ a : α, q a :=
      Finset.sum_lt_sum (fun i _ => le_of_lt (hall i)) ⟨a0, Finset.mem_univ a0, hall a0⟩
    rw [hp_sum, hq_sum] at hlt
    exact lt_irrefl _ hlt
  by_cases hsc : sc.Nonempty
  · -- both parts nonempty: reduce to binary Pinsker
    have hp_s : ∀ a ∈ s, 0 < p a := fun a _ => hp_pos a
    have hq_s : ∀ a ∈ s, 0 < q a := fun a _ => hq_pos a
    have hp_sc : ∀ a ∈ sc, 0 < p a := fun a _ => hp_pos a
    have hq_sc : ∀ a ∈ sc, 0 < q a := fun a _ => hq_pos a
    have hP : 0 < ∑ a ∈ s, p a := Finset.sum_pos hp_s hs_nonempty
    have hQ : 0 < ∑ a ∈ s, q a := Finset.sum_pos hq_s hs_nonempty
    have hPc : 0 < ∑ a ∈ sc, p a := Finset.sum_pos hp_sc hsc
    have hQc : 0 < ∑ a ∈ sc, q a := Finset.sum_pos hq_sc hsc
    have hsumP : ∑ a ∈ s, p a + ∑ a ∈ sc, p a = 1 := by
      have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a ≤ p a) p
      simpa [hs_def, hsc_def, hp_sum] using h
    have hsumQ : ∑ a ∈ s, q a + ∑ a ∈ sc, q a = 1 := by
      have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a ≤ p a) q
      simpa [hs_def, hsc_def, hq_sum] using h
    have hP1 : ∑ a ∈ s, p a < 1 := by linarith
    have hQ1 : ∑ a ∈ s, q a < 1 := by linarith
    have hPc_eq : ∑ a ∈ sc, p a = 1 - ∑ a ∈ s, p a := by linarith
    have hQc_eq : ∑ a ∈ sc, q a = 1 - ∑ a ∈ s, q a := by linarith
    have hlog_s := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div s p q
      (fun a ha => (hp_s a ha).le) hq_s
    have hlog_sc := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div sc p q
      (fun a ha => (hp_sc a ha).le) hq_sc
    have hKL_split : ∑ a : α, p a * Real.log (p a / q a)
        = (∑ a ∈ s, p a * Real.log (p a / q a)) + (∑ a ∈ sc, p a * Real.log (p a / q a)) := by
      have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a ≤ p a)
        (fun a => p a * Real.log (p a / q a))
      simpa [hs_def, hsc_def] using h.symm
    have hKL_ge : (∑ a ∈ s, p a) * Real.log ((∑ a ∈ s, p a) / (∑ a ∈ s, q a))
        + (∑ a ∈ sc, p a) * Real.log ((∑ a ∈ sc, p a) / (∑ a ∈ sc, q a))
        ≤ ∑ a : α, p a * Real.log (p a / q a) := by
      linarith
    rw [hPc_eq, hQc_eq] at hKL_ge
    have hbin := binary_pinsker hP hP1 hQ hQ1
    have hL1 : ∑ a : α, |p a - q a|
        = 2 * ((∑ a ∈ s, p a) - (∑ a ∈ s, q a)) := by
      have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a ≤ p a)
        (fun a => |p a - q a|)
      have h1 : ∀ a ∈ Finset.univ.filter (fun a => q a ≤ p a), |p a - q a| = p a - q a := by
        intro a ha
        exact abs_of_nonneg (sub_nonneg.mpr (Finset.mem_filter.mp ha).2)
      have h2 : ∀ a ∈ Finset.univ.filter (fun a => ¬ q a ≤ p a), |p a - q a| = q a - p a := by
        intro a ha
        have hlt : p a < q a := not_le.mp (Finset.mem_filter.mp ha).2
        rw [abs_of_neg (sub_neg.mpr hlt)]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2] at h
      have hL : ∑ a : α, |p a - q a|
          = (∑ a ∈ s, (p a - q a)) + (∑ a ∈ sc, (q a - p a)) := by
        simpa [hs_def, hsc_def] using h.symm
      rw [hL, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      linarith [hsumP, hsumQ]
    rw [hL1]
    have hsq : (2 * ((∑ a ∈ s, p a) - (∑ a ∈ s, q a))) ^ 2
        = 2 * (2 * ((∑ a ∈ s, p a) - (∑ a ∈ s, q a)) ^ 2) := by ring
    rw [hsq]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    linarith
  · -- complement empty: p = q pointwise, both sides vanish
    rw [Finset.not_nonempty_iff_eq_empty] at hsc
    have hle : ∀ a : α, q a ≤ p a := by
      intro a
      by_contra hlt
      have hmem : a ∈ sc := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hlt⟩
      rw [hsc] at hmem
      simp at hmem
    have heq : ∀ a : α, p a = q a := by
      have hsum : ∑ a ∈ Finset.univ, (p a - q a) = 0 := by
        rw [Finset.sum_sub_distrib]
        simpa using (by rw [hp_sum, hq_sum, sub_self] : (∑ a : α, p a) - (∑ a : α, q a) = 0)
      have hnonneg : ∀ a ∈ Finset.univ, 0 ≤ p a - q a := fun a _ => sub_nonneg.mpr (hle a)
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
      intro a
      have h0 := hzero a (Finset.mem_univ a)
      linarith
    have hL : (∑ a : α, |p a - q a|) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [heq a, sub_self, abs_zero]
    have hR : (∑ a : α, p a * Real.log (p a / q a)) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      rw [heq a]
      have hne : q a ≠ 0 := ne_of_gt (hq_pos a)
      simp [div_self hne, Real.log_one]
    rw [hL, hR]
    simp

end MathlibExt.InformationTheory.Pinsker
