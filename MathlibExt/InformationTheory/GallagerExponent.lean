/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalMutualInformation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# Gallager's function `E₀(ρ, p)` for a discrete memoryless channel

For a discrete memoryless channel `W : α → PMF β` on finite alphabets and an input law
`p : PMF α`, Gallager's function is

`E₀(ρ, p) = -ln ∑_b (∑_a p(a) W(b | a)^{1/(1+ρ)})^{1+ρ}`,

in nats (natural logarithm), as in Gallager (1965), equation (20). It is the exponent in the
random coding bound `P̄ₑ ≤ (M - 1)^ρ exp(-N E₀(ρ, p))`, `0 ≤ ρ ≤ 1` (equation (17)).

* `gallagerE0_zero`: `E₀(0, p) = 0` (Theorem 2, equation (26)).
* `hasDerivAt_gallagerE0_zero`: `∂E₀/∂ρ` at `ρ = 0` is the mutual information `I(p; W)` in
  nats, that is `finiteMutualInformation` (which is in bits) times `ln 2` (Theorem 2,
  equation (29)). Unlike Gallager's statement, no hypothesis `I(p; W) ≠ 0` is needed for these
  two facts; Gallager assumes it for the strict inequalities (27) and (28).
* `hasDerivAt_gallagerE0_zero_nats`: the same derivative written out as
  `∑_{a,b} p(a) W(b|a) ln W(b|a) - ∑_b q(b) ln q(b)` with `q(b) = ∑_a p(a) W(b|a)`.
* `exists_gallagerE0_sub_pos`: below the mutual information (in nats) the exponent
  `E₀(ρ, p) - ρ R` is positive for some `0 < ρ ≤ 1`.
* `concaveOn_gallagerE0`: `ρ ↦ E₀(ρ, p)` is concave on `(-1, ∞)` (Theorem 2, equation (30), via
  Hölder's inequality `sum_rpow_mul_rpow_le`).

Zero-probability inputs and outputs are allowed: `0 ^ (1/(1+ρ)) = 0` for `ρ > -1`, and
`0 · ln 0 = 0` through Lean's `Real.log 0 = 0`.

## References

* R. G. Gallager, A simple derivation of the coding theorem and some applications, IEEE Trans.
  Inform. Theory IT-11 (1965), 3–18: equation (20) (definition), Theorem 2, equations (26),
  (29) and (30), and Section III.
-/

namespace MathlibExt.InformationTheory.GallagerExponent

open Real Filter Topology _root_.InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Gallager's inner sum.** `∑_a p(a) W(b | a)^{1/(1+ρ)}`, the quantity raised to the power
`1 + ρ` in Gallager's function (Gallager 1965, equation (20)). -/
noncomputable def gallagerInner (p : PMF α) (W : α → PMF β) (ρ : ℝ) (b : β) : ℝ :=
  ∑ a, (p a).toReal * ((W a) b).toReal ^ (1 / (1 + ρ))

/-- **Gallager's function `E₀(ρ, p)`.** For a discrete memoryless channel `W : α → PMF β` on
finite alphabets and an input law `p`,
`E₀(ρ, p) = -ln ∑_b (∑_a p(a) W(b | a)^{1/(1+ρ)})^{1+ρ}`, in nats
(R. G. Gallager, A simple derivation of the coding theorem and some applications, IEEE Trans.
Inform. Theory IT-11 (1965), equation (20)). It is meaningful for `ρ > -1`; Gallager uses
`0 ≤ ρ ≤ 1` in the coding theorem. -/
noncomputable def gallagerE0 (p : PMF α) (W : α → PMF β) (ρ : ℝ) : ℝ :=
  -Real.log (∑ b, gallagerInner p W ρ b ^ (1 + ρ))

omit [Fintype α] in
theorem sum_toReal_eq_one (q : PMF β) : ∑ b, (q b).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun b _ => q.apply_ne_top b),
    ← tsum_fintype (L := .unconditional _), q.tsum_coe, ENNReal.toReal_one]

omit [Fintype β] in
/-- **Gallager's inner sum at `ρ = 0`.** At `ρ = 0` the inner sum is the output law
`q(b) = ∑_a p(a) W(b | a)`, as a real number. -/
theorem gallagerInner_zero (p : PMF α) (W : α → PMF β) (b : β) :
    gallagerInner p W 0 b = ∑ a, (p a).toReal * ((W a) b).toReal := by
  simp [gallagerInner]

theorem sum_gallagerInner_zero_rpow (p : PMF α) (W : α → PMF β) :
    ∑ b, gallagerInner p W 0 b ^ (1 + (0 : ℝ)) = 1 := by
  simp only [add_zero, Real.rpow_one, gallagerInner_zero]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_toReal_eq_one, mul_one]
  exact sum_toReal_eq_one p

/-- **`E₀` vanishes at `ρ = 0`.** `E₀(0, p) = -ln ∑_b ∑_a p(a) W(b | a) = -ln 1 = 0`
(Gallager 1965, Theorem 2, equation (26); no hypothesis on `I(p; W)` is needed). -/
theorem gallagerE0_zero (p : PMF α) (W : α → PMF β) : gallagerE0 p W 0 = 0 := by
  rw [gallagerE0, sum_gallagerInner_zero_rpow, Real.log_one, neg_zero]

/-- **Derivative of `w ^ (1/(1+ρ))` at `ρ = 0`.** For `w ≥ 0` it is `-w ln w` (for `w = 0` the
function vanishes near `0`). -/
theorem hasDerivAt_rpow_one_div_one_add {w : ℝ} (hw : 0 ≤ w) :
    HasDerivAt (fun ρ : ℝ => w ^ (1 / (1 + ρ))) (-(w * Real.log w)) 0 := by
  rcases hw.lt_or_eq with hw | rfl
  · have hc : HasDerivAt (fun ρ : ℝ => 1 + ρ) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
    have hinv : HasDerivAt (fun ρ : ℝ => 1 / (1 + ρ)) (-1) 0 := by
      have := hc.inv (by norm_num)
      simp only [one_div]
      exact this.congr_deriv (by norm_num)
    exact (hinv.const_rpow (a := w) hw).congr_deriv (by norm_num; ring)
  · simp only [Real.log_zero, mul_zero, neg_zero]
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with ρ hρ
    have : 0 < 1 + ρ := by linarith
    rw [Real.zero_rpow (by positivity)]

omit [Fintype β] in
/-- **Derivative of one summand of `E₀` at `ρ = 0`.** The function
`ρ ↦ (∑_a p(a) W(b|a)^{1/(1+ρ)})^{1+ρ}` has derivative `q(b) ln q(b) - ∑_a p(a) W(b|a) ln W(b|a)`
at `0`, where `q(b) = ∑_a p(a) W(b|a)`; both sides vanish when `q(b) = 0`. -/
theorem hasDerivAt_gallagerInner_rpow (p : PMF α) (W : α → PMF β) (b : β) :
    HasDerivAt (fun ρ => gallagerInner p W ρ b ^ (1 + ρ))
      ((∑ a, (p a).toReal * ((W a) b).toReal) *
          Real.log (∑ a, (p a).toReal * ((W a) b).toReal) -
        ∑ a, (p a).toReal * (((W a) b).toReal * Real.log ((W a) b).toReal)) 0 := by
  have hterm : ∀ a, 0 ≤ (p a).toReal * ((W a) b).toReal := fun a => by positivity
  have hinner : HasDerivAt (fun ρ => gallagerInner p W ρ b)
      (-∑ a, (p a).toReal * (((W a) b).toReal * Real.log ((W a) b).toReal)) 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) (x := (0 : ℝ))
      (A := fun a ρ => (p a).toReal * ((W a) b).toReal ^ (1 / (1 + ρ)))
      (A' := fun a => (p a).toReal * (-(((W a) b).toReal * Real.log ((W a) b).toReal)))
      (fun a _ => (hasDerivAt_rpow_one_div_one_add ENNReal.toReal_nonneg).const_mul _)
    simpa [gallagerInner, Finset.sum_neg_distrib, mul_neg] using this
  rcases (Finset.sum_nonneg fun a _ => hterm a :
      0 ≤ ∑ a, (p a).toReal * ((W a) b).toReal).lt_or_eq with hpos | hzero
  · have h0 := gallagerInner_zero p W b
    have hc : HasDerivAt (fun ρ : ℝ => 1 + ρ) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
    have := hinner.rpow hc (by rw [h0]; exact hpos)
    refine this.congr_deriv ?_
    rw [h0]
    simp only [add_zero, sub_self, Real.rpow_zero, mul_one, Real.rpow_one, one_mul]
    ring
  · -- `q(b) = 0`: every term `p(a) W(b|a)` vanishes, and the summand is `0` near `ρ = 0`.
    have hall : ∀ a, (p a).toReal * ((W a) b).toReal = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hterm a).1 hzero.symm a (Finset.mem_univ a)
    have hval : ((∑ a, (p a).toReal * ((W a) b).toReal) *
          Real.log (∑ a, (p a).toReal * ((W a) b).toReal) -
        ∑ a, (p a).toReal * (((W a) b).toReal * Real.log ((W a) b).toReal)) = 0 := by
      rw [← hzero]
      simp only [zero_mul, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [← mul_assoc, hall a, zero_mul]
    rw [hval]
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num)] with ρ hρ
    have hρ' : 0 < 1 + ρ := by linarith
    have hg : gallagerInner p W ρ b = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      rcases mul_eq_zero.1 (hall a) with h | h
      · rw [h, zero_mul]
      · rw [h, Real.zero_rpow (by positivity), mul_zero]
    simp only [hg]
    exact Real.zero_rpow hρ'.ne'

/-- **Derivative of `E₀` at `ρ = 0`, explicit form.** `∂E₀/∂ρ (0, p)` equals
`∑_{a,b} p(a) W(b|a) ln W(b|a) - ∑_b q(b) ln q(b)` with `q(b) = ∑_a p(a) W(b|a)`, the mutual
information of `p` and `W` in nats (Gallager 1965, Theorem 2, equation (29)). -/
theorem hasDerivAt_gallagerE0_zero_nats (p : PMF α) (W : α → PMF β) :
    HasDerivAt (gallagerE0 p W)
      (∑ a, ∑ b, (p a).toReal * (((W a) b).toReal * Real.log ((W a) b).toReal) -
        ∑ b, (∑ a, (p a).toReal * ((W a) b).toReal) *
          Real.log (∑ a, (p a).toReal * ((W a) b).toReal)) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (x := (0 : ℝ))
    (fun b _ => hasDerivAt_gallagerInner_rpow p W b)
  have hS0 := sum_gallagerInner_zero_rpow p W
  have hlog := (hsum.log (by simp only [hS0]; norm_num)).neg
  refine hlog.congr_deriv ?_
  simp only [hS0, div_one, Finset.sum_sub_distrib, neg_sub]
  rw [Finset.sum_comm]

/-- **Derivative of `E₀` at `ρ = 0` is the mutual information.** For a discrete memoryless
channel `W` on finite alphabets and every input law `p`, `∂E₀/∂ρ` at `ρ = 0` equals the mutual
information `I(X; Y)` of the joint law `p(a) W(b | a)`, in nats: `finiteMutualInformation`
(in bits) times `ln 2` (Gallager 1965, Theorem 2, equation (29), where it is written `I(p)`).
Gallager assumes `I(p) ≠ 0` throughout Theorem 2; that hypothesis is not needed here. -/
theorem hasDerivAt_gallagerE0_zero (p : PMF α) (W : α → PMF β) :
    HasDerivAt (gallagerE0 p W)
      (finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)) * Real.log 2) 0 := by
  classical
  convert hasDerivAt_gallagerE0_zero_nats p W using 1
  set J := p.bind fun a => (W a).map (Prod.mk a)
  have hJ : ∀ a b, (J (a, b)).toReal = (p a).toReal * ((W a) b).toReal := by
    intro a b
    have : J (a, b) = p a * (W a) b := by
      simp only [J, PMF.bind_apply, PMF.map_apply, Prod.mk.injEq]
      rw [tsum_eq_single a]
      · congr 1
        rw [tsum_eq_single b]
        · simp
        · intro b' hb'; simp [Ne.symm hb']
      · intro a' ha'; simp [Ne.symm ha']
    rw [this, ENNReal.toReal_mul]
  have hfst : ∀ a, ((J.map Prod.fst) a).toReal = (p a).toReal := by
    intro a
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun _ _ => by
      split_ifs <;> simp [PMF.apply_ne_top])]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · simp only [ite_true]
      simp_rw [hJ]
      rw [← Finset.mul_sum, sum_toReal_eq_one, mul_one]
    · intro a' _ ha'
      simp [Ne.symm ha']
    · simp
  have hsnd : ∀ b, ((J.map Prod.snd) b).toReal = ∑ a, (p a).toReal * ((W a) b).toReal := by
    intro b
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (fun _ _ => by
      split_ifs <;> simp [PMF.apply_ne_top])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [hJ]
    · intro b' _ hb'
      simp [Ne.symm hb']
    · simp
  rw [finiteMutualInformation_eq]
  simp only [shannonEntropy]
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  rw [show ((∑ a, negMulLog ((J.map Prod.fst) a).toReal) / Real.log 2 +
      (∑ b, negMulLog ((J.map Prod.snd) b).toReal) / Real.log 2 -
      (∑ x, negMulLog (J x).toReal) / Real.log 2) * Real.log 2 =
      (∑ a, negMulLog ((J.map Prod.fst) a).toReal) + (∑ b, negMulLog ((J.map Prod.snd) b).toReal) -
      (∑ x, negMulLog (J x).toReal) by field_simp]
  simp_rw [hfst, hsnd]
  rw [Fintype.sum_prod_type]
  simp_rw [hJ, Real.negMulLog_mul, Finset.sum_add_distrib]
  have h1 : ∀ x, ∑ y, ((W x) y).toReal * (p x).toReal.negMulLog = (p x).toReal.negMulLog := by
    intro x
    rw [← Finset.sum_mul, sum_toReal_eq_one, one_mul]
  simp_rw [h1]
  simp only [Real.negMulLog, Finset.sum_neg_distrib, neg_mul, mul_neg]
  ring

/-- **Positive random coding exponent below the mutual information.** If the rate `R` (in nats)
is below the mutual information `I(p; W)` in nats, then `E₀(ρ, p) - ρ R > 0` for some
`0 < ρ ≤ 1`, so the exponent `max_{0 ≤ ρ ≤ 1} (E₀(ρ, p) - ρ R)` of the random coding bound is
positive. This is the first step of Gallager's argument that `E(R, p) > 0` for `R < I(p)`
(Gallager 1965, Section III, after equation (36)); here it follows from `E₀(0, p) = 0` and
`∂E₀/∂ρ (0, p) = I(p)` alone. -/
theorem exists_gallagerE0_sub_pos (p : PMF α) (W : α → PMF β) {R : ℝ}
    (hR : R < finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)) * Real.log 2) :
    ∃ ρ ∈ Set.Ioc (0 : ℝ) 1, 0 < gallagerE0 p W ρ - ρ * R := by
  set I := finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)) * Real.log 2
  have hd : HasDerivAt (fun ρ => gallagerE0 p W ρ - ρ * R) (I - R) 0 := by
    have := (hasDerivAt_gallagerE0_zero p W).fun_sub ((hasDerivAt_id' (0 : ℝ)).mul_const R)
    exact this.congr_deriv (by simp [I])
  have hslope := hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t⁻¹ • ((gallagerE0 p W (0 + t) - (0 + t) * R) - (gallagerE0 p W 0 - 0 * R)) :=
    hslope.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioc (0 : ℝ) 1 :=
    Ioc_mem_nhdsGT (by norm_num)
  obtain ⟨t, ht, ht'⟩ := (hev.and hev2).exists
  refine ⟨t, ht', ?_⟩
  simp only [zero_add, gallagerE0_zero, zero_mul, sub_zero, smul_eq_mul] at ht
  exact (mul_pos_iff_of_pos_left (inv_pos.2 ht'.1)).1 ht

/-! ### Concavity in `ρ` -/

omit [Fintype β] in
theorem gallagerInner_nonneg (p : PMF α) (W : α → PMF β) (ρ : ℝ) (b : β) :
    0 ≤ gallagerInner p W ρ b :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg
    ENNReal.toReal_nonneg _)

/-- **The sum inside `E₀` is positive.** For every `ρ`,
`∑_b (∑_a p(a) W(b|a)^{1/(1+ρ)})^{1+ρ} > 0`, so `E₀(ρ, p)` is the logarithm of a positive number. -/
theorem sum_gallagerInner_rpow_pos (p : PMF α) (W : α → PMF β) (ρ : ℝ) :
    0 < ∑ b, gallagerInner p W ρ b ^ (1 + ρ) := by
  obtain ⟨a, ha⟩ : ∃ a, p a ≠ 0 := by
    by_contra h
    push Not at h
    have := sum_toReal_eq_one p
    simp [h] at this
  obtain ⟨b, hb⟩ : ∃ b, (W a) b ≠ 0 := by
    by_contra h
    push Not at h
    have := sum_toReal_eq_one (W a)
    simp [h] at this
  have hpa : 0 < (p a).toReal := ENNReal.toReal_pos ha (PMF.apply_ne_top _ _)
  have hwb : 0 < ((W a) b).toReal := ENNReal.toReal_pos hb (PMF.apply_ne_top _ _)
  have hg : 0 < gallagerInner p W ρ b :=
    lt_of_lt_of_le (mul_pos hpa (Real.rpow_pos_of_pos hwb _))
      (Finset.single_le_sum (f := fun a => (p a).toReal * ((W a) b).toReal ^ (1 / (1 + ρ)))
        (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (Finset.mem_univ a))
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hg _)
    (Finset.single_le_sum (f := fun b => gallagerInner p W ρ b ^ (1 + ρ))
      (fun b _ => Real.rpow_nonneg (gallagerInner_nonneg p W ρ b) _) (Finset.mem_univ b))

/-- **Hölder's inequality, geometric-mean form.** For `0 < μ < 1` and nonnegative `X, Y`,
`∑ X_i^μ Y_i^{1-μ} ≤ (∑ X_i)^μ (∑ Y_i)^{1-μ}`. -/
theorem sum_rpow_mul_rpow_le {ι : Type*} (s : Finset ι) {X Y : ι → ℝ} (hX : ∀ i ∈ s, 0 ≤ X i)
    (hY : ∀ i ∈ s, 0 ≤ Y i) {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    ∑ i ∈ s, X i ^ μ * Y i ^ (1 - μ) ≤ (∑ i ∈ s, X i) ^ μ * (∑ i ∈ s, Y i) ^ (1 - μ) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (Real.holderConjugate_one_div hμ0 (by linarith : 0 < 1 - μ) (by ring))
    (f := fun i => X i ^ μ) (g := fun i => Y i ^ (1 - μ))
    (fun i hi => Real.rpow_nonneg (hX i hi) _) (fun i hi => Real.rpow_nonneg (hY i hi) _)
  have e1 : ∀ i ∈ s, (X i ^ μ) ^ (1 / μ) = X i := fun i hi => by
    rw [← Real.rpow_mul (hX i hi), mul_one_div_cancel hμ0.ne', Real.rpow_one]
  have e2 : ∀ i ∈ s, (Y i ^ (1 - μ)) ^ (1 / (1 - μ)) = Y i := fun i hi => by
    rw [← Real.rpow_mul (hY i hi), mul_one_div_cancel (by linarith), Real.rpow_one]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
  simpa only [one_div_one_div] using h

/-- **Concavity of `E₀` in `ρ`.** For a discrete memoryless channel on finite alphabets and every
input law `p`, `ρ ↦ E₀(ρ, p)` is concave on `ρ > -1` (Gallager 1965, Theorem 2, equation (30):
`∂²E₀/∂ρ² ≤ 0` for `ρ ≥ 0`, proved there with Hölder's inequality). The statement here is for the
larger interval `(-1, ∞)` and needs neither differentiability nor Gallager's hypothesis
`I(p) ≠ 0`. -/
theorem concaveOn_gallagerE0 (p : PMF α) (W : α → PMF β) :
    ConcaveOn ℝ (Set.Ioi (-1)) (gallagerE0 p W) := by
  refine ⟨convex_Ioi _, fun ρ₁ hρ₁ ρ₂ hρ₂ a b ha hb hab => ?_⟩
  simp only [Set.mem_Ioi] at hρ₁ hρ₂
  simp only [smul_eq_mul]
  rcases ha.lt_or_eq with ha' | rfl
  swap
  · simp only [zero_add] at hab; subst hab; simp
  rcases hb.lt_or_eq with hb' | rfl
  swap
  · simp only [add_zero] at hab; subst hab; simp
  set ρ := a * ρ₁ + b * ρ₂
  have ht₁ : 0 < 1 + ρ₁ := by linarith
  have ht₂ : 0 < 1 + ρ₂ := by linarith
  have ht : 1 + ρ = a * (1 + ρ₁) + b * (1 + ρ₂) := by
    simp only [ρ]; linear_combination (-1 : ℝ) * hab
  have htpos : 0 < 1 + ρ := by rw [ht]; positivity
  set μ := a * (1 + ρ₁) / (1 + ρ)
  have hμ0 : 0 < μ := by positivity
  have hμ1 : μ < 1 := by
    rw [div_lt_one htpos, ht]; nlinarith
  have h1μ : 1 - μ = b * (1 + ρ₂) / (1 + ρ) := by
    simp only [μ]; field_simp; linarith
  -- Step 1: Hölder in the input letter, for each output `b`.
  have hinner : ∀ y, gallagerInner p W ρ y ≤
      gallagerInner p W ρ₁ y ^ μ * gallagerInner p W ρ₂ y ^ (1 - μ) := by
    intro y
    unfold gallagerInner
    refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_)
      (sum_rpow_mul_rpow_le _ (fun x _ => mul_nonneg ENNReal.toReal_nonneg
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)) (fun x _ => mul_nonneg ENNReal.toReal_nonneg
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)) hμ0 hμ1)
    have hp0 : 0 ≤ (p x).toReal := ENNReal.toReal_nonneg
    have hw0 : 0 ≤ ((W x) y).toReal := ENNReal.toReal_nonneg
    rw [Real.mul_rpow hp0 (Real.rpow_nonneg hw0 _), Real.mul_rpow hp0 (Real.rpow_nonneg hw0 _),
      ← Real.rpow_mul hw0, ← Real.rpow_mul hw0]
    calc (p x).toReal * ((W x) y).toReal ^ (1 / (1 + ρ))
        = ((p x).toReal ^ μ * (p x).toReal ^ (1 - μ)) *
            (((W x) y).toReal ^ (1 / (1 + ρ₁) * μ) *
              ((W x) y).toReal ^ (1 / (1 + ρ₂) * (1 - μ))) := by
          rw [← Real.rpow_add' hp0 (by ring_nf; norm_num), ← Real.rpow_add' hw0]
          · congr 1
            · ring_nf; simp
            · congr 1
              rw [h1μ]; simp only [μ]; field_simp; linarith
          · rw [h1μ]; simp only [μ]
            have : 1 / (1 + ρ₁) * (a * (1 + ρ₁) / (1 + ρ)) +
                1 / (1 + ρ₂) * (b * (1 + ρ₂) / (1 + ρ)) = 1 / (1 + ρ) := by
              field_simp; linarith
            rw [this]; positivity
      _ = _ := by ring
  -- Step 2: raise to the power `1 + ρ`.
  have hterm : ∀ y, gallagerInner p W ρ y ^ (1 + ρ) ≤
      (gallagerInner p W ρ₁ y ^ (1 + ρ₁)) ^ a * (gallagerInner p W ρ₂ y ^ (1 + ρ₂)) ^ b := by
    intro y
    have g1 := gallagerInner_nonneg p W ρ₁ y
    have g2 := gallagerInner_nonneg p W ρ₂ y
    refine (Real.rpow_le_rpow (gallagerInner_nonneg p W ρ y) (hinner y) htpos.le).trans
      (le_of_eq ?_)
    rw [Real.mul_rpow (Real.rpow_nonneg g1 _) (Real.rpow_nonneg g2 _), ← Real.rpow_mul g1,
      ← Real.rpow_mul g2, ← Real.rpow_mul g1, ← Real.rpow_mul g2, h1μ]
    congr 2
    · simp only [μ]; field_simp
    · field_simp
  -- Step 3: Hölder in the output letter.
  have hF : ∑ y, gallagerInner p W ρ y ^ (1 + ρ) ≤
      (∑ y, gallagerInner p W ρ₁ y ^ (1 + ρ₁)) ^ a *
        (∑ y, gallagerInner p W ρ₂ y ^ (1 + ρ₂)) ^ b := by
    have hb1 : b = 1 - a := by linarith
    refine (Finset.sum_le_sum fun y _ => hterm y).trans ?_
    rw [hb1]
    exact sum_rpow_mul_rpow_le _ (fun y _ => Real.rpow_nonneg (gallagerInner_nonneg p W ρ₁ y) _)
      (fun y _ => Real.rpow_nonneg (gallagerInner_nonneg p W ρ₂ y) _) ha' (by linarith)
  -- Step 4: take `-log`.
  have hF1 := sum_gallagerInner_rpow_pos p W ρ₁
  have hF2 := sum_gallagerInner_rpow_pos p W ρ₂
  have hF0 := sum_gallagerInner_rpow_pos p W ρ
  have hlog := Real.log_le_log hF0 hF
  rw [Real.log_mul (Real.rpow_pos_of_pos hF1 _).ne' (Real.rpow_pos_of_pos hF2 _).ne',
    Real.log_rpow hF1, Real.log_rpow hF2] at hlog
  simp only [gallagerE0]
  linarith

end MathlibExt.InformationTheory.GallagerExponent
