/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ViscositySolution.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Comparison principle for first-order Hamilton–Jacobi equations

The doubling-of-variables proof of the comparison principle of Crandall and Lions on a bounded
open subset of a finite-dimensional real inner product space, for continuous sub- and
supersolutions: first for the model equation `γ u + H(Du) = f(x)` with `γ > 0`, then for a
general first-order equation under the structure conditions of the user's guide. For semicontinuous
sub- and supersolutions, finite dimensionality ensures that the bounded closure is compact, so
maximizers of the doubled functional have a convergent subsequence.

## Main results

* `le_of_isViscositySubsolution_of_isViscositySupersolution`: if `u` is a viscosity subsolution
  and `v` a viscosity supersolution of `γ u + H(Du) - f(x) = 0` on a bounded open `Ω`, both
  continuous on `closure Ω`, `f` is continuous on `closure Ω`, and `u ≤ v` on `∂Ω`, then
  `u ≤ v` on `Ω`.
* `eqOn_of_isViscositySolution`: uniqueness of viscosity solutions of the Dirichlet problem for
  that equation.
* `le_of_isViscositySubsolution_of_isViscositySupersolution_of_proper`: the comparison principle
  for a general first-order `F(x, r, p)` under the structure conditions (3.13)–(3.14) of the
  user's guide, for continuous sub- and supersolutions.
* `ViscositySolutionWanted.le_of_isViscositySubsolution_of_isViscositySupersolution_of_structure`:
  comparison under (3.13)–(3.14) for semicontinuous sub- and supersolutions.

## References

* M. G. Crandall, H. Ishii and P.-L. Lions, *User's guide to viscosity solutions of second order
  partial differential equations*, Bull. Amer. Math. Soc. 27 (1992) 1–67, arXiv:math/9207212,
  §3 (Lemma 3.1, Theorem 3.3 and Example 3.6).
-/

@[expose] public section

namespace MathlibExt.Analysis.ViscositySolution

open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the quadratic penalty `y ↦ (a/2) ‖y - c‖²` at `x` is `a ⟪x - c, ·⟫`. -/
private theorem hasFDerivAt_half_mul_norm_sub_sq (a : ℝ) (c x : E) :
    HasFDerivAt (fun y : E => a / 2 * ‖y - c‖ ^ 2) (a • innerSL ℝ (x - c)) x := by
  have h := ((hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const c)
  have h2 := h.const_mul (a / 2)
  have heq : (a / 2) • ((2 • innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ E)) =
      a • innerSL ℝ (x - c) := by
    ext w
    simp
    ring
  rw [heq] at h2
  exact h2

private theorem contDiff_half_mul_norm_sub_sq (a : ℝ) (c : E) :
    ContDiff ℝ 1 fun y : E => a / 2 * ‖y - c‖ ^ 2 :=
  contDiff_const.mul (contDiff_norm_sq ℝ |>.comp (contDiff_id.sub contDiff_const))

variable [FiniteDimensional ℝ E]

/-- **Comparison principle for `γ u + H(Du) = f(x)`** (Crandall and Lions; Crandall, Ishii and
Lions, *User's guide*, Bull. AMS 1992, Theorem 3.3 in the first-order model case of
Example 3.6, `F(x, r, p) = γ r + H(p) - f(x)` with `γ > 0`; proof by Lemma 3.1's doubling of
variables). Let `Ω` be a bounded open subset of a finite-dimensional real inner product space,
`f` continuous on `closure Ω`, `u` a viscosity subsolution and `v` a viscosity supersolution of
`γ u + H(Du) - f(x) = 0` on `Ω`, both continuous on `closure Ω`, with `u ≤ v` on `∂Ω`. Then
`u ≤ v` on `Ω`. The Hamiltonian `H` is arbitrary: in the doubled problem both test functions
have the same gradient `α (x̂ - ŷ)`, so `H` cancels. Theorem 3.3 itself allows semicontinuous
`u`, `v` and second-order `F` under the structure conditions (3.13)–(3.14); this is the
continuous first-order model case. -/
theorem le_of_isViscositySubsolution_of_isViscositySupersolution {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {γ : ℝ} (hγ : 0 < γ) (H : (E →L[ℝ] ℝ) → ℝ) {f u v : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hu : ContinuousOn u (closure Ω))
    (hv : ContinuousOn v (closure Ω))
    (hsub : IsViscositySubsolution (fun x r p => γ * r + H p - f x) Ω u)
    (hsup : IsViscositySupersolution (fun x r p => γ * r + H p - f x) Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x) : ∀ x ∈ Ω, u x ≤ v x := by
  intro z hz
  by_contra hlt
  replace hlt := not_le.mp hlt
  set δ := u z - v z with hδ
  have hδpos : 0 < δ := by linarith
  set K := closure Ω with hKdef
  have hK : IsCompact K := hΩb.isCompact_closure
  have hzK : z ∈ K := subset_closure hz
  -- moduli of continuity on the compact set `K`
  have huc := hK.uniformContinuousOn_of_continuous hu
  have hvc := hK.uniformContinuousOn_of_continuous hv
  have hfc := hK.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc hvc hfc
  obtain ⟨η₁, hη₁, hu'⟩ := huc (δ / 2) (by positivity)
  obtain ⟨η₂, hη₂, hv'⟩ := hvc (δ / 2) (by positivity)
  obtain ⟨η₃, hη₃, hf'⟩ := hfc (γ * δ / 2) (by positivity)
  set η := min η₁ (min η₂ η₃) with hηdef
  have hη : 0 < η := lt_min hη₁ (lt_min hη₂ hη₃)
  -- bounds on `K`
  obtain ⟨Mu, hMu⟩ := hK.exists_bound_of_continuousOn hu
  obtain ⟨Mv, hMv⟩ := hK.exists_bound_of_continuousOn hv
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu z hzK)
  have hMv0 : 0 ≤ Mv := (norm_nonneg _).trans (hMv z hzK)
  set B := Mu + Mv with hB
  set α := 4 * (B + 1) / η ^ 2 with hα
  have hαpos : 0 < α := by positivity
  -- maximise the doubled functional on `K × K`
  set Φ : E × E → ℝ := fun q => u q.1 - v q.2 - α / 2 * ‖q.1 - q.2‖ ^ 2 with hΦ
  have hΦc : ContinuousOn Φ (K ×ˢ K) := by
    refine ((hu.comp continuousOn_fst fun q (hq : q ∈ K ×ˢ K) => hq.1).sub
      (hv.comp continuousOn_snd fun q (hq : q ∈ K ×ˢ K) => hq.2)).sub ?_
    exact (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2)).continuousOn
  obtain ⟨q, hqK, hqmax⟩ := (hK.prod hK).exists_isMaxOn ⟨(z, z), hzK, hzK⟩ hΦc
  set x := q.1 with hx
  set y := q.2 with hy
  have hxK : x ∈ K := hqK.1
  have hyK : y ∈ K := hqK.2
  have hΦq : Φ (z, z) ≤ Φ q := hqmax ⟨hzK, hzK⟩
  simp only [hΦ, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, sub_zero] at hΦq
  -- `u x - v y ≥ δ + (α/2)‖x - y‖²`
  have hgap : δ + α / 2 * ‖x - y‖ ^ 2 ≤ u x - v y := by
    simp only [hδ]; linarith
  have hsq : 0 ≤ α / 2 * ‖x - y‖ ^ 2 := by positivity
  have hxy : dist x y < η := by
    have h1 : u x ≤ Mu := (le_abs_self _).trans (hMu x hxK)
    have h2 : -v y ≤ Mv := (neg_le_abs _).trans (hMv y hyK)
    have h3 : α / 2 * ‖x - y‖ ^ 2 ≤ B := by simp only [hB]; linarith
    have h4 : ‖x - y‖ ^ 2 < η ^ 2 := by
      have hη2 : 0 < η ^ 2 := by positivity
      rw [hα] at h3
      have : ‖x - y‖ ^ 2 * (2 * (B + 1)) ≤ B * η ^ 2 := by
        have := h3
        field_simp at this
        nlinarith
      nlinarith
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hη.le h4
  have hdu : |u x - u y| < δ / 2 := hu' x hxK y hyK (hxy.trans_le (min_le_left _ _))
  have hdv : |v x - v y| < δ / 2 :=
    hv' x hxK y hyK (hxy.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hdf : |f x - f y| < γ * δ / 2 :=
    hf' x hxK y hyK (hxy.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  -- both points are interior
  have hxΩ : x ∈ Ω := by
    by_contra hxΩ
    have hfr : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hxK, hxΩ⟩
    have := hbdry x hfr
    have := (abs_lt.mp hdv).2
    linarith
  have hyΩ : y ∈ Ω := by
    by_contra hyΩ
    have hfr : y ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hyK, hyΩ⟩
    have := hbdry y hfr
    have := (abs_lt.mp hdu).2
    linarith
  -- the subsolution test at `x`
  set p : E →L[ℝ] ℝ := α • innerSL ℝ (x - y) with hp
  have hsubx : γ * u x + H p - f x ≤ 0 := by
    have hφ := (hasFDerivAt_half_mul_norm_sub_sq α y x).const_add (v y)
    have h := hsub.2 x hxΩ (fun w => v y + α / 2 * ‖w - y‖ ^ 2)
      (contDiff_const.add (contDiff_half_mul_norm_sub_sq α y)) ?_
    · rw [hφ.fderiv] at h
      exact h
    refine IsMaxOn.isLocalMaxOn fun w hw => ?_
    have : Φ (w, y) ≤ Φ q := hqmax (show (w, y) ∈ K ×ˢ K from ⟨subset_closure hw, hyK⟩)
    simp only [hΦ, ← hx, ← hy] at this
    change u w - (v y + α / 2 * ‖w - y‖ ^ 2) ≤ u x - (v y + α / 2 * ‖x - y‖ ^ 2)
    linarith
  -- the supersolution test at `y`
  have hsupy : 0 ≤ γ * v y + H p - f y := by
    have hψ := (hasFDerivAt_half_mul_norm_sub_sq α x y).const_sub (u x)
    have hder : -(α • innerSL ℝ (y - x)) = p := by
      ext w
      simp [hp]
      ring
    have h := hsup.2 y hyΩ (fun w => u x - α / 2 * ‖w - x‖ ^ 2)
      (contDiff_const.sub (contDiff_half_mul_norm_sub_sq α x)) ?_
    · rw [hψ.fderiv, hder] at h
      exact h
    refine IsMinOn.isLocalMinOn fun w hw => ?_
    have : Φ (x, w) ≤ Φ q := hqmax (show (x, w) ∈ K ×ˢ K from ⟨hxK, subset_closure hw⟩)
    simp only [hΦ, ← hx, ← hy] at this
    rw [norm_sub_rev x w, norm_sub_rev x y] at this
    change v y - (u x - α / 2 * ‖y - x‖ ^ 2) ≤ v w - (u x - α / 2 * ‖w - x‖ ^ 2)
    linarith
  -- contradiction: `γ δ ≤ γ (u x - v y) ≤ f x - f y < γ δ / 2`
  have hfxy := (abs_lt.mp hdf).2
  have : γ * δ ≤ γ * (u x - v y) := by
    apply mul_le_mul_of_nonneg_left _ hγ.le
    linarith
  nlinarith

/-- **Uniqueness for the Dirichlet problem for `γ u + H(Du) = f(x)`** (Crandall, Ishii and Lions,
*User's guide*, Theorem 3.3, first-order model case of Example 3.6). Two viscosity solutions on a
bounded open set `Ω`, continuous on `closure Ω` and equal on `∂Ω`, are equal on `Ω`. -/
theorem eqOn_of_isViscositySolution {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {γ : ℝ} (hγ : 0 < γ) (H : (E →L[ℝ] ℝ) → ℝ) {f u v : E → ℝ}
    (hf : ContinuousOn f (closure Ω)) (hu : ContinuousOn u (closure Ω))
    (hv : ContinuousOn v (closure Ω))
    (hu' : IsViscositySolution (fun x r p => γ * r + H p - f x) Ω u)
    (hv' : IsViscositySolution (fun x r p => γ * r + H p - f x) Ω v)
    (hbdry : EqOn u v (frontier Ω)) : EqOn u v Ω := fun x hx =>
  le_antisymm
    (le_of_isViscositySubsolution_of_isViscositySupersolution hΩ hΩb hγ H hf hu hv hu'.1 hv'.2
      (fun _ hy => (hbdry hy).le) x hx)
    (le_of_isViscositySubsolution_of_isViscositySupersolution hΩ hΩb hγ H hf hv hu hv'.1 hu'.2
      (fun _ hy => (hbdry hy).ge) x hx)

/-- **Comparison principle for first-order equations, continuous case** (Crandall and Lions;
Crandall, Ishii and Lions, *User's guide*, Bull. AMS 1992, Theorem 3.3 for an `F` independent of
the Hessian variable, with continuous `u` and `v`; proof by Lemma 3.1's doubling of variables).
Let `Ω` be a bounded open subset of a finite-dimensional real inner product space, `γ > 0`, and
`F` satisfy
* (3.13) `γ (r - s) ≤ F(x, r, p) - F(x, s, p)` for `r ≥ s` and `x ∈ closure Ω`;
* (3.14) `F(y, r, α⟪x - y, ·⟫) - F(x, r, α⟪x - y, ·⟫) ≤ ω(α‖x - y‖² + ‖x - y‖)` for
  `x, y ∈ Ω`, `r ∈ ℝ`, `α > 0`, with `ω(t) → 0` as `t → 0⁺`.

As in the printed user's guide, (3.13) is asked on `closure Ω` and (3.14) only on `Ω`.
If `u` is a viscosity subsolution and `v` a viscosity supersolution of `F = 0` on `Ω`, both
continuous on `closure Ω`, and `u ≤ v` on `∂Ω`, then `u ≤ v` on `Ω`. No continuity of `F` is
used. The penalisation parameter is chosen among `α₀ 2ᵏ` so that `α ‖x_α - y_α‖²` is small, the
quantitative form of Lemma 3.1 (i). Theorem 3.3 also allows semicontinuous `u`, `v` and
second-order `F`; that generality is not claimed here. -/
theorem le_of_isViscositySubsolution_of_isViscositySupersolution_of_proper {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (F : E → ℝ → (E →L[ℝ] ℝ) → ℝ) {γ : ℝ}
    (hγ : 0 < γ)
    (hproper : ∀ x ∈ closure Ω, ∀ r s : ℝ, ∀ p : E →L[ℝ] ℝ, s ≤ r →
      γ * (r - s) ≤ F x r p - F x s p)
    (ω : ℝ → ℝ) (hω : Tendsto ω (𝓝[>] 0) (𝓝 0))
    (hstruct : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ r : ℝ, ∀ α : ℝ, 0 < α →
      F y r (α • innerSL ℝ (x - y)) - F x r (α • innerSL ℝ (x - y)) ≤
        ω (α * ‖x - y‖ ^ 2 + ‖x - y‖))
    {u v : E → ℝ} (hu : ContinuousOn u (closure Ω)) (hv : ContinuousOn v (closure Ω))
    (hsub : IsViscositySubsolution F Ω u) (hsup : IsViscositySupersolution F Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x) : ∀ x ∈ Ω, u x ≤ v x := by
  intro z hz
  by_contra hlt
  replace hlt := not_le.mp hlt
  set δ := u z - v z with hδ
  have hδpos : 0 < δ := by linarith
  set K := closure Ω with hKdef
  have hK : IsCompact K := hΩb.isCompact_closure
  have hzK : z ∈ K := subset_closure hz
  have huc := hK.uniformContinuousOn_of_continuous hu
  have hvc := hK.uniformContinuousOn_of_continuous hv
  rw [Metric.uniformContinuousOn_iff] at huc hvc
  obtain ⟨η₁, hη₁, hu'⟩ := huc (δ / 2) (by positivity)
  obtain ⟨η₂, hη₂, hv'⟩ := hvc (δ / 2) (by positivity)
  -- the modulus is below `γ δ` on `(0, ρ)`
  obtain ⟨ρ, hρ, hωρ⟩ := Metric.tendsto_nhdsWithin_nhds.1 hω (γ * δ) (by positivity)
  obtain ⟨Mu, hMu⟩ := hK.exists_bound_of_continuousOn hu
  obtain ⟨Mv, hMv⟩ := hK.exists_bound_of_continuousOn hv
  have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu z hzK)
  have hMv0 : 0 ≤ Mv := (norm_nonneg _).trans (hMv z hzK)
  set B := Mu + Mv with hB
  set μ := min (min η₁ η₂) (ρ / 2) with hμ
  have hμpos : 0 < μ := lt_min (lt_min hη₁ hη₂) (by positivity)
  set α₀ := 4 * (B + 1) / μ ^ 2 with hα₀
  have hα₀pos : 0 < α₀ := by positivity
  -- maximisers of the doubled functional for every penalisation
  set Φ : ℝ → E × E → ℝ := fun α q => u q.1 - v q.2 - α / 2 * ‖q.1 - q.2‖ ^ 2 with hΦ
  have hΦc : ∀ α, ContinuousOn (Φ α) (K ×ˢ K) := fun α =>
    ((hu.comp continuousOn_fst fun q (hq : q ∈ K ×ˢ K) => hq.1).sub
      (hv.comp continuousOn_snd fun q (hq : q ∈ K ×ˢ K) => hq.2)).sub
      (continuous_const.mul ((continuous_fst.sub continuous_snd).norm.pow 2)).continuousOn
  have hex : ∀ α, ∃ q ∈ K ×ˢ K, IsMaxOn (Φ α) (K ×ˢ K) q := fun α =>
    (hK.prod hK).exists_isMaxOn ⟨(z, z), hzK, hzK⟩ (hΦc α)
  choose q hqK hqmax using hex
  set M : ℝ → ℝ := fun α => Φ α (q α) with hM
  have hMδ : ∀ α, δ ≤ M α := fun α => by
    have h0 : Φ α (z, z) = δ := by simp [hΦ, hδ]
    have : Φ α (z, z) ≤ Φ α (q α) := hqmax α (show (z, z) ∈ K ×ˢ K from ⟨hzK, hzK⟩)
    rw [h0] at this
    exact this
  have hbound : ∀ w ∈ K ×ˢ K, u w.1 - v w.2 ≤ B := fun w hw => by
    have h1 : u w.1 ≤ Mu := (le_abs_self _).trans (hMu w.1 hw.1)
    have h2 : -v w.2 ≤ Mv := (neg_le_abs _).trans (hMv w.2 hw.2)
    linarith
  -- halving the penalisation controls `α ‖x - y‖²` at the maximiser of `Φ (2α)`
  have hstep : ∀ α, α / 2 * ‖(q (2 * α)).1 - (q (2 * α)).2‖ ^ 2 ≤ M α - M (2 * α) := fun α => by
    have : Φ α (q (2 * α)) ≤ Φ α (q α) := hqmax α (hqK (2 * α))
    change α / 2 * ‖(q (2 * α)).1 - (q (2 * α)).2‖ ^ 2 ≤ Φ α (q α) - Φ (2 * α) (q (2 * α))
    simp only [hΦ] at this ⊢
    nlinarith [this]
  -- pick `k` with a small decrement along `α₀ 2ᵏ`
  set a : ℕ → ℝ := fun k => α₀ * 2 ^ k with ha
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * B / ρ)
  have hNpos : 0 < N := by
    have : (0 : ℝ) ≤ 8 * B / ρ := by positivity
    exact_mod_cast this.trans_lt hN
  have htel : ∑ k ∈ Finset.range N, (M (a k) - M (a (k + 1))) ≤
      ∑ _k ∈ Finset.range N, B / N := by
    rw [Finset.sum_range_sub' (fun k => M (a k)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have h1 : M (a 0) ≤ B := by
      have := hbound (q (a 0)) (hqK _)
      have : 0 ≤ a 0 / 2 * ‖(q (a 0)).1 - (q (a 0)).2‖ ^ 2 := by
        simp only [ha]; positivity
      simp only [hM, hΦ] at *
      linarith
    have h2 := hMδ (a N)
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    rw [mul_div_cancel₀ _ hNne]
    linarith
  obtain ⟨k, -, hk⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.2 hNpos⟩ htel
  set α := a k with hαdef
  have hαpos : 0 < α := by simp only [hαdef, ha]; positivity
  have hα₀le : α₀ ≤ α := by
    simp only [hαdef, ha]
    exact le_mul_of_one_le_right hα₀pos.le (one_le_pow₀ (by norm_num))
  have h2α : a (k + 1) = 2 * α := by simp only [ha, hαdef, pow_succ]; ring
  set x := (q (2 * α)).1 with hx
  set y := (q (2 * α)).2 with hy
  have hxK : x ∈ K := (hqK (2 * α)).1
  have hyK : y ∈ K := (hqK (2 * α)).2
  have hBN : B / N < ρ / 8 := by
    rw [div_lt_iff₀ (by exact_mod_cast hNpos)]
    rw [div_lt_iff₀ hρ] at hN
    linarith
  have hsmall : 2 * α * ‖x - y‖ ^ 2 < ρ / 2 := by
    have h1 := hstep α
    have hk' : M α - M (2 * α) ≤ B / N := by rw [← h2α]; exact hk
    nlinarith
  -- `u x - v y ≥ δ` and `‖x - y‖ < μ`
  have hgap : δ + (2 * α) / 2 * ‖x - y‖ ^ 2 ≤ u x - v y := by
    have := hMδ (2 * α)
    simp only [hM, hΦ] at this
    linarith
  have hsq : 0 ≤ (2 * α) / 2 * ‖x - y‖ ^ 2 := by positivity
  have hxy : ‖x - y‖ < μ := by
    have h3 : (2 * α) / 2 * ‖x - y‖ ^ 2 ≤ B := by
      have := hbound (q (2 * α)) (hqK _)
      linarith
    have h4 : ‖x - y‖ ^ 2 < μ ^ 2 := by
      have hμ2 : 0 < μ ^ 2 := by positivity
      have hα₀' : α₀ * μ ^ 2 = 4 * (B + 1) := by
        rw [hα₀]; field_simp
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hμpos.le h4
  have hxyd : dist x y < μ := by rwa [dist_eq_norm]
  have hdu : |u x - u y| < δ / 2 :=
    hu' x hxK y hyK (hxyd.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hdv : |v x - v y| < δ / 2 :=
    hv' x hxK y hyK (hxyd.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hxΩ : x ∈ Ω := by
    by_contra hxΩ
    have hfr : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hxK, hxΩ⟩
    have := hbdry x hfr
    have := (abs_lt.mp hdv).2
    linarith
  have hyΩ : y ∈ Ω := by
    by_contra hyΩ
    have hfr : y ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hyK, hyΩ⟩
    have := hbdry y hfr
    have := (abs_lt.mp hdu).2
    linarith
  -- the two viscosity tests, with the common gradient `p = 2α ⟪x - y, ·⟫`
  set p : E →L[ℝ] ℝ := (2 * α) • innerSL ℝ (x - y) with hp
  have hsubx : F x (u x) p ≤ 0 := by
    have hφ := (hasFDerivAt_half_mul_norm_sub_sq (2 * α) y x).const_add (v y)
    have h := hsub.2 x hxΩ (fun w => v y + (2 * α) / 2 * ‖w - y‖ ^ 2)
      (contDiff_const.add (contDiff_half_mul_norm_sub_sq (2 * α) y)) ?_
    · rw [hφ.fderiv] at h
      exact h
    refine IsMaxOn.isLocalMaxOn fun w hw => ?_
    have : Φ (2 * α) (w, y) ≤ Φ (2 * α) (q (2 * α)) :=
      hqmax (2 * α) (show (w, y) ∈ K ×ˢ K from ⟨subset_closure hw, hyK⟩)
    simp only [hΦ, ← hx, ← hy] at this
    change u w - (v y + (2 * α) / 2 * ‖w - y‖ ^ 2) ≤ u x - (v y + (2 * α) / 2 * ‖x - y‖ ^ 2)
    linarith
  have hsupy : 0 ≤ F y (v y) p := by
    have hψ := (hasFDerivAt_half_mul_norm_sub_sq (2 * α) x y).const_sub (u x)
    have hder : -((2 * α) • innerSL ℝ (y - x)) = p := by
      ext w
      simp [hp]
      ring
    have h := hsup.2 y hyΩ (fun w => u x - (2 * α) / 2 * ‖w - x‖ ^ 2)
      (contDiff_const.sub (contDiff_half_mul_norm_sub_sq (2 * α) x)) ?_
    · rw [hψ.fderiv, hder] at h
      exact h
    refine IsMinOn.isLocalMinOn fun w hw => ?_
    have : Φ (2 * α) (x, w) ≤ Φ (2 * α) (q (2 * α)) :=
      hqmax (2 * α) (show (x, w) ∈ K ×ˢ K from ⟨hxK, subset_closure hw⟩)
    simp only [hΦ, ← hx, ← hy] at this
    rw [norm_sub_rev x w, norm_sub_rev x y] at this
    change v y - (u x - (2 * α) / 2 * ‖y - x‖ ^ 2) ≤ v w - (u x - (2 * α) / 2 * ‖w - x‖ ^ 2)
    linarith
  -- properness at `x`, then the structure condition between `y` and `x`
  have hprop := hproper x hxK (u x) (v y) p (by linarith)
  have hγδ : γ * δ ≤ γ * (u x - v y) := mul_le_mul_of_nonneg_left (by linarith) hγ.le
  by_cases hxyeq : x = y
  · have hFeq : F y (v y) p = F x (v y) p := by rw [hxyeq]
    have := mul_pos hγ hδpos
    linarith
  · have htpos : 0 < 2 * α * ‖x - y‖ ^ 2 + ‖x - y‖ := by
      have : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxyeq)
      positivity
    have htlt : 2 * α * ‖x - y‖ ^ 2 + ‖x - y‖ < ρ := by
      have : ‖x - y‖ < ρ / 2 := hxy.trans_le (min_le_right _ _)
      linarith
    have hωt := hωρ htpos (by rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htlt)
    rw [Real.dist_eq, sub_zero] at hωt
    have hst := hstruct x hxΩ y hyΩ (v y) (2 * α) (by positivity)
    have := (abs_lt.mp hωt).2
    linarith

end MathlibExt.Analysis.ViscositySolution

namespace MathlibExt.Analysis.ViscositySolutionWanted

open Filter Topology Set MathlibExt.Analysis.ViscositySolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The compact first-order doubling argument of the user's guide, Lemma 3.1:
a positive diagonal gap yields interior maximizers with arbitrarily small modulus argument. -/
private theorem exists_interior_doubled_max [FiniteDimensional ℝ E] {Ω : Set E}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {u v : E → ℝ}
    (hu : UpperSemicontinuousOn u (closure Ω)) (hv : LowerSemicontinuousOn v (closure Ω))
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x) {z : E} (hz : z ∈ Ω)
    {δ ρ : ℝ} (hδ : 0 < δ) (hzδ : δ ≤ u z - v z) (hρ : 0 < ρ) :
    ∃ α : ℝ, 0 < α ∧ ∃ x ∈ Ω, ∃ y ∈ Ω,
      IsMaxOn (fun q : E × E => u q.1 - v q.2 - α / 2 * ‖q.1 - q.2‖ ^ 2)
        (closure Ω ×ˢ closure Ω) (x, y) ∧
      δ ≤ u x - v y ∧ α * ‖x - y‖ ^ 2 + ‖x - y‖ < ρ := by
  let K := closure Ω ×ˢ closure Ω
  have hK := hΩb.isCompact_closure.prod hΩb.isCompact_closure
  have hzK : (z, z) ∈ K := ⟨subset_closure hz, subset_closure hz⟩
  let G (q : E × E) := u q.1 - v q.2
  let d (q : E × E) := ‖q.1 - q.2‖
  have hd : Continuous d := (continuous_fst.sub continuous_snd).norm
  have hG : UpperSemicontinuousOn G K := by
    have hv' : UpperSemicontinuousOn (fun y => -v y) (closure Ω) :=
      continuous_neg.comp_lowerSemicontinuousOn_antitone hv (fun _ _ h => neg_le_neg h)
    have hfst : UpperSemicontinuousOn (fun q : E × E => u q.1) K :=
      hu.comp continuousOn_fst fun _ h => h.1
    have hsnd : UpperSemicontinuousOn (fun q : E × E => -v q.2) K :=
      hv'.comp continuousOn_snd fun _ h => h.2
    exact hfst.add hsnd
  obtain ⟨B, hB⟩ := hG.bddAbove_of_isCompact hK
  let a (n : ℕ) : ℝ := (n : ℝ) + 1
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  let Φ (n : ℕ) (q : E × E) := G q - a n * d q ^ 2
  have hΦ (n : ℕ) : UpperSemicontinuousOn (Φ n) K := by
    have hp : Continuous (fun q => -(a n * d q ^ 2)) :=
      (continuous_const.mul (hd.pow 2)).neg
    exact hG.add (hp.upperSemicontinuous.upperSemicontinuousOn K)
  have hex (n : ℕ) := (hΦ n).exists_isMaxOn ⟨(z, z), hzK⟩ hK
  choose q hq hqmax using hex
  have hgap (n : ℕ) : δ + a n * d (q n) ^ 2 ≤ G (q n) := by
    have h : G (z, z) ≤ Φ n (q n) := by
      simpa [Φ, d] using hqmax n hzK
    change G (z, z) ≤ G (q n) - a n * d (q n) ^ 2 at h
    linarith [show δ ≤ G (z, z) from hzδ]
  -- Boundedness of the unpenalized gap forces the distance between the points to zero.
  have haTop : Tendsto a atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hdSq : Tendsto (fun n => d (q n) ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => (B - δ) / a n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop haTop
    refine squeeze_zero (fun _ => sq_nonneg _) (fun n => ?_) hlim
    rw [le_div_iff₀ (ha n)]
    have h := hB (mem_image_of_mem G (hq n))
    linarith [hgap n, mul_comm (d (q n) ^ 2) (a n)]
  obtain ⟨w, hw, s, hs, hqw⟩ := hK.tendsto_subseq hq
  have hdw : d w = 0 := by
    have h : d w ^ 2 = 0 := tendsto_nhds_unique
      (((hd.pow 2).tendsto w).comp hqw) (hdSq.comp hs.tendsto_atTop)
    by_contra hne
    exact pow_ne_zero 2 hne h
  have hdiag : w.1 = w.2 := sub_eq_zero.mp (norm_eq_zero.mp hdw)
  have hqwK : Tendsto (q ∘ s) atTop (𝓝[K] w) :=
    tendsto_nhdsWithin_iff.2 ⟨hqw, Eventually.of_forall fun n => hq (s n)⟩
  have hupper {r : ℝ} (hr : G w < r) : ∀ᶠ n in atTop, G (q (s n)) < r :=
    hqwK.eventually (hG w hw r hr)
  -- Upper semicontinuity preserves the positive gap at the diagonal limit, excluding the boundary.
  have hGw : δ ≤ G w := by
    by_contra! h
    obtain ⟨n, hn⟩ := (hupper h).exists
    have hpen : 0 ≤ a (s n) * d (q (s n)) ^ 2 := mul_nonneg (ha _).le (sq_nonneg _)
    linarith [hgap (s n)]
  have hwΩ : w ∈ Ω ×ˢ Ω := by
    have hw₁ : w.1 ∈ Ω := by
      by_contra h
      have hfr : w.1 ∈ frontier Ω := by
        rw [hΩ.frontier_eq]
        exact ⟨hw.1, h⟩
      have hle := hbdry w.1 hfr
      change δ ≤ u w.1 - v w.2 at hGw
      rw [← hdiag] at hGw
      linarith
    exact ⟨hw₁, hdiag ▸ hw₁⟩
  have hinside := hqw.eventually ((hΩ.prod hΩ).mem_nhds hwΩ)
  -- Comparing with the diagonal limit itself controls even the scaled penalty.
  have hclose := (((hd.tendsto w).comp hqw).eventually
    (show ∀ᶠ t in 𝓝 (d w), t < ρ / 2 from eventually_lt_nhds (by rw [hdw]; positivity)))
  obtain ⟨n, hnΩ, hnd, hnG⟩ := (hinside.and (hclose.and
    (hupper (show G w < G w + ρ / 4 by linarith)))).exists
  let k := s n
  have hmax : G w ≤ G (q k) - a k * d (q k) ^ 2 := by
    simpa [Φ, hdw] using hqmax k hw
  have hpen : 0 ≤ a k * d (q k) ^ 2 := mul_nonneg (ha _).le (sq_nonneg _)
  refine ⟨2 * a k, by positivity, (q k).1, hnΩ.1, (q k).2, hnΩ.2, ?_, ?_, ?_⟩
  · simpa only [Φ, G, d, show 2 * a k / 2 = a k by ring] using hqmax k
  · change δ ≤ G (q k)
    linarith [hgap k]
  · change 2 * a k * d (q k) ^ 2 + d (q k) < ρ
    change d (q k) < ρ / 2 at hnd
    change G (q k) < G w + ρ / 4 at hnG
    linarith

/-- **Comparison principle for first-order equations** (Crandall and Lions 1983; Crandall, Ishii
and Lions, *User's guide*, Bull. AMS 1992, Theorem 3.3 for an `F` independent of the Hessian
variable). Let `Ω` be a bounded open subset of a finite-dimensional real inner product space and
`F` continuous on `closure Ω × ℝ × E*`, with
* (3.13) properness: `γ (r - s) ≤ F(x, r, p) - F(x, s, p)` for `r ≥ s` and `x ∈ closure Ω`,
  with `γ > 0`;
* (3.14) a modulus `ω` with `ω(0+) = 0`, `ω ≥ 0`, such that
  `F(y, r, α⟪x - y, ·⟫) - F(x, r, α⟪x - y, ·⟫) ≤ ω(α‖x - y‖² + ‖x - y‖)` for `x, y ∈ Ω`,
  `r ∈ ℝ` and `α > 0` (the matrix condition (3.10) is vacuous here, take `X = Y = 0`).
As in the printed user's guide, (3.13) is asked on `closure Ω` and (3.14) only on `Ω`.
If `u` is upper semicontinuous on `closure Ω` and a viscosity subsolution, `v` lower
semicontinuous on `closure Ω` and a viscosity supersolution of `F = 0` on `Ω`, and `u ≤ v` on
`∂Ω`, then `u ≤ v` on `Ω`. Test functions are `C¹` here and `C²` in the user's guide; a
`C¹`-tested subsolution is in particular a `C²`-tested one, so this is a special case of
Theorem 3.3. The case of continuous `u` and `v` is proved in
`MathlibExt.Analysis.ViscositySolution` as
`le_of_isViscositySubsolution_of_isViscositySupersolution_of_proper`; what remains is
semicontinuity. -/
theorem le_of_isViscositySubsolution_of_isViscositySupersolution_of_structure
    [FiniteDimensional ℝ E] {Ω : Set E} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (F : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (hF : ContinuousOn (fun q : E × ℝ × (E →L[ℝ] ℝ) => F q.1 q.2.1 q.2.2)
      (closure Ω ×ˢ univ ×ˢ univ))
    {γ : ℝ} (hγ : 0 < γ)
    (hproper : ∀ x ∈ closure Ω, ∀ r s : ℝ, ∀ p : E →L[ℝ] ℝ, s ≤ r →
      γ * (r - s) ≤ F x r p - F x s p)
    (ω : ℝ → ℝ) (hω : Tendsto ω (𝓝[>] 0) (𝓝 0)) (hω0 : ∀ t, 0 ≤ t → 0 ≤ ω t)
    (hstruct : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ r : ℝ, ∀ α : ℝ, 0 < α →
      F y r (α • innerSL ℝ (x - y)) - F x r (α • innerSL ℝ (x - y)) ≤
        ω (α * ‖x - y‖ ^ 2 + ‖x - y‖))
    {u v : E → ℝ} (hu : UpperSemicontinuousOn u (closure Ω))
    (hv : LowerSemicontinuousOn v (closure Ω))
    (hsub : IsViscositySubsolution F Ω u) (hsup : IsViscositySupersolution F Ω v)
    (hbdry : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x := by
  -- These two assumptions are retained for the statement's API, but not used in the proof.
  have _ := hF
  have _ := hω0
  intro z hz
  by_contra! hlt
  let δ := u z - v z
  have hδ : 0 < δ := sub_pos.mpr hlt
  obtain ⟨ρ, hρ, hωρ⟩ := Metric.tendsto_nhdsWithin_nhds.1 hω (γ * δ) (mul_pos hγ hδ)
  obtain ⟨α, hα, x, hx, y, hy, hmax, hgap, hsmall⟩ :=
    exists_interior_doubled_max hΩ hΩb hu hv hbdry hz hδ le_rfl hρ
  -- Fixing either coordinate gives a quadratic test with the same derivative in both tests.
  let p := α • innerSL ℝ (x - y)
  have hsubx : F x (u x) p ≤ 0 := by
    have hφ := hasFDerivAt_half_mul_norm_sub_sq α y x
    have h := hsub.2 x hx (fun w => α / 2 * ‖w - y‖ ^ 2) (contDiff_half_mul_norm_sub_sq α y) ?_
    · rwa [hφ.fderiv] at h
    refine IsMaxOn.isLocalMaxOn fun w hw => ?_
    have h := hmax (show (w, y) ∈ closure Ω ×ˢ closure Ω from
      ⟨subset_closure hw, subset_closure hy⟩)
    change u w - v y - α / 2 * ‖w - y‖ ^ 2 ≤ u x - v y - α / 2 * ‖x - y‖ ^ 2 at h
    change u w - α / 2 * ‖w - y‖ ^ 2 ≤ u x - α / 2 * ‖x - y‖ ^ 2
    linarith
  have hsupy : 0 ≤ F y (v y) p := by
    have hψ := (hasFDerivAt_half_mul_norm_sub_sq α x y).neg
    have hder : -(α • innerSL ℝ (y - x)) = p := by
      ext w
      simp [p]
      ring
    have h := hsup.2 y hy (-(fun w : E => α / 2 * ‖w - x‖ ^ 2))
      (contDiff_half_mul_norm_sub_sq α x).neg ?_
    · rwa [hψ.fderiv, hder] at h
    refine IsMinOn.isLocalMinOn fun w hw => ?_
    have h := hmax (show (x, w) ∈ closure Ω ×ˢ closure Ω from
      ⟨subset_closure hx, subset_closure hw⟩)
    change u x - v w - α / 2 * ‖x - w‖ ^ 2 ≤ u x - v y - α / 2 * ‖x - y‖ ^ 2 at h
    rw [norm_sub_rev x w, norm_sub_rev x y] at h
    change v y - -(α / 2 * ‖y - x‖ ^ 2) ≤ v w - -(α / 2 * ‖w - x‖ ^ 2)
    linarith
  have hprop := hproper x (subset_closure hx) (u x) (v y) p (by linarith)
  have hγδ : γ * δ ≤ F y (v y) p - F x (v y) p := by
    linarith [mul_le_mul_of_nonneg_left hgap hγ.le]
  by_cases hxy : x = y
  · have heq : F y (v y) p = F x (v y) p := by rw [hxy]
    linarith [mul_pos hγ hδ]
  · let t := α * ‖x - y‖ ^ 2 + ‖x - y‖
    have ht : 0 < t := add_pos_of_nonneg_of_pos (by positivity)
      (norm_pos_iff.2 (sub_ne_zero.2 hxy))
    have hωt := hωρ (show t ∈ Ioi 0 from ht)
      (show dist t 0 < ρ by rwa [Real.dist_eq, sub_zero, abs_of_pos ht])
    rw [Real.dist_eq, sub_zero] at hωt
    exact (not_lt_of_ge (hγδ.trans (hstruct x hx y hy (v y) α hα))) ((abs_lt.mp hωt).2)

end MathlibExt.Analysis.ViscositySolutionWanted
