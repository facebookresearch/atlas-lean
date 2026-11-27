/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.WirsingConstant
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.LinearCombination

/-!
# The Mayer–Roepstorff upper bound for the Wirsing constant

Every holomorphic eigenvalue of the Gauss–Kuzmin–Wirsing operator other than one has modulus at
most $0.30366327$. On the real unit interval, conjugation by the invariant density gives a
Markov operator $U$ that sends increasing functions to decreasing functions. We construct a
rational function $h$ with $h' ≥ 1$ and $(c h + U h)' ≥ 0$ for $c = 0.30366327$. For an
eigenfunction with $|λ| > c$, iterating the resulting difference estimate makes the normalized
eigenfunction constant on the interval. The identity theorem then rules out $λ ≠ 1$.

## Main results

* `norm_le_of_isHolomorphicEigenvalue`: every holomorphic eigenvalue other than one has modulus at
  most $0.30366327$.
* `bddAbove_norm_isHolomorphicEigenvalue`: the set of these moduli is bounded above.
* `mayerRoepstorffUpperBound_wanted`: the Wirsing constant is at most $0.30366327$.
-/

open Set Filter Topology
open MathlibExt.Analysis.WirsingConstant

namespace MathlibExt.Analysis.WirsingConstantWanted

noncomputable section

private abbrev I := Icc (0 : ℝ) 1

private def branch (x : ℝ) (k : ℕ) := (x + (k : ℝ) + 1)⁻¹
private def tailMass (x : ℝ) (k : ℕ) := (1 + x) / (x + (k : ℝ) + 1)
private def weight (x : ℝ) (k : ℕ) := tailMass x k - tailMass x (k + 1)

private theorem branch_mem {x : ℝ} (hx : x ∈ I) (k : ℕ) : branch x k ∈ I := by
  have hx0 := hx.1
  constructor
  · dsimp [branch]
    positivity
  · dsimp [branch]
    apply inv_le_one_of_one_le₀
    linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem branch_anti {x y : ℝ} (hx : x ∈ I) (hxy : x ≤ y) (i j : ℕ) (hij : i ≤ j) :
    branch y j ≤ branch x i := by
  have hx0 := hx.1
  apply inv_anti₀ (by positivity)
  gcongr

private theorem tail_mono {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hxy : x ≤ y) (k : ℕ) :
    tailMass x k ≤ tailMass y k := by
  have hx0 := hx.1
  have hy0 := hy.1
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (Nat.cast_nonneg (α := ℝ) k)]

private theorem weight_nonneg {x : ℝ} (hx : x ∈ I) (k : ℕ) : 0 ≤ weight x k := by
  have hx0 := hx.1
  apply sub_nonneg.mpr
  dsimp [tailMass]
  gcongr
  linarith

-- Partial sums let us compare two transition distributions before taking their limits.
private def Transfers (g G : ℝ → ℝ) : Prop :=
  ∀ x ∈ I, Tendsto (fun n => ∑ k ∈ Finset.range n, weight x k * g (branch x k))
    atTop (𝓝 (G x))

private theorem transfers_add {f F g G : ℝ → ℝ} (hf : Transfers f F) (hg : Transfers g G) :
    Transfers (fun x => f x + g x) (fun x => F x + G x) := by
  intro x hx
  simpa only [mul_add, Finset.sum_add_distrib] using (hf x hx).add (hg x hx)

private theorem transfers_mul (a : ℝ) {f F : ℝ → ℝ} (hf : Transfers f F) :
    Transfers (fun x => a * f x) (fun x => a * F x) := by
  intro x hx
  simpa only [Finset.mul_sum, mul_left_comm (weight x _) a] using (hf x hx).const_mul a

private theorem transfers_anti {g G : ℝ → ℝ} (hg : MonotoneOn g I) (hG : Transfers g G) :
    AntitoneOn G I := by
  intro x hx y hy hxy
  -- First keep the nodes at y and vary only the masses. The difference of tail masses
  -- controls the boundary term in summation by parts.
  let t (u : ℝ) (n : ℕ) := ∑ k ∈ Finset.range n, weight u k * g (branch y k)
  have hpartial (n : ℕ) :
      (tailMass y n - tailMass x n) * g (branch y n) ≤ t x n - t y n := by
    induction n with
    | zero =>
      have hx0 := hx.1
      have hy0 := hy.1
      simp [tailMass, t, add_comm 1 x, add_comm 1 y, ne_of_gt (by linarith : 0 < x + 1),
        ne_of_gt (by linarith : 0 < y + 1)]
    | succ n ih =>
      have hstep := hg (branch_mem hy (n + 1)) (branch_mem hy n)
        (branch_anti hy le_rfl _ _ (Nat.le_succ n))
      have hpos := tail_mono hx hy hxy (n + 1)
      dsimp [t] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [weight] at ih ⊢
      nlinarith [mul_nonneg (sub_nonneg.mpr hpos) (sub_nonneg.mpr hstep)]
  have hb : ∃ C : ℝ, ∀ z ∈ I, ‖g z‖ ≤ C := by
    refine ⟨|g 0| + |g 1|, fun z hz => ?_⟩
    have h₀ := hg (left_mem_Icc.mpr zero_le_one) hz hz.1
    have h₁ := hg hz (right_mem_Icc.mpr zero_le_one) hz.2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      linarith [abs_nonneg (g 0), abs_nonneg (g 1), neg_abs_le (g 0), le_abs_self (g 1)]
  obtain ⟨C, hC⟩ := hb
  have ht (u : ℝ) : Tendsto (tailMass u) atTop (𝓝 0) := by
    have hd := (tendsto_const_nhds (x := u)).add_atTop tendsto_natCast_atTop_atTop
    have h := tendsto_inv_atTop_zero.comp (hd.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    change Tendsto (fun n : ℕ => (1 + u) / (u + (n : ℝ) + 1)) _ _
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using h.const_mul (1 + u)
  have hz := (ht y).sub (ht x)
  rw [sub_zero] at hz
  have hlim := hz.zero_mul_isBoundedUnder_le
    (g := fun n => g (branch y n)) (isBoundedUnder_of_eventually_le (a := C)
      (Eventually.of_forall fun n => hC _ (branch_mem hy n)))
  have hsum (n : ℕ) : t x n ≤ ∑ k ∈ Finset.range n, weight x k * g (branch x k) := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (hg (branch_mem hy _) (branch_mem hx _)
      (branch_anti hx hxy _ _ le_rfl)) (weight_nonneg hx _)
  exact sub_nonneg.mp <| le_of_tendsto_of_tendsto' hlim ((hG x hx).sub (hG y hy))
    (fun n => (hpartial n).trans (sub_le_sub_right (hsum n) _))

-- This family is chosen so that each transfer sum telescopes to a single fraction.
private def atom (a x : ℝ) := (1 + x) / ((1 + a * x) * (1 + (a + 1) * x))
private def imageAtom (a x : ℝ) := (1 + x) / (1 + a + x)

private theorem atom_transfer (a : ℝ) (ha : 0 ≤ a) : Transfers (atom a) (imageAtom a) := by
  intro x hx
  have hx0 := hx.1
  let v (k : ℕ) := (1 + x) / (x + (k : ℝ) + 1 + a)
  have step (k : ℕ) : weight x k * atom a (branch x k) = v k - v (k + 1) := by
    dsimp [v, weight, tailMass, branch, atom]
    push_cast
    have hk := Nat.cast_nonneg (α := ℝ) k
    field_simp
    ring
  have lim : Tendsto v atTop (𝓝 0) := by
    have hd := (tendsto_const_nhds (x := x)).add_atTop tendsto_natCast_atTop_atTop
    have h := (hd.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).atTop_add
      (tendsto_const_nhds (x := a))
    exact tendsto_const_nhds.div_atTop h
  have eqn (n : ℕ) : ∑ k ∈ Finset.range n, weight x k * atom a (branch x k) = v 0 - v n := by
    simp_rw [step]
    exact Finset.sum_range_sub' v n
  simp_rw [eqn]
  simpa [v, imageAtom, add_comm, add_left_comm, add_assoc] using
    (tendsto_const_nhds (x := v 0)).sub lim

private abbrev disk := Metric.ball (1 : ℂ) (3 / 2)
private theorem real_mem_disk {x : ℝ} (hx : x ∈ I) : (x : ℂ) ∈ disk := by
  rw [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hx.1, hx.2]

private def normalized (f : ℂ → ℂ) (x : ℝ) := (1 + (x : ℂ)) * f x

private theorem eigen_transfer {f : ℂ → ℂ} {l : ℂ} (hf : DifferentiableOn ℂ f disk)
    (he : ∀ z ∈ disk, gkwOperatorHol f z = l * f z) (u : ℂ) :
    Transfers (fun x => (u * normalized f x).re) (fun x => (u * l * normalized f x).re) := by
  intro x hx
  have hcont : ContinuousOn (fun z : ℝ => f z) I :=
    hf.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun _ => real_mem_disk)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hx0 := hx.1
  have hs := summable_gkwTerm (f := fun z => ‖f z‖) (M := M) hx (by simpa using hM)
  have hnorm (k : ℕ) : ‖gkwTermHol f x k‖ = gkwTerm (fun z => ‖f z‖) x k := by
    simp only [gkwTermHol, gkwTerm, norm_mul, norm_div, norm_one, norm_pow]
    have hb : (x : ℂ) + ((k : ℂ) + 1) = ((x + (k + 1 : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hb, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    push_cast
    rfl
  have hs' : Summable (gkwTermHol f x) := Summable.of_norm (hs.congr (fun k => (hnorm k).symm))
  have hl := hs'.hasSum.tendsto_sum_nat
  change Tendsto _ _ (𝓝 (gkwOperatorHol f x)) at hl
  rw [he _ (real_mem_disk hx)] at hl
  have hc := Complex.continuous_re.continuousAt.tendsto.comp (hl.const_mul (u * (1 + (x : ℂ))))
  have step (k : ℕ) : weight x k * (u * normalized f (branch x k)).re =
      (u * (1 + (x : ℂ)) * gkwTermHol f x k).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    dsimp [weight, tailMass, normalized, branch, gkwTermHol]
    push_cast
    have h₁ : (x : ℂ) + (k : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show x + (k : ℝ) + 1 ≠ 0 by positivity)
    have h₂ : (x : ℂ) + (k + 1 : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (show x + (k + 1 : ℝ) + 1 ≠ 0 by positivity)
    rw [← add_assoc (x : ℂ) (k : ℂ) 1]
    simp only [one_div, ← add_assoc] at h₂ ⊢
    field_simp [h₁, h₂]
    ring
  simp_rw [step, ← Complex.re_sum, ← Finset.mul_sum]
  simpa only [normalized, Function.comp_def, mul_assoc, mul_left_comm l (1 + (x : ℂ))] using hc

-- Testing every real projection gives a weighted Lipschitz bound for a complex function.
private def Controls (h : ℝ → ℝ) (g : ℝ → ℂ) (K : ℝ) : Prop :=
  ∀ u : ℂ, MonotoneOn (fun x => K * ‖u‖ * h x + (u * g x).re) I

private theorem initial_control {h : ℝ → ℝ} (hh : MonotoneOn (fun x => h x - x) I)
    {g : ℝ → ℂ} {K : NNReal} (hg : LipschitzOnWith K g I) : Controls h g K := by
  intro u x hx y hy hxy
  have h₁ := hh hx hy hxy
  have h₂ := hg.norm_sub_le hx hy
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hxy)] at h₂
  have h₃ := Complex.re_le_norm (u * (g x - g y))
  rw [norm_mul, mul_sub, Complex.sub_re] at h₃
  dsimp only at h₁ h₂ h₃ ⊢
  linear_combination h₃ + ‖u‖ * h₂ + ((K : ℝ) * ‖u‖) * h₁

private theorem contract {h H : ℝ → ℝ} {c K : ℝ} {g : ℝ → ℂ} {l : ℂ}
    (hH : Transfers h H) (hm : MonotoneOn (fun x => c * h x + H x) I)
    (he : ∀ u : ℂ, Transfers (fun x => (u * g x).re) (fun x => (u * l * g x).re))
    (hl : l ≠ 0) (hK : 0 ≤ K) (hg : Controls h g K) : Controls h g (K * (c / ‖l‖)) := by
  intro u x hx y hy hxy
  let v := -u / l
  have hv : v * l = -u := div_mul_cancel₀ _ hl
  have hvn : ‖v‖ = ‖u‖ / ‖l‖ := by simp [v]
  have ha := transfers_anti (hg v) (transfers_add (transfers_mul (K * ‖v‖) hH) (he v)) hx hy hxy
  have hb := mul_le_mul_of_nonneg_left (hm hx hy hxy) (mul_nonneg hK (norm_nonneg v))
  dsimp only at ha hb ⊢
  rw [hv, hvn, neg_mul, neg_mul, Complex.neg_re, Complex.neg_re] at ha
  rw [hvn] at hb
  simp only [div_eq_mul_inv] at ha hb ⊢
  linear_combination ha + hb

private theorem control_constant {h H : ℝ → ℝ} {c : ℝ} {g : ℝ → ℂ} {l : ℂ}
    (hH : Transfers h H) (hm : MonotoneOn (fun x => c * h x + H x) I)
    (he : ∀ u : ℂ, Transfers (fun x => (u * g x).re) (fun x => (u * l * g x).re))
    (hc : 0 ≤ c) (hl : c < ‖l‖) {K : ℝ} (hK : 0 ≤ K) (hg : Controls h g K) :
    ∀ y ∈ I, g y = g 0 := by
  have hlp := hc.trans_lt hl
  have hn := norm_pos_iff.mp hlp
  let q := c / ‖l‖
  have hq : 0 ≤ q := div_nonneg hc hlp.le
  have hiter (n : ℕ) : Controls h g (K * q ^ n) := by
    induction n with
    | zero => simpa using hg
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact contract hH hm he hn (mul_nonneg hK (pow_nonneg hq _)) ih
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq ((div_lt_one hlp).mpr hl)
  intro y hy
  let u := (starRingEnd ℂ) (g 0 - g y)
  have lim (x : ℝ) : Tendsto (fun n : ℕ => K * q ^ n * ‖u‖ * h x + (u * g x).re)
      atTop (𝓝 (u * g x).re) := by
    simpa using ((((hlim.const_mul K).mul_const ‖u‖).mul_const (h x)).add_const (u * g x).re)
  have := le_of_tendsto_of_tendsto' (lim 0) (lim y) (fun n =>
    hiter n u (left_mem_Icc.mpr zero_le_one) hy hy.1)
  have hsq : (u * (g 0 - g y)).re ≤ 0 := by rwa [mul_sub, Complex.sub_re, sub_nonpos]
  dsimp only [u] at hsq
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] at hsq
  exact (sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (g 0 - g y)]))).symm

private theorem eigenvalue_bound {c : ℝ} (hc : 0 ≤ c) {h H : ℝ → ℝ} (hH : Transfers h H)
    (hh : MonotoneOn (fun x => h x - x) I) (hm : MonotoneOn (fun x => c * h x + H x) I)
    {l : ℂ} (hl : IsHolomorphicEigenvalue l) (hl₁ : l ≠ 1) : ‖l‖ ≤ c := by
  by_contra! hlt
  obtain ⟨f, hf, ⟨z, hz, hnz⟩, he⟩ := hl
  have hD : ContDiffOn ℝ 1 (fun x : ℝ => f x) I :=
    ((hf.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ).comp
      Complex.ofRealCLM.contDiff.contDiffOn (fun _ => real_mem_disk)
  have hg : ContDiffOn ℝ 1 (normalized f) I := by
    apply ContDiffOn.mul _ hD
    exact contDiffOn_const.add Complex.ofRealCLM.contDiff.contDiffOn
  obtain ⟨K, hK⟩ := hg.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hconst := control_constant hH hm (eigen_transfer hf he) hc hlt K.2 (initial_control hh hK)
  have htrans (u : ℂ) : (u * l * normalized f 0).re = (u * normalized f 0).re := by
    have h₀ : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
    have hsum := eigen_transfer hf he u 0 h₀
    have hcst := transfers_mul (u * normalized f 0).re (atom_transfer 0 le_rfl) 0 h₀
    apply tendsto_nhds_unique hsum
    convert hcst using 2 with n
    · apply Finset.sum_congr rfl
      intro k _
      dsimp only
      rw [hconst _ (branch_mem h₀ k)]
      have hb := (branch_mem h₀ k).1
      simp [atom, div_self (show 1 + branch 0 k ≠ 0 by positivity)]
    · simp [imageAtom]
  have hz₀ : normalized f 0 = 0 := by
    let w := l * normalized f 0 - normalized f 0
    have hw : (((starRingEnd ℂ) w) * w).re = 0 := by
      simpa only [w, mul_sub, ← mul_assoc, Complex.sub_re, sub_eq_zero] using
        (htrans ((starRingEnd ℂ) w))
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] at hw
    have hzero : w = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg w])
    have hp : (l - 1) * normalized f 0 = 0 := by simpa [w, sub_mul] using hzero
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hl₁)
  have hreal (y : ℝ) (hy : y ∈ I) : f y = 0 := by
    have hfy := (hconst y hy).trans hz₀
    apply (mul_eq_zero.mp hfy).resolve_left
    exact_mod_cast (show 1 + y ≠ 0 by linarith [hy.1])
  apply hnz
  refine (hf.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_mem_closure
    (convex_ball _ _).isPreconnected (z₀ := 0)
    (by simpa using real_mem_disk (x := 0) ⟨le_rfl, zero_le_one⟩) ?_ hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, hy₀, hy⟩ := exists_between (lt_min hε zero_lt_one)
  refine ⟨(y : ℂ), ⟨hreal y ⟨hy₀.le, (lt_min_iff.mp hy).2.le⟩, ?_⟩, ?_⟩
  · simpa using hy₀.ne'
  · simpa [dist_zero_right, Real.norm_of_nonneg hy₀.le] using (lt_min_iff.mp hy).1

private def atomSlope (a x : ℝ) :=
  a * (2 + 2 * (1 + a) * x + (1 + a) * x ^ 2) / (((1 + a * x) * (1 + (a + 1) * x)) ^ 2)

private def imageSlope (a x : ℝ) := a / (1 + a + x) ^ 2

private theorem atom_deriv {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (atom a) (-atomSlope a x) x := by
  unfold atom
  convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).div
    (((hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul a)).mul
      ((hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul (a + 1)))) (by dsimp; positivity)
    using 1
  · rfl
  · dsimp [atomSlope]
    ring

private theorem image_deriv {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (imageAtom a) (imageSlope a x) x := by
  unfold imageAtom
  convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).div
    ((hasDerivAt_const x (1 + a)).add (hasDerivAt_id x)) (by dsimp; positivity) using 1
  · rfl
  · dsimp [imageSlope]
    ring

private abbrev Terms := List (ℕ × ℤ)

private def mixture (L : Terms) (f : ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  (L.map fun (i, c) => (c : ℝ) * f ((i : ℝ) / 10) x).sum

private theorem mixture_transfer (L : Terms) :
    Transfers (mixture L atom) (mixture L imageAtom) := by
  induction L with
  | nil => intro x _; simp [mixture]
  | cons p L ih =>
    exact transfers_add (transfers_mul p.2 (atom_transfer ((p.1 : ℝ) / 10) (by positivity))) ih

private theorem mixture_deriv {f f' : ℝ → ℝ → ℝ} {x : ℝ}
    (hf : ∀ a, 0 ≤ a → HasDerivAt (f a) (f' a x) x) (L : Terms) :
    HasDerivAt (mixture L f) (mixture L f' x) x := by
  induction L with
  | nil => exact hasDerivAt_const x 0
  | cons p L ih => exact ((hf _ (by positivity)).const_mul (p.2 : ℝ)).add ih

-- After x = t/(1+t), all denominators are positive for t ≥ 0.
private theorem chart_atom {i t : ℝ} (hi : 0 ≤ i) (ht : 0 ≤ t) :
    atomSlope (i / 10) (t / (1 + t)) =
      100 * i * (20 * (1 + t) ^ 2 + 2 * (10 + i) * t * (1 + t) + (10 + i) * t ^ 2) * (1 + t) ^ 2 /
        ((10 + (10 + i) * t) ^ 2 * (10 + (20 + i) * t) ^ 2) := by
  unfold atomSlope
  field_simp
  ring

private theorem chart_image {i t : ℝ} (hi : 0 ≤ i) (ht : 0 ≤ t) :
    imageSlope (i / 10) (t / (1 + t)) = 10 * i * (1 + t) ^ 2 / ((10 + i) + (20 + i) * t) ^ 2 := by
  unfold imageSlope
  field_simp
  ring

-- For i = 1, …, 9 use the atom with parameter i/10. These weights were obtained by setting
-- the slope residual c ∑ wᵢ atomSlopeᵢ − ∑ wᵢ imageSlopeᵢ equal to 1 at x = j/8,
-- j = 0, …, 8, then multiplying the solution by 10000 and rounding. Only the two exact
-- polynomial sign checks below use the weights.
private def certificate : Terms :=
  [(1, -149273123070), (2, 2471521657455), (3, -15610099603032),
   (4, 53562758954219), (5, -110685744547367), (6, 140712471171648),
   (7, -106449797047200), (8, 43792918793402), (9, -7542278028500)]

private theorem chart_parameter {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∃ t : ℝ, 0 ≤ t ∧ x = t / (1 + t) := by
  have hx₀ := hx.1
  have hx₁ := sub_pos.mpr hx.2
  refine ⟨x / (1 - x), by positivity, ?_⟩
  field_simp
  ring

-- Clearing the positive denominators leaves a polynomial with nonnegative coefficients in t.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Expanding the nine rational derivatives produces a degree-36 numerator.
private theorem certificate_increasing {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 ≤ mixture certificate atomSlope x := by
  obtain ⟨t, ht, rfl⟩ := chart_parameter hx
  apply sub_nonneg.mp
  simp (disch := positivity) only [mixture, certificate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, chart_atom]
  norm_num1
  field_simp
  ring_nf
  positivity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Clearing both sets of denominators gives a degree-54 polynomial sign check.
private theorem certificate_residual {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ mixture certificate
      (fun a y => 30366327 * atomSlope a y - 100000000 * imageSlope a y) x := by
  obtain ⟨t, ht, rfl⟩ := chart_parameter hx
  simp (disch := positivity) only [mixture, certificate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, chart_atom, chart_image]
  norm_num1
  field_simp
  ring_nf
  positivity

private theorem mixture_cons (p : ℕ × ℤ) (L : Terms) (f : ℝ → ℝ → ℝ) (x : ℝ) :
    mixture (p :: L) f x = (p.2 : ℝ) * f ((p.1 : ℝ) / 10) x + mixture L f x := rfl

private theorem mixture_linear (L : Terms) (f g : ℝ → ℝ → ℝ) (r s x : ℝ) :
    mixture L (fun a y => r * f a y - s * g a y) x = r * mixture L f x - s * mixture L g x := by
  induction L with
  | nil => simp [mixture]
  | cons p L ih =>
    simp only [mixture_cons, ih]
    ring

/-- **Mayer–Roepstorff bound for each holomorphic eigenvalue.** Every holomorphic eigenvalue
$\lambda \ne 1$ of the Gauss–Kuzmin–Wirsing operator on the Mayer disk
$\{z \in \mathbb{C} : |z - 1| < 3/2\}$ satisfies $|\lambda| \le 0.30366327$.

Source: Mayer and Roepstorff (1987), eq. (5.20), catalogue upper
bound `0.30366327`. -/
public theorem norm_le_of_isHolomorphicEigenvalue {l : ℂ} (hl : IsHolomorphicEigenvalue l)
    (hl₁ : l ≠ 1) : ‖l‖ ≤ (30366327 / 100000000 : ℝ) := by
  let c : ℝ := 30366327 / 100000000
  let h x := -mixture certificate atom x
  let H x := -mixture certificate imageAtom x
  have hneg (L : Terms) (x : ℝ) : mixture L (fun a y => -atomSlope a y) x =
      -mixture L atomSlope x := by
    induction L with
    | nil => simp [mixture]
    | cons p L ih => simp [mixture_cons, ih, add_comm]
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt h (mixture certificate atomSlope x) x := by
    have he := (mixture_deriv (f' := fun a y => -atomSlope a y)
      (fun a ha => atom_deriv ha hx) certificate).neg
    rw [hneg, neg_neg] at he
    exact he
  have hD (x : ℝ) (hx : 0 ≤ x) : HasDerivAt H (-mixture certificate imageSlope x) x :=
    (mixture_deriv (f' := imageSlope) (fun a ha => image_deriv ha hx) certificate).neg
  apply eigenvalue_bound (h := h) (H := H) (by norm_num) _ _ _ hl hl₁
  · simpa only [neg_one_mul] using transfers_mul (-1) (mixture_transfer certificate)
  · apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun x hx => ((hd _ hx.1).sub (hasDerivAt_id x)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hd _ hx.1.le).sub (hasDerivAt_id x)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv (h - id) x
      rw [((hd _ hx.1.le).sub (hasDerivAt_id x)).deriv]
      exact sub_nonneg.mpr (certificate_increasing hx)
  · have hder (x : ℝ) (hx : 0 ≤ x) := ((hd _ hx).const_mul c).add (hD _ hx)
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun x hx => (hder _ hx.1).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hder _ hx.1.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      change 0 ≤ deriv ((fun z => c * h z) + H) x
      rw [(hder _ hx.1.le).deriv]
      have hres := certificate_residual hx
      rw [mixture_linear] at hres
      dsimp [c]
      linarith only [hres]

end

/-- **The holomorphic eigenvalue moduli are bounded above.** The set of moduli $|\lambda|$ of the
holomorphic eigenvalues $\lambda \ne 1$ of the Gauss–Kuzmin–Wirsing operator on the Mayer disk
$\{z \in \mathbb{C} : |z - 1| < 3/2\}$, whose supremum defines the Wirsing constant, is bounded
above.

Source: Mayer and Roepstorff (1987), eq. (5.20), catalogue upper
bound `0.30366327`. -/
public theorem bddAbove_norm_isHolomorphicEigenvalue :
    BddAbove {r : ℝ | ∃ lam : ℂ, IsHolomorphicEigenvalue lam ∧ lam ≠ 1 ∧ r = ‖lam‖} := by
  refine ⟨30366327 / 100000000, ?_⟩
  rintro _ ⟨l, hl, hl₁, rfl⟩
  exact norm_le_of_isHolomorphicEigenvalue hl hl₁

/-- **Mayer–Roepstorff upper bound for the Wirsing constant.** The
Wirsing constant is at most $0.30366327$.

Source: Mayer and Roepstorff (1987), eq. (5.20), catalogue upper
bound `0.30366327`. -/
public theorem mayerRoepstorffUpperBound_wanted :
    wirsingConstant ≤ (30366327 / 100000000 : ℝ) := by
  apply Real.sSup_le _ (by norm_num)
  rintro _ ⟨l, hl, hl₁, rfl⟩
  exact norm_le_of_isHolomorphicEigenvalue hl hl₁

end MathlibExt.Analysis.WirsingConstantWanted
