/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import MathlibExt.NumberTheory.DiophantineApproximation.WeylCriterion
import MathlibExt.Combinatorics.Additive.Sarkozy

/-!
# Square roots of square pyramidal numbers

The distance from the square root of a square pyramidal number to the nearest integer
is uniformly distributed on the interval from zero to one half.

For each fixed positive lag, the difference of the two square roots is a nonzero multiple
of √n up to an error tending to zero. Telescoping the weighted phases of √n gives vanishing
correlations. The van der Corput lemma and Weyl’s criterion then give uniform distribution
modulo one, and folding the unit interval gives the distribution of the distances.
-/

open Filter Topology
namespace MetaMathlibExt

@[expose] public section

/-- **Square pyramidal number.** For a natural number $n$, the $n$-th square pyramidal number
is $P_n = 1^2 + 2^2 + \dots + n^2 = \sum_{i=1}^{n} i^2$ (so $P_0 = 0$).

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, equation (defn: square pyramidal number) of arXiv:2412.10097v2. -/
def squarePyramidalNumber (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc 1 n, i ^ 2

/-- **Distance from a square pyramidal number to the nearest square.** For a natural number
$n$, let $P_n$ be the $n$-th square pyramidal number and $s = \lfloor \sqrt{P_n} \rfloor$. The
distance from $P_n$ to the nearest square is
$$a_n = \min\bigl(P_n - s^2, (s + 1)^2 - P_n\bigr).$$
Since $s^2 \le P_n < (s + 1)^2$, this is $a_n = |P_n - y_n^2|$, where $y_n^2$ is the square
nearest to $P_n$.

No ties occur, since the midpoint $m^2 + m + 1/2$ of two consecutive squares is never an integer.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, equation (a_n first definition) of arXiv:2412.10097v2 (OEIS A351830). -/
def squarePyramidalSquareDistance (n : ℕ) : ℕ :=
  min (squarePyramidalNumber n - Nat.sqrt (squarePyramidalNumber n) ^ 2)
    ((Nat.sqrt (squarePyramidalNumber n) + 1) ^ 2 - squarePyramidalNumber n)

/-- **Small square pyramidal numbers and their distances to squares.** Let $P_n$ be the $n$-th
square pyramidal number and $a_n$ the distance from $P_n$ to the nearest square. Then
$P_1, P_2, P_3, P_4$ are $1, 5, 14, 30$; $a_2 = 1$ (since $P_2 = 5$ and the nearest square is
$4$); $P_{24} = 4900 = 70^2$; and $a_{24} = 0$ (the cannonball solution).

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Introduction. -/
theorem squarePyramidalSquareDistance_examples :
    (List.range 4).map (fun i => squarePyramidalNumber (i + 1)) = [1, 5, 14, 30] ∧
      squarePyramidalSquareDistance 2 = 1 ∧ squarePyramidalNumber 24 = 4900 ∧
      squarePyramidalSquareDistance 24 = 0 := by
  have h2 : squarePyramidalNumber 2 = 5 := by decide
  have h24 : squarePyramidalNumber 24 = 4900 := by decide
  have s2 : Nat.sqrt 5 = 2 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  have s24 : Nat.sqrt 4900 = 70 := (Nat.eq_sqrt.2 ⟨by norm_num, by norm_num⟩).symm
  refine ⟨by decide, ?_, h24, ?_⟩ <;> simp [squarePyramidalSquareDistance, h2, h24, s2, s24]

namespace squarePyramidal_dist_nearest_square_root_equidistributed

private theorem nearest {p y : ℕ}
    (hy : ∀ z : ℕ, |(p : ℤ) - (y : ℤ) ^ 2| ≤ |(p : ℤ) - (z : ℤ) ^ 2|) :
    round (Real.sqrt p) = (y : ℤ) := by
  have hu := hy (y + 1)
  push_cast at hu
  have hu' : (p : ℤ) ≤ (y : ℤ) ^ 2 + y := by
    by_contra! h
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (p : ℤ) - (y : ℤ) ^ 2)] at hu
    rw [le_abs'] at hu
    rcases hu with h | h <;> nlinarith
  have huR : (p : ℝ) ≤ (y : ℝ) ^ 2 + y := by exact_mod_cast hu'
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  apply round_eq_iff.mpr
  push_cast
  constructor
  · cases y with
    | zero => simp; linarith [Real.sqrt_nonneg (p : ℝ)]
    | succ k =>
      have hl := hy k
      push_cast at hl
      have hl' : (k : ℤ) ^ 2 + k + 1 ≤ p := by
        by_contra! h
        rw [abs_of_nonpos (by nlinarith : (p : ℤ) - ((k : ℤ) + 1) ^ 2 ≤ 0)] at hl
        rw [le_abs'] at hl
        rcases hl with h | h <;> nlinarith
      have hlR : (k : ℝ) ^ 2 + k + 1 ≤ p := by exact_mod_cast hl'
      push_cast
      by_contra! h
      nlinarith [mul_self_le_mul_self (Real.sqrt_nonneg (p : ℝ)) h.le]
  · by_contra! h
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ (y : ℝ) + 1 / 2) h]

private theorem pyramid_eq (n : ℕ) :
    (squarePyramidalNumber n : ℝ) = n * ((n : ℝ) + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp [squarePyramidalNumber]
  | succ n ih =>
    rw [squarePyramidalNumber, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    change ((squarePyramidalNumber n + (n + 1) ^ 2 : ℕ) : ℝ) = _
    push_cast
    rw [ih]
    ring

private noncomputable def lead : ℝ := Real.sqrt (1 / 3)

private noncomputable def root (n : ℕ) : ℝ := Real.sqrt (squarePyramidalNumber n)

/-- Expand the shifted cubic root through its term of order √n. Rationalizing the
difference leaves a linear numerator and a denominator of order n√n. -/
private theorem root_expansion (k : ℕ) :
    Tendsto (fun n : ℕ => root (n + k) -
      lead * Real.sqrt n * (n + (3 * (k : ℝ) / 2 + 3 / 4))) atTop (𝓝 0) := by
  let A : ℝ := 3 * (k : ℝ) / 2 + 3 / 4
  let B : ℝ := (k : ℝ) ^ 2 + k + 1 / 6 - A ^ 2 / 3
  let C : ℝ := k * ((k : ℝ) + 1) * (2 * k + 1) / 6
  have hL : 0 < lead := Real.sqrt_pos.2 (by norm_num)
  have hL2 : lead ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hlim : Tendsto (fun n : ℕ => (|B| + |C|) / (lead * Real.sqrt n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hL)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  let u := root (n + k)
  let v := lead * Real.sqrt n * (n + A)
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hu : u ^ 2 = ((n : ℝ) + k) * ((n : ℝ) + k + 1) * (2 * ((n : ℝ) + k) + 1) / 6 := by
    rw [show u = Real.sqrt _ from rfl, Real.sq_sqrt (Nat.cast_nonneg _), pyramid_eq, Nat.cast_add]
  have hv : v ^ 2 = (1 / 3) * n * (n + A) ^ 2 := by simp only [v, mul_pow, hL2, hs]
  have hid : (u - v) * (u + v) = B * n + C := by
    rw [mul_comm, ← sq_sub_sq, hu, hv]
    dsimp [A, B, C]
    ring
  have hden : lead * Real.sqrt n * n ≤ u + v := by
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hA : 0 ≤ A := by dsimp [A]; positivity
    dsimp [v]
    rw [mul_add]
    linarith [mul_nonneg (mul_nonneg hL.le (Real.sqrt_nonneg (n : ℝ))) hA]
  have hmul : |u - v| * (lead * Real.sqrt n * n) ≤ (|B| + |C|) * n := calc
    _ ≤ |u - v| * |u + v| := by gcongr; exact hden.trans (le_abs_self _)
    _ = |B * n + C| := by rw [← abs_mul, hid]
    _ ≤ |B| * n + |C| := by simpa [abs_mul] using abs_add_le (B * n) C
    _ ≤ _ := by rw [add_mul]; gcongr; exact le_mul_of_one_le_right (abs_nonneg C) hx
  change |u - v| ≤ _
  apply (le_div_iff₀ (mul_pos hL (Real.sqrt_pos.2 (by linarith)))).mpr
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < n by linarith)).mp
  simpa [mul_assoc] using hmul

private theorem root_difference (k : ℕ) :
    Tendsto (fun n : ℕ => root (n + k + 1) - root (n + 1) -
      (lead * (3 * k / 2)) * Real.sqrt n) atTop (𝓝 0) := by
  convert (root_expansion (k + 1)).sub (root_expansion 1) using 1
  · funext n
    push_cast
    rw [Nat.add_assoc]
    ring
  · norm_num

private noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

private lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

private lemma mul_phase_zero {f g : ℕ → ℂ} (hf : Tendsto f atTop (𝓝 0))
    (hg : ∀ n, ‖g n‖ = 1) : Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul, hg, mul_one] using (tendsto_zero_iff_norm_tendsto_zero.mp hf)

private noncomputable def mean (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f n

private lemma mean_zero {f : ℕ → ℂ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (mean f) atTop (𝓝 0) := by
  unfold mean
  simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    using hf.cesaro_smul

/-- The Fourier averages of √n vanish. With δₙ = √(n + 1) − √n, the weighted
difference of consecutive phases is a difference quotient for the exponential. -/
private lemma mean_phase_sqrt (c : ℝ) (hc : c ≠ 0) :
    Tendsto (mean (fun n => phase (c * Real.sqrt n))) atTop (𝓝 0) := by
  let s (n : ℕ) := Real.sqrt (n : ℝ)
  let δ (n : ℕ) := s (n + 1) - s n
  let w (n : ℕ) := s (n + 1) + s n
  let e (n : ℕ) := phase (c * s n)
  let z : ℂ := c * Complex.I
  have hδpos (n) : 0 < δ n :=
    sub_pos.mpr (Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast n.lt_succ_self))
  have hid (n) : δ n * w n = 1 := by
    change (s (n + 1) - s n) * (s (n + 1) + s n) = 1
    rw [mul_comm, ← sq_sub_sq]
    dsimp [s]
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hδinv (n) : δ n = (w n)⁻¹ := eq_inv_of_mul_eq_one_left (hid n)
  have hs : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simp_rw [show δ = fun n => (w n)⁻¹ from funext hδinv]
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun n =>
      le_add_of_nonneg_left (Real.sqrt_nonneg _)) hs)
  have hdw : Tendsto (fun n => w (n + 1) - w n) atTop (𝓝 0) := by
    convert (hδ.comp (tendsto_add_atTop_nat 1)).add hδ using 1
    · funext n
      dsimp [w, δ]
      ring
    · simp
  have hder : HasDerivAt (fun t : ℂ => Complex.exp (t * z)) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const z).cexp
  have hquot : Tendsto (fun n => (Complex.exp ((δ n : ℂ) * z) - 1) / (δ n : ℂ))
      atTop (𝓝 z) := by
    have hδ' : Tendsto (fun n => (δ n : ℂ)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa using hδ.ofReal,
        Eventually.of_forall (fun n => by simpa using (hδpos n).ne')⟩
    simpa [Function.comp_def, slope_def_field] using hder.tendsto_slope.comp hδ'
  have hstep (n) : e (n + 1) = phase (c * δ n) * e n := by
    change phase _ = phase _ * phase _
    rw [← phase_add]
    congr 1
    dsimp [δ]
    ring
  have herr : Tendsto (fun n => (w (n + 1) : ℂ) * e (n + 1) - (w n : ℂ) * e n - z * e n)
      atTop (𝓝 0) := by
    have h₁ := mul_phase_zero (by simpa using hdw.ofReal)
      (fun n => norm_phase (c * s (n + 1)))
    have h₂ := mul_phase_zero (tendsto_sub_nhds_zero_iff.mpr hquot)
      (fun n => norm_phase (c * s n))
    convert h₁.add h₂ using 1
    · funext n
      change _ = ((w (n + 1) : ℂ) - (w n : ℂ)) * e (n + 1) +
        ((Complex.exp ((δ n : ℂ) * z) - 1) / (δ n : ℂ) - z) * e n
      have hinv : ((δ n : ℂ))⁻¹ = (w n : ℂ) := by
        rw [hδinv, Complex.ofReal_inv, inv_inv]
      have hexp : Complex.exp ((δ n : ℂ) * z) = phase (c * δ n) := by
        dsimp [z, phase]
        push_cast
        ring_nf
      rw [hstep, div_eq_mul_inv, hinv, hexp]
      ring
    · simp
  -- The average of these weighted differences telescopes to a vanishing boundary term.
  let F (n : ℕ) : ℂ := (w n : ℂ) * e n
  have hbound : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * w n) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n : ℕ => s n / n) atTop (𝓝 0) := by
      simpa only [s, Real.sqrt_div_self, Function.comp_def] using tendsto_inv_atTop_zero.comp hs
    have h₂ := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).mul hδ
    convert (h₁.add h₁).add h₂ using 1
    · funext n
      dsimp [s, w, δ, Function.comp_def]
      ring
    · simp
  have hF : Tendsto (mean (fun n => F (n + 1) - F n)) atTop (𝓝 0) := by
    have h₁ := mul_phase_zero (by simpa using hbound.ofReal) (fun n => norm_phase (c * s n))
    have h₂ := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).ofReal
    convert h₁.sub (h₂.mul_const (F 0)) using 1
    · funext n
      rw [mean, Finset.sum_range_sub F]
      simp only [F, e, Function.comp_apply, Complex.ofReal_inv, Complex.ofReal_natCast]
      ring
    · simp
  have hscaled := hF.sub (mean_zero herr)
  have hz : z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hc) Complex.I_ne_zero
  convert hscaled.const_mul z⁻¹ using 1
  · funext n
    simp only [mean, Finset.sum_sub_distrib, ← Finset.mul_sum, F, e]
    field_simp
    ring
  · simp

private lemma mean_phase_difference (c : ℝ) (hc : c ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (mean (fun n => phase (c * (root (n + k + 1) - root (n + 1))))) atTop (𝓝 0) := by
  let b : ℝ := lead * (3 * k / 2)
  let t (n : ℕ) := b * Real.sqrt n
  let r (n : ℕ) := root (n + k + 1) - root (n + 1) - t n
  have hr : Tendsto r atTop (𝓝 0) := root_difference k
  have hph : Continuous phase := by unfold phase; fun_prop
  have he : Tendsto (fun n => phase (c * r n) - 1) atTop (𝓝 0) := by
    simpa [Function.comp_def, phase] using
      ((hph.tendsto _).comp (hr.const_mul c)).sub (tendsto_const_nhds (x := (1 : ℂ)))
  have herr := mean_zero (mul_phase_zero he (fun n => norm_phase (c * t n)))
  have hb : b ≠ 0 := by
    have : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
    have : 0 < lead := Real.sqrt_pos.2 (by norm_num)
    dsimp [b]
    positivity
  convert herr.add (mean_phase_sqrt (c * b) (mul_ne_zero hc hb)) using 1
  · funext N
    simp only [mean, sub_mul, one_mul, Finset.sum_sub_distrib]
    have hterm (n : ℕ) : phase (c * (root (n + k + 1) - root (n + 1))) =
        phase (c * r n) * phase (c * t n) := by
      rw [← phase_add]
      congr 1
      dsimp [r]
      ring
    simp only [hterm, t, mul_assoc]
    ring
  · simp

private lemma inner_phase (x y : ℝ) :
    inner ℝ (phase x) (phase y) = (phase (x - y)).re := by
  rw [real_inner_comm, real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  simp only [RCLike.re_to_complex, phase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_add, Complex.ofReal_sub]
  congr 2
  ring

private theorem uniform_fract :
    ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      Tendsto (fun N : ℕ =>
        ((Finset.range N).filter (fun n => a ≤ Int.fract (root (n + 1)) ∧
          Int.fract (root (n + 1)) < b)).card / (N : ℝ)) atTop (𝓝 (b - a)) := by
  apply (weyl_criterion (fun n => root (n + 1))).mpr
  intro h hh
  let c : ℝ := 2 * Real.pi * h
  have hc : c ≠ 0 := by dsimp [c]; exact mul_ne_zero (by positivity) (Int.cast_ne_zero.mpr hh)
  let e (n : ℕ) := phase (c * root (n + 1))
  have he := MathlibExt.Combinatorics.Additive.SarkozyWanted.sarkozy_vdc_tendsto
    e 1 zero_le_one (fun n => (norm_phase _).le) (fun k hk => ?_)
  · simpa [e, phase, c, one_div, Complex.real_smul] using he
  · have H := (Complex.continuous_re.tendsto 0).comp (mean_phase_difference c hc k hk)
    simp only [Function.comp_def, mean, Complex.zero_re, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, Complex.re_ofReal_mul, Complex.re_sum] at H
    simpa only [e, inner_phase, ← mul_sub] using H

private noncomputable def freq (p : ℕ → Prop) (N : ℕ) : ℝ := by
  classical exact ((Finset.range N).filter p).card / (N : ℝ)

private lemma freq_mono {p q : ℕ → Prop} (h : ∀ n, p n → q n) (N : ℕ) :
    freq p N ≤ freq q N := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_le_card ((Finset.range N).monotone_filter_right (fun n _ => h n))

private lemma freq_diff {p q : ℕ → Prop} (h : ∀ n, q n → p n) (N : ℕ) :
    freq (fun n => p n ∧ ¬q n) N = freq p N - freq q N := by
  classical
  have hsub := (Finset.range N).monotone_filter_right (fun n _ => h n)
  have he : (Finset.range N).filter (fun n => p n ∧ ¬q n) =
      (Finset.range N).filter p \ (Finset.range N).filter q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  unfold freq
  rw [Finset.filter_congr_decidable (Finset.range N) (fun n => p n ∧ ¬q n)
    (fun n => Classical.propDecidable _), he, Finset.card_sdiff_of_subset hsub,
    Nat.cast_sub (Finset.card_le_card hsub), sub_div]

private noncomputable def frac (n : ℕ) : ℝ := Int.fract (root (n + 1))

private lemma freq_lt (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Tendsto (freq (fun n => frac n < t)) atTop (𝓝 t) := by
  classical
  unfold freq
  rcases h0.eq_or_lt with rfl | ht
  · simp [frac, not_lt_of_ge (Int.fract_nonneg _)]
  · convert uniform_fract 0 t le_rfl ht h1 using 1
    · funext N
      congr 2
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro n _
      simp [frac, Int.fract_nonneg]
    · simp

private lemma freq_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Tendsto (freq (fun n => frac n ≤ t)) atTop (𝓝 t) := by
  rcases h1.eq_or_lt with rfl | ht
  · simpa [frac, Int.fract_lt_one, (Int.fract_lt_one _).le] using freq_lt 1 zero_le_one le_rfl
  refine tendsto_order.mpr ⟨fun l hl => ?_, fun u hu => ?_⟩
  · filter_upwards [(tendsto_order.mp (freq_lt t h0 ht.le)).1 l hl] with N hN
    exact hN.trans_le (freq_mono (fun n (h : frac n < t) => h.le) N)
  · obtain ⟨v, htv, hv⟩ := exists_between (lt_min hu ht)
    filter_upwards [(tendsto_order.mp (freq_lt v (h0.trans htv.le) (lt_min_iff.mp hv).2.le)).2
      u (lt_min_iff.mp hv).1] with N hN
    exact lt_of_le_of_lt (freq_mono (fun n (h : frac n ≤ t) => h.trans_lt htv) N) hN

/-- The folded distance belongs to [a,b] precisely on the closed central interval
[a,1−a] with the open central interval (b,1−b) removed. -/
private lemma freq_fold (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1 / 2) :
    Tendsto (freq (fun n => min (frac n) (1 - frac n) ∈ Set.Icc a b))
      atTop (𝓝 (2 * (b - a))) := by
  let outer (n : ℕ) := a ≤ frac n ∧ frac n ≤ 1 - a
  let inner (n : ℕ) := b < frac n ∧ frac n < 1 - b
  have hout : Tendsto (freq outer) atTop (𝓝 (1 - a - a)) := by
    convert (freq_le (1 - a) (by linarith) (by linarith)).sub
      (freq_lt a ha (by linarith)) using 1
    funext N
    rw [← freq_diff (p := fun n => frac n ≤ 1 - a) (q := fun n => frac n < a)
      (fun n h => by linarith)]
    simp only [outer, not_lt, and_comm]
  have hin : Tendsto (freq inner) atTop (𝓝 (1 - b - b)) := by
    rcases hb.eq_or_lt with rfl | hb'
    · have he : inner = fun _ => False := by
        funext n
        dsimp [inner]
        apply propext
        constructor
        · rintro ⟨h, h'⟩
          linarith
        · simp
      rw [he]
      unfold freq
      norm_num
    · convert (freq_lt (1 - b) (by linarith) (by linarith)).sub
        (freq_le b (by linarith) (by linarith)) using 1
      funext N
      rw [← freq_diff (p := fun n => frac n < 1 - b) (q := fun n => frac n ≤ b)
        (fun n h => by linarith)]
      simp only [inner, not_le, and_comm]
  convert hout.sub hin using 1
  · funext N
    rw [← freq_diff (fun n (h : inner n) => show outer n by
      obtain ⟨hl, hu⟩ := h
      exact ⟨by linarith, by linarith⟩)]
    congr 1
    funext n
    simp only [outer, inner, Set.mem_Icc, le_min_iff, min_le_iff]
    grind
  · congr 1
    ring

end squarePyramidal_dist_nearest_square_root_equidistributed

open squarePyramidal_dist_nearest_square_root_equidistributed in
/-- **The distance from the square root of a square pyramidal number to the nearest integer is
uniformly distributed.** Let $P_n$ be the $n$-th square pyramidal number, write
$\|x\| = |x - \operatorname{round}(x)|$ for the distance from a real $x$ to the nearest integer,
and let $(y_n)_{n \ge 0}$ be natural numbers such that $|P_n - y_n^2| \le |P_n - z^2|$ for all
natural numbers $n$ and $z$ (so $y_n^2$ is a square nearest to $P_n$). Put
$d_n = |\sqrt{P_n} - y_n|$. Then $d_n = \|\sqrt{P_n}\|$ and $d_n \le 1/2$ for every $n \ge 0$,
and $(d_n)_{n \ge 1}$ is uniformly distributed in $[0, 1/2]$: for all real $\alpha, \beta$ with
$0 \le \alpha < \beta \le 1/2$,
$$\lim_{N \to \infty} \frac{1}{N}
\#\{1 \le n \le N : \alpha \le d_n \le \beta\} = 2(\beta - \alpha).$$

The source shows that $y_n$ is unique, and takes the limit over real $x \to \infty$, which is
equivalent to the limit along integers $N$.

Source: Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution
Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29
(2026), Article 26.5.5, Proposition 9 (`jis-2026-26.5.5-prop-9`). -/
theorem squarePyramidal_dist_nearest_square_root_equidistributed (y : ℕ → ℕ)
    (hy : ∀ n z : ℕ, |(squarePyramidalNumber n : ℤ) - (y n : ℤ) ^ 2| ≤
      |(squarePyramidalNumber n : ℤ) - (z : ℤ) ^ 2|) :
    (∀ n : ℕ, |Real.sqrt (squarePyramidalNumber n) - y n| =
        |Real.sqrt (squarePyramidalNumber n) - round (Real.sqrt (squarePyramidalNumber n))| ∧
      |Real.sqrt (squarePyramidalNumber n) - y n| ≤ 1 / 2) ∧
    ∀ α β : ℝ, 0 ≤ α → α < β → β ≤ 1 / 2 →
      Tendsto (fun N : ℕ =>
        ((Finset.filter (fun n : ℕ => |Real.sqrt (squarePyramidalNumber n) - y n| ∈ Set.Icc α β)
          (Finset.Icc 1 N)).card : ℝ) / (N : ℝ)) atTop (nhds (2 * (β - α))) := by
  have hr (n : ℕ) := nearest (hy n)
  have he (n : ℕ) : |Real.sqrt (squarePyramidalNumber n) - y n| =
      |Real.sqrt (squarePyramidalNumber n) - round (Real.sqrt (squarePyramidalNumber n))| := by
    rw [hr]
    norm_cast
  refine ⟨fun n => ⟨he n, (he n).trans_le (abs_sub_round _)⟩, ?_⟩
  intro a b ha hab hb
  apply (freq_fold a b ha hab hb).congr
  intro N
  unfold freq
  rw [Finset.filter_congr_decidable _ (fun n => min (frac n) (1 - frac n) ∈ Set.Icc a b)
    (fun _ => Classical.propDecidable _)]
  congr 2
  apply Finset.card_nbij' (· + 1) (· - 1)
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, he, abs_sub_round_eq_min]
    exact ⟨⟨by omega, by omega⟩, hn.2⟩
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, he, abs_sub_round_eq_min] at hn
    apply Finset.mem_filter.mpr
    simp only [Finset.mem_range, frac, root]
    rw [Nat.sub_add_cancel hn.1.1]
    exact ⟨by omega, hn.2⟩
  · intro n _
    simp
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    exact Nat.sub_add_cancel hn.1.1

end

end MetaMathlibExt
