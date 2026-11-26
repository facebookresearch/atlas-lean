/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import MathlibExt.Analysis.Complex.Rouche

/-!
# Hayman Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028]

The Jacobi theta function gives the counterexample in
`exists_bounded_each_value_not_isBoundedValueDistribution` and `conjecture_refuted`. Its
quasi-periodicity and Rouché's theorem give a bound on the number of preimages of each fixed
finite value in discs of a given radius, and it has no poles. On rescaling around $ni$, the
functions $e^{-π n^2}θ(ni+z/n)-θ(0)$ converge on compact sets to $θ(0)(e^{-2πiz}-1)$. Its
integer zeros force arbitrarily many preimages of $e^{π n^2}θ(0)$ in a unit disc. The proof of
`conjecture_refuted` takes the three distinguished values to be the finite values `0`, `1`, `2`.

Stable source: Hayman - Research Problems in Function Theory (2018), Problem 2.28,
source URL `https://arxiv.org/abs/1809.07200`, extraction `source-tex`.

## Clause list from the source (enumeration before formalization)

1. `f` is meromorphic in the plane (domain `ℂ`, `MeromorphicOn f Set.univ`).
2. Quantifier: for every positive `r : ℝ`, `r > 0`.
3. There exists a fixed constant `C(r) : ℕ` depending only on `r`
   (not on the disc centre nor on `w`).
4. Equation `f(z) = w` for arbitrary value `w`, finite or infinite in the
   source. Finite roots are counted with multiplicity via
   `meromorphicOrderAt (fun z => f z - w) z`, not via the raw fibre
   `f ⁻¹' {w}`: the point value of a meromorphic function at a pole or
   removable singularity is not intrinsic, and changing values on a
   locally finite set must not create roots. The value `∞` is counted by
   pole multiplicity (the negative part of `meromorphicOrderAt f z`).
   Values are modeled by `Option ℂ` with `none` for `∞`.
5. In any disc of radius `r` (formalized as `Metric.ball c r` for arbitrary
   centre `c : ℂ`).
6. Never more than `C(r)` roots in such a disc, counted with multiplicity
   (formalized as: for every `Finset ℂ` contained in the disc, the sum of
   root multiplicities is `≤ C`).
7. `f` is nonconstant as a meromorphic germ: for every value `w` there is
   a point at which `f` is not locally identically `w`
   (`meromorphicOrderAt (f - w) z ≠ ⊤`). A pointwise condition would not
   suffice: changing one value of the zero function leaves it meromorphic
   and pointwise nonconstant while its germ is constant. The source
   problem concerns nonconstant meromorphic functions; without this, a
   constant `f` satisfies the three-value bound (three values have empty
   root sets) while failing bounded value distribution at its own value.
8. Context only (not a formal target): it suffices to assume the bound for
   a single value of `r`.
9. Context only (not a formal target): if `f` is entire then `C(r) = O(r)`
   as `r → ∞`, hence at most exponential type.
10. Context only (not a formal target): Wittich's theorem on
    `y⁽ⁿ⁾ + f₁(z)y⁽ⁿ⁻¹⁾ + ⋯ + fₙ(z)y = 0` with entire coefficients having only
    b.v.d. solutions implies the `f_ν` are constants, and conversely.
11. Question hypothesis (P. Turán): the basic bound is assumed for only three
    values `w₁, w₂, w₃`, pairwise distinct. The source says "three such values"
    without saying whether `∞` may be one of them. As in clause 4, the formal
    values lie on the Riemann sphere (`w₁, w₂, w₃ : Option ℂ`, with `none` for
    `∞`). This weakens the hypothesis, so `conjecture` implies the reading in
    which the three values are finite; the counterexample takes the finite
    values `0`, `1`, `2`, so it refutes both readings.
12. Question claim: does the three-value bound imply `f` is of bounded value
    distribution for all `w`?

Clauses 1–6 are formalized in `IsBoundedValueDistribution`.
Clauses 11–12 are formalized in `conjecture`.
Clauses 8–10 are recorded here as context evidence and are not separate targets.
-/

@[expose] public section

namespace MathlibExt.Analysis.TuranThreeValueBoundedDistributionWanted

/-- **Multiplicity of a root of $f = w$.** Let $f : \mathbb{C} \to \mathbb{C}$ and
$w, z \in \mathbb{C}$. The multiplicity of $z$ as a root of the equation $f = w$ is an extended
natural number: it is $\infty$ if $f(t) = w$ for every $t \neq z$ in some neighbourhood of $z$;
otherwise it is $n$ if $f - w$ has meromorphic order $n \ge 0$ at $z$, and it is $0$ if that
order is negative or $f - w$ is not meromorphic at $z$.

It depends only on the values of $f$ on a punctured neighbourhood of $z$, so changing $f(z)$
does not change it. It is $0$ when $f$ has a pole at $z$, and when $f - w$ is analytic at $z$
with $f(z) \neq w$.

Source: Hayman - Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028],
`https://arxiv.org/abs/1809.07200`. -/
noncomputable def rootMult (f : ℂ → ℂ) (w z : ℂ) : ℕ∞ :=
  if meromorphicOrderAt (fun t => f t - w) z = ⊤ then ⊤
  else ((meromorphicOrderAt (fun t => f t - w) z).untopD 0).toNat

/-- **Multiplicity of a pole.** Let $f : \mathbb{C} \to \mathbb{C}$ and $z \in \mathbb{C}$. The
multiplicity of $z$ as a pole of $f$, that is, the multiplicity of the value $\infty$ at $z$, is
$-n$ if $f$ has finite meromorphic order $n < 0$ at $z$, and $0$ otherwise. In particular it is
$0$ unless $f$ has a pole at $z$.

Source: Hayman - Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028],
`https://arxiv.org/abs/1809.07200`. -/
noncomputable def poleMult (f : ℂ → ℂ) (z : ℂ) : ℕ∞ :=
  ((-(meromorphicOrderAt f z).untopD 0).toNat : ℕ∞)

/-- **Multiplicity of a value on the Riemann sphere.** Let $f : \mathbb{C} \to \mathbb{C}$ and
$z \in \mathbb{C}$, and let $w$ be a point of the Riemann sphere $\mathbb{C} \cup \{\infty\}$.
The multiplicity of $w$ as a value of $f$ at $z$ is the multiplicity of $z$ as a root of
$f = w$ when $w$ is finite, and the multiplicity of $z$ as a pole of $f$ when $w = \infty$.

Source: Hayman - Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028],
`https://arxiv.org/abs/1809.07200`. -/
noncomputable def rootMultSph (f : ℂ → ℂ) (w : Option ℂ) (z : ℂ) : ℕ∞ :=
  match w with
  | some w => rootMult f w z
  | none => poleMult f z

/-- **Bounded value distribution.** A function $f : \mathbb{C} \to \mathbb{C}$ has bounded value
distribution if for every real $r > 0$ there is a natural number $C$ such that, for every value
$w$ of the Riemann sphere $\mathbb{C} \cup \{\infty\}$ and every open disc of radius $r$, the
multiplicities of $w$ as a value of $f$ at the points of any finite subset of the disc add up
to at most $C$.

The source states this for functions meromorphic in the plane; the definition itself does not
assume meromorphy.

Source: Hayman - Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028],
`https://arxiv.org/abs/1809.07200`. -/
def IsBoundedValueDistribution (f : ℂ → ℂ) : Prop :=
  ∀ (r : ℝ), r > 0 →
    ∃ C : ℕ, ∀ (c : ℂ) (w : Option ℂ) (s : Finset ℂ),
      (↑s ⊆ Metric.ball c r) → ∑ z ∈ s, rootMultSph f w z ≤ (C : ℕ∞)

/-- **Turán's three-value question.** The statement that every function
$f : \mathbb{C} \to \mathbb{C}$ with the following properties has bounded value distribution:
$f$ is meromorphic on $\mathbb{C}$; for every $w \in \mathbb{C}$ there is a point at which
$f - w$ has finite meromorphic order; and there are three distinct values $w_1, w_2, w_3$ of
the Riemann sphere $\mathbb{C} \cup \{\infty\}$ such that for every real $r > 0$ there is a
natural number $C$ for which, for each $i$ and every open disc of radius $r$, the
multiplicities of $w_i$ as a value of $f$ at the points of any finite subset of the disc add
up to at most $C$.

Source: Hayman - Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028],
`https://arxiv.org/abs/1809.07200`, question by P. Turán. -/
def conjecture : Prop :=
  ∀ (f : ℂ → ℂ), MeromorphicOn f Set.univ →
    (∀ w : ℂ, ∃ z : ℂ, meromorphicOrderAt (fun t => f t - w) z ≠ ⊤) →
    (∃ w₁ w₂ w₃ : Option ℂ, w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧
      ∀ (r : ℝ), r > 0 →
        ∃ C : ℕ, ∀ (c : ℂ) (w : Option ℂ), w ∈ ({w₁, w₂, w₃} : Set (Option ℂ)) →
          ∀ (s : Finset ℂ),
            (↑s ⊆ Metric.ball c r) → ∑ z ∈ s, rootMultSph f w z ≤ (C : ℕ∞)) →
    IsBoundedValueDistribution f

open _root_.Complex Filter Metric Set
open scoped Topology

private noncomputable def theta (z : ℂ) := jacobiTheta₂ z I

@[local fun_prop] private theorem theta_diff : Differentiable ℂ theta :=
  fun z => differentiableAt_jacobiTheta₂_fst z (by simp)

private theorem theta_zero_ne_zero : theta 0 ≠ 0 := by
  have h := hasSum_re (hasSum_jacobiTheta₂_term 0 (show 0 < I.im by simp))
  have term (k : ℤ) : (jacobiTheta₂_term k 0 I).re = Real.exp (-Real.pi * (k : ℝ) ^ 2) := by
    simp only [jacobiTheta₂_term, mul_zero, zero_add]
    rw [show (Real.pi * I * (k : ℂ) ^ 2 * I : ℂ) = ↑(-Real.pi * (k : ℝ) ^ 2) by
      push_cast
      linear_combination (Real.pi * (k : ℂ) ^ 2) * I_mul_I, ← ofReal_exp, ofReal_re]
  have hp := h.summable.tsum_pos (fun k => (term k ▸ Real.exp_pos _).le)
    (0 : ℤ) (term 0 ▸ Real.exp_pos _)
  rw [h.tsum_eq] at hp
  exact fun he => (ne_of_gt hp) (by rw [← theta, he, zero_re])

-- The exponential multiplier for translation by an imaginary integer.
private noncomputable def phase (n : ℤ) (z : ℂ) : ℂ :=
  Real.pi * n ^ 2 - 2 * Real.pi * I * n * z

private theorem theta_shift (m n : ℤ) (z : ℂ) :
    theta (z + ((m : ℂ) + n * I)) = exp (phase n z) * theta z := by
  have hp : Function.Periodic theta 1 := fun v => jacobiTheta₂_add_left v I
  rw [show z + ((m : ℂ) + n * I) = (z + n * I) + m • (1 : ℂ) by simp; ring,
    hp.zsmul m]
  unfold theta
  conv_rhs => rw [jacobiTheta₂, ← tsum_mul_left, ← (Equiv.addRight n).tsum_eq]
  apply tsum_congr
  intro k
  simp only [jacobiTheta₂_term, ← exp_add, Equiv.coe_addRight, Int.cast_add, phase]
  congr 1
  linear_combination -(Real.pi * (n : ℂ) ^ 2) * I_mul_I

private theorem theta_nonconstant (w : ℂ) : ∃ z, theta z ≠ w := by
  by_contra! h
  have hi : theta I = exp (Real.pi : ℂ) * theta 0 := by simpa [phase] using theta_shift 0 1 0
  rw [h I, ← h 0] at hi
  have he : exp (Real.pi : ℂ) ≠ 1 := by
    rw [← ofReal_exp, ← ofReal_one, ne_eq, ofReal_inj]
    exact (Real.one_lt_exp_iff.mpr Real.pi_pos).ne'
  exact he (mul_right_cancel₀ theta_zero_ne_zero (hi.symm.trans (one_mul _).symm))

private theorem theta_finite (w z : ℂ) :
    meromorphicOrderAt (fun t => theta t - w) z ≠ ⊤ := by
  obtain ⟨v, hv⟩ := theta_nonconstant w
  have ha := (theta_diff.sub_const w).differentiableOn.analyticOnNhd isOpen_univ
  apply ha.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ v) (mem_univ z)
  rw [(ha v trivial).meromorphicOrderAt_eq,
    (ha v trivial).analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hv)]
  simp

private noncomputable def mass (w z : ℂ) : ℤ :=
  (meromorphicOrderAt (fun t => theta t - w) z).untop₀

private theorem mass_nonneg (w z : ℂ) : 0 ≤ mass w z := by
  have h := ((theta_diff.sub_const w).analyticAt z).meromorphicOrderAt_nonneg
  rwa [← WithTop.coe_untop₀_of_ne_top (theta_finite w z), ← WithTop.coe_zero,
    WithTop.coe_le_coe] at h

private theorem sum_root_le_iff (w : ℂ) (s : Finset ℂ) (C : ℕ) :
    (∑ z ∈ s, rootMult theta w z ≤ (C : ℕ∞)) ↔ ∑ z ∈ s, mass w z ≤ (C : ℤ) := by
  simp only [rootMult, theta_finite, ↓reduceIte]
  change (∑ z ∈ s, ((mass w z).toNat : ℕ∞) ≤ _) ↔ _
  rw [← Nat.cast_sum, Nat.cast_le]
  zify
  simp [Int.toNat_of_nonneg (mass_nonneg _ _)]

private noncomputable def count (f : ℂ → ℂ) (R : ℝ) : ℤ :=
  ∑ᶠ z, MeromorphicOn.divisor f (ball 0 R) z

private theorem finite_sum_le_count {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (R : ℝ) (s : Finset ℂ) :
    ∑ z ∈ s, MeromorphicOn.divisor f (ball 0 R) z ≤ count f R := by
  classical
  have hf' : AnalyticOnNhd ℂ f (closedBall 0 R) := fun z _ => hf.analyticAt z
  have hfin := hf'.meromorphicOn.divisor_ball_support_finite
  let t := s ∪ hfin.toFinset
  unfold count
  rw [finsum_eq_sum_of_support_subset (s := t) _ (by simp [t])]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun z _ _ => MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf'.mono ball_subset_closedBall) z)

-- Pick a circle clear of the finitely many zeros in a larger compact disc.
private theorem clear_circle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfinord : ∀ z, meromorphicOrderAt f z ≠ ⊤) (r : ℝ) (hr : 0 < r) :
    ∃ R > r, ∃ δ > 0, ∀ z ∈ sphere (0 : ℂ) R, δ ≤ ‖f z‖ := by
  let D := MeromorphicOn.divisor f (closedBall 0 (r + 1))
  have hfin := D.finiteSupport (isCompact_closedBall _ _)
  obtain ⟨R, hR, hav⟩ := (Ioo_infinite (show r < r + 1 by linarith)).exists_notMem_finite
    (hfin.image (fun z : ℂ => ‖z‖))
  have hpos : 0 < R := hr.trans hR.1
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hpos.le) hf.continuous.norm.continuousOn
  refine ⟨R, hR.1, ‖f z‖, norm_pos_iff.mpr ?_, hmin⟩
  intro hzero
  have hzR : ‖z‖ = R := by simpa using hz
  have hzB : z ∈ closedBall (0 : ℂ) (r + 1) := by simpa [hzR] using hR.2.le
  apply hav ⟨z, ?_, hzR⟩
  have h := hfinord z
  rw [Function.mem_support, show D z = _ from
    MeromorphicOn.divisor_apply (fun y _ => (hf.analyticAt y).meromorphicAt) hzB]
  intro he
  have ho : meromorphicOrderAt f z = 0 := by
    rw [← WithTop.coe_untop₀_of_ne_top h, he, WithTop.coe_zero]
  simp [(hf.analyticAt z).meromorphicOrderAt_eq,
    (hf.analyticAt z).analyticOrderAt_eq_zero, hzero] at ho

private theorem translated_sum_le (a w : ℂ) (R : ℝ) (s : Finset ℂ)
    (hs : ∀ z ∈ s, z - a ∈ ball 0 R) :
    ∑ z ∈ s, mass w z ≤ count (fun z => theta (z + a) - w) R := by
  classical
  let f (z : ℂ) := theta (z + a) - w
  have hf : Differentiable ℂ f := (theta_diff.comp (differentiable_id.add_const a)).sub_const w
  have hm : MeromorphicOn f (ball 0 R) := fun z _ => (hf.analyticAt z).meromorphicAt
  have h := finite_sum_le_count hf R (s.image (· - a))
  rw [Finset.sum_image (fun x _ y _ => sub_left_inj.mp)] at h
  refine le_trans (Finset.sum_le_sum fun z hz => ?_) h
  rw [MeromorphicOn.divisor_apply hm (hs z hz)]
  change _ ≤ (meromorphicOrderAt ((fun t => theta t - w) ∘ (· + a)) (z - a)).untop₀
  rw [meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, sub_add_cancel]
  rfl

private theorem translated_count (m n : ℤ) (R : ℝ) :
    count (fun z => theta (z + ((m : ℂ) + n * I))) R = count theta R := by
  let a : ℂ := m + n * I
  have ha : Differentiable ℂ (fun z => theta (z + a)) :=
    theta_diff.comp (differentiable_id.add_const a)
  apply finsum_congr
  intro z
  by_cases hz : z ∈ ball (0 : ℂ) R
  · rw [MeromorphicOn.divisor_apply (fun t _ => (ha.analyticAt t).meromorphicAt) hz,
      MeromorphicOn.divisor_apply (fun t _ => (theta_diff.analyticAt t).meromorphicAt) hz]
    have he : AnalyticAt ℂ (fun t => exp (phase n t)) z := by unfold phase; fun_prop
    simp_rw [a, theta_shift m n]
    exact congrArg WithTop.untop₀ (meromorphicOrderAt_mul_of_ne_zero he (exp_ne_zero _))
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

private theorem phase_re (n : ℤ) (z : ℂ) :
    (phase n z).re = Real.pi * (n : ℝ) ^ 2 + 2 * Real.pi * n * z.im := by
  simp [phase, mul_re, mul_im, pow_two]

-- On distant horizontal rows the quadratic term in the exponent dominates the linear term
-- uniformly on the circle. Subtracting the fixed value then preserves the zero count.
private theorem large_shift_count (w : ℂ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hmin : ∀ z ∈ sphere (0 : ℂ) R, δ ≤ ‖theta z‖) {N : ℕ}
    (hN : 2 * R + ‖w‖ / δ + 1 < N) (m n : ℤ) (hn : N ≤ n.natAbs) :
    count (fun z => theta (z + ((m : ℂ) + n * I)) - w) R = count theta R := by
  let a : ℂ := m + n * I
  have ha : Differentiable ℂ (fun z => theta (z + a)) :=
    theta_diff.comp (differentiable_id.add_const a)
  have hcomp := MathlibExt.Analysis.Complex.Rouche.rouche_closedBall (c := 0) hR
    (fun t _ => ha.analyticAt t) (g := fun _ => -w) (fun _ _ => analyticAt_const)
  have hnorm (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : ‖-w‖ < ‖theta (z + a)‖ := by
    have hzn : ‖z‖ = R := by simpa using hz
    have hi := abs_im_le_norm z
    rw [hzn] at hi
    have hn' : (N : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast (show (N : ℤ) ≤ |n| by rwa [← Int.natCast_natAbs, Nat.cast_le])
    have h1 : 1 ≤ |(n : ℝ)| := by linarith [div_nonneg (norm_nonneg w) hδ.le]
    have hprod := neg_abs_le ((n : ℝ) * z.im)
    rw [abs_mul] at hprod
    have hb : -(|(n : ℝ)| * R) ≤ n * z.im := by
      nlinarith [mul_le_mul_of_nonneg_left hi (abs_nonneg (n : ℝ))]
    have hbig : ‖w‖ / δ < (phase n z).re := by
      rw [phase_re]
      calc
        ‖w‖ / δ < |(n : ℝ)| - 2 * R := by linarith
        _ ≤ Real.pi * |(n : ℝ)| * (|(n : ℝ)| - 2 * R) := by
          apply le_mul_of_one_le_left
          · linarith [div_nonneg (norm_nonneg w) hδ.le]
          · nlinarith [Real.two_le_pi, mul_le_mul_of_nonneg_left h1 Real.pi_pos.le]
        _ ≤ _ := by
          nlinarith [congrArg (Real.pi * ·) (sq_abs (n : ℝ)),
            mul_le_mul_of_nonneg_left hb Real.pi_pos.le]
    rw [norm_neg, theta_shift, norm_mul, norm_exp]
    have hexp : (phase n z).re ≤ Real.exp (phase n z).re := by
      linarith [Real.add_one_le_exp (phase n z).re]
    exact ((div_lt_iff₀ hδ).mp (hbig.trans_le hexp)).trans_le
      (mul_le_mul_of_nonneg_left (hmin z hz) (Real.exp_pos _).le)
  exact (hcomp hnorm).symm.trans (translated_count m n R)

private theorem near_lattice (c : ℂ) :
    ∃ m n : ℤ, ‖c - ((m : ℂ) + n * I)‖ < 2 := by
  refine ⟨⌊c.re⌋, ⌊c.im⌋, ?_⟩
  apply lt_of_le_of_lt (norm_le_abs_re_add_abs_im _)
  simp [mul_re, mul_im, abs_of_nonneg (Int.fract_nonneg c.re),
    abs_of_nonneg (Int.fract_nonneg c.im)]
  linarith [Int.fract_lt_one c.re, Int.fract_lt_one c.im]

-- Discs in the remaining rows fit in one larger disc after a real period translation.
private theorem bounded_at (w : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ C : ℕ, ∀ (c : ℂ) (s : Finset ℂ), ↑s ⊆ ball c r →
      ∑ z ∈ s, rootMult theta w z ≤ (C : ℕ∞) := by
  obtain ⟨R, hR, δ, hδ, hmin⟩ :=
    clear_circle theta_diff (fun z => by simpa using theta_finite 0 z) (r + 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * R + ‖w‖ / δ + 1)
  let B := count (fun z => theta z - w) (R + N)
  refine ⟨(max (count theta R) B).toNat, fun c s hs => (sum_root_le_iff _ _ _).mpr ?_⟩
  apply le_trans _ (Int.self_le_toNat _)
  obtain ⟨m, n, hnear⟩ := near_lattice c
  let a : ℂ := m + n * I
  have hclose (z : ℂ) (hz : z ∈ s) : ‖z - a‖ < R := by
    calc
      ‖z - a‖ ≤ ‖z - c‖ + ‖c - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < r + 2 := add_lt_add (by simpa [mem_ball, dist_eq_norm] using hs hz) hnear
      _ < R := hR
  by_cases hn : N ≤ n.natAbs
  · have h := translated_sum_le a w R s (fun z hz => by simpa using hclose z hz)
    rw [large_shift_count w (by linarith) hδ hmin hN m n hn] at h
    exact h.trans (le_max_left _ _)
  · have hsmall : ‖(n : ℂ) * I‖ ≤ (N : ℝ) := by
      simp only [norm_mul, norm_intCast, norm_I, mul_one]
      exact_mod_cast (show |n| ≤ (N : ℤ) by
        rw [← Int.natCast_natAbs, Nat.cast_le]
        omega)
    have h := translated_sum_le (m : ℂ) w (R + N) s (fun z hz => by
      rw [mem_ball_zero_iff]
      calc
        ‖z - m‖ = ‖z - a + n * I‖ := by congr 1; dsimp [a]; ring
        _ ≤ _ := norm_add_le _ _
        _ < _ := add_lt_add_of_lt_of_le (hclose z hz) hsmall)
    have hp (z : ℂ) : theta (z + m) = theta z := by simpa [phase] using theta_shift m 0 z
    simp_rw [hp] at h
    exact h.trans (le_max_right _ _)

-- Near the translates nI, magnifying the variable by n and normalizing the value
-- gives a limit with a simple zero at every integer.
private noncomputable def wave (z : ℂ) := exp (-2 * Real.pi * I * z)

private noncomputable def model (z : ℂ) := wave z * theta 0 - theta 0

private theorem model_diff : Differentiable ℂ model := by
  unfold model wave
  fun_prop

private theorem model_order (k : ℕ) : meromorphicOrderAt model (k : ℂ) = 1 := by
  let b : ℂ := -2 * Real.pi * I
  have hb : b ≠ 0 := by simp [b, Real.pi_ne_zero]
  have hder := ((((hasDerivAt_id' (k : ℂ)).const_mul b).cexp).mul_const
    (theta 0)).sub_const (theta 0)
  have hw : wave k = 1 := by
    rw [wave, show (-2 * Real.pi * I * k : ℂ) = -(k * (2 * Real.pi * I)) by ring,
      exp_neg, exp_nat_mul_two_pi_mul_I, inv_one]
  have ha := model_diff.analyticAt (k : ℂ)
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (by simp [model, hw]) (by
      change deriv (fun z => exp (b * z) * theta 0 - theta 0) _ ≠ 0
      rw [hder.deriv]
      exact mul_ne_zero (mul_ne_zero (exp_ne_zero _) (mul_ne_zero hb one_ne_zero))
        theta_zero_ne_zero)]
  simp

private theorem model_count {C : ℕ} {R : ℝ} (hR : C < R) : (C : ℤ) + 1 ≤ count model R := by
  classical
  let t := Finset.range (C + 1)
  have h := finite_sum_le_count model_diff R (t.image (Nat.cast : ℕ → ℂ))
  rw [Finset.sum_image (fun x _ y _ hxy => Nat.cast_injective (R := ℂ) hxy)] at h
  have hterm (k : ℕ) (hk : k ∈ t) : MeromorphicOn.divisor model (ball 0 R) (k : ℂ) = 1 := by
    have hk' : k ≤ C := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hmem : (k : ℂ) ∈ ball 0 R := by
      simpa using (show (k : ℝ) < R from lt_of_le_of_lt (by exact_mod_cast hk') hR)
    rw [MeromorphicOn.divisor_apply (fun z _ => (model_diff.analyticAt z).meromorphicAt) hmem,
      model_order]
    rfl
  simpa [Finset.sum_congr rfl hterm, t] using h

private noncomputable def scaled (n : ℕ) (z : ℂ) := wave z * theta (z / n) - theta 0

private theorem scaled_diff (n : ℕ) : Differentiable ℂ (scaled n) := by
  unfold scaled wave
  fun_prop

-- On any fixed circle avoiding the zeros of the model the normalized translates
-- eventually have the same zero count as the model, by Rouché's theorem.
private theorem exists_scaled_count {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hmin : ∀ z ∈ sphere (0 : ℂ) R, δ ≤ ‖model z‖) :
    ∃ n : ℕ, R < n ∧ count (scaled n) R = count model R := by
  have hcont : Continuous (fun z => ‖wave z‖) := by unfold wave; fun_prop
  obtain ⟨p, hp, hmax⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hR.le) hcont.continuousOn
  have hp0 : 0 < ‖wave p‖ := norm_pos_iff.mpr (exp_ne_zero _)
  obtain ⟨ε, hε, hclose⟩ := Metric.continuousAt_iff.mp (theta_diff.continuous.continuousAt
    (x := 0)) (δ / ‖wave p‖) (div_pos hδ hp0)
  obtain ⟨n, hn⟩ := exists_nat_gt (max R (R / ε))
  have hRn := (le_max_left _ _).trans_lt hn
  have hn' : 0 < (n : ℝ) := hR.trans hRn
  let g (z : ℂ) := wave z * (theta (z / n) - theta 0)
  have hg : Differentiable ℂ g := by unfold g wave; fun_prop
  have heq (z : ℂ) : model z + g z = scaled n z := by unfold model g scaled; ring
  refine ⟨n, hRn, ?_⟩
  have h := MathlibExt.Analysis.Complex.Rouche.rouche_closedBall (c := 0) hR
    (fun z _ => model_diff.analyticAt z) (fun z _ => hg.analyticAt z) (fun z hz => ?_)
  · simpa only [count, heq] using h.symm
  · have hzn : ‖z‖ = R := by simpa using hz
    have hεn : R < ε * n := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    have hz' : dist (z / n) 0 < ε := by
      simpa [norm_div, hzn, div_lt_iff₀ hn'] using hεn
    have hd : ‖theta (z / n) - theta 0‖ < δ / ‖wave p‖ := by
      simpa [dist_eq_norm] using hclose hz'
    calc
      ‖g z‖ = ‖wave z‖ * ‖theta (z / n) - theta 0‖ := norm_mul _ _
      _ ≤ ‖wave p‖ * _ := mul_le_mul_of_nonneg_right (hmax hz) (norm_nonneg _)
      _ < δ := by simpa [mul_comm] using (lt_div_iff₀ hp0).mp hd
      _ ≤ _ := hmin z hz

-- The affine map z ↦ z/n + nI takes the comparison disc into a unit disc,
-- preserving every multiplicity.
private theorem scaled_count_le {C : ℕ}
    (hC : ∀ (c w : ℂ) (s : Finset ℂ), ↑s ⊆ ball c 1 → ∑ z ∈ s, mass w z ≤ (C : ℤ))
    {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : R < n) : count (scaled n) R ≤ C := by
  classical
  have hn' : 0 < (n : ℝ) := hR.trans hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by exact_mod_cast hn'.ne')
  let L (z : ℂ) := z / n + n * I
  let a : ℂ := exp (Real.pi * (n : ℂ) ^ 2)
  let w := a * theta 0
  have heq : (fun z => theta (L z) - w) = a • scaled n := by
    funext z
    have hs := theta_shift 0 (n : ℤ) (z / n)
    simp only [Int.cast_zero, Int.cast_natCast, zero_add] at hs
    have hphase : phase n (z / n) = Real.pi * (n : ℂ) ^ 2 + (-2 * Real.pi * I * z) := by
      unfold phase
      push_cast
      field_simp
      ring
    simp only [L, hs, hphase, exp_add, Pi.smul_apply, smul_eq_mul, scaled, w, a, wave]
    ring
  have hdL (z : ℂ) : HasDerivAt L (1 / n) z :=
    ((hasDerivAt_id' z).div_const (n : ℂ)).add_const _
  let D := MeromorphicOn.divisor (scaled n) (ball 0 R)
  have hfin : D.support.Finite := MeromorphicOn.divisor_ball_support_finite
    (fun z _ => ((scaled_diff n).analyticAt z).meromorphicAt)
  let s := hfin.toFinset
  have hmem {z : ℂ} (hz : z ∈ s) : z ∈ ball 0 R :=
    D.supportWithinDomain (hfin.mem_toFinset.mp hz)
  have hdiv (z : ℂ) (hz : z ∈ s) : D z = mass w (L z) := by
    dsimp [D]
    rw [← MeromorphicOn.divisor_const_smul (s := a) (exp_ne_zero _), ← heq]
    have hdiff : Differentiable ℂ (fun z => theta (L z) - w) :=
      (theta_diff.comp (fun t => (hdL t).differentiableAt)).sub_const w
    rw [MeromorphicOn.divisor_apply (fun t _ => (hdiff.analyticAt t).meromorphicAt) (hmem hz)]
    apply congrArg WithTop.untop₀
    exact meromorphicOrderAt_comp_of_deriv_ne_zero (f := fun t => theta t - w)
      ((show Differentiable ℂ L from fun t => (hdL t).differentiableAt).analyticAt z)
      (by rw [(hdL z).deriv]; exact one_div_ne_zero hn0)
  have hbound := hC (n * I) w (s.image L) (by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzR : ‖z‖ < R := by simpa using hmem hz
    simpa [L, mem_ball, dist_eq_norm, norm_div, div_lt_iff₀ hn'] using hzR.trans hn)
  have hinj : Function.Injective L := fun _ _ hxy => (div_left_inj₀ hn0).mp (add_right_cancel hxy)
  rw [Finset.sum_image (fun _ _ _ _ hxy => hinj hxy)] at hbound
  rw [count, finsum_eq_sum_of_support_subset (s := s) _ (by simp [s, D])]
  exact (Finset.sum_congr rfl hdiv).trans_le hbound

private theorem not_bounded : ¬ IsBoundedValueDistribution theta := by
  intro h
  obtain ⟨C, hC⟩ := h 1 zero_lt_one
  have hm (z : ℂ) : meromorphicOrderAt model z ≠ ⊤ := by
    have ha : MeromorphicOn model univ := fun t _ => (model_diff.analyticAt t).meromorphicAt
    apply ha.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ ((0 : ℕ) : ℂ)) (mem_univ z)
    rw [model_order]
    exact WithTop.one_ne_top
  obtain ⟨R, hR, δ, hδ, hmin⟩ := clear_circle model_diff hm (C + 1) (by positivity)
  have hR' : 0 < R := lt_trans (by positivity) hR
  obtain ⟨n, hn, hcount⟩ := exists_scaled_count hR' hδ hmin
  have hle := scaled_count_le (C := C) (fun c w s hs =>
    (sum_root_le_iff _ _ _).mp (hC c (some w) s hs)) hR' hn
  rw [hcount] at hle
  linarith [model_count (C := C) (R := R) (by linarith)]

/-- **Bounding each value separately does not give bounded value distribution.** There is a
function $f : \mathbb{C} \to \mathbb{C}$, meromorphic on $\mathbb{C}$, such that for every
$w \in \mathbb{C}$ there is a point at which $f - w$ has finite meromorphic order, and such that
for every value $w$ of the Riemann sphere $\mathbb{C} \cup \{\infty\}$ and every real $r > 0$
there is a natural number $C$, depending on $w$ and $r$, for which, for every open disc of
radius $r$, the multiplicities of $w$ as a value of $f$ at the points of any finite subset of
the disc add up to at most $C$; and yet $f$ does not have bounded value distribution. In
particular, Turán's question has a negative answer even when the three values are required to
be finite.

Source: Hayman - Research Problems in Function Theory (2018), Problem 2.28 [AMR-022-2028],
`https://arxiv.org/abs/1809.07200`, question by P. Turán. -/
theorem exists_bounded_each_value_not_isBoundedValueDistribution :
    ∃ f : ℂ → ℂ, MeromorphicOn f Set.univ ∧
      (∀ w : ℂ, ∃ z : ℂ, meromorphicOrderAt (fun t => f t - w) z ≠ ⊤) ∧
      (∀ (w : Option ℂ) (r : ℝ), r > 0 →
        ∃ C : ℕ, ∀ (c : ℂ) (s : Finset ℂ),
          (↑s ⊆ Metric.ball c r) → ∑ z ∈ s, rootMultSph f w z ≤ (C : ℕ∞)) ∧
      ¬ IsBoundedValueDistribution f := by
  refine ⟨theta, fun z _ => (theta_diff.analyticAt z).meromorphicAt,
    fun w => ⟨0, theta_finite w 0⟩, fun w r hr => ?_, not_bounded⟩
  cases w with
  | some w => exact bounded_at w r hr
  | none =>
    have hp (z : ℂ) : poleMult theta z = 0 := by
      have hn := (theta_diff.analyticAt z).meromorphicOrderAt_nonneg
      unfold poleMult
      cases ho : meromorphicOrderAt theta z with
      | top => simp
      | coe k =>
        rw [ho, ← WithTop.coe_zero, WithTop.coe_le_coe] at hn
        simp [Int.toNat_of_nonpos (neg_nonpos.mpr hn)]
    exact ⟨0, fun c s _ => by simp [rootMultSph, hp]⟩

/--
**Turán's three-value question has a negative answer.** There is a function
$f : \mathbb{C} \to \mathbb{C}$, meromorphic on $\mathbb{C}$, such that for every $w \in \mathbb{C}$
there is a point at which $f - w$ has finite meromorphic order, together with three distinct
values $w_1, w_2, w_3$ of the Riemann sphere $\mathbb{C} \cup \{\infty\}$ such that for every real
$r > 0$ there is a natural number $C$ for which, for each $i$ and every open disc of radius $r$,
the multiplicities of $w_i$ as a value of $f$ at the points of any finite subset of the disc add
up to at most $C$; and yet $f$ does not have bounded value distribution.

A. A. Gol'dberg (Izv. Vyssh. Uchebn. Zaved. Mat. 1972) answered Turan's question negatively, as
recorded in Hayman-Lingham Update 2.28; the Weierstrass sigma-function is another
counterexample: it has boundedly many $w$-points per disc for every bounded set of $w$ but has
order $2$, so it does not have bounded value distribution.

Source: W. K. Hayman and E. F. Lingham, Research Problems in Function
Theory (2018), arXiv:1809.07200, https://arxiv.org/abs/1809.07200. Moved from
`OpenConjectures/Analysis/TuranThreeValueBoundedDistribution`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨f, hf, hnc, hb, hnot⟩ := exists_bounded_each_value_not_isBoundedValueDistribution
  refine hnot (h f hf hnc ⟨some 0, some 1, some 2, by norm_num, by norm_num, by norm_num,
    fun r hr => ?_⟩)
  obtain ⟨A, hA⟩ := hb (some 0) r hr
  obtain ⟨B, hB⟩ := hb (some 1) r hr
  obtain ⟨D, hD⟩ := hb (some 2) r hr
  refine ⟨max A (max B D), fun c w hw s hs => ?_⟩
  rcases hw with rfl | rfl | hw
  · exact (hA c s hs).trans (by exact_mod_cast le_max_left _ _)
  · exact (hB c s hs).trans (by exact_mod_cast (le_max_left B D).trans (le_max_right _ _))
  · obtain rfl : w = some 2 := hw
    exact (hD c s hs).trans (by exact_mod_cast (le_max_right B D).trans (le_max_right _ _))

end MathlibExt.Analysis.TuranThreeValueBoundedDistributionWanted
