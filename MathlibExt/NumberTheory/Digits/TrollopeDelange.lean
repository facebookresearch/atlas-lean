/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Bounds for Delange's function and the Trollope–Delange fluctuation

For every base at least two, `trollopeDelangeIntegral_isBigO_one` bounds Delange's function
at infinity. The fluctuation is also uniformly bounded. Multiplying its pointwise
supremum bound by the reciprocal digit-sum weights gives
`digitSum_reciprocal_fluctuation_sum_le`.
-/

namespace MetaMathlibExt

@[expose] public section

open Asymptotics Filter Real

/-- **Delange's function.** For a natural number $q$, Delange's function in base $q$ is the
function of a real number $x$ given by
$g(x) = \int_0^x \left(\lfloor q t \rfloor - q \lfloor t \rfloor - \frac{q - 1}{2}\right) dt$,
where $\lfloor \cdot \rfloor$ is the floor function.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `g`). -/
noncomputable def trollopeDelangeIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, ((⌊(q : ℝ) * t⌋ : ℝ) - q * ⌊t⌋ - ((q : ℝ) - 1) / 2)

/-- **Delange's function vanishes at zero.** For every natural number $q$, Delange's function $g$
in base $q$ satisfies $g(0) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1. -/
theorem trollopeDelangeIntegral_zero (q : ℕ) : trollopeDelangeIntegral q 0 = 0 :=
  intervalIntegral.integral_same

/-- **Delange's series.** For a natural number $q$, let $g$ be Delange's function in base $q$.
Delange's series in base $q$ is the function of a real number $x$ given by
$h(x) = \sum_{r \ge 0} g(q^r x)/q^r$, where the sum is taken to be $0$ when the series is not
summable.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `h`). -/
noncomputable def trollopeDelangeSeries (q : ℕ) (x : ℝ) : ℝ :=
  ∑' r : ℕ, trollopeDelangeIntegral q ((q : ℝ) ^ r * x) / (q : ℝ) ^ r

/-- **Delange's series vanishes at zero.** For every natural number $q$, Delange's series $h$ in
base $q$ satisfies $h(0) = 0$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1. -/
theorem trollopeDelangeSeries_zero (q : ℕ) : trollopeDelangeSeries q 0 = 0 := by
  simp [trollopeDelangeSeries, trollopeDelangeIntegral_zero]

/-- **Trollope–Delange fluctuation.** Let $q$ be a natural number and let $h$ be Delange's series
in base $q$. The Trollope–Delange fluctuation in base $q$ is the function of a real number $x$
given by $F(x) = \frac{q - 1}{2}(1 + \lfloor x \rfloor - x) +
q^{1 + \lfloor x \rfloor - x}\, h(q^{x - \lfloor x \rfloor - 1})$, where $\lfloor x \rfloor$ is
the floor of $x$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `F`). -/
noncomputable def trollopeDelangeFluctuation (q : ℕ) (x : ℝ) : ℝ :=
  ((q : ℝ) - 1) / 2 * (1 + ⌊x⌋ - x) +
    (q : ℝ) ^ (1 + ⌊x⌋ - x) * trollopeDelangeSeries q ((q : ℝ) ^ (x - ⌊x⌋ - 1))

/-- **Periodicity of the Trollope–Delange fluctuation.** For every natural number $q$ and every
real number $x$, the Trollope–Delange fluctuation $F$ in base $q$ satisfies $F(x + 1) = F(x)$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (`F` is `1`-periodic). -/
theorem trollopeDelangeFluctuation_add_one (q : ℕ) (x : ℝ) :
    trollopeDelangeFluctuation q (x + 1) = trollopeDelangeFluctuation q x := by
  have h1 : (1 + ((⌊x + 1⌋ : ℤ) : ℝ) - (x + 1)) = 1 + ⌊x⌋ - x := by
    rw [Int.floor_add_one]; push_cast; ring
  have h2 : (x + 1 - ((⌊x + 1⌋ : ℤ) : ℝ) - 1) = x - ⌊x⌋ - 1 := by
    rw [Int.floor_add_one]; push_cast; ring
  simp only [trollopeDelangeFluctuation, h1, h2]

namespace digitSum_reciprocal_fluctuation_sum_le

open MeasureTheory intervalIntegral

private noncomputable def centeredFract (t : ℝ) : ℝ := Int.fract t - 1 / 2

private lemma centeredFract_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable centeredFract volume a b := by
  have hfloor : Monotone (fun t : ℝ => (⌊t⌋ : ℝ)) := fun _ _ h => by
    exact Int.cast_le.mpr (Int.floor_le_floor h)
  exact ((continuous_id.intervalIntegrable a b).sub hfloor.intervalIntegrable).sub
    intervalIntegrable_const

-- The centered fractional part has mean zero, so its primitive is continuous and periodic.
private lemma centeredFract_primitive_bounded :
    ∃ C : ℝ, ∀ x : ℝ, |∫ t in 0..x, centeredFract t| ≤ C := by
  have hmean : (∫ t in (0 : ℝ)..1, centeredFract t) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..1, t - 1 / 2 := by
        apply integral_congr_Ioo_of_le zero_le_one
        intro t ht
        rw [centeredFract, Int.fract_eq_self.mpr ⟨ht.1.le, ht.2⟩]
      _ = 0 := by
        rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => 1 / 2)
          (continuous_id.intervalIntegrable 0 1) intervalIntegrable_const]
        norm_num
  have hp : Function.Periodic centeredFract 1 := fun x => by simp [centeredFract]
  have hprim : Function.Periodic (fun x : ℝ => ∫ t in 0..x, centeredFract t) 1 := by
    intro x
    simpa [hmean] using hp.intervalIntegral_add_eq_add 0 x centeredFract_intervalIntegrable
  obtain ⟨C, hC⟩ := (hprim.isBounded_of_continuous one_ne_zero
    (continuous_primitive centeredFract_intervalIntegrable 0)).exists_norm_le
  exact ⟨C, fun x => hC _ ⟨x, rfl⟩⟩

-- The integrand is q times the centered fractional part at t minus the same function at q*t.
private lemma integral_bounded {q : ℕ} (hq : 2 ≤ q) :
    ∃ C : ℝ, ∀ x : ℝ, |trollopeDelangeIntegral q x| ≤ C := by
  obtain ⟨C, hC⟩ := centeredFract_primitive_bounded
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  refine ⟨q * C + (q : ℝ)⁻¹ * C, fun x => ?_⟩
  have heq : trollopeDelangeIntegral q x =
      q * (∫ t in 0..x, centeredFract t) - (q : ℝ)⁻¹ * ∫ t in 0..q * x, centeredFract t := by
    calc
      _ = ∫ t in 0..x, q * centeredFract t - centeredFract (q * t) := by
        apply integral_congr
        intro t _
        simp only [centeredFract, Int.fract]
        ring
      _ = _ := by
        have hscaled : IntervalIntegrable (fun t => centeredFract (q * t)) volume 0 x := by
          simpa [hq₀.ne'] using (centeredFract_intervalIntegrable 0 (x * q)).comp_mul_left
            (c := (q : ℝ))
        rw [intervalIntegral.integral_sub ((centeredFract_intervalIntegrable 0 x).const_mul _)
          hscaled,
          intervalIntegral.integral_const_mul, integral_comp_mul_left centeredFract hq₀.ne']
        simp
  rw [heq]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos hq₀, abs_of_pos (inv_pos.mpr hq₀)]
  gcongr <;> apply hC

private lemma series_bounded {q : ℕ} (hq : 2 ≤ q) :
    ∃ C : ℝ, ∀ x : ℝ, |trollopeDelangeSeries q x| ≤ C := by
  obtain ⟨C, hC⟩ := integral_bounded hq
  have hq₁ : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q from hq)
  have hgeom := hasSum_geometric_of_lt_one (inv_nonneg.mpr (by positivity : 0 ≤ (q : ℝ)))
    (inv_lt_one_of_one_lt₀ hq₁)
  refine ⟨C * (1 - (q : ℝ)⁻¹)⁻¹, fun x => ?_⟩
  unfold trollopeDelangeSeries
  rw [← Real.norm_eq_abs]
  apply tsum_of_norm_bounded (hgeom.mul_left C)
  intro r
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (show 0 ≤ (q : ℝ) ^ r by positivity),
    inv_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (hC _) (by positivity)

private lemma fluctuation_bddAbove {q : ℕ} (hq : 2 ≤ q) :
    BddAbove (Set.range (fun t => |trollopeDelangeFluctuation q t|)) := by
  obtain ⟨C, hC⟩ := series_bounded hq
  have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  refine ⟨((q : ℝ) - 1) / 2 + q * C, ?_⟩
  rintro _ ⟨t, rfl⟩
  have h₀ : 0 ≤ 1 + (⌊t⌋ : ℝ) - t := by linarith [Int.lt_floor_add_one t]
  have h₁ : 1 + (⌊t⌋ : ℝ) - t ≤ 1 := by linarith [Int.floor_le t]
  have hpow : (q : ℝ) ^ (1 + (⌊t⌋ : ℝ) - t) ≤ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hq₁ h₁
  unfold trollopeDelangeFluctuation
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((q : ℝ) - 1) / 2),
    abs_of_nonneg h₀, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)]
  exact add_le_add (mul_le_of_le_one_right (by positivity) h₁)
    (mul_le_mul hpow (hC _) (abs_nonneg _) (Nat.cast_nonneg q))

end digitSum_reciprocal_fluctuation_sum_le

/-- **Delange's function is eventually bounded.** For every natural number $q \ge 2$, Delange's
function $g$ in base $q$ satisfies $g(x) = O(1)$ as $x \to +\infty$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 2 (`integers-2026-A43-lem-2`). -/
theorem trollopeDelangeIntegral_isBigO_one (q : ℕ) (hq : 2 ≤ q) :
    trollopeDelangeIntegral q =O[atTop] (fun _ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := digitSum_reciprocal_fluctuation_sum_le.integral_bounded hq
  exact (isBigO_one_iff ℝ).mpr ⟨C, eventually_map.mpr (Eventually.of_forall hC)⟩

set_option linter.unusedVariables false in
/-- **Bound for a weighted sum of the fluctuation.** Let $q \ge 2$ be an integer, let $s_q(n)$
denote the sum of the base-$q$ digits of $n$, let $F$ be the Trollope–Delange fluctuation in base
$q$, and let $F_M = \sup_{t \in \mathbb{R}} |F(t)|$ (taken to be $0$ if $|F|$ is unbounded). For
all real numbers $x > 0$ and $y$,
$$\sum_{n=1}^{\lfloor y \rfloor} \frac{s_q(n)}{n} \, F\left(\frac{\log(x/n)}{\log q}\right) \le
F_M \sum_{n=1}^{\lfloor y \rfloor} \frac{s_q(n)}{n}.$$

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 4 (`integers-2026-A43-lem-4`). -/
theorem digitSum_reciprocal_fluctuation_sum_le (q : ℕ) (hq : 2 ≤ q) (x y : ℝ)
    (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ((Nat.digits q n).sum : ℝ) / n * trollopeDelangeFluctuation q (log (x / n) / log q) ≤
      (⨆ t : ℝ, |trollopeDelangeFluctuation q t|) *
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((Nat.digits q n).sum : ℝ) / n := by
  rw [mul_comm (⨆ t : ℝ, |trollopeDelangeFluctuation q t|), Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (le_abs_self _).trans (le_ciSup (digitSum_reciprocal_fluctuation_sum_le.fluctuation_bddAbove
    hq) _)

end

end MetaMathlibExt
