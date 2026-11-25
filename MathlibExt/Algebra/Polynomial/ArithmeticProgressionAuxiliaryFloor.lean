/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import MathlibExt.Algebra.Polynomial.ArithmeticProgressionAuxiliaryRoot
import MathlibExt.Analysis.SpecialFunctions.RpowRationalLowerBound

/-!
# Floors at powers of the positive arithmetic-progression auxiliary root

The lower floor bound uses the second-order defect of a fractional power. For the upper
bound a cubic estimate works at the weak cutoff `(m + 1) * d ≤ 2 * a`; the strong hypothesis
leaves only one case outside this cutoff.
-/

namespace MetaMathlibExt

private theorem rpow_nat_div {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) (p : ℕ) :
    (x ^ n) ^ ((p : ℝ) / n) = x ^ p := by
  rw [← Real.rpow_natCast_mul hx, mul_div_cancel₀ (p : ℝ) (Nat.cast_ne_zero.mpr hn),
    Real.rpow_natCast]

private theorem second_order_lower {r u : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hu : 0 ≤ u) :
    1 + r * u - r * (1 - r) * u ^ 2 / 2 ≤ (1 + u) ^ r := by
  have monotone (f f' : ℝ → ℝ) (h : ∀ x ≥ 0, HasDerivAt f (f' x) x)
      (hn : ∀ x ≥ 0, 0 ≤ f' x) : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun x hx ↦ (h x hx).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Ici]
      exact fun x hx ↦ (h x hx.le).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      rw [(h x hx.le).deriv]
      exact hn x hx.le
  have hpow (q x : ℝ) (hx : 0 ≤ x) :
      HasDerivAt (fun t : ℝ ↦ (1 + t) ^ q) (q * (1 + x) ^ (q - 1)) x := by
    have hx' : 1 + x ≠ 0 := by positivity
    simpa only [id, one_mul] using
      ((hasDerivAt_id x).const_add 1).rpow_const (p := q) (Or.inl hx')
  let D (x : ℝ) := (1 + x) ^ (r - 1) - 1 + (1 - r) * x
  have hD : MonotoneOn D (Set.Ici 0) := by
    refine monotone D (fun x ↦ (r - 1) * (1 + x) ^ (r - 1 - 1) + (1 - r)) ?_ ?_
    · intro x hx
      exact ((hpow (r - 1) x hx).sub_const 1).add (hasDerivAt_const_mul (1 - r))
    · intro x hx
      have hq := Real.rpow_le_one_of_one_le_of_nonpos (show 1 ≤ 1 + x by linarith)
        (show r - 1 - 1 ≤ 0 by linarith)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr hq)]
  have hD₀ (x : ℝ) (hx : 0 ≤ x) : 0 ≤ D x := by
    simpa [D] using hD (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  let E (x : ℝ) := (1 + x) ^ r - (1 + r * x - r * (1 - r) * x ^ 2 / 2)
  have hE : MonotoneOn E (Set.Ici 0) := by
    refine monotone E (fun x ↦ r * D x) ?_ ?_
    · intro x hx
      apply ((hpow r x hx).sub (((hasDerivAt_const_mul r).const_add 1).sub
        ((((hasDerivAt_id x).pow 2).const_mul (r * (1 - r))).div_const 2))).congr_deriv
      simp only [D, id, Nat.cast_ofNat, mul_one]
      ring
    · intro x hx
      exact mul_nonneg hr (hD₀ x hx)
  exact sub_nonneg.mp (by simpa [E] using hE (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu)

-- In the cubic comparison, it is enough that (m + 1) * t ≤ 2, not strict inequality.
private theorem upper_at_last {m : ℕ} (hm : 2 ≤ m) {t x : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (hcut : ((m : ℝ) + 1) * t ≤ 2) (hx :
      (2 + ((m : ℝ) + 1) * t) / (2 + ((m : ℝ) - 1) * t) < x)
    (hG : x ^ (m + 2) + (1 - t) * x ^ (m + 1) - (1 + ((m : ℝ) + 1) * t) * x -
      (1 + (m : ℝ) * t) = 0) : x ^ (m - 1) < 1 + ((m : ℝ) - 1) * t := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₁ : 0 < (m : ℝ) - 1 := by linarith
  let u := ((m : ℝ) - 1) * t
  let v := ((m : ℝ) + 1) * t
  let y := (2 + v) / (2 + u)
  have hu : 0 < u := mul_pos hm₁ ht
  have hv : 0 < v := by dsimp [v]; positivity
  have hq : 0 < 2 + u := by positivity
  have hvu : v = u + 2 * t := by dsimp [v, u]; ring
  have hy : 1 ≤ y := by
    apply (le_div_iff₀ hq).2
    linarith
  have hyx : y < x := hx
  have hx₁ : 1 ≤ x := hy.trans hyx.le
  let N (z : ℝ) := (1 + u) * (z ^ 3 + (1 - t) * z ^ 2) - (1 + v) * z - (1 + m * t)
  have hypos : 0 < N y := by
    have hfactor : N y * (2 + u) ^ 3 = u * t * ((2 + u) * (4 - v ^ 2) + 4 * t ^ 2) := by
      dsimp only [N, y]
      rw [hvu]
      have hmt : (m : ℝ) * t = u + t := by dsimp [u]; ring
      rw [hmt]
      field_simp
      ring
    have hv₂ : 0 ≤ 4 - v ^ 2 := by
      have hvle : v ≤ 2 := hcut
      nlinarith only [mul_nonneg (sub_nonneg.mpr hvle) (show 0 ≤ 2 + v by positivity)]
    have hpos : 0 < N y * (2 + u) ^ 3 := by rw [hfactor]; positivity
    exact pos_of_mul_pos_left hpos (by positivity)
  have hN : N y < N x := by
    have hfactor : N x - N y = (x - y) *
        ((1 + u) * (x ^ 2 + x * y + y ^ 2 + (1 - t) * (x + y)) - (1 + v)) := by
      dsimp [N]; ring
    have hquad : 3 ≤ x ^ 2 + x * y + y ^ 2 + (1 - t) * (x + y) := by
      have h₁ : (1 : ℝ) ^ 2 ≤ x ^ 2 := by gcongr
      have h₂ : (1 : ℝ) * 1 ≤ x * y := by gcongr
      have h₃ : (1 : ℝ) ^ 2 ≤ y ^ 2 := by gcongr
      have h₄ := mul_nonneg (sub_nonneg.mpr ht₁) (show 0 ≤ x + y by linarith)
      linarith
    have hbound := mul_le_mul_of_nonneg_left hquad (show 0 ≤ 1 + u by positivity)
    have huv : 0 ≤ u - t := by
      dsimp [u]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hm') ht.le]
    rw [← sub_pos, hfactor]
    exact mul_pos (sub_pos.mpr hyx) (by linarith)
  have hNx : 0 < N x := hypos.trans hN
  have hident : N x = (1 + u - x ^ (m - 1)) * (x ^ 3 + (1 - t) * x ^ 2) := by
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    dsimp [N, v]
    simp only [pow_succ] at hG
    linear_combination hG
  rw [hident] at hNx
  exact sub_pos.mp (pos_of_mul_pos_left hNx (by positivity))

private theorem weak_cutoff_or_exception {m a d : ℕ} (hm : 2 ≤ m) (ha : 0 < a) (hd : 0 < d)
    (had : m ^ 2 * d ^ 2 < 8 * a) : (m + 1) * d ≤ 2 * a ∨ (m = 2 ∧ a = 1 ∧ d = 1) := by
  by_cases h : 6 ≤ m * d
  · left
    have h₁ : 6 * m ≤ (m * d) * m := Nat.mul_le_mul_right m h
    have h₂ : 4 * (m + 1) ≤ (m * d) * m := by omega
    have h₃ := Nat.mul_le_mul_right d h₂
    have h₄ : ((m * d) * m) * d = m ^ 2 * d ^ 2 := by ring
    have h₅ : (4 * (m + 1)) * d = 4 * ((m + 1) * d) := by ring
    omega
  · have h₁ : m ≤ m * d := by simpa using Nat.mul_le_mul_left m hd
    have h₂ : 2 * d ≤ m * d := Nat.mul_le_mul_right d hm
    have hm' : m ≤ 5 := by omega
    have hd' : d ≤ 2 := by omega
    interval_cases m <;> interval_cases d <;> (try norm_num at had h ⊢) <;> omega

/-- **Exact floors at powers of the auxiliary root (all exponents).** Let $m \ge 2$, let $a$, $d$
be positive integers with $m^2 d^2 < 8a$, and let $\lambda > 0$ be a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$. Then
$\lfloor a \lambda^p \rfloor = a + pd - 1$ for every integer $p$ with $1 \le p \le m - 1$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 5, second statement
(`integers-2026-A92-prop-5`). -/
public theorem arithProgPoly_floor_lam_pow_eq_of_eight {m a d : ℕ} (hm : 2 ≤ m)
    (ha : 0 < a) (hd : 0 < d) (had : m ^ 2 * d ^ 2 < 8 * a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (p : ℕ) (hp1 : 1 ≤ p)
    (hpm : p ≤ m - 1) :
    ⌊(a : ℝ) * lam ^ p⌋ = (a : ℤ) + p * d - 1 := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpm' : (p : ℝ) < m := by exact_mod_cast (show p < m by omega)
  have hbig : (m : ℝ) ^ 2 * (d : ℝ) ^ 2 < 8 * a := by exact_mod_cast had
  have hda : d ≤ a := by
    by_cases hd₁ : d = 1
    · omega
    have h₂ : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    have h₃ : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have h₄ : 2 * (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have h₅ : 8 * (d : ℝ) ≤ (m : ℝ) ^ 2 * (d : ℝ) ^ 2 := by
      calc
        _ ≤ 4 * (d : ℝ) ^ 2 := by linarith
        _ ≤ _ := by gcongr
    exact_mod_cast (show (d : ℝ) ≤ a by linarith)
  let t : ℝ := d / a
  have ht : 0 < t := div_pos hd' ha'
  have ht₁ : t ≤ 1 := (div_le_one ha').2 (by exact_mod_cast hda)
  have hat : (a : ℝ) * t = d := by dsimp [t]; field_simp
  have hroot : 1 + (m : ℝ) * t < lam ^ m := by
    have h := arithProgPoly_lam_pow_gt hm hd hda lam hlam hG
    exact (lt_of_mul_lt_mul_left (by nlinarith only [h, congrArg ((m : ℝ) * ·) hat]) ha'.le)
  have hfrac (k : ℕ) (hk : 0 < k) : (1 + (m : ℝ) * t) ^ ((k : ℝ) / m) < lam ^ k := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    rw [← rpow_nat_div hlam.le (by omega : m ≠ 0) k]
    exact Real.rpow_lt_rpow (by positivity) hroot (by positivity)
  have hlower : (a : ℝ) + p * d - 1 < a * lam ^ p := by
    have hquad : (p : ℝ) * ((m : ℝ) - p) * (d : ℝ) ^ 2 < 2 * a := by
      have h₁ := mul_nonneg (sq_nonneg ((m : ℝ) - 2 * p)) (sq_nonneg (d : ℝ))
      nlinarith only [h₁, hbig]
    have hr : (p : ℝ) / m ≤ 1 := (div_le_one (by positivity)).2 hpm'.le
    have h := second_order_lower (show 0 ≤ (p : ℝ) / m by positivity) hr
      (show 0 ≤ (m : ℝ) * t by positivity)
    have h₁ := mul_le_mul_of_nonneg_left h ha'.le
    have h₂ := mul_lt_mul_of_pos_left (hfrac p (by omega)) ha'
    have hform : (a : ℝ) * (1 + ((p : ℝ) / m) * ((m : ℝ) * t) -
        ((p : ℝ) / m) * (1 - (p : ℝ) / m) * ((m : ℝ) * t) ^ 2 / 2) =
        a + p * d - (p * ((m : ℝ) - p) * (d : ℝ) ^ 2) / (2 * a) := by
      dsimp [t]
      field_simp
    rw [hform] at h₁
    have := (div_lt_one (by positivity : 0 < 2 * (a : ℝ))).2 hquad
    linarith
  have hupper : (a : ℝ) * lam ^ p < a + p * d := by
    rcases weak_cutoff_or_exception hm ha hd had with hcut | ⟨rfl, rfl, rfl⟩
    · have hcut' : ((m : ℝ) + 1) * t ≤ 2 := by
        apply (le_of_mul_le_mul_left ?_ ha')
        have h₁ : ((m : ℝ) + 1) * d ≤ 2 * a := by exact_mod_cast hcut
        nlinarith only [h₁, congrArg (((m : ℝ) + 1) * ·) hat]
      have hrat := (one_add_mul_rpow_inv_gt hm ht).trans (by simpa using hfrac 1 (by decide))
      have hnorm : lam ^ (m + 2) + (1 - t) * lam ^ (m + 1) -
          (1 + ((m : ℝ) + 1) * t) * lam - (1 + (m : ℝ) * t) = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left ha'.ne'
        linear_combination hG - (lam ^ (m + 1) + ((m : ℝ) + 1) * lam + m) * hat
      have hlast := upper_at_last hm ht ht₁ hcut' hrat hnorm
      let n := m - 1
      have hn : 0 < n := by dsimp [n]; omega
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hcast : (n : ℝ) = (m : ℝ) - 1 := by
        simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) (show 1 ≤ m by omega))
      rw [← hcast] at hlast
      let r : ℝ := p / (n : ℝ)
      have hr : 0 < r := div_pos hp' hn'
      have hr₁ : r ≤ 1 := (div_le_one hn').2 (by exact_mod_cast hpm)
      have hkey : r * (n : ℝ) = p := by dsimp [r]; field_simp
      have hgeom := Real.geom_mean_le_arith_mean2_weighted (p₁ := 1 + (n : ℝ) * t)
        (p₂ := 1) hr.le (sub_nonneg.mpr hr₁) (by positivity) zero_le_one
        (show r + (1 - r) = 1 by ring)
      have hpow : lam ^ p < (1 + (n : ℝ) * t) ^ r := by
        rw [← rpow_nat_div hlam.le hn.ne' p]
        exact Real.rpow_lt_rpow (by positivity) hlast hr
      have hgeom' : (1 + (n : ℝ) * t) ^ r ≤ 1 + (p : ℝ) * t := by
        simpa only [Real.one_rpow, mul_one,
          show r * (1 + (n : ℝ) * t) + (1 - r) = 1 + (p : ℝ) * t by
            linear_combination t * hkey] using hgeom
      have h := mul_lt_mul_of_pos_left (hpow.trans_le hgeom') ha'
      nlinarith only [h, congrArg ((p : ℝ) * ·) hat]
    · have hx₁ := (arithProgPoly_eq3_existsUnique_pos hm hd hda).2 lam hlam hG
      have hp : p = 1 := by omega
      subst p
      norm_num at hG ⊢
      by_contra! hh
      have hcube : (2 : ℝ) ^ 3 ≤ lam ^ 3 := by gcongr
      nlinarith only [hG, hx₁, mul_nonneg (sub_nonneg.mpr hcube) hlam.le]
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith

end MetaMathlibExt
