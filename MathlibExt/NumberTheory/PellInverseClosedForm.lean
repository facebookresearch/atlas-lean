/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellRotatedSquare
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.Zsqrtd.ToReal

/-!
# Inverting the sum of the Pell interpolating functions

The smaller quadratic root gives the first coordinate `z` of the point on
`u² - D v² = 1` with nonnegative coordinates and `u + v = x`.
-/

namespace MetaMathlibExt

namespace pell_inverse_closed_form

private theorem inverse_coordinates {d x : ℝ} (hd : 1 < d) (hx : 1 ≤ x) :
    let z := (d * x - Real.sqrt (d * x ^ 2 - d + 1)) / (d - 1)
    1 ≤ z ∧ Real.sqrt (z ^ 2 - 1) = Real.sqrt d * (x - z) := by
  intro z
  let r := Real.sqrt (d * x ^ 2 - d + 1)
  have hd₀ := sub_pos.mpr hd
  have hx₂ : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hxr : x ≤ r := Real.le_sqrt_of_sq_le (by
    nlinarith only [mul_nonneg hd₀.le (sub_nonneg.mpr hx₂)])
  have hr₂ : r ^ 2 = d * x ^ 2 - d + 1 := Real.sq_sqrt (by
    nlinarith only [mul_nonneg (zero_lt_one.trans hd).le (sub_nonneg.mpr hx₂)])
  have hz : z * (d - 1) = d * x - r := div_mul_cancel₀ _ hd₀.ne'
  have hz₁ : 1 ≤ z := by
    apply (le_div_iff₀ hd₀).2
    have hr : r ≤ d * (x - 1) + 1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · nlinarith only [mul_nonneg (zero_lt_one.trans hd).le (sub_nonneg.mpr hx)]
      · nlinarith only [mul_nonneg (mul_nonneg (zero_lt_one.trans hd).le hd₀.le)
          (sq_nonneg (x - 1))]
    linarith
  have hzx : z ≤ x := by
    apply (div_le_iff₀ hd₀).2
    linarith
  -- The defining quadratic gives the norm equation for (z, x - z).
  have hnorm : z ^ 2 - 1 = d * (x - z) ^ 2 := by
    apply mul_left_cancel₀ hd₀.ne'
    linear_combination (d * x - z * (d - 1) + r) * hz - hr₂
  refine ⟨hz₁, ?_⟩
  rw [hnorm, Real.sqrt_mul (zero_lt_one.trans hd).le, Real.sqrt_sq (sub_nonneg.mpr hzx)]

end pell_inverse_closed_form

/-- **Closed form for inverting the sum of the Pell interpolating functions.** Let $D$ be an
integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation $X^2 - D Y^2 = 1$,
put $\varepsilon = \alpha + \beta \sqrt{D}$ and $\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(t) = (\varepsilon^t + \bar\varepsilon^t) / 2$ and
$v(t) = (\varepsilon^t - \bar\varepsilon^t) / (2 \sqrt{D})$ for real $t$. For every real $x \ge 1$,
put $z = (D x - \sqrt{D x^2 - D + 1}) / (D - 1)$ and
$g = \log(z + \sqrt{z^2 - 1}) / \log \varepsilon$. Then $g \ge 0$ and $u(g) + v(g) = x$.

Here $\log(z + \sqrt{z^2 - 1})$ is $\cosh^{-1}(z)$ written in logarithmic form.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.2, Equation (2.1)
(`integers-2025-A112-thm-2-2`). -/
public theorem pell_inverse_closed_form {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x : ℝ} (hx : 1 ≤ x) :
    let z : ℝ := (D * x - Real.sqrt (D * x ^ 2 - D + 1)) / (D - 1)
    let g : ℝ := Real.log (z + Real.sqrt (z ^ 2 - 1)) / Real.log (a.x + a.y * Real.sqrt D)
    0 ≤ g ∧ pellU D a.x a.y g + pellV D a.x a.y g = x := by
  intro z g
  have hD : (1 : ℝ) < D := by
    have hne : D ≠ 1 := fun h => ha.d_nonsquare (h ▸ IsSquare.one)
    have hpos := ha.d_pos
    exact_mod_cast (show (1 : ℤ) < D by omega)
  obtain ⟨hz, hrad⟩ := pell_inverse_closed_form.inverse_coordinates hD hx
  let ε : ℝ := a.x + a.y * Real.sqrt D
  have hε : 1 < ε := by
    have hα : 1 < (a.x : ℝ) := by exact_mod_cast ha.1
    have hβ : 0 ≤ (a.y : ℝ) := by exact_mod_cast ha.2.1.le
    exact lt_add_of_lt_of_nonneg hα (mul_nonneg hβ (Real.sqrt_nonneg _))
  let s := Real.sqrt (z ^ 2 - 1)
  have harg : 1 ≤ z + s := le_add_of_le_of_nonneg hz (Real.sqrt_nonneg _)
  have hpow : ε ^ g = z + s :=
    Real.rpow_logb (zero_lt_one.trans hε) hε.ne' (zero_lt_one.trans_le harg)
  have hconj : (a.x : ℝ) - a.y * Real.sqrt D = ε⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (zero_lt_one.trans hε).ne').mp
    change (_ - _) * (_ + _) = 1
    rw [mul_comm, ← sq_sub_sq, mul_pow, Real.sq_sqrt (zero_lt_one.trans hD).le, mul_comm _ (D : ℝ)]
    exact_mod_cast a.prop
  have hinv : (z + s)⁻¹ = z - s := by
    apply (mul_eq_one_iff_inv_eq₀ (zero_lt_one.trans_le harg).ne').mp
    rw [← sq_sub_sq]
    have hs : s ^ 2 = z ^ 2 - 1 := Real.sq_sqrt (sub_nonneg.mpr (one_le_pow₀ hz))
    linarith
  refine ⟨Real.logb_nonneg hε harg, ?_⟩
  unfold pellU pellV
  change (ε ^ g + _ ^ g) / 2 + (ε ^ g - _ ^ g) / (2 * Real.sqrt D) = x
  rw [hconj, Real.inv_rpow (zero_lt_one.trans hε).le, hpow, hinv]
  rw [show s = Real.sqrt D * (x - z) from hrad]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (zero_lt_one.trans hD))]
  ring

/-- **Floor of the inverse of the sum of the Pell interpolating functions.** Let $D$ be an
integer, let $(\alpha, \beta)$ be the fundamental solution of the Pell equation $X^2 - D Y^2 = 1$,
put $\varepsilon = \alpha + \beta \sqrt{D}$ and $\bar\varepsilon = \alpha - \beta \sqrt{D}$, and let
$u(s) = (\varepsilon^s + \bar\varepsilon^s) / 2$ and
$v(s) = (\varepsilon^s - \bar\varepsilon^s) / (2 \sqrt{D})$ for real $s$. If $x \ge 1$ and $t \ge 0$
are real numbers with $u(t) + v(t) = x$, then
$\lfloor t \rfloor = \lfloor (\log \lfloor x \rfloor + C) / \log \varepsilon \rfloor$, where
$C = \log(2 \sqrt{D} / (1 + \sqrt{D}))$.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Theorem 2.3, Equation (2.5)
(`integers-2025-A112-thm-2-3`). -/
public theorem pell_inverse_floor {D : ℤ} {a : Pell.Solution₁ D}
    (ha : Pell.IsFundamental a) {x t : ℝ} (hx : 1 ≤ x) (ht : 0 ≤ t)
    (htx : pellU D a.x a.y t + pellV D a.x a.y t = x) :
    ⌊t⌋ = ⌊(Real.log (⌊x⌋ : ℝ) + Real.log (2 * Real.sqrt D / (1 + Real.sqrt D))) /
      Real.log (a.x + a.y * Real.sqrt D)⌋ := by
  let r := Real.sqrt D
  have hD : (1 : ℝ) < D := by
    have hne : D ≠ 1 := fun h => ha.d_nonsquare (h ▸ IsSquare.one)
    have hpos := ha.d_pos
    exact_mod_cast (show (1 : ℤ) < D by omega)
  have hr : 1 < r := Real.lt_sqrt_of_sq_lt (by simpa using hD)
  have hr₀ : 0 < r := zero_lt_one.trans hr
  let ε : ℝ := a.x + a.y * r
  have hε : 1 < ε := by
    have hα : 1 < (a.x : ℝ) := by exact_mod_cast ha.1
    have hβ : 0 ≤ (a.y : ℝ) := by exact_mod_cast ha.2.1.le
    exact lt_add_of_lt_of_nonneg hα (mul_nonneg hβ hr₀.le)
  let e : Pell.Solution₁ D →* ℝ :=
    (Zsqrtd.toReal ha.d_pos.le).toMonoidHom.comp (Submonoid.subtype (unitary (ℤ√D)))
  have he (b : Pell.Solution₁ D) : e b = (b.x : ℝ) + b.y * r := rfl
  have hea : e a = ε := he a
  have he_inv (b : Pell.Solution₁ D) : e b⁻¹ = (b.x : ℝ) - b.y * r := by
    rw [he, Pell.Solution₁.x_inv, Pell.Solution₁.y_inv, Int.cast_neg, neg_mul, sub_eq_add_neg]
  have hε₀ := zero_lt_one.trans hε
  have hconj : e a⁻¹ = ε⁻¹ := (mul_eq_one_iff_eq_inv₀ hε₀.ne').mp (by
    rw [← hea, ← map_mul, inv_mul_cancel, map_one])
  let A := (1 + r) / (2 * r)
  let B := 1 - A
  have hden : 0 < 2 * r := by positivity
  have hA : 0 < A := div_pos (by positivity) hden
  have hA₁ : A < 1 := (div_lt_iff₀ hden).2 (by linarith)
  have hhalf : 1 / 2 < A := (lt_div_iff₀ hden).2 (by linarith)
  have hB : 0 < B := sub_pos.mpr hA₁
  have hBA : B < A := by dsimp only [B]; linarith
  let f (s : ℝ) := pellU D a.x a.y s + pellV D a.x a.y s
  have hF (s : ℝ) : f s = A * ε ^ s + B * (ε ^ s)⁻¹ := by
    unfold f pellU pellV
    change (ε ^ s + _ ^ s) / 2 + (ε ^ s - _ ^ s) / (2 * r) = _
    rw [← he_inv a, hconj, Real.inv_rpow hε₀.le]
    dsimp only [A, B]
    field_simp [hr₀.ne']
    ring
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    intro u hu v _ huv
    let p := ε ^ u
    let q := ε ^ v
    have hp : 1 ≤ p := Real.one_le_rpow hε.le hu
    have hpq : p < q := Real.rpow_lt_rpow_of_exponent_lt hε huv
    have hprod : 1 ≤ p * q := one_le_mul_of_one_le_of_one_le hp (hp.trans hpq.le)
    -- For 1 ≤ p < q, the inverse term drops by at most q - p.
    have hinv : p⁻¹ - q⁻¹ ≤ q - p := by
      calc
        p⁻¹ - q⁻¹ = (q - p) / (p * q) := by
          field_simp [(zero_lt_one.trans_le hp).ne', (zero_lt_one.trans_le (hp.trans hpq.le)).ne']
        _ ≤ q - p := div_le_self (sub_nonneg.mpr hpq.le) hprod
    rw [hF, hF]
    change A * p + B * p⁻¹ < A * q + B * q⁻¹
    nlinarith only [mul_le_mul_of_nonneg_left hinv hB.le,
      mul_lt_mul_of_pos_right hBA (sub_pos.mpr hpq)]
  let m (j : ℕ) : ℤ := (a ^ j).x + (a ^ j).y
  -- At natural exponents the conjugate evaluations give the two integer Pell coordinates.
  have hm (j : ℕ) : f j = (m j : ℝ) := by
    have hp : ε ^ j = ((a ^ j).x : ℝ) + (a ^ j).y * r := by
      rw [← hea, ← map_pow, he]
    have hq : ε⁻¹ ^ j = ((a ^ j).x : ℝ) - (a ^ j).y * r := by
      rw [← hconj, ← map_pow, inv_pow, he_inv]
    rw [hF, Real.rpow_natCast, ← inv_pow, hp, hq]
    simp only [m, Int.cast_add, A, B]
    field_simp [hr₀.ne']
    ring
  have htail (j : ℕ) : 0 < B * (ε ^ (j : ℝ))⁻¹ ∧ B * (ε ^ (j : ℝ))⁻¹ < 1 := by
    have hpow : 0 < ε ^ (j : ℝ) := Real.rpow_pos_of_pos hε₀ _
    refine ⟨mul_pos hB (inv_pos.mpr hpow), ?_⟩
    have hinv := (inv_le_one₀ hpow).2 (Real.one_le_rpow hε.le (Nat.cast_nonneg _))
    exact (mul_le_of_le_one_right hB.le hinv).trans_lt (by dsimp only [B]; linarith)
  -- The integer values at the two ends of the unit interval bound the rounded input.
  let n := ⌊t⌋₊
  have hn : (n : ℤ) = ⌊t⌋ := Int.natCast_floor_eq_floor ht
  have hlo : m n ≤ ⌊x⌋ := Int.le_floor.mpr (by
    rw [← hm, ← htx]
    exact hmono.monotoneOn (Nat.cast_nonneg _) ht (Nat.floor_le ht))
  have hhi : ⌊x⌋ < m (n + 1) := Int.floor_lt.mpr (by
    rw [← hm, ← htx, Nat.cast_add, Nat.cast_one]
    exact hmono ht (Set.mem_Ici.mpr (by positivity)) (Nat.lt_floor_add_one t))
  have hlo' : A * ε ^ (n : ℝ) ≤ (⌊x⌋ : ℝ) := calc
    _ ≤ f n := by rw [hF]; exact le_add_of_nonneg_right (htail n).1.le
    _ = (m n : ℝ) := hm n
    _ ≤ _ := by exact_mod_cast hlo
  have hhi' : (⌊x⌋ : ℝ) < A * ε ^ ((n : ℝ) + 1) := by
    have h : (⌊x⌋ : ℝ) + 1 ≤ (m (n + 1) : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hhi)
    rw [← hm, hF, Nat.cast_add, Nat.cast_one] at h
    have htail' := (htail (n + 1)).2
    rw [Nat.cast_add, Nat.cast_one] at htail'
    linarith only [h, htail']
  have hx₀ : 0 < (⌊x⌋ : ℝ) := by exact_mod_cast (Int.floor_pos.mpr hx)
  have hy : 0 < (⌊x⌋ : ℝ) / A := div_pos hx₀ hA
  change ⌊t⌋ = ⌊(Real.log (⌊x⌋ : ℝ) + Real.log (2 * r / (1 + r))) / Real.log ε⌋
  rw [show 2 * r / (1 + r) = A⁻¹ from (inv_div _ _).symm,
    ← Real.log_mul hx₀.ne' (inv_pos.mpr hA).ne', ← div_eq_mul_inv, Real.log_div_log, ← hn]
  symm
  apply Int.floor_eq_iff.mpr
  push_cast
  exact ⟨(Real.le_logb_iff_rpow_le hε hy).2 ((le_div_iff₀ hA).2 (by rwa [mul_comm])),
    (Real.logb_lt_iff_lt_rpow hε hy).2 ((div_lt_iff₀ hA).2 (by rwa [mul_comm]))⟩

end MetaMathlibExt
