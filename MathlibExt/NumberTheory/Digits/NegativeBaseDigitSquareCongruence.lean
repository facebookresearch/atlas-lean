/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A congruence for the negative-base digit-square sum

We prove Lemma 3.1 of Grundman's *Closing an Open Problem on Negative Base Happy Numbers*.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Truncated digit-square sum in a negative base.** For an integer $b$, define $T_b(f, a)$ for a
natural number $f$ and an integer $a$ by recursion on $f$: $T_b(0, a) = 0$, $T_b(f + 1, 0) = 0$,
and for $a \ne 0$, $T_b(f + 1, a) = r^2 + T_b(f, (a - r)/b)$, where $r = a \bmod b$ is the
remainder of $a$ on division by $b$, with $0 \le r < |b|$ (for $b = 0$ one takes $r = a$ and
$(a - r)/b = 0$). For $b \le -2$, $T_b(f, a)$ is thus the sum of the squares of the first $f$
base-$b$ digits of $a$, counted from the least significant one.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def negBaseSqDigitSumAux (b : ℤ) : ℕ → ℤ → ℤ
  | 0, _ => 0
  | fuel + 1, a =>
      if a = 0 then 0 else (a % b) ^ 2 + negBaseSqDigitSumAux b fuel ((a - a % b) / b)

/-- **Sum of squared digits in a negative base.** Let $b \le -2$ be an integer. Every integer $a$
has an expansion $a = \sum_{i=0}^{n} a_i b^i$ with digits $0 \le a_i \le |b| - 1$, unique up to
leading zero digits, and $S_{2,b}(a) = \sum_{i=0}^{n} a_i^2$ is the sum of the squares of these
digits. The digits are produced from the least significant one by taking $a_0 = a \bmod b$ and
passing to $(a - a_0)/b$, until $0$ is reached.

The definition is made for every integer $b$, by running this digit extraction for at most
$2|a| + 2$ steps; for $b \le -2$ this suffices, since the quantity $2a$ (for $a \ge 0$) or
$2|a| + 1$ (for $a < 0$) strictly decreases at each step.

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Section 2. -/
def negBaseSqDigitSum (b a : ℤ) : ℤ :=
  negBaseSqDigitSumAux b (2 * a.natAbs + 2) a

end

-- The extra unit on negative inputs handles the step from `-1` to `1`.
private def digitRank (a : ℤ) : ℕ := 2 * a.natAbs + if a < 0 then 1 else 0

private theorem digitRank_lt {B q d : ℤ} (hB : 2 ≤ B) (hd0 : 0 ≤ d) (hd : d < B)
    (ha : -B * q + d ≠ 0) : digitRank q < digitRank (-B * q + d) := by
  set a := -B * q + d with ea
  have haq : (a.natAbs : ℤ) = |a| := Int.natCast_natAbs a
  have hqq : (q.natAbs : ℤ) = |q| := Int.natCast_natAbs q
  by_cases hq : q < 0
  · have hmul := mul_le_mul_of_nonneg_right hB (show 0 ≤ -q by omega)
    have h : -q < a := by nlinarith
    rw [abs_of_neg hq] at hqq
    rw [abs_of_nonneg (show 0 ≤ a by omega)] at haq
    simp only [digitRank, ite_eq_left hq, ite_eq_right (show ¬a < 0 by omega), add_zero]
    omega
  · by_cases hq0 : q = 0
    · have hap : 0 < a := by rw [hq0, mul_zero, zero_add] at ea; omega
      rw [abs_of_nonneg hap.le] at haq
      simp only [digitRank, hq0, Int.natAbs_zero, mul_zero, lt_irrefl, ite_false,
        ite_eq_right (not_lt.mpr hap.le), add_zero]
      omega
    · have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ q by omega)
        (show 0 ≤ B - 1 by omega)
      have h : q ≤ -a := by nlinarith
      have han : a < 0 := by omega
      rw [abs_of_nonneg (show 0 ≤ q by omega)] at hqq
      rw [abs_of_neg han] at haq
      simp only [digitRank, ite_eq_right hq, ite_eq_left han, add_zero]
      omega

private theorem digitSumAux_zero (B : ℤ) (f : ℕ) : negBaseSqDigitSumAux (-B) f 0 = 0 := by
  cases f <;> simp [negBaseSqDigitSumAux]

private theorem digitSumAux_stable {B : ℤ} (hB : 2 ≤ B) {f g : ℕ} {a : ℤ}
    (hf : digitRank a ≤ f) (hg : digitRank a ≤ g) :
    negBaseSqDigitSumAux (-B) f a = negBaseSqDigitSumAux (-B) g a := by
  induction f generalizing a g with
  | zero =>
    have ha : a = 0 := by
      have := Int.natAbs_eq_zero (a := a)
      unfold digitRank at hf
      omega
    subst a
    simp only [digitSumAux_zero]
  | succ f ih =>
    by_cases ha : a = 0
    · subst a
      simp only [digitSumAux_zero]
    have hgpos : 0 < g := by
      have := Int.natAbs_eq_zero (a := a)
      unfold digitRank at hg
      omega
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hgpos.ne'
    let d := a % (-B)
    let q := (a - d) / (-B)
    have hb : -B ≠ 0 := by omega
    have hd0 : 0 ≤ d := Int.emod_nonneg _ hb
    have hd : d < B := by
      dsimp [d]
      rw [Int.emod_neg]
      exact Int.emod_lt_of_pos _ (by omega)
    have ea : -B * q + d = a := by
      have hdecomp := Int.mul_ediv_add_emod a (-B)
      have hquot : q = a / (-B) := by
        dsimp [q, d]
        rw [show a - a % (-B) = (-B) * (a / (-B)) by linarith]
        rw [mul_comm, Int.mul_ediv_cancel _ hb]
      rw [hquot, hdecomp]
    have hqa : digitRank q < digitRank a := by
      rw [← ea]
      exact digitRank_lt hB hd0 hd (ea ▸ ha)
    simp only [negBaseSqDigitSumAux, ite_eq_right ha]
    rw [ih (show digitRank q ≤ f by omega) (show digitRank q ≤ g by omega)]

private theorem digitSum_cons {B q d : ℤ} (hB : 2 ≤ B) (hd0 : 0 ≤ d) (hd : d < B) :
    negBaseSqDigitSum (-B) (-B * q + d) = d ^ 2 + negBaseSqDigitSum (-B) q := by
  let a := -B * q + d
  have hb : -B ≠ 0 := by omega
  have hr : a % (-B) = d := by
    dsimp [a]
    rw [Int.add_emod, Int.mul_emod_right, zero_add, Int.emod_emod, Int.emod_neg,
      Int.emod_eq_of_lt hd0 hd]
  have hq : (a - d) / (-B) = q := by
    rw [show a - d = q * (-B) by dsimp [a]; ring, Int.mul_ediv_cancel _ hb]
  change negBaseSqDigitSum (-B) a = _
  by_cases ha : a = 0
  · have hdz : d = 0 := by simpa [ha] using hr.symm
    have hqz : q = 0 := by simpa [ha, hdz] using hq.symm
    simp [ha, hdz, hqz]
  have hqa : digitRank q < digitRank a := digitRank_lt hB hd0 hd ha
  have bound (z : ℤ) : digitRank z ≤ 2 * z.natAbs + 1 := by
    unfold digitRank
    split <;> omega
  unfold negBaseSqDigitSum
  rw [show 2 * a.natAbs + 2 = (2 * a.natAbs + 1) + 1 from rfl, negBaseSqDigitSumAux,
    ite_eq_right ha, hr, hq]
  congr 1
  exact digitSumAux_stable hB (by have := bound a; omega) (by have := bound q; omega)

private theorem digitSum_three {B e d c : ℤ} (hB : 2 ≤ B)
    (he0 : 0 ≤ e) (he : e < B) (hd0 : 0 ≤ d) (hd : d < B) (hc0 : 0 ≤ c) (hc : c < B) :
    negBaseSqDigitSum (-B) (e * (-B) ^ 2 + d * (-B) + c) = c ^ 2 + d ^ 2 + e ^ 2 := by
  rw [show e * (-B) ^ 2 + d * (-B) + c = -B * (-B * e + d) + c by ring,
    digitSum_cons hB hc0 hc, digitSum_cons hB hd0 hd]
  conv_lhs => rw [show e = -B * 0 + e by ring, digitSum_cons hB he0 he]
  unfold negBaseSqDigitSum
  rw [digitSumAux_zero, add_zero, add_assoc]

-- Work with the positive magnitude of the base. The only disallowed choices of `c`
-- in a full residue system correspond to the two residues 2 and 4 of this expression.
private def congrValue (B v w : ℤ) : ℤ :=
  negBaseSqDigitSum (-B) ((B - 1) * (-B) + v - w - 1) -
    negBaseSqDigitSum (-B) ((B - 1) * (-B) ^ 2 + B - 1 - w) + 5

private theorem base_modEq (B : ℤ) : B ≡ -1 [ZMOD B + 1] :=
  Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩

private theorem cancelTwo {B t x y : ℤ} (ht : 2 * t = B)
    (h : 2 * x ≡ 2 * y [ZMOD B + 1]) : x ≡ y [ZMOD B + 1] := by
  have hbxy : B * x ≡ B * y [ZMOD B + 1] := by
    convert h.mul_left t using 1 <;> rw [← ht] <;> ring
  have hneg := ((base_modEq B).mul_right x).symm.trans
    (hbxy.trans ((base_modEq B).mul_right y))
  exact Int.neg_modEq_neg.mp (by simpa using hneg)

private theorem eq_of_close_modEq {n x y : ℤ} (hn : 0 ≤ n) (h : x ≡ y [ZMOD n])
    (hlo : -n < y - x) (hhi : y - x < n) : x = y := by
  have ha : |y - x| < n := abs_lt.mpr ⟨hlo, hhi⟩
  have hc := Int.natCast_natAbs (y - x)
  have hnc := Int.natCast_natAbs n
  rw [abs_of_nonneg hn] at hnc
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h.dvd (by omega)
  omega

private theorem badResidue {B t E : ℤ} (hB : 12 ≤ B) (ht : 2 * t = B)
    (hbad : ¬ ∃ c : ℤ, 0 ≤ c ∧ c ≤ B - 2 ∧ E + 2 * c ≡ 0 [ZMOD B + 1]) :
    ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ E ≡ 2 * r [ZMOD B + 1] := by
  let c := (t * E) % (B + 1)
  have hc0 : 0 ≤ c := Int.emod_nonneg _ (by omega)
  have hcB : c < B + 1 := Int.emod_lt_of_pos _ (by omega)
  have hc : 2 * c ≡ -E [ZMOD B + 1] := calc
    2 * c ≡ 2 * (t * E) [ZMOD B + 1] := (Int.mod_modEq _ _).mul_left 2
    _ = B * E := by rw [← ht]; ring
    _ ≡ -E [ZMOD B + 1] := by simpa using (base_modEq B).mul_right E
  have hzero : E + 2 * c ≡ 0 [ZMOD B + 1] := by simpa using hc.add_left E
  have htop : c = B - 1 ∨ c = B := by
    by_contra hn
    exact hbad ⟨c, hc0, by omega, hzero⟩
  have hE : E ≡ -(2 * c) [ZMOD B + 1] := by simpa using hc.symm.neg
  rcases htop with hc' | hc'
  · refine ⟨2, Or.inr rfl, hE.trans ?_⟩
    rw [hc']
    exact Int.modEq_iff_dvd.mpr ⟨2, by ring⟩
  · refine ⟨1, Or.inl rfl, hE.trans ?_⟩
    rw [hc']
    exact Int.modEq_iff_dvd.mpr ⟨2, by ring⟩

private theorem halfStep {B t E₀ E₁ s r₀ r₁ : ℤ} (ht : 2 * t = B)
    (h₀ : E₀ ≡ 2 * r₀ [ZMOD B + 1]) (h₁ : E₁ ≡ 2 * r₁ [ZMOD B + 1])
    (hs : E₁ - E₀ = 2 * s) : s ≡ r₁ - r₀ [ZMOD B + 1] := by
  apply cancelTwo ht
  have hd := h₁.sub h₀
  rw [hs] at hd
  convert hd using 1; ring

private theorem noThreeBad {B t E₀ E₁ E₂ s : ℤ} (hB : 12 ≤ B) (ht : 2 * t = B)
    (hs₀ : -(B + 1) < s) (hs₁ : s < B + 1) (hs : s ≠ 0)
    (hd₁ : E₁ - E₀ = 2 * s) (hd₂ : E₂ - E₁ = 2 * s)
    (h₀ : ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ E₀ ≡ 2 * r [ZMOD B + 1])
    (h₁ : ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ E₁ ≡ 2 * r [ZMOD B + 1])
    (h₂ : ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ E₂ ≡ 2 * r [ZMOD B + 1]) : False := by
  obtain ⟨r₀, hr₀, hr₀'⟩ := h₀
  obtain ⟨r₁, hr₁, hr₁'⟩ := h₁
  obtain ⟨r₂, hr₂, hr₂'⟩ := h₂
  have h01 := halfStep ht hr₀' hr₁' hd₁
  have h12 := halfStep ht hr₁' hr₂' hd₂
  have he := eq_of_close_modEq (by omega) (h01.symm.trans h12) (by omega) (by omega)
  have hr : r₁ - r₀ = 0 := by omega
  rw [hr] at h01
  exact hs (eq_of_close_modEq (by omega) h01 (by omega) (by omega))

-- If advancing `w` twice changes only the two units digits, the difference of
-- their squares has constant step. A nonzero step cannot stay in two bad residues.
private theorem lowDigitsNotAllBad {B t v w q d : ℤ} (hB : 12 ≤ B) (ht : 2 * t = B)
    (hw : 0 ≤ w) (hwB : w + 2 < B) (hwv : w + 2 < v) (hd0 : 2 ≤ d) (hdB : d < B)
    (hne : d ≠ B - 1 - w) (ha : (B - 1) * (-B) + v - w - 1 = -B * q + d)
    (hbad : ∀ w : ℤ, 0 ≤ w → w < v →
      ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ congrValue B v w ≡ 2 * r [ZMOD B + 1]) : False := by
  have hval (j : ℤ) (hj : 0 ≤ j) (hj' : j ≤ 2) :
      congrValue B v (w + j) =
        (d - j) ^ 2 + negBaseSqDigitSum (-B) q -
          ((B - 1 - w - j) ^ 2 + negBaseSqDigitSum (-B) ((B - 1) * (-B))) + 5 := by
    unfold congrValue
    rw [show (B - 1) * (-B) + v - (w + j) - 1 = -B * q + (d - j) by linarith,
      show (B - 1) * (-B) ^ 2 + B - 1 - (w + j) =
        -B * ((B - 1) * (-B)) + (B - 1 - w - j) by ring,
      digitSum_cons (by omega) (by omega : 0 ≤ d - j) (by omega),
      digitSum_cons (by omega) (by omega : 0 ≤ B - 1 - w - j) (by omega)]
  apply noThreeBad hB ht (s := B - 1 - w - d) (by omega) (by omega) (by omega)
      (E₀ := congrValue B v (w + 0)) (E₁ := congrValue B v (w + 1))
      (E₂ := congrValue B v (w + 2))
  · rw [hval 0 (by decide) (by decide), hval 1 (by decide) (by decide)]
    ring
  · rw [hval 1 (by decide) (by decide), hval 2 (by decide) (by decide)]
    ring
  · exact hbad _ (by omega) (by omega)
  · exact hbad _ (by omega) (by omega)
  · exact hbad _ (by omega) (by omega)

private theorem congrValue_small {B v : ℤ} (hB : 12 ≤ B) (hv0 : 1 ≤ v) (hv : v ≤ 2) :
    congrValue B v (v - 1) = 5 - (B - v) ^ 2 := by
  unfold congrValue
  rw [show (B - 1) * (-B) + v - (v - 1) - 1 = 0 * (-B) ^ 2 + (B - 1) * (-B) + 0 by ring,
    show (B - 1) * (-B) ^ 2 + B - 1 - (v - 1) =
      (B - 1) * (-B) ^ 2 + 0 * (-B) + (B - v) by ring,
    digitSum_three (by omega) (by decide : (0 : ℤ) ≤ 0) (by omega) (by omega) (by omega)
      (by decide : (0 : ℤ) ≤ 0) (by omega),
    digitSum_three (by omega) (by omega) (by omega) (by decide : (0 : ℤ) ≤ 0) (by omega)
      (by omega) (by omega)]
  ring

-- When the units digits coincide, shift `w` by whole multiples of `B`
-- to compare the middle digits instead.
private theorem multiplesNotAllBad {B t v q : ℤ} (hB : 12 ≤ B) (ht : 2 * t = B)
    (hq₀ : 0 < q) (hq₂ : q < 2 * B) (hvq : v = B * q)
    (hbad : ∀ w : ℤ, 0 ≤ w → w < v →
      ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ congrValue B v w ≡ 2 * r [ZMOD B + 1]) : False := by
  let e : ℤ := if q ≤ B then 0 else 1
  let a : ℤ := B - q + e * B
  have he : e = 0 ∨ e = 1 := by unfold e; split <;> simp
  have ha : 0 ≤ a ∧ a < B := by unfold a e; split <;> simp <;> omega
  have hval (j : ℤ) (hj₀ : 0 ≤ j) (hj₂ : j ≤ 2) (hjB : a + j < B) :
      congrValue B v (j * B) = (a + j) ^ 2 + e ^ 2 + 5 - (B - 1) ^ 2 - j ^ 2 := by
    unfold congrValue
    rw [show (B - 1) * (-B) + v - j * B - 1 =
          e * (-B) ^ 2 + (a + j) * (-B) + (B - 1) by rw [hvq]; dsimp [a]; ring,
      show (B - 1) * (-B) ^ 2 + B - 1 - j * B =
          (B - 1) * (-B) ^ 2 + j * (-B) + (B - 1) by ring,
      digitSum_three (by omega) (by omega) (by omega) (by omega) hjB (by omega) (by omega),
      digitSum_three (by omega) (by omega) (by omega) hj₀ (by omega) (by omega) (by omega)]
    ring
  have hsquare : (B - 1) ^ 2 ≡ 4 [ZMOD B + 1] := by
    simpa using ((base_modEq B).sub_right 1).pow 2
  have hvpos : 0 < v := hvq ▸ mul_pos (show 0 < B by omega) hq₀
  have hval₀ : congrValue B v 0 = a ^ 2 + e ^ 2 + 5 - (B - 1) ^ 2 := by
    simpa using hval 0 (by decide) (by decide) (by simpa using ha.2)
  obtain ⟨r₀, hr₀, h₀⟩ := hbad 0 (by decide) hvpos
  have he2 : e ^ 2 = e := by rcases he with he' | he' <;> simp [he']
  have hane : a ≠ B - 1 := by
    intro hae
    have h := h₀
    rw [hval₀, hae, he2, show (B - 1) ^ 2 + e + 5 - (B - 1) ^ 2 = e + 5 by ring] at h
    have := eq_of_close_modEq (by omega) h (by omega) (by omega)
    omega
  have hq₁ : 1 < q := by
    by_contra! hq
    have hq' : q = 1 := by omega
    apply hane
    simp [a, e, hq', show 1 ≤ B by omega]
  have hval₁ : congrValue B v B = (a + 1) ^ 2 + e ^ 2 + 5 - (B - 1) ^ 2 - 1 := by
    simpa using hval 1 (by decide) (by decide) (by omega)
  have hvB : B < v := by
    rw [hvq]
    simpa using mul_lt_mul_of_pos_left hq₁ (show 0 < B by omega)
  obtain ⟨r₁, hr₁, h₁⟩ := hbad B (by omega) hvB
  have hstep : congrValue B v B - congrValue B v 0 = 2 * a := by
    rw [hval₁, hval₀]
    ring
  have hamod := halfStep ht h₀ h₁ hstep
  have hasmall : a = 0 ∨ a = 1 := by
    have := eq_of_close_modEq (by omega) hamod (by omega) (by omega)
    omega
  have ha2 : a ^ 2 = a := by rcases hasmall with ha' | ha' <;> simp [ha']
  have hred₀ : congrValue B v 0 ≡ a + e + 1 [ZMOD B + 1] := by
    rw [hval₀, ha2, he2]
    convert (hsquare.sub_left (a + e + 5)) using 1; ring
  have hsmall := eq_of_close_modEq (by omega) (hred₀.symm.trans h₀) (by omega) (by omega)
  have ha' : a = 1 ∧ e = 0 := by
    have hdef : a = B - q + e * B := rfl
    rcases he with he' | he' <;> (rw [he'] at hdef; omega)
  have hq' : q = B - 1 := by
    have hdef : a = B - q + e * B := rfl
    rw [ha'.1, ha'.2] at hdef
    omega
  have hv2B : 2 * B < v := by
    rw [hvq, hq', mul_comm 2 B]
    exact mul_lt_mul_of_pos_left (by omega) (by omega)
  obtain ⟨r₂, hr₂, h₂⟩ := hbad (2 * B) (by omega) hv2B
  have hred₂ : congrValue B v (2 * B) ≡ 6 [ZMOD B + 1] := by
    rw [hval 2 (by decide) (by decide) (by omega), ha'.1, ha'.2]
    convert (hsquare.sub_left 10) using 1 <;> ring
  have := eq_of_close_modEq (by omega) (hred₂.symm.trans h₂) (by omega) (by omega)
  omega

/-- **A congruence for the negative-base digit-square map.** Let $b \le -12$ be an even integer,
let $S_{2,b}$ be the map sending an integer to the sum of the squares of its base-$b$ digits, and
let $v$ be an integer with $0 < v < 2b^2$. Then there are integers $w$ and $c$ with
$0 \le w < v$ and $0 \le c \le |b| - 2$ such that
$$S_{2,b}\bigl((|b| - 1)b + v - w - 1\bigr) -
S_{2,b}\bigl((|b| - 1)b^2 + |b| - 1 - w\bigr) + 5 + 2c \equiv 0 \pmod{|b| + 1}.$$

Source: Helen G. Grundman, *Closing an Open Problem on Negative Base Happy Numbers*, The Fibonacci
Quarterly 62 (2024), Article 62-2/grundman11162023, Lemma 3.1. -/
public theorem exists_negBaseSqDigitSum_congr (b : ℤ) (hb : b ≤ -12) (heven : Even b)
    (v : ℤ) (hv0 : 0 < v) (hv : v < 2 * b ^ 2) :
    ∃ w c : ℤ, 0 ≤ w ∧ w < v ∧ 0 ≤ c ∧ c ≤ |b| - 2 ∧
      negBaseSqDigitSum b ((|b| - 1) * b + v - w - 1) -
          negBaseSqDigitSum b ((|b| - 1) * b ^ 2 + |b| - 1 - w) + 5 + 2 * c ≡ 0 [ZMOD |b| + 1] := by
  rw [abs_of_neg (show b < 0 by omega)]
  set B := -b with hB_def
  have hb' : b = -B := by omega
  rw [hb'] at heven hv ⊢
  rw [neg_sq] at hv
  have hB : 12 ≤ B := by omega
  obtain ⟨k, hk⟩ := heven
  let t := -k
  have ht : 2 * t = B := by dsimp [t]; omega
  change ∃ w c : ℤ, 0 ≤ w ∧ w < v ∧ 0 ≤ c ∧ c ≤ B - 2 ∧
    congrValue B v w + 2 * c ≡ 0 [ZMOD B + 1]
  by_cases hv₂ : v ≤ 2
  · have hsmall := congrValue_small hB (by omega) hv₂
    rcases (show v = 1 ∨ v = 2 by omega) with rfl | rfl
    · refine ⟨0, t, by omega, by omega, by omega, by omega, Int.modEq_zero_iff_dvd.mpr ?_⟩
      refine ⟨4 - B, ?_⟩
      rw [show congrValue B 1 0 = 5 - (B - 1) ^ 2 from hsmall, ht]
      ring
    · refine ⟨1, 2, by omega, by omega, by omega, by omega, Int.modEq_zero_iff_dvd.mpr ?_⟩
      refine ⟨5 - B, ?_⟩
      rw [show congrValue B 2 1 = 5 - (B - 2) ^ 2 from hsmall]
      ring
  by_contra h
  have hbad (w : ℤ) (hw : 0 ≤ w) (hwv : w < v) :
      ∃ r : ℤ, (r = 1 ∨ r = 2) ∧ congrValue B v w ≡ 2 * r [ZMOD B + 1] := by
    apply badResidue hB ht
    rintro ⟨c, hc₀, hc, hcongr⟩
    exact h ⟨w, c, hw, hwv, hc₀, hc, hcongr⟩
  let q := v / B
  let r := v % B
  have hr₀ : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrB : r < B := Int.emod_lt_of_pos _ (by omega)
  have hvqr : v = B * q + r := (Int.mul_ediv_add_emod v B).symm
  by_cases hr : r = 0
  · have hvq : v = B * q := by simpa [hr] using hvqr
    have hq₀ : 0 < q := by
      by_contra! hq
      have := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ B by omega) hq
      omega
    have hq₂ : q < 2 * B := by
      apply lt_of_mul_lt_mul_left (a := B) _ (by omega)
      calc
        B * q = v := hvq.symm
        _ < 2 * B ^ 2 := hv
        _ = B * (2 * B) := by ring
    exact multiplesNotAllBad hB ht hq₀ hq₂ hvq hbad
  by_cases hr₃ : 3 ≤ r
  · refine lowDigitsNotAllBad hB ht (w := 0) (q := B - 1 - q) (d := r - 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ hbad
    rw [hvqr]
    ring
  · have hq : 1 ≤ q := by
      have hq₀ := Int.ediv_nonneg hv0.le (show 0 ≤ B by omega)
      change 0 ≤ q at hq₀
      by_contra! hq₁
      have hqz : q = 0 := by omega
      rw [hqz, mul_zero, zero_add] at hvqr
      omega
    have hBq : B ≤ B * q := by
      simpa using mul_le_mul_of_nonneg_left hq (show 0 ≤ B by omega)
    refine lowDigitsNotAllBad hB ht (w := r) (q := B - q) (d := B - 1)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ hbad
    rw [hvqr]
    ring

end MetaMathlibExt
