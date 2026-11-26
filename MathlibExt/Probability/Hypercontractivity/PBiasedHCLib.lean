/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Hypercontractivity.PBiasedConvexity
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The two-point hypercontractive inequality for `2 ≤ q ≤ 4`

The two-point (Bonami–Gross) inequality on the symmetric two-point space:
`((|a + b|^q + |a - b|^q) / 2)^(2/q) ≤ a² + (q - 1) b²` for `q ≥ 2`. Despite the module name, the
measure here is the uniform one on `{±1}`, not a `p`-biased one.

The proof shows that `K(t) = (1 + (q-1)t²)^(q/2) - ((1+t)^q + (1-t)^q)/2` is convex on `[-1, 1]`;
convexity reduces to the pointwise "bracket" inequality `hclib_BracketResidue q`. The bracket
inequality is proved here only for `2 ≤ q ≤ 4` (`hclib_BracketResidue_of_le_four`), so the
unconditional results (`hclib_two_point_forward`, `hclib_forward_scalar`) are restricted to
`q ≤ 4`, i.e. `ρ² ≥ 1/3` when `q = 1 + 1/ρ²`. For `q > 4` the forward inequality
`hclib_forward_core_of_bracket` is conditional on `hclib_BracketResidue q`, which is not discharged.

## Main definitions

* `StatMech.Probability.hclib_BracketResidue q`: the bracket inequality used for convexity of `K`.
* `StatMech.Probability.hclib_K`: the convexity witness `K`.

## Main results

* `StatMech.Probability.hclib_BracketResidue_of_le_four`.
* `StatMech.Probability.hclib_forward_core_of_bracket`: conditional forward inequality, all `q ≥ 2`.
* `StatMech.Probability.hclib_two_point_forward`: the two-point inequality for `2 ≤ q ≤ 4`.
* `StatMech.Probability.hclib_forward_scalar`: the same with `q = 1 + 1/ρ²`, `1/3 ≤ ρ² ≤ 1`.

## References

* A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p(G)`*, Ann. Inst. Fourier 20
  (1970), 335–402.
* L. Gross, *Logarithmic Sobolev inequalities*, Amer. J. Math. 97 (1975), 1061–1083.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014, Chapter 9.
-/

@[expose] public section

open Real Set

namespace StatMech.Probability

/-- Concavity of `x ↦ x^(r/2)` for `0 ≤ r ≤ 2`: `((1+t)^r + (1-t)^r)/2 ≤ (1 + t²)^(r/2)` for `|t| ≤
1`. -/
theorem hclib_jensen_two_point {r t : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (ht : |t| ≤ 1) :
    ((1 + t) ^ r + (1 - t) ^ r) / 2 ≤ (1 + t ^ 2) ^ (r / 2) := by
  rw [abs_le] at ht
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  have h2 : (0 : ℝ) ≤ 1 - t := by linarith
  have hconc := Real.concaveOn_rpow (p := r / 2) (by linarith) (by linarith)
  have hmem1 : ((1 + t) ^ 2 : ℝ) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; positivity
  have hmem2 : ((1 - t) ^ 2 : ℝ) ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; positivity
  have hJ := hconc.2 hmem1 hmem2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hJ
  have e1 : ((1 + t) ^ 2 : ℝ) ^ (r / 2) = (1 + t) ^ r := by
    rw [← Real.rpow_natCast (1 + t) 2, ← Real.rpow_mul h1]; congr 1; ring
  have e2 : ((1 - t) ^ 2 : ℝ) ^ (r / 2) = (1 - t) ^ r := by
    rw [← Real.rpow_natCast (1 - t) 2, ← Real.rpow_mul h2]; congr 1; ring
  have e3 : ((1 : ℝ) / 2 * (1 + t) ^ 2 + 1 / 2 * (1 - t) ^ 2) = 1 + t ^ 2 := by ring
  rw [e1, e2, e3] at hJ
  linarith

/-- The bracket inequality
`((1+t)^(q-2) + (1-t)^(q-2))/2 ≤ (1 + (q-1)t²)^((q-4)/2) (1 + (q-1)²t²)` for all `|t| ≤ 1`, which
makes the second derivative of `hclib_K q` nonnegative. Proved for `2 ≤ q ≤ 4` only. -/
def hclib_BracketResidue (q : ℝ) : Prop :=
  ∀ t : ℝ, |t| ≤ 1 →
    ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2
      ≤ (1 + (q - 1) * t ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2)

/-- The bracket inequality for `2 ≤ q ≤ 4`. -/
theorem hclib_bracket {q t : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) (ht : |t| ≤ 1) :
    ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2
      ≤ (1 + (q - 1) * t ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2) := by
  set w := 1 + (q - 1) * t ^ 2 with hw
  have hq1 : 0 ≤ q - 1 := by linarith
  have hwpos : 0 < w := by rw [hw]; nlinarith [mul_nonneg hq1 (sq_nonneg t)]
  have hJ := hclib_jensen_two_point (r := q - 2) (by linarith) (by linarith) ht
  have hbase : (1 : ℝ) + t ^ 2 ≤ w := by rw [hw]; nlinarith [sq_nonneg t]
  have hmono : (1 + t ^ 2) ^ ((q - 2) / 2) ≤ w ^ ((q - 2) / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hI : ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)) / 2 ≤ w ^ ((q - 2) / 2) := le_trans hJ hmono
  have hsplit : w ^ ((q - 2) / 2) = w ^ ((q - 4) / 2) * w := by
    rw [show (q - 2) / 2 = (q - 4) / 2 + 1 by ring, Real.rpow_add hwpos, Real.rpow_one]
  have hwle : w ≤ 1 + (q - 1) ^ 2 * t ^ 2 := by
    rw [hw]; nlinarith [mul_nonneg (mul_nonneg hq1 hq1) (sq_nonneg t), sq_nonneg t,
      mul_nonneg hq1 (sq_nonneg t)]
  have hII : w ^ ((q - 2) / 2) ≤ w ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * t ^ 2) := by
    rw [hsplit]; exact mul_le_mul_of_nonneg_left hwle (Real.rpow_nonneg hwpos.le _)
  linarith

/-- `hclib_BracketResidue q` holds for `2 ≤ q ≤ 4`. -/
theorem hclib_BracketResidue_of_le_four {q : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) :
    hclib_BracketResidue q :=
  fun _ ht => hclib_bracket hq2 hq4 ht

/-- The gap `(1 + (q-1)t²)^(q/2) - ((1+t)^q + (1-t)^q)/2` of the two-point inequality. -/
noncomputable def hclib_K (q t : ℝ) : ℝ :=
  (1 + (q - 1) * t ^ 2) ^ (q / 2) - ((1 + t) ^ q + (1 - t) ^ q) / 2

theorem hclib_w_pos {q t : ℝ} (hq1 : 1 ≤ q) : 0 < 1 + (q - 1) * t ^ 2 := by
  have : 0 ≤ (q - 1) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg t)
  linarith

/-- `hclib_K q` is convex on `[-1, 1]`, given the bracket inequality. -/
theorem hclib_convexOn_K {q : ℝ} (hq2 : 2 ≤ q) (Hbr : hclib_BracketResidue q) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (hclib_K q) := by
  have hq1 : 1 ≤ q := by linarith
  have hD : Convex ℝ (Set.Icc (-1 : ℝ) 1) := convex_Icc _ _
  have hint : interior (Set.Icc (-1 : ℝ) 1) = Set.Ioo (-1) 1 := by rw [interior_Icc]
  have hcont : ContinuousOn (hclib_K q) (Set.Icc (-1 : ℝ) 1) := by
    unfold hclib_K
    apply ContinuousOn.sub
    · exact ((continuousOn_const.add (continuousOn_const.mul (continuousOn_pow 2))).rpow_const
        (fun x _ => Or.inl (hclib_w_pos (t := x) hq1).ne'))
    · apply ContinuousOn.div_const
      apply ContinuousOn.add
      · exact (continuousOn_const.add continuousOn_id).rpow_const (fun x _ => Or.inr (by linarith))
      · exact (continuousOn_const.sub continuousOn_id).rpow_const (fun x _ => Or.inr (by linarith))
  apply convexOn_of_hasDerivWithinAt2_nonneg hD hcont
      (f' := fun t => q * (q - 1) * t * (1 + (q - 1) * t ^ 2) ^ (q / 2 - 1)
        - (q / 2) * ((1 + t) ^ (q - 1) - (1 - t) ^ (q - 1)))
      (f'' := fun t => q * (q - 1) * (1 + (q - 1) * t ^ 2) ^ (q / 2 - 2) * (1 + (q - 1) ^ 2 * t ^ 2)
        - (q / 2) * (q - 1) * ((1 + t) ^ (q - 2) + (1 - t) ^ (q - 2)))
  · intro x hx
    rw [hint] at hx
    obtain ⟨hl, hr⟩ := Set.mem_Ioo.mp hx
    have hwx : 0 < 1 + (q - 1) * x ^ 2 := hclib_w_pos (t := x) hq1
    have h1 : (0 : ℝ) < 1 + x := by linarith
    have h2 : (0 : ℝ) < 1 - x := by linarith
    have dA : HasDerivAt (fun t => (1 + (q - 1) * t ^ 2) ^ (q / 2))
        ((q / 2) * (1 + (q - 1) * x ^ 2) ^ (q / 2 - 1) * ((q - 1) * (2 * x))) x := by
      have inner : HasDerivAt (fun t : ℝ => 1 + (q - 1) * t ^ 2) ((q - 1) * (2 * x)) x := by
        have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
        simpa using (h.const_mul (q - 1)).const_add 1
      have := inner.rpow_const (p := q / 2) (Or.inl hwx.ne')
      convert this using 1; ring
    have d1 : HasDerivAt (fun s => (1 + s) ^ q) (1 * q * (1 + x) ^ (q - 1)) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (Or.inl h1.ne')
    have d2 : HasDerivAt (fun s => (1 - s) ^ q) (-1 * q * (1 - x) ^ (q - 1)) x :=
      ((hasDerivAt_id x).const_sub (1 : ℝ)).rpow_const (Or.inl h2.ne')
    have D := dA.sub ((d1.add d2).div_const 2)
    convert D.hasDerivWithinAt using 1
    · rfl
    ring
  · intro x hx
    rw [hint] at hx
    obtain ⟨hl, hr⟩ := Set.mem_Ioo.mp hx
    have hwx : 0 < 1 + (q - 1) * x ^ 2 := hclib_w_pos (t := x) hq1
    have h1 : (0 : ℝ) < 1 + x := by linarith
    have h2 : (0 : ℝ) < 1 - x := by linarith
    have eA : HasDerivAt (fun t => q * (q - 1) * t * (1 + (q - 1) * t ^ 2) ^ (q / 2 - 1))
        (q * (q - 1) * (1 + (q - 1) * x ^ 2) ^ (q / 2 - 2) * (1 + (q - 1) ^ 2 * x ^ 2)) x := by
      have inner : HasDerivAt (fun t : ℝ => 1 + (q - 1) * t ^ 2) ((q - 1) * (2 * x)) x := by
        have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
        simpa using (h.const_mul (q - 1)).const_add 1
      have hpow := inner.rpow_const (p := q / 2 - 1) (Or.inl hwx.ne')
      have hlin : HasDerivAt (fun t : ℝ => q * (q - 1) * t) (q * (q - 1)) x := by
        simpa using (hasDerivAt_id x).const_mul (q * (q - 1))
      have D := hlin.mul hpow
      convert D using 1
      set w := 1 + (q - 1) * x ^ 2 with hwdef
      have hh1 : w ^ (q / 2 - 1) = w ^ (q / 2 - 2) * w := by
        rw [show (q / 2 - 1) = (q / 2 - 2) + 1 by ring, Real.rpow_add hwx, Real.rpow_one]
      have hh2 : w ^ (q / 2 - 1 - 1) = w ^ (q / 2 - 2) := by congr 1; ring
      rw [hh1, hh2, hwdef]; ring
    have e1 : HasDerivAt (fun s => (1 + s) ^ (q - 1)) (1 * (q - 1) * (1 + x) ^ (q - 1 - 1)) x :=
      ((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (Or.inl h1.ne')
    have e2 : HasDerivAt (fun s => (1 - s) ^ (q - 1)) (-1 * (q - 1) * (1 - x) ^ (q - 1 - 1)) x :=
      ((hasDerivAt_id x).const_sub (1 : ℝ)).rpow_const (Or.inl h2.ne')
    have E := eA.sub ((e1.sub e2).const_mul (q / 2))
    convert E.hasDerivWithinAt using 1
    rw [show q - 1 - 1 = q - 2 by ring]
    ring
  · intro x hx
    rw [hint] at hx
    obtain ⟨hl, hr⟩ := Set.mem_Ioo.mp hx
    have htabs : |x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hbr := Hbr x htabs
    have hexp : (1 + (q - 1) * x ^ 2) ^ (q / 2 - 2) = (1 + (q - 1) * x ^ 2) ^ ((q - 4) / 2) := by
      congr 1; ring
    rw [hexp]
    have hK : 0 ≤ q * (q - 1) := by nlinarith
    nlinarith [mul_nonneg hK
      (by linarith [hbr] :
        (0 : ℝ) ≤ (1 + (q - 1) * x ^ 2) ^ ((q - 4) / 2) * (1 + (q - 1) ^ 2 * x ^ 2)
          - ((1 + x) ^ (q - 2) + (1 - x) ^ (q - 2)) / 2)]

theorem hclib_K_at_zero (q : ℝ) : hclib_K q 0 = 0 := by
  unfold hclib_K
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    sub_zero, add_zero, Real.one_rpow]
  ring

theorem hclib_K_even (q t : ℝ) : hclib_K q (-t) = hclib_K q t := by
  unfold hclib_K
  rw [show (1 : ℝ) + -t = 1 - t by ring, show (1 : ℝ) - -t = 1 + t by ring,
    show (-t) ^ 2 = t ^ 2 by ring]
  ring

/-- Forward two-point inequality `((1+t)^q + (1-t)^q)/2 ≤ (1 + (q-1)t²)^(q/2)` for `|t| ≤ 1`,
conditional on `hclib_BracketResidue q`. -/
theorem hclib_forward_core_of_bracket {q : ℝ} (hq2 : 2 ≤ q) (Hbr : hclib_BracketResidue q)
    {t : ℝ} (ht : |t| ≤ 1) :
    ((1 + t) ^ q + (1 - t) ^ q) / 2 ≤ (1 + (q - 1) * t ^ 2) ^ (q / 2) := by
  have hconv := hclib_convexOn_K hq2 Hbr
  have htmem : t ∈ Set.Icc (-1 : ℝ) 1 := by rw [abs_le] at ht; exact ⟨ht.1, ht.2⟩
  have htneg : -t ∈ Set.Icc (-1 : ℝ) 1 := by
    obtain ⟨h1, h2⟩ := htmem; constructor <;> linarith
  have hmid := hconv.2 htmem htneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  have hpt : (1 : ℝ) / 2 * t + 1 / 2 * (-t) = 0 := by ring
  rw [hpt, hclib_K_even q t, hclib_K_at_zero] at hmid
  have hKnn : 0 ≤ hclib_K q t := by linarith
  unfold hclib_K at hKnn
  linarith

/-- Forward two-point inequality for `2 ≤ q ≤ 4`. -/
theorem hclib_forward_core {q : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) {t : ℝ} (ht : |t| ≤ 1) :
    ((1 + t) ^ q + (1 - t) ^ q) / 2 ≤ (1 + (q - 1) * t ^ 2) ^ (q / 2) :=
  hclib_forward_core_of_bracket hq2 (hclib_BracketResidue_of_le_four hq2 hq4) ht

/-- The forward inequality raised to the power `2/q`. -/
theorem hclib_forward_core_2q {q : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) {t : ℝ} (ht : |t| ≤ 1) :
    (((1 + t) ^ q + (1 - t) ^ q) / 2) ^ (2 / q) ≤ 1 + (q - 1) * t ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hwpos : 0 < 1 + (q - 1) * t ^ 2 := hclib_w_pos (t := t) (by linarith)
  have hcore := hclib_forward_core hq2 hq4 ht
  have hLHSnn : (0 : ℝ) ≤ ((1 + t) ^ q + (1 - t) ^ q) / 2 := by
    rw [abs_le] at ht
    have h1 : (0 : ℝ) ≤ 1 + t := by linarith
    have h2 : (0 : ℝ) ≤ 1 - t := by linarith
    positivity
  have hmono := Real.rpow_le_rpow hLHSnn hcore (by positivity : (0 : ℝ) ≤ 2 / q)
  rwa [← Real.rpow_mul hwpos.le, show q / 2 * (2 / q) = 1 by field_simp, Real.rpow_one] at hmono

/-- The two-point inequality for `0 ≤ b ≤ a`. -/
theorem hclib_forward_nonneg {q a b : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b ≤ a) :
    ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) ≤ a ^ 2 + (q - 1) * b ^ 2 := by
  have hq0 : 0 < q := by linarith
  rcases eq_or_lt_of_le ha with rfl | ha0
  · have hb0 : b = 0 := le_antisymm (by simpa using hab) hb
    subst hb0
    simp only [add_zero, sub_zero, abs_zero]
    rw [Real.zero_rpow (by positivity : q ≠ 0)]
    simp only [add_zero, zero_div]
    rw [Real.zero_rpow (by positivity : (2 : ℝ) / q ≠ 0)]
    norm_num
  · set t := b / a with ht
    have ht0 : 0 ≤ t := by rw [ht]; positivity
    have ht1 : t ≤ 1 := by rw [ht, div_le_one ha0]; exact hab
    have htabs : |t| ≤ 1 := by rw [abs_le]; exact ⟨by linarith, ht1⟩
    have core := hclib_forward_core_2q hq2 hq4 htabs
    have e1 : a + b = a * (1 + t) := by rw [ht]; field_simp
    have e2 : a - b = a * (1 - t) := by rw [ht]; field_simp
    have hab1 : |a + b| = a * (1 + t) := by rw [e1, abs_of_nonneg]; positivity
    have hab2 : |a - b| = a * (1 - t) := by
      rw [e2, abs_of_nonneg]
      have : 0 ≤ 1 - t := by linarith
      positivity
    rw [hab1, hab2, Real.mul_rpow ha (by linarith : (0 : ℝ) ≤ 1 + t),
      Real.mul_rpow ha (by linarith : (0 : ℝ) ≤ 1 - t)]
    have hfac : (a ^ q * (1 + t) ^ q + a ^ q * (1 - t) ^ q) / 2
        = a ^ q * (((1 + t) ^ q + (1 - t) ^ q) / 2) := by ring
    rw [hfac, Real.mul_rpow (Real.rpow_nonneg ha q) (by positivity),
      ← Real.rpow_mul ha, show q * (2 / q) = 2 by field_simp, Real.rpow_two]
    have hRHS : a ^ 2 + (q - 1) * b ^ 2 = a ^ 2 * (1 + (q - 1) * t ^ 2) := by
      rw [ht]; field_simp
    rw [hRHS]
    exact mul_le_mul_of_nonneg_left core (sq_nonneg a)

/-- **Two-point hypercontractive inequality** (Bonami 1970; Gross 1975) for `2 ≤ q ≤ 4`:
`((|a + b|^q + |a - b|^q)/2)^(2/q) ≤ a² + (q - 1) b²`. The literature statement holds for all
`q ≥ 2`; the range `q > 4` is not covered here. -/
theorem hclib_two_point_forward {q : ℝ} (hq2 : 2 ≤ q) (hq4 : q ≤ 4) (a b : ℝ) :
    ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) ≤ a ^ 2 + (q - 1) * b ^ 2 := by
  have key : ((|a + b| ^ q + |a - b| ^ q) / 2) ^ (2 / q) ≤ |a| ^ 2 + (q - 1) * |b| ^ 2 := by
    rw [← bts_abs_sum_eq a b q]
    rcases le_total |b| |a| with hba | hab
    · exact hclib_forward_nonneg hq2 hq4 (abs_nonneg a) (abs_nonneg b) hba
    · have hswap : (abs (|a| + |b|) ^ q + abs (|a| - |b|) ^ q) / 2
          = (abs (|b| + |a|) ^ q + abs (|b| - |a|) ^ q) / 2 := by
        rw [show |a| + |b| = |b| + |a| by ring, show |a| - |b| = -(|b| - |a|) by ring, abs_neg]
      rw [hswap]
      have hforward := hclib_forward_nonneg hq2 hq4 (abs_nonneg b) (abs_nonneg a) hab
      calc ((abs (|b| + |a|) ^ q + abs (|b| - |a|) ^ q) / 2) ^ (2 / q)
          ≤ |b| ^ 2 + (q - 1) * |a| ^ 2 := hforward
        _ ≤ |a| ^ 2 + (q - 1) * |b| ^ 2 := by
            have hsq : |a| ^ 2 ≤ |b| ^ 2 := by
              have := abs_nonneg a; nlinarith [hab, abs_nonneg b]
            nlinarith [hsq, hq2]
  rwa [sq_abs, sq_abs] at key

/-- The two-point inequality with `q = 1 + 1/ρ²` and `b` replaced by `ρ b`, for `1/3 ≤ ρ² ≤ 1`
(equivalently `2 ≤ q ≤ 4`). -/
theorem hclib_forward_scalar {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρlo : (1 : ℝ) / 3 ≤ ρ ^ 2) (a b : ℝ) :
    ((|a + ρ * b| ^ (1 + 1 / ρ ^ 2) + |a - ρ * b| ^ (1 + 1 / ρ ^ 2)) / 2) ^ (2 / (1 + 1 / ρ ^ 2))
      ≤ a ^ 2 + b ^ 2 := by
  set q : ℝ := 1 + 1 / ρ ^ 2 with hq
  have hρsq : 0 < ρ ^ 2 := by positivity
  have hq2 : 2 ≤ q := by
    rw [hq]
    have : 1 ≤ 1 / ρ ^ 2 := by rw [le_div_iff₀ hρsq, one_mul]; nlinarith
    linarith
  have hq4 : q ≤ 4 := by
    rw [hq]
    have : 1 / ρ ^ 2 ≤ 3 := by rw [div_le_iff₀ hρsq]; nlinarith [hρlo]
    linarith
  have hqm1 : q - 1 = 1 / ρ ^ 2 := by rw [hq]; ring
  have hfwd := hclib_two_point_forward hq2 hq4 a (ρ * b)
  have hrw : a ^ 2 + (q - 1) * (ρ * b) ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hqm1]; field_simp
  rw [hrw] at hfwd
  exact hfwd

/-- At `q = 2` the forward inequality is an equality. -/
theorem hclib_forward_at_two (t : ℝ) :
    ((1 + t) ^ (2 : ℝ) + (1 - t) ^ (2 : ℝ)) / 2 = (1 + ((2 : ℝ) - 1) * t ^ 2) ^ ((2 : ℝ) / 2) := by
  rw [show ((2 : ℝ) - 1) = 1 by norm_num, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, Real.rpow_two]
  ring

/-- At `t = 0` the forward inequality is an equality. -/
theorem hclib_forward_at_zero (q : ℝ) :
    ((1 + (0 : ℝ)) ^ q + (1 - (0 : ℝ)) ^ q) / 2 = (1 + (q - 1) * (0 : ℝ) ^ 2) ^ (q / 2) := by
  simp only [add_zero, sub_zero, Real.one_rpow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero]
  norm_num

/-- At `q = 2` the inequality raised to `2/q` is an equality; the hypotheses `0 ≤ t ≤ 1` are not
needed. -/
theorem hclib_reverse_of_bts {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    (((1 + t) ^ (2 : ℝ) + (1 - t) ^ (2 : ℝ)) / 2) ^ (2 / (2 : ℝ)) = 1 + ((2 : ℝ) - 1) * t ^ 2 := by
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, show ((2 : ℝ) - 1) = 1 by norm_num,
    Real.rpow_two, Real.rpow_two]
  ring

end StatMech.Probability
