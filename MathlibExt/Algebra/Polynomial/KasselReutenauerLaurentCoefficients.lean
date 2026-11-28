/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.ChebyshevCPartialSumLaurent
public import MathlibExt.Algebra.Polynomial.KasselReutenauerTopCoefficient
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination

/-!
# Absolute coefficient sum of the Kassel–Reutenauer Laurent polynomial

For `n ≥ 1`, the absolute coefficient sum of the Laurent polynomial `Cₙ(q) / qⁿ` is four times
the number of odd divisors of `n`. We obtain a weighted sum of Chebyshev partial sums by
cancelling the even-divisor endpoints of the divisor-count formula. Each odd divisor then
contributes two signed pairs of monomials, with disjoint support between the pairs.

## References

* Christian Kassel and Christophe Reutenauer, *Pairs of Intertwined Integer Sequences*,
  Journal of Integer Sequences 29 (2026), Article 26.4.4, pp. 1–25, Lemma 14, Theorem 16,
  Lemma 22, Theorem 23, Corollary 24, and Lemma 26. We derive the odd-divisor formula directly
  from the divisor counts, then use the exponent uniqueness argument of Lemma 22.
* Christian Kassel and Christophe Reutenauer, *Complete determination of the zeta function of the
  Hilbert scheme of n points on a two-dimensional torus*, The Ramanujan Journal 46 (2018),
  pp. 633–655, Theorem 1.3 (divisor counts) and Lemma 3.5(ii) (exponent uniqueness).
* `MathlibExt.Algebra.Polynomial.ChebyshevCPartialSumLaurent`,
  `chebyshevCPartialSum_laurent_identity`, supplies the Laurent expansion of each partial sum
  and the factor rewrite used in `prefix_sub_laurent`.
-/

open LaurentPolynomial Polynomial

namespace MetaMathlibExt

/-- **Kassel–Reutenauer polynomial.** For a natural number $n$, the Kassel–Reutenauer polynomial
$\bar P_n(X) \in \mathbb{Z}[X]$ is defined by
$$
\bar P_n(X) = a_{n,0} + \sum_{i=1}^{n-1} a_{n,i} \, \bar T_i(X),
$$
where $a_{n,i}$ is the number of divisors $d$ of $n$ with $d(d - 2i) \le 2n$ and
$n < 2d(d - i)$ (equivalently, $(i + \sqrt{2n + i^2})/2 < d \le i + \sqrt{2n + i^2}$), and
$\bar T_i$ is the monic Chebyshev polynomial: $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{i+2} = X \bar T_{i+1} - \bar T_i$. For $n = 0$ the sum is empty and the set of divisors
of $0$ is taken to be empty, so $\bar P_0 = 0$.

In the paper, $\bar P_n$ is characterized for $n \ge 1$ by
$\bar P_n(q + q^{-1}) = P_n(q)/q^{n-1}$, where $(q - 1)^2 P_n(q)$ is the number of ideals of
codimension $n$ of $\mathbb{F}_q[x, y, x^{-1}, y^{-1}]$; the definition here uses the explicit
expansion (9) and the divisor counts in the proof of Lemma 14 instead.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, (6), (8)–(10), Lemma 14, and Table 2. -/
@[expose] public noncomputable def kasselReutenauerPoly (n : ℕ) : ℤ[X] :=
  (kasselReutenauerCoeff n 0 : ℤ[X]) +
    ∑ i ∈ Finset.Icc 1 (n - 1), (kasselReutenauerCoeff n i : ℤ[X]) * Chebyshev.C ℤ i

private noncomputable def chebyshevBasis (i : ℕ) : ℤ[X] :=
  if i = 0 then 1 else Chebyshev.C ℤ i

-- The partial sum is zero when its upper endpoint is negative.
private noncomputable def chebyshevPrefix (r : ℤ) : ℤ[X] :=
  if 0 ≤ r then chebyshevCPartialSum r.toNat else 0

private theorem chebyshevPrefix_eq_sum {r : ℤ} {n : ℕ} (hr : r < n) :
    chebyshevPrefix r = ∑ i ∈ Finset.range n, if (i : ℤ) ≤ r then chebyshevBasis i else 0 := by
  rw [chebyshevPrefix, ← Finset.sum_filter]
  split_ifs with h
  · have hfilter : ((Finset.range n).filter fun (i : ℕ) => (i : ℤ) ≤ r) =
        Finset.range (r.toNat + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hfilter, Finset.sum_range_eq_add_Ico _ (Nat.succ_pos _), Nat.succ_eq_add_one,
      Finset.Ico_add_one_right_eq_Icc, chebyshevCPartialSum]
    simp only [chebyshevBasis, ↓reduceIte]
    congr 1
    exact Finset.sum_congr rfl fun i hi =>
      (ite_eq_right (Nat.ne_of_gt (Finset.mem_Icc.mp hi).1)).symm
  · symm
    apply Finset.sum_eq_zero
    intro i hi
    exact (h ((Nat.cast_nonneg i).trans (Finset.mem_filter.mp hi).2)).elim

-- The two tests in `kasselReutenauerCoeff` give the endpoints of a single interval.
private theorem coefficient_interval {d m n i : ℕ} (hd : 0 < d) (hdm : d * m = n) :
    d * (d - 2 * i) ≤ 2 * n ∧ n < 2 * d * (d - i) ↔
      ((d : ℤ) + 1) / 2 - m ≤ i ∧ (i : ℤ) ≤ d - (m : ℤ) / 2 - 1 := by
  rw [← hdm, show 2 * (d * m) = d * (2 * m) by ac_rfl,
    show 2 * d * (d - i) = d * (2 * (d - i)) by ac_rfl,
    Nat.mul_le_mul_left_iff hd, Nat.mul_lt_mul_left hd]
  omega

private theorem kasselReutenauerPoly_eq_endpoint_sum (n : ℕ) (hn : 1 ≤ n) :
    kasselReutenauerPoly n = ∑ p ∈ n.divisorsAntidiagonal,
      (chebyshevPrefix ((p.1 : ℤ) - (p.2 : ℤ) / 2 - 1) -
        chebyshevPrefix (((p.1 : ℤ) + 1) / 2 - p.2 - 1)) := by
  classical
  let upper (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ) / 2 - 1
  let before (p : ℕ × ℕ) : ℤ := ((p.1 : ℤ) + 1) / 2 - p.2 - 1
  change kasselReutenauerPoly n = ∑ p ∈ n.divisorsAntidiagonal,
    (chebyshevPrefix (upper p) - chebyshevPrefix (before p))
  have hexpand : kasselReutenauerPoly n =
      ∑ i ∈ Finset.range n, (kasselReutenauerCoeff n i : ℤ[X]) * chebyshevBasis i := by
    rw [kasselReutenauerPoly, Finset.sum_range_eq_add_Ico _ (by omega)]
    rw [← Nat.sub_add_cancel hn, Finset.Ico_add_one_right_eq_Icc]
    simp only [Nat.sub_add_cancel hn, chebyshevBasis, ↓reduceIte, mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (by have := (Finset.mem_Icc.mp hi).1; omega)]
  have hexpandRight : (∑ p ∈ n.divisorsAntidiagonal,
      (chebyshevPrefix (upper p) - chebyshevPrefix (before p))) =
      ∑ p ∈ n.divisorsAntidiagonal, ∑ i ∈ Finset.range n,
        ((if (i : ℤ) ≤ upper p then chebyshevBasis i else 0) -
          (if (i : ℤ) ≤ before p then chebyshevBasis i else 0)) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hdn := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have hu : upper p < n := by dsimp [upper]; omega
    have hb : before p < n := by dsimp [before]; omega
    rw [chebyshevPrefix_eq_sum hu, chebyshevPrefix_eq_sum hb, Finset.sum_sub_distrib]
  rw [hexpand, hexpandRight, Finset.sum_comm (s := n.divisorsAntidiagonal) (t := Finset.range n)]
  apply Finset.sum_congr rfl
  intro i _
  rw [kasselReutenauerCoeff, ← show
      (∑ _d ∈ n.divisors.filter (fun d => d * (d - 2 * i) ≤ 2 * n ∧
          n < 2 * d * (d - i)), chebyshevBasis i) = _ * chebyshevBasis i by
        simp [nsmul_eq_mul], Finset.sum_filter]
  rw [← Nat.sum_divisorsAntidiagonal (fun d _m =>
    if d * (d - 2 * i) ≤ 2 * n ∧ n < 2 * d * (d - i) then chebyshevBasis i else 0)]
  apply Finset.sum_congr rfl
  intro p hp
  have hd := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
  have hm := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hbu : before p ≤ upper p := by dsimp [before, upper]; omega
  simp only [coefficient_interval (Nat.pos_of_ne_zero hd) hprod]
  have hib : ((p.1 : ℤ) + 1) / 2 - p.2 ≤ i ↔ ¬ (i : ℤ) ≤ before p := by
    dsimp [before]
    omega
  simp only [hib]
  change (if ¬ (i : ℤ) ≤ before p ∧ (i : ℤ) ≤ upper p then chebyshevBasis i else 0) =
    (if (i : ℤ) ≤ upper p then chebyshevBasis i else 0) -
      (if (i : ℤ) ≤ before p then chebyshevBasis i else 0)
  by_cases hb' : (i : ℤ) ≤ before p
  · simp [hb', hb'.trans hbu]
  · by_cases hu' : (i : ℤ) ≤ upper p <;> simp [hb', hu']

private def divisorEndpoint (n d : ℕ) : ℤ := (n / d : ℕ) - ((d : ℤ) + 1) / 2

private theorem kasselReutenauerPoly_eq_odd_prefixes (n : ℕ) (hn : 1 ≤ n) :
    kasselReutenauerPoly n = ∑ d ∈ n.divisors.filter Odd,
      (chebyshevPrefix (divisorEndpoint n d) - chebyshevPrefix (-divisorEndpoint n d - 1)) := by
  classical
  let upper (p : ℕ × ℕ) : ℤ := (p.2 : ℤ) - (p.1 : ℤ) / 2 - 1
  let before (p : ℕ × ℕ) : ℤ := ((p.1 : ℤ) + 1) / 2 - p.2 - 1
  have hswap : (∑ p ∈ n.divisorsAntidiagonal, chebyshevPrefix (upper p.swap)) =
      ∑ p ∈ n.divisorsAntidiagonal, chebyshevPrefix (upper p) := by
    conv_rhs => rw [← Nat.map_swap_divisorsAntidiagonal]
    rw [Finset.sum_map]
    rfl
  let evens := n.divisorsAntidiagonal.filter (fun p => ¬ Odd p.1)
  let flip (p : ℕ × ℕ) : ℕ × ℕ := (2 * p.2, p.1 / 2)
  have heven (p : ℕ × ℕ) (hp : p ∈ evens) : 2 * (p.1 / 2) = p.1 := by
    have ho := (Finset.mem_filter.mp hp).2
    rw [Nat.odd_iff] at ho
    omega
  have hflip (p : ℕ × ℕ) (hp : p ∈ evens) : flip p ∈ evens := by
    obtain ⟨hp₀, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨hprod, hn₀⟩ := Nat.mem_divisorsAntidiagonal.mp hp₀
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hn₀⟩, ?_⟩
    · change (2 * p.2) * (p.1 / 2) = n
      rw [show (2 * p.2) * (p.1 / 2) = (2 * (p.1 / 2)) * p.2 by ac_rfl, heven p hp, hprod]
    · simp [flip, Nat.odd_iff]
  have hinv (p : ℕ × ℕ) (hp : p ∈ evens) : flip (flip p) = p := by
    apply Prod.ext
    · exact heven p hp
    · dsimp [flip]
      omega
  have hcancel : (∑ p ∈ evens, chebyshevPrefix (upper p)) =
      ∑ p ∈ evens, chebyshevPrefix (before p) := by
    refine Finset.sum_bij' (fun p _ => flip p) (fun p _ => flip p)
      hflip hflip hinv hinv (fun p hp => ?_)
    congr 1
    have h := heven p hp
    dsimp [upper, before, flip]
    omega
  rw [kasselReutenauerPoly_eq_endpoint_sum n hn]
  change (∑ p ∈ n.divisorsAntidiagonal,
    (chebyshevPrefix (upper p.swap) - chebyshevPrefix (before p))) = _
  rw [Finset.sum_sub_distrib, hswap, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => Odd p.1)]
  change (∑ p ∈ n.divisorsAntidiagonal.filter (fun p => Odd p.1),
      (chebyshevPrefix (upper p) - chebyshevPrefix (before p))) +
    (∑ p ∈ evens, (chebyshevPrefix (upper p) - chebyshevPrefix (before p))) = _
  rw [Finset.sum_sub_distrib (s := evens), hcancel, sub_self, add_zero]
  have hodd (p : ℕ × ℕ) (hp : Odd p.1) :
      upper p = (p.2 : ℤ) - ((p.1 : ℤ) + 1) / 2 := by
    obtain ⟨k, hk⟩ := hp
    dsimp [upper]
    omega
  rw [Finset.sum_filter, Nat.sum_divisorsAntidiagonal (fun d m =>
    if Odd d then chebyshevPrefix (upper (d, m)) - chebyshevPrefix (before (d, m)) else 0),
    ← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hodd _ (Finset.mem_filter.mp hd).2]
  simp only [divisorEndpoint, before]
  ring_nf

private noncomputable def monomialPair (a : ℤ) : LaurentPolynomial ℤ := T a + T (-a)

private theorem prefix_sub_laurent (r : ℤ) :
    (T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
        (chebyshevPrefix r - chebyshevPrefix (-r - 1)) =
      monomialPair (-r - 1) - monomialPair r := by
  have hinv : (T 1 * T (-1) : LaurentPolynomial ℤ) = 1 := by
    rw [← T_add]
    exact T_zero
  have hfactor : (T (-1) * (T 1 - 1) ^ 2 : LaurentPolynomial ℤ) = T 1 - 2 + T (-1) := by
    linear_combination (T 1 - 2) * hinv
  have hpartial (k : ℕ) :
      (T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
          (chebyshevCPartialSum k) = monomialPair ((k : ℤ) + 1) - monomialPair k := by
    rw [← hfactor]
    simpa [monomialPair, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      (chebyshevCPartialSum_laurent_identity k).symm
  by_cases hr : 0 ≤ r
  · rw [chebyshevPrefix, ite_eq_left hr, chebyshevPrefix,
      ite_eq_right (by omega : ¬ 0 ≤ -r - 1), sub_zero, hpartial, Int.toNat_of_nonneg hr]
    simp [monomialPair, sub_eq_add_neg, add_comm]
  · have hs : 0 ≤ -r - 1 := by omega
    rw [chebyshevPrefix, ite_eq_right hr, chebyshevPrefix, ite_eq_left hs, zero_sub,
      map_neg, mul_neg, hpartial, Int.toNat_of_nonneg hs, neg_sub, show -r - 1 + 1 = -r by omega]
    simp [monomialPair, add_comm]

-- For opposite nonzero starting offsets, compare two products whose factor gaps differ by two.
private theorem no_opposite_offsets {h k a : ℤ} (hh : 0 < h) (hk : 0 < k) (ha : 0 < a)
    (heq : h * (h + 1 + 2 * a) = k * (k + 2 * a - 1)) : False := by
  have hz : (h - k + 1) * (h + k) + (2 * a) * (h - k) = 0 := by
    linear_combination heq
  by_cases hle : k ≤ h
  · have hp := mul_pos (show 0 < h - k + 1 by omega) (show 0 < h + k by omega)
    have hq := mul_nonneg (show 0 ≤ 2 * a by omega) (sub_nonneg.mpr hle)
    omega
  · have hp := mul_nonpos_of_nonpos_of_nonneg (show h - k + 1 ≤ 0 by omega)
      (show 0 ≤ h + k by omega)
    have hq := mul_neg_of_pos_of_neg (show 0 < 2 * a by omega) (show h - k < 0 by omega)
    omega

private theorem length_eq_of_abs_offset_eq {n h k a b : ℤ} (hn : 0 < n)
    (hh : 0 < h) (hk : 0 < k) (ha : h * (h + 1 + 2 * a) = 2 * n)
    (hb : k * (k + 1 + 2 * b) = 2 * n) (hab : |a| = |b|) : h = k := by
  have hh' : 0 < h + 1 + 2 * a := pos_of_mul_pos_right (ha.symm ▸ (by omega : 0 < 2 * n)) hh.le
  have hk' : 0 < k + 1 + 2 * b := pos_of_mul_pos_right (hb.symm ▸ (by omega : 0 < 2 * n)) hk.le
  by_cases heq : a = b
  · subst b
    have hz : (h - k) * (h + k + 1 + 2 * a) = 0 := by linear_combination ha - hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (by omega))
  · have hneg : a = -b := (abs_eq_abs.mp hab).resolve_left heq
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · exfalso
      apply no_opposite_offsets hk hh' (a := b) (by omega)
      have hf : h + 1 + 2 * a + 2 * b - 1 = h := by omega
      rw [hf, mul_comm (h + 1 + 2 * a) h, ha, hb]
    · exfalso
      apply no_opposite_offsets hh hk' (a := a) (by omega)
      have hf : k + 1 + 2 * b + 2 * a - 1 = k := by omega
      rw [hf, mul_comm (k + 1 + 2 * b) k, ha, hb]

-- The two choices for each odd divisor encode the odd and even progression lengths.
private def progressionLength (n : ℕ) (p : ℕ × Bool) : ℕ :=
  if p.2 then 2 * (n / p.1) else p.1

private def progressionOffset (n : ℕ) (p : ℕ × Bool) : ℤ :=
  if p.2 then -divisorEndpoint n p.1 - 1 else divisorEndpoint n p.1

private theorem progression_product {n : ℕ} {p : ℕ × Bool} (hp : p.1 ∈ n.divisors.filter Odd) :
    0 < progressionLength n p ∧
      (progressionLength n p : ℤ) * (progressionLength n p + 1 + 2 * progressionOffset n p) =
        2 * (n : ℤ) := by
  obtain ⟨hd, ho⟩ := Finset.mem_filter.mp hp
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hprod := Nat.mul_div_cancel' hdvd
  have hm : 0 < n / p.1 := Nat.div_pos (Nat.divisor_le hd) hdpos
  obtain ⟨j, hj⟩ := ho
  have hhalf : 2 * (((p.1 : ℤ) + 1) / 2) = (p.1 : ℤ) + 1 := by omega
  obtain ⟨d, flag⟩ := p
  change d * (n / d) = n at hprod
  cases flag
  · refine ⟨hdpos, ?_⟩
    simp only [progressionLength, progressionOffset, Bool.false_eq_true, ite_false, divisorEndpoint]
    have h : (d : ℤ) + 1 + 2 * ((n / d : ℕ) - ((d : ℤ) + 1) / 2) = 2 * (n / d : ℕ) := by
      change 2 * (((d : ℤ) + 1) / 2) = (d : ℤ) + 1 at hhalf
      omega
    rw [h]
    push_cast
    exact_mod_cast (show d * (2 * (n / d)) = 2 * n by rw [← mul_left_comm, hprod])
  · refine ⟨by simp [progressionLength, hm], ?_⟩
    simp only [progressionLength, progressionOffset, ite_true, divisorEndpoint, Nat.cast_mul,
      Nat.cast_ofNat]
    have h : 2 * ((n / d : ℕ) : ℤ) + 1 +
        2 * (-(((n / d : ℕ) : ℤ) - ((d : ℤ) + 1) / 2) - 1) = d := by
      change 2 * (((d : ℤ) + 1) / 2) = (d : ℤ) + 1 at hhalf
      omega
    rw [h]
    exact_mod_cast (show (2 * (n / d)) * d = 2 * n by rw [mul_assoc, mul_comm (n / d) d, hprod])

private theorem progressionOffset_injOn {n : ℕ} (hn : 1 ≤ n) {p q : ℕ × Bool}
    (hp : p.1 ∈ n.divisors.filter Odd) (hq : q.1 ∈ n.divisors.filter Odd)
    (habs : |progressionOffset n p| = |progressionOffset n q|) : p = q := by
  have hp' := progression_product hp
  have hq' := progression_product hq
  have h := length_eq_of_abs_offset_eq (by omega) (by exact_mod_cast hp'.1)
    (by exact_mod_cast hq'.1) hp'.2 hq'.2 habs
  have heq : progressionLength n p = progressionLength n q := by exact_mod_cast h
  obtain ⟨hd, ho⟩ := Finset.mem_filter.mp hp
  obtain ⟨he, ho'⟩ := Finset.mem_filter.mp hq
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hevd := Nat.dvd_of_mem_divisors he
  rw [Nat.odd_iff] at ho ho'
  obtain ⟨d, b⟩ := p
  obtain ⟨e, c⟩ := q
  cases b <;> cases c <;> simp only [progressionLength, Bool.false_eq_true, ite_false,
    ite_true, Nat.mul_right_inj (by decide : 2 ≠ 0)] at heq
  · exact Prod.ext heq rfl
  · change d % 2 = 1 at ho
    omega
  · change e % 2 = 1 at ho'
    omega
  · exact Prod.ext ((Nat.div_eq_iff_eq_of_dvd_dvd (by omega) hdvd hevd).mp heq) rfl

private noncomputable def signedPairCoeffs (n : ℕ) (p : ℕ × Bool) : ℤ →₀ ℤ :=
  let a := progressionOffset n p
  let c : ℤ := if p.2 then 1 else -1
  Finsupp.single a c + Finsupp.single (-a) c

-- A pair contributes twice, even when the two terms both lie at exponent zero.
private theorem sum_abs_single_pair (a c : ℤ) :
    (Finsupp.single a c + Finsupp.single (-a) c).sum (fun _ x => |x|) = 2 * |c| := by
  by_cases heq : -a = a
  · rw [heq, ← Finsupp.single_add, Finsupp.sum_single_index (by simp), ← two_mul, abs_mul]
    norm_num
  · have hd : Disjoint (Finsupp.single a c).support (Finsupp.single (-a) c).support :=
      (Finset.disjoint_singleton.mpr (Ne.symm heq)).mono Finsupp.support_single_subset
        Finsupp.support_single_subset
    rw [Finsupp.sum_add_index_of_disjoint hd]
    simp [Finsupp.sum_single_index, two_mul]

private theorem sum_abs_sum_of_pairwiseDisjoint {ι : Type*} (s : Finset ι) (f : ι → ℤ →₀ ℤ)
    (hd : (s : Set ι).PairwiseDisjoint (fun x => (f x).support)) :
    (∑ x ∈ s, f x).sum (fun _ c => |c|) = ∑ x ∈ s, (f x).sum (fun _ c => |c|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hrest : Disjoint (f x).support (∑ y ∈ s, f y).support := by
      apply Disjoint.mono_right Finsupp.support_finsetSum
      rw [Finset.disjoint_biUnion_right]
      intro y hy
      exact hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hy)
        (fun heq => hx (heq ▸ hy))
    rw [Finset.sum_insert hx, Finsupp.sum_add_index_of_disjoint hrest, Finset.sum_insert hx,
      ih (fun y hy z hz hne =>
        hd (Finset.mem_insert_of_mem hy) (Finset.mem_insert_of_mem hz) hne)]

private theorem abs_eq_of_mem_pair_support {n : ℕ} {p : ℕ × Bool} {i : ℤ}
    (hi : i ∈ (signedPairCoeffs n p).support) : |i| = |progressionOffset n p| := by
  have h := Finsupp.support_add hi
  rw [Finset.mem_union] at h
  rcases h with h | h
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h), abs_neg]

/-- **The absolute coefficient sum of $C_n$ counts odd divisors.** Let $n \ge 1$, let $\bar P_n$ be
the Kassel–Reutenauer polynomial, and write $C_n(q)/q^n$ for the Laurent polynomial
$(q - 2 + q^{-1})\,\bar P_n(q + q^{-1})$ in $\mathbb{Z}[q, q^{-1}]$. Then the sum of the absolute
values of the coefficients of $C_n(q)/q^n$ equals four times the number of odd divisors of $n$.

Multiplying by $q^n$ does not change the coefficients, so this is the source's statement about
the polynomial $C_n(q)$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Corollary 24
(`jis-2026-26.4.4-cor-24`). -/
public theorem kasselReutenauer_C_abs_coeff_sum (n : ℕ) (hn : 1 ≤ n) :
    ((LaurentPolynomial.T 1 - 2 + LaurentPolynomial.T (-1)) *
        aeval (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : LaurentPolynomial ℤ)
          (kasselReutenauerPoly n)).coeff.sum (fun _ c => |c|) =
      4 * (((Nat.divisors n).filter Odd).card : ℤ) := by
  classical
  let oddDivisors := n.divisors.filter Odd
  let pairs := oddDivisors ×ˢ (Finset.univ : Finset Bool)
  have hcoeff : ((T 1 - 2 + T (-1)) * aeval (T 1 + T (-1) : LaurentPolynomial ℤ)
      (kasselReutenauerPoly n)).coeff = ∑ p ∈ pairs, signedPairCoeffs n p := by
    rw [kasselReutenauerPoly_eq_odd_prefixes n hn, map_sum, Finset.mul_sum]
    simp_rw [prefix_sub_laurent, AddMonoidAlgebra.coeff_sum]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d _
    rw [Fintype.univ_bool, Finset.sum_pair (by decide)]
    ext i
    simp [monomialPair, signedPairCoeffs, progressionOffset, AddMonoidAlgebra.coeff_add,
      Finsupp.single_apply, sub_eq_add_neg, neg_ite, add_assoc, add_comm, add_left_comm]
  rw [hcoeff, sum_abs_sum_of_pairwiseDisjoint]
  · calc
      ∑ p ∈ pairs, (signedPairCoeffs n p).sum (fun _ c => |c|) = ∑ _p ∈ pairs, (2 : ℤ) := by
        apply Finset.sum_congr rfl
        intro p _
        unfold signedPairCoeffs
        rw [sum_abs_single_pair]
        cases p.2 <;> norm_num
      _ = 4 * (oddDivisors.card : ℤ) := by
        simp [pairs, Finset.card_product]
        ring
  · intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hp' := (Finset.mem_product.mp hp).1
    have hq' := (Finset.mem_product.mp hq).1
    exact hpq (progressionOffset_injOn hn hp' hq'
      ((abs_eq_of_mem_pair_support hi).symm.trans (abs_eq_of_mem_pair_support hj)))

end MetaMathlibExt
