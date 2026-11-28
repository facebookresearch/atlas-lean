/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Order.WellQuasiOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndex

/-!
# Dickson's finiteness theorem for odd perfect numbers

For each natural number `m`, only finitely many odd perfect numbers have exactly `m` distinct
prime divisors. The case `m = 0` is empty, since neither `0` nor `1` is perfect. For positive `m`,
an infinite sequence of distinct such numbers would have a subsequence on which all prime and
exponent coordinates either stabilize or tend to infinity. The largest fixed prime
with an unbounded exponent cannot occur in a limiting abundancy product of `2`, by Dickson's
divisibility argument. Then any unbounded prime would force the abundancy of each sufficiently
late term to exceed `2`, and if all primes and exponents stabilize the numbers cannot be distinct.

## References

* Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers – Part I*, INTEGERS 24 (2024),
  Article A114, pp. 1–38, Lemma 1 (iii).
* Leonard Eugene Dickson, *Finiteness of the Odd Perfect and Primitive Abundant Numbers with n
  Distinct Prime Factors*, American Journal of Mathematics 35 (1913), pp. 413–422, §1, Corollary,
  and §5, Lemma C (the largest-prime argument).
* The prime-power and product formulas for the abundancy index come from
  `MathlibExt.NumberTheory.ArithmeticFunction.AbundancyIndex`.
-/

open Filter Finset
open scoped Function Topology

namespace MetaMathlibExt

private theorem eventually_eq_of_monotone_of_not_tendsto_atTop {f : ℕ → ℕ}
    (hf : Monotone f) (h : ¬ Tendsto f atTop atTop) : ∃ k, ∀ᶠ n in atTop, f n = k := by
  rw [hf.tendsto_atTop_atTop_iff] at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  have hfin : (Set.range f).Finite := (Set.finite_le_nat b).subset (by
    rintro _ ⟨n, rfl⟩
    exact (hb n).le)
  obtain ⟨k, ⟨n, rfl⟩, hk⟩ := Set.exists_max_image _ id hfin (Set.range_nonempty f)
  exact ⟨f n, (eventually_ge_atTop n).mono fun j hj =>
    (hk _ (Set.mem_range_self j)).antisymm (hf hj)⟩

private theorem tendsto_abundancyIndex_prime_pow {p a : ℕ → ℕ} {l : ℝ}
    (hp : ∀ n, (p n).Prime)
    (hbase : Tendsto (fun n => (p n : ℝ) / ((p n : ℝ) - 1)) atTop (𝓝 l))
    (hpow : Tendsto (fun n => (p n : ℝ) ^ (a n + 1)) atTop atTop) :
    Tendsto (fun n => (Nat.abundancyIndex (p n ^ a n) : ℝ)) atTop (𝓝 l) := by
  have h := hbase.mul ((tendsto_inv_atTop_zero.comp hpow).const_sub 1)
  simp only [sub_zero, mul_one] at h
  refine h.congr fun n => ?_
  rw [Nat.abundancyIndex_prime_pow_eq _ _ (hp n)]
  push_cast
  simp only [Function.comp_apply, one_div]

private theorem tendsto_abundancyIndex_prime_pow_of_prime_tendsto {p a : ℕ → ℕ}
    (hp : ∀ n, (p n).Prime) (h : Tendsto p atTop atTop) :
    Tendsto (fun n => (Nat.abundancyIndex (p n ^ a n) : ℝ)) atTop (𝓝 1) := by
  have hpR : Tendsto (fun n => (p n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp h
  have hsub : Tendsto (fun n => (p n : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hpR
  have hbase := (tendsto_inv_atTop_zero.comp hsub).const_add (1 : ℝ)
  simp only [add_zero] at hbase
  apply tendsto_abundancyIndex_prime_pow hp
  · refine hbase.congr fun n => ?_
    have hp1 : (1 : ℝ) < p n := by exact_mod_cast (hp n).one_lt
    simp only [Function.comp_apply]
    field_simp [ne_of_gt (sub_pos.mpr hp1)]
    ring
  · refine tendsto_atTop_mono (fun n => ?_) hpR
    have hp1 : (1 : ℝ) ≤ p n := by exact_mod_cast (hp n).one_le
    simpa only [pow_one] using pow_le_pow_right₀ hp1 (Nat.succ_le_succ (Nat.zero_le (a n)))

private theorem one_lt_abundancyIndex_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    1 < (Nat.abundancyIndex (p ^ a) : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hpos : (0 : ℚ) < 1 / (p : ℚ) ^ (k + 1) := one_div_pos.mpr (pow_pos hpQ _)
  have h := (Nat.one_le_abundancyIndex (pow_pos hp.pos k)).trans_lt (lt_add_of_pos_right _ hpos)
  rw [← Nat.abundancyIndex_prime_pow_succ hp] at h
  exact_mod_cast h

/-- **Dickson's finiteness theorem for odd perfect numbers.** For every natural number $m$, there
are only finitely many odd perfect numbers with exactly $m$ distinct prime divisors.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 1 (iii) (`integers-2024-A114-lem-1`). -/
public theorem finite_setOf_oddPerfect_card_primeFactors_eq (m : ℕ) :
    {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card = m}.Finite := by
  classical
  by_cases hm : m = 0
  · subst m
    refine (Set.finite_empty : (∅ : Set ℕ).Finite).subset ?_
    rintro N ⟨_, hperf, hcard⟩
    rcases Nat.primeFactors_eq_empty.mp (Finset.card_eq_zero.mp hcard) with rfl | rfl
    · exact (Nat.lt_irrefl _ hperf.2).elim
    · have hsum := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
      simp at hsum
  by_contra hinf
  let S := {N : ℕ | Odd N ∧ N.Perfect ∧ N.primeFactors.card = m}
  let ns := (show S.Infinite from hinf).natEmbedding S
  let N (n : ℕ) : ℕ := ns n
  have hN (n : ℕ) : Odd (N n) ∧ (N n).Perfect ∧ (N n).primeFactors.card = m := (ns n).2
  let enumerate (n : ℕ) : Fin m ≃ (N n).primeFactors :=
    ((N n).primeFactors.equivFinOfCardEq (hN n).2.2).symm
  let coords (n : ℕ) : (Fin m → ℕ) × (Fin m → ℕ) :=
    (fun i => enumerate n i, fun i => (N n).factorization (enumerate n i))
  obtain ⟨φ, hφ⟩ := wellQuasiOrdered_le.exists_monotone_subseq coords
  let p (n : ℕ) (i : Fin m) : ℕ := (coords (φ n)).1 i
  let a (n : ℕ) (i : Fin m) : ℕ := (coords (φ n)).2 i
  have hpMem (n : ℕ) (i : Fin m) : p n i ∈ (N (φ n)).primeFactors := (enumerate (φ n) i).2
  have hp (n : ℕ) (i : Fin m) : (p n i).Prime := Nat.prime_of_mem_primeFactors (hpMem n i)
  have hpTwo (n : ℕ) (i : Fin m) : p n i ≠ 2 := by
    intro heq
    have hd := Nat.dvd_of_mem_primeFactors (hpMem n i)
    rw [heq] at hd
    exact (Nat.not_even_iff_odd.mpr (hN (φ n)).1) (even_iff_two_dvd.mpr hd)
  have hpInj (n : ℕ) : Function.Injective (p n) := fun _ _ h =>
    (enumerate (φ n)).injective (Subtype.ext h)
  have ha (n : ℕ) (i : Fin m) : 0 < a n i :=
    (hp n i).factorization_pos_of_dvd (hN (φ n)).2.1.2.ne' (Nat.dvd_of_mem_primeFactors (hpMem n i))
  have hNprod (n : ℕ) : ∏ i, p n i ^ a n i = N (φ n) := by
    let k := N (φ n)
    let f (q : ℕ) := q ^ k.factorization q
    change (∏ i, f (p n i)) = k
    calc
      _ = ∏ q : k.primeFactors, f q := (enumerate (φ n)).prod_comp (fun q => f q)
      _ = ∏ q ∈ k.primeFactors, f q := Finset.prod_coe_sort _ _
      _ = k := (Nat.prod_primeFactors_pow_factorization (hN (φ n)).2.1.2.ne').symm
  let abund (n : ℕ) (i : Fin m) : ℝ := ((p n i ^ a n i).abundancyIndex : ℝ)
  have hAbund (n : ℕ) : ∏ i, abund n i = 2 := by
    let f (i : Fin m) := p n i ^ a n i
    have hcop : (↑(univ : Finset (Fin m)) : Set (Fin m)).Pairwise (Nat.Coprime on f) := by
      intro i _ j _ hij
      exact ((Nat.coprime_primes (hp n i) (hp n j)).mpr ((hpInj n).ne hij)).pow _ _
    change (∏ i, ((f i).abundancyIndex : ℝ)) = 2
    rw [← Rat.cast_prod, ← Nat.abundancyIndex_prod _ _ hcop, hNprod]
    have hperf := (hN (φ n)).2.1
    simp [Nat.abundancyIndex, (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf,
      Nat.cast_ne_zero.mpr hperf.2.ne']
  let fixed := univ.filter fun i : Fin m => ¬ Tendsto (p · i) atTop atTop
  let growing := fixed.filter fun i => Tendsto (a · i) atTop atTop
  have hP (i : Fin m) : ∃ q, i ∈ fixed → ∀ᶠ n in atTop, p n i = q := by
    by_cases hi : i ∈ fixed
    · obtain ⟨q, hq⟩ := eventually_eq_of_monotone_of_not_tendsto_atTop
        (fun _ _ h => (hφ _ _ h).1 i) ((mem_filter.mp hi).2)
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  have hA (i : Fin m) : ∃ e, i ∈ fixed → i ∉ growing → ∀ᶠ n in atTop, a n i = e := by
    by_cases hi : i ∈ fixed
    · by_cases hg : i ∈ growing
      · exact ⟨0, fun _ h => (h hg).elim⟩
      · obtain ⟨e, he⟩ := eventually_eq_of_monotone_of_not_tendsto_atTop
          (fun _ _ h => (hφ _ _ h).2 i) (fun h => hg (mem_filter.mpr ⟨hi, h⟩))
        exact ⟨e, fun _ _ => he⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose P hP using hP
  choose A hA using hA
  obtain ⟨n₀, hn₀⟩ := (fixed.eventually_all.mpr hP).exists
  have hPprime {i : Fin m} (hi : i ∈ fixed) : (P i).Prime := hn₀ i hi ▸ hp n₀ i
  have hPtwo {i : Fin m} (hi : i ∈ fixed) : P i ≠ 2 := hn₀ i hi ▸ hpTwo n₀ i
  have hPinj : Set.InjOn P ↑fixed := fun i hi j hj heq =>
    hpInj n₀ ((hn₀ i hi).trans (heq.trans (hn₀ j hj).symm))
  let num (i : Fin m) : ℕ := if i ∈ fixed then
    if i ∈ growing then P i else ∑ d ∈ (P i ^ A i).divisors, d else 1
  let den (i : Fin m) : ℕ := if i ∈ fixed then
    if i ∈ growing then P i - 1 else P i ^ A i else 1
  let limit (i : Fin m) : ℝ := (num i : ℝ) / (den i : ℝ)
  have hLimit (i : Fin m) : Tendsto (abund · i) atTop (𝓝 (limit i)) := by
    by_cases hi : i ∈ fixed
    · by_cases hg : i ∈ growing
      · have hp1 : (1 : ℝ) < P i := by exact_mod_cast (hPprime hi).one_lt
        have haTop : Tendsto (a · i) atTop atTop := (mem_filter.mp hg).2
        have hpow := (tendsto_pow_atTop_atTop_of_one_lt hp1).comp
          (tendsto_atTop_mono (fun n => Nat.le_succ (a n i)) haTop)
        have h := tendsto_abundancyIndex_prime_pow (p := fun _ => P i) (a := (a · i))
          (fun _ => hPprime hi) tendsto_const_nhds hpow
        simp only [limit, num, den, hi, hg, ite_true, Nat.cast_sub (hPprime hi).one_le,
          Nat.cast_one]
        exact h.congr' ((hP i hi).mono fun n hn => by simp [abund, hn])
      · simp only [limit, num, den, hi, hg, ite_true, ite_false]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hP i hi, hA i hi hg] with n hn he
        simp [abund, Nat.abundancyIndex, hn, he]
    · have hpTop : Tendsto (p · i) atTop atTop := by simpa [fixed] using hi
      simpa [limit, num, den, hi] using
        tendsto_abundancyIndex_prime_pow_of_prime_tendsto (fun n => hp n i) hpTop
  have hProduct : ∏ i, limit i = 2 :=
    tendsto_nhds_unique (tendsto_finsetProd univ fun i _ => hLimit i)
      (tendsto_const_nhds.congr fun n => (hAbund n).symm)
  -- A largest fixed prime with a growing exponent divides the numerator but not the denominator.
  have hGrowing : growing = ∅ := by
    by_contra h
    obtain ⟨j, hj, hmax⟩ := exists_max_image growing P (nonempty_iff_ne_empty.mpr h)
    have hjf : j ∈ fixed := (mem_filter.mp hj).1
    have hq := hPprime hjf
    have hden (i : Fin m) : 0 < den i := by
      by_cases hi : i ∈ fixed
      · by_cases hg : i ∈ growing
        · simpa [den, hi, hg] using Nat.sub_pos_of_lt (hPprime hi).one_lt
        · simpa [den, hi, hg] using pow_pos (hPprime hi).pos (A i)
      · simp [den, hi]
    have hclear : (∏ i, num i) = 2 * (∏ i, den i) := by
      simp only [limit, prod_div_distrib, ← Nat.cast_prod] at hProduct
      have hdenPos : 0 < ∏ i, den i := prod_pos fun i _ => hden i
      exact_mod_cast (div_eq_iff (Nat.cast_ne_zero.mpr hdenPos.ne')).mp hProduct
    have hdvd : P j ∣ ∏ i, num i := by
      simpa [num, hj, hjf] using dvd_prod_of_mem num (mem_univ j)
    rw [hclear] at hdvd
    have hdvdTwo : ¬ P j ∣ 2 := fun h₂ =>
      hPtwo hjf ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h₂)
    refine hq.prime.not_dvd_finsetProd (fun i _ => ?_) ((hq.dvd_mul.mp hdvd).resolve_left hdvdTwo)
    by_cases hi : i ∈ fixed
    · by_cases hg : i ∈ growing
      · rw [show den i = P i - 1 by simp [den, hi, hg]]
        exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt (hPprime hi).one_lt)
          (by have := hmax i hg; have := (hPprime hi).one_lt; omega)
      · rw [show den i = P i ^ A i by simp [den, hi, hg]]
        intro hdiv
        have heq := (Nat.prime_dvd_prime_iff_eq hq (hPprime hi)).mp (hq.dvd_of_dvd_pow hdiv)
        exact hg ((hPinj hjf hi heq) ▸ hj)
    · simpa [den, hi] using hq.not_dvd_one
  have hStable : ∀ᶠ n in atTop, ∀ i ∈ fixed, p n i = P i ∧ a n i = A i := by
    apply fixed.eventually_all.mpr
    intro i hi
    exact (hP i hi).and (hA i hi (by simp [hGrowing]))
  have hFixed : fixed = univ := by
    by_contra hne
    have hnot : ∃ i, i ∉ fixed := by
      simpa [Finset.eq_univ_iff_forall] using hne
    obtain ⟨i, hi⟩ := hnot
    obtain ⟨n, hn⟩ := hStable.exists
    have hmatch (j : Fin m) (hj : j ∈ fixed) : limit j = abund n j := by
      simp [limit, num, den, hj, hGrowing, abund, Nat.abundancyIndex,
        (hn j hj).1, (hn j hj).2]
    have hunit (j : Fin m) (hj : j ∉ fixed) : limit j = 1 := by simp [limit, num, den, hj]
    have hlt (j : Fin m) : 1 < abund n j := one_lt_abundancyIndex_prime_pow (hp n j) (ha n j)
    have hstrict : ∏ j, limit j < ∏ j, abund n j := prod_lt_prod₀
      (fun j _ => by
        by_cases hj : j ∈ fixed
        · rw [hmatch j hj]; exact zero_lt_one.trans (hlt j)
        · rw [hunit j hj]; exact zero_lt_one)
      (fun j _ => by
        by_cases hj : j ∈ fixed
        · rw [hmatch j hj]
        · rw [hunit j hj]; exact (hlt j).le)
      ⟨i, mem_univ _, by rw [hunit i hi]; exact hlt i⟩
    rw [hProduct, hAbund] at hstrict
    exact (lt_irrefl _ hstrict)
  obtain ⟨n, hn⟩ := eventually_atTop.mp hStable
  have hconst (j : ℕ) (hj : n ≤ j) : N (φ j) = ∏ i, P i ^ A i := by
    rw [← hNprod j]
    exact prod_congr rfl fun i hi => by rw [(hn j hj i (hFixed ▸ hi)).1,
      (hn j hj i (hFixed ▸ hi)).2]
  have hsame := (hconst (n + 1) (Nat.le_succ n)).trans (hconst n le_rfl).symm
  exact Nat.succ_ne_self n (φ.injective (ns.injective (Subtype.ext hsame)))

end MetaMathlibExt
