/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PolygonalNumber
public import MathlibExt.NumberTheory.PracticalNumber
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import MathlibExt.NumberTheory.PolygonalSumModPrimePow
import MathlibExt.NumberTheory.PolygonalSumParity
import MathlibExt.NumberTheory.PracticalPolygonalSums
import all MathlibExt.NumberTheory.PracticalPolygonalSumsIsPracticalNumberMulOfLeSigmaAddOne

/-!
# Large integers as sums of a practical number and two polygonal numbers

For each natural number `s > 3`, all sufficiently large natural numbers are a sum of a
practical number and two `s`-gonal numbers. The proof chooses a primorial with large divisor
sum relative to its size, enlarges it by powers of a suitable odd prime, and uses the Chinese
remainder theorem to pick two bounded polygonal indices. The indices chosen in the proof are
positive, although the polygonal-number convention also allows zero.

## References

* Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal Numbers*,
  Journal of Integer Sequences 27 (2024), Article 24.5.1, pp. 1–12, Theorem 2 and its proof in §4.
* M. Margenstern, *Les nombres pratiques: théorie, observations et conjectures*,
  J. Number Theory 37 (1991), pp. 1–36, Corollary 1 (the small-factor multiplication rule).
* B. M. Stewart, *Sums of distinct divisors*, Amer. J. Math. 76 (1954), pp. 779–785, §3
  (the practical number characterization cited by Somu and Tran; here the multiplication rule
  suffices).
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., Oxford
  University Press (2008), Theorem 19; K. Knopp, *Theory and Application of Infinite Series*,
  2nd ed., Blackie & Son (1954), Chapter 7, Theorem 3. The paper cites these for the divergence
  argument; here we use Mathlib's `not_summable_one_div_on_primes` and sum over prime divisors.
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset
open scoped BigOperators

private theorem isPracticalNumber_primorial (b : ℕ) : IsPracticalNumber (primorial b) := by
  induction b with
  | zero =>
    rw [primorial_zero]
    refine ⟨by decide, fun m hm hle ↦ ?_⟩
    have : m = 1 := by omega
    subst m
    exact ⟨{1}, by simp, by simp⟩
  | succ b ih =>
    rw [primorial_eq_prod_primesLE, Nat.primesLE_succ]
    split_ifs with hprime
    · rw [prod_insert (Nat.notMem_primesLE b), ← primorial_eq_prod_primesLE, mul_comm]
      exact isPracticalNumber_mul_of_le_sigma_add_one _ _ ih (Nat.succ_pos _) <|
        Nat.succ_le_succ (le_primorial_self.trans (le_sigma_one _ ih.1))
    · rwa [← primorial_eq_prod_primesLE]

/-- Prime reciprocals give a lower bound for the divisor sum of every nonzero multiple of a
sufficiently large primorial. -/
private theorem exists_mul_le_sigma_one_of_primorial_dvd (A b : ℕ) :
    ∃ r ≥ b, ∀ m : ℕ, 0 < m → primorial r ∣ m → A * m ≤ sigma 1 m := by
  let f : ℕ → ℝ := Set.indicator {q | Nat.Prime q} (fun q : ℕ ↦ (1 : ℝ) / q)
  have hunbounded : ∃ k, (A : ℝ) < ∑ q ∈ range k, f q := by
    by_contra! h
    apply not_summable_one_div_on_primes
    refine summable_of_sum_range_le (fun q ↦ ?_) h
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split <;> positivity
  obtain ⟨k, hk⟩ := hunbounded
  refine ⟨max b k, le_max_left _ _, fun m hm hdiv ↦ ?_⟩
  have hd (q : ℕ) (hq : q ∈ Nat.primesBelow k) : q ∣ m :=
    ((Nat.prime_of_mem_primesBelow hq).dvd_primorial_iff.mpr
      ((Nat.lt_of_mem_primesBelow hq).le.trans (le_max_right _ _))).trans hdiv
  have hsum : (A : ℝ) ≤ ∑ q ∈ Nat.primesBelow k, (1 / q : ℝ) := by
    rw [Nat.primesBelow_eq_filter_range, sum_filter]
    simpa only [f, Set.indicator_apply, Set.mem_ofPred_eq] using hk.le
  suffices (A : ℝ) * m ≤ (sigma 1 m : ℝ) by exact_mod_cast this
  calc
    (A : ℝ) * m ≤ (∑ q ∈ Nat.primesBelow k, (1 / q : ℝ)) * m :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = ∑ q ∈ Nat.primesBelow k, ((m / q : ℕ) : ℝ) := by
      rw [sum_mul]
      refine sum_congr rfl fun q hq ↦ ?_
      rw [Nat.cast_div (hd q hq) (by exact_mod_cast (Nat.prime_of_mem_primesBelow hq).ne_zero)]
      ring
    _ ≤ (sigma 1 m : ℝ) := by
      rw [sigma_eq_sum_div, Nat.cast_sum]
      simp only [pow_one]
      exact sum_le_sum_of_subset_of_nonneg
        (fun q hq ↦ Nat.mem_divisors.mpr ⟨hd q hq, hm.ne'⟩) (fun _ _ _ ↦ by positivity)

private theorem polygonalNumber_modEq_of_coprime_two (s : ℕ) {m x y : ℕ}
    (hm : m.Coprime 2) (h : x ≡ y [MOD m]) :
    Nat.polygonalNumber s x ≡ Nat.polygonalNumber s y [MOD m] := by
  have hchoose : x.choose 2 ≡ y.choose 2 [MOD m] := by
    apply Nat.ModEq.cancel_left_of_coprime hm
    apply h.add_right_cancel
    simpa only [← Nat.polygonalNumber_four, Nat.polygonalNumber, Nat.reduceSub] using h.pow 2
  exact (hchoose.mul_left (s - 2)).add h

/-- Put the local solutions together, using modulus four on the indices at the prime two. -/
private theorem exists_bounded_polygonal_sum_modEq (s n r p j : ℕ) (hs : 3 < s) (hn : 0 < n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpr : p ≤ r)
    (hpow : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
      Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD p ^ (j + 1)]) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≤ 2 * (primorial r * p ^ j) ∧
      y ≤ 2 * (primorial r * p ^ j) ∧
      Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD primorial r * p ^ j] := by
  let e (a q : ℕ) := if q = p then j + 1 else if q = 2 then a + 1 else 1
  let m (a q : ℕ) := q ^ e a q
  have hpL : p ∈ Nat.primesLE r := Nat.mem_primesLE.mpr ⟨hpr, hp⟩
  have h2L : 2 ∈ Nat.primesLE r := Nat.mem_primesLE.mpr ⟨hp.two_le.trans hpr, Nat.prime_two⟩
  have hprod (a : ℕ) : ∏ q ∈ Nat.primesLE r, m a q = primorial r * p ^ j * 2 ^ a := by
    calc
      _ = ∏ q ∈ Nat.primesLE r, q * (if q = p then p ^ j else 1) *
          (if q = 2 then 2 ^ a else 1) := by
        refine prod_congr rfl fun q _ ↦ ?_
        rcases eq_or_ne q p with rfl | hqp
        · simp [m, e, hp2, pow_succ, mul_comm]
        · rcases eq_or_ne q 2 with rfl | hq2
          · simp [m, e, hqp, pow_succ, mul_comm]
          · simp [m, e, hqp, hq2]
      _ = _ := by
        rw [prod_mul_distrib, prod_mul_distrib, prod_ite_eq_of_mem' _ _ _ hpL,
          prod_ite_eq_of_mem' _ _ _ h2L, ← primorial_eq_prod_primesLE]
  have hne (a : ℕ) (q : ℕ) (hq : q ∈ Nat.primesLE r) : m a q ≠ 0 :=
    pow_ne_zero _ (Nat.prime_of_mem_primesLE hq).ne_zero
  have hcop (a : ℕ) :
      Set.Pairwise (↑(Nat.primesLE r) : Set ℕ) (fun q t ↦ (m a q).Coprime (m a t)) :=
    fun _ hq _ ht hqt ↦ ((Nat.coprime_primes (Nat.prime_of_mem_primesLE hq)
      (Nat.prime_of_mem_primesLE ht)).mpr hqt).pow _ _
  have hlocal (q : ℕ) (hq : q ∈ Nat.primesLE r) : ∃ x y : ℕ,
      ∀ u v : ℕ, 0 < u → 0 < v → u ≡ x [MOD m 1 q] → v ≡ y [MOD m 1 q] →
        Nat.polygonalNumber s u + Nat.polygonalNumber s v ≡ n [MOD m 0 q] := by
    rcases eq_or_ne q 2 with rfl | hq2
    · obtain ⟨x, y, _, _, h⟩ := exists_polygonal_add_polygonal_modEq_two n s hn hs
      exact ⟨x, y, by simpa [m, e, hp2.symm] using h⟩
    · have hsame : m 1 q = m 0 q := by simp [m, e, hq2]
      have hprime := Nat.prime_of_mem_primesLE hq
      have hcop2 : (m 0 q).Coprime 2 :=
        ((Nat.coprime_primes hprime Nat.prime_two).mpr hq2).pow_left _
      have hseed : ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
          Nat.polygonalNumber s x + Nat.polygonalNumber s y ≡ n [MOD m 0 q] := by
        rcases eq_or_ne q p with rfl | hqp
        · simpa [m, e] using hpow
        · simpa [m, e, hqp, hq2] using exists_polygonal_add_polygonal_modEq_prime q n s
            hprime hq2 hn hs
      obtain ⟨x, y, _, _, hxy⟩ := hseed
      refine ⟨x, y, fun u v _ _ hu hv ↦ ?_⟩
      rw [hsame] at hu hv
      exact ((polygonalNumber_modEq_of_coprime_two s hcop2 hu).add
        (polygonalNumber_modEq_of_coprime_two s hcop2 hv)).trans hxy
  choose! x y hxy using hlocal
  have representative (f : ℕ → ℕ) : ∃ z : ℕ, 0 < z ∧ z ≤ 2 * (primorial r * p ^ j) ∧
      ∀ q ∈ Nat.primesLE r, z ≡ f q [MOD m 1 q] := by
    let L := ∏ q ∈ Nat.primesLE r, m 1 q
    have hL : L = 2 * (primorial r * p ^ j) := by
      dsimp [L]
      rw [hprod, pow_one, mul_comm]
    let t := Nat.chineseRemainderOfFinset f (m 1) (Nat.primesLE r) (hne 1) (hcop 1)
    have ht : (t : ℕ) < L := Nat.chineseRemainderOfFinset_lt_prod f (m 1) (hne 1) (hcop 1)
    by_cases ht0 : (t : ℕ) = 0
    · refine ⟨L, by omega, by omega, fun q hq ↦ ?_⟩
      have hmod := t.property q hq
      rw [ht0] at hmod
      exact (Nat.modEq_zero_iff_dvd.mpr (dvd_prod_of_mem (m 1) hq)).trans hmod
    · exact ⟨t, Nat.pos_of_ne_zero ht0, by omega, t.property⟩
  obtain ⟨u, hu, hul, hum⟩ := representative x
  obtain ⟨v, hv, hvl, hvm⟩ := representative y
  refine ⟨u, v, hu, hv, hul, hvl, ?_⟩
  have hpairs : (Nat.primesLE r).toList.Pairwise (fun q t ↦ (m 0 q).Coprime (m 0 t)) :=
    List.Nodup.pairwise_of_forall_ne (nodup_toList _) fun _ ha _ hb hab ↦
      hcop 0 (mem_toList.mp ha) (mem_toList.mp hb) hab
  have h := (Nat.modEq_list_map_prod_iff (a := Nat.polygonalNumber s u +
    Nat.polygonalNumber s v) (b := n) hpairs).mpr (fun q hq ↦ by
      rw [mem_toList] at hq
      exact hxy q hq u v hu hv (hum q hq) (hvm q hq))
  simpa only [prod_map_toList, hprod, pow_zero, mul_one] using h

/-- **Large integers as a practical number plus two polygonal numbers.** Let $s > 3$ be a natural
number and, for a natural number $x$, let $P_s(x) = (s-2)\binom{x}{2} + x$ be the $x$-th
$s$-gonal number, so that $P_s(0) = 0$. There is a natural number $N$ such that every natural
number $n > N$ can be written as $n = q + P_s(x) + P_s(y)$ with $q$ a practical number and
$x, y$ natural numbers.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Theorem 2
(`jis-2024-24.5.1-thm-2`). -/
public theorem eventually_practical_add_two_polygonal (s : ℕ) (hs : 3 < s) :
    ∃ N : ℕ, ∀ n > N, ∃ q x y : ℕ,
      IsPracticalNumber q ∧ n = q + Nat.polygonalNumber s x + Nat.polygonalNumber s y := by
  obtain ⟨p, hp, hp4, _, hpow⟩ := exists_prime_polygonal_add_polygonal_modEq_prime_pow s hs
  have hp2 : p ≠ 2 := by omega
  obtain ⟨A, hA⟩ := exists_two_polygonal_two_mul_le_mul_sq s p hs
  obtain ⟨r, hpr, hσ⟩ := exists_mul_le_sigma_one_of_primorial_dvd A p
  let M (j : ℕ) := primorial r * p ^ j
  have hM (j : ℕ) : 0 < M j := mul_pos (primorial_pos _) (pow_pos hp.pos _)
  have hM_succ (j : ℕ) : M (j + 1) = M j * p := by simp [M, pow_succ, mul_assoc]
  have hM_dvd (j : ℕ) : primorial r ∣ M j := dvd_mul_right _ _
  have hP (k : ℕ) : k ≤ Nat.polygonalNumber s k := Nat.le_add_left _ _
  have hmono : Monotone (Nat.polygonalNumber s) := fun _ _ h ↦
    Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.choose_le_choose 2 h)) h
  have hpractical (j : ℕ) : IsPracticalNumber (M j) := by
    induction j with
    | zero => simpa [M] using isPracticalNumber_primorial r
    | succ j ih =>
      have hpd := (hp.dvd_primorial_iff.mpr hpr).trans (hM_dvd j)
      have hle := (Nat.le_of_dvd (hM j) hpd).trans (le_sigma_one _ (hM j))
      rw [hM_succ]
      exact isPracticalNumber_mul_of_le_sigma_add_one _ p ih hp.pos (Nat.le_succ_of_le hle)
  refine ⟨2 * Nat.polygonalNumber s (2 * M 0), fun n hn ↦ ?_⟩
  have hnpos : 0 < n := by omega
  -- The first scale whose upper bound reaches `n` has a predecessor by the cutoff hypothesis.
  have hlarge : ∃ j, n ≤ 2 * Nat.polygonalNumber s (2 * M j) := by
    refine ⟨(Nat.log p n).succ, ?_⟩
    have hlt := Nat.lt_pow_succ_log_self hp.one_lt n
    have hl := Nat.le_mul_of_pos_left (p ^ (Nat.log p n).succ) (primorial_pos r)
    have hl' := hP (2 * M (Nat.log p n).succ)
    change p ^ (Nat.log p n).succ ≤ M (Nat.log p n).succ at hl
    omega
  have hj0 : Nat.find hlarge ≠ 0 := by
    intro h0
    have h := Nat.find_spec hlarge
    rw [h0] at h
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hlt : 2 * Nat.polygonalNumber s (2 * M j) < n :=
    Nat.lt_of_not_ge (Nat.find_min hlarge (by rw [hj]; omega))
  have hnext := Nat.find_spec hlarge
  rw [hj] at hnext
  have hsize : n ≤ A * (M j) ^ 2 := by
    have harg : 2 * M (j + 1) = 2 * p * M j := by rw [hM_succ]; ring
    rw [harg] at hnext
    exact hnext.trans (hA (M j) (hM j))
  obtain ⟨x, y, _, _, hx, hy, hxy⟩ := exists_bounded_polygonal_sum_modEq s n r p j hs hnpos hp
    hp2 hpr (hpow (j + 1) n (Nat.succ_pos _) hnpos)
  change x ≤ 2 * M j at hx
  change y ≤ 2 * M j at hy
  have hsum : Nat.polygonalNumber s x + Nat.polygonalNumber s y < n := by
    have hx' := hmono hx
    have hy' := hmono hy
    omega
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hsum.le).mp hxy
  change n - (Nat.polygonalNumber s x + Nat.polygonalNumber s y) = M j * k at hk
  have hkpos : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    rw [this, mul_zero] at hk
    omega
  have hkle : k ≤ sigma 1 (M j) := by
    have hkm : (M j) * k ≤ A * (M j) ^ 2 := hk ▸ (Nat.sub_le _ _).trans hsize
    have hmul : A * (M j) ^ 2 = (M j) * (A * M j) := by ring
    rw [hmul] at hkm
    exact (Nat.le_of_mul_le_mul_left hkm (hM j)).trans (hσ (M j) (hM j) (hM_dvd j))
  exact ⟨M j * k, x, y, isPracticalNumber_mul_of_le_sigma_add_one _ _ (hpractical j) hkpos
    (by omega), by omega⟩

end MetaMathlibExt
