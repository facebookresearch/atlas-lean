/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import MathlibExt.NumberTheory.ArithmeticFunction.PrimitiveNondeficient
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grün's bounds for non-deficient numbers

We bound the number of distinct prime factors from below in terms of the least prime factor.
For odd primes, squaring the abundancy product allows comparison with a telescoping product
along the odd integers. The case of least prime factor five uses the first six eligible primes.

## References

* Joshua Zelinsky, *Must a Primitive Non-Deficient Number Always Have a Small Component?*,
  Journal of Integer Sequences **29** (2026), Article 26.4.3, pp. 1–14, Lemma 5.
  <https://cs.uwaterloo.ca/journals/JIS/VOL29/Zelinsky/zel14.pdf>
* Otto Grün, *Über ungerade vollkommene Zahlen*, Mathematische Zeitschrift **55** (1952),
  pp. 353–354. <https://doi.org/10.1007/BF01181133>
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.PrimitiveNondeficientWanted

private def primeRatio (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

-- Normalize the divisor sum by the prime-power factorization of the denominator.
private theorem two_lt_abundancySup {n p₁ : ℕ} (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors) : 2 < abundancySup n := by
  have hnpos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn.1
  have hindex : 2 ≤ abundancyIndex n := by
    rw [abundancyIndex, le_div_iff₀ hnpos]
    exact_mod_cast hn.2
  apply hindex.trans_lt
  have hprod : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by
    have h : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
      Nat.prod_primeFactors_pow_factorization hn.1
    simpa only [Nat.cast_prod, Nat.cast_pow] using congrArg (fun m : ℕ => (m : ℚ)) h
  rw [abundancyIndex, Nat.sum_divisors hn.1, hprod]
  simp only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, ← Finset.prod_div_distrib, abundancySup]
  refine Finset.prod_lt_prod_of_nonempty₀ ?_ ?_ ⟨p₁, hp₁⟩
  · intro p hp
    have hp0 : (0 : ℚ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    apply div_pos _ (pow_pos hp0 _)
    exact Finset.sum_pos (fun i _ => pow_pos hp0 i) ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  · intro p hp
    have hp1 : (1 : ℚ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [div_lt_div_iff₀ (pow_pos (zero_lt_one.trans hp1) _) (sub_pos.mpr hp1),
      geom_sum_mul, pow_succ']
    exact sub_lt_self _ zero_lt_one

private theorem abundancySup_eq_prod_orderEmbOfFin {n k : ℕ} (hk : n.primeFactors.card = k) :
    abundancySup n = ∏ i : Fin k, primeRatio (n.primeFactors.orderEmbOfFin hk i) := by
  change (∏ q ∈ n.primeFactors, primeRatio q) = _
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ _ hk, Finset.prod_map]
  rfl

private theorem div_sub_antitone {d x y : ℚ} (hd : 0 ≤ d) (hx : d < x) (hxy : x ≤ y) :
    y / (y - d) ≤ x / (x - d) := by
  rw [div_le_div_iff₀ (sub_pos.mpr (hx.trans_le hxy)) (sub_pos.mpr hx)]
  nlinarith only [mul_nonneg hd (sub_nonneg.mpr hxy)]

private theorem sq_primeRatio_lt {p : ℕ} (hp : 2 < p) :
    primeRatio p ^ 2 < ((p : ℚ) + 1 / 2) / ((p : ℚ) + 1 / 2 - 2) := by
  have hp' : (2 : ℚ) < p := by exact_mod_cast hp
  unfold primeRatio
  rw [div_pow, div_lt_div_iff₀ (pow_pos (by linarith) _) (by linarith)]
  nlinarith only [hp']

private theorem odd_gap {k : ℕ} {p : Fin k ↪o ℕ} (hodd : ∀ i, Odd (p i))
    {i j : Fin k} (hij : i < j) : p i + 2 ≤ p j := by
  have hlt := p.strictMono hij
  obtain ⟨a, ha⟩ := hodd i
  obtain ⟨b, hb⟩ := hodd j
  omega

private theorem odd_rank_lower_bound {k b : ℕ} {p : Fin k ↪o ℕ} (hodd : ∀ i, Odd (p i))
    (hmin : ∀ i, b ≤ p i) (i : Fin k) : b + 2 * i.val ≤ p i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => simpa using hmin ⟨0, hi⟩
  | succ i ih =>
    have hi' : i < k := by omega
    have hstep := odd_gap hodd (show (⟨i, hi'⟩ : Fin k) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)
    have hprev : b + 2 * i ≤ p ⟨i, hi'⟩ := ih hi'
    change b + 2 * (i + 1) ≤ p ⟨i + 1, hi⟩
    omega

private theorem prod_step_two (b : ℚ) (hb : 2 < b) (k : ℕ) :
    (∏ i : Fin k, (b + 2 * (i.val : ℚ)) / (b + 2 * (i.val : ℚ) - 2)) =
      (b + 2 * (k : ℚ) - 2) / (b - 2) := by
  induction k with
  | zero => simp [ne_of_gt (sub_pos.mpr hb)]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ, ih]
    have hcancel : b + 2 * ((k : ℚ) + 1) - 2 = b + 2 * (k : ℚ) := by ring
    have hne : b + 2 * (k : ℚ) - 2 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℚ) k]
    rw [hcancel, div_mul_div_comm, mul_comm (b + 2 * (k : ℚ) - 2)]
    exact mul_div_mul_right _ _ hne

-- The half-unit shift sharpens the telescoping estimate enough to round to Grün's bound.
private theorem grun_bound_of_two_lt {n p₁ : ℕ} (hp₁ : p₁ ∈ n.primeFactors) (hp : 2 < p₁)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) (hH : 2 < abundancySup n) :
    3 * p₁ < 2 * n.primeFactors.card + 4 := by
  let p := n.primeFactors.orderEmbOfFin rfl
  have hmem (i : Fin n.primeFactors.card) : p i ∈ n.primeFactors :=
    n.primeFactors.orderEmbOfFin_mem rfl i
  have hleast i := hmin (p i) (hmem i)
  have hodd i := (Nat.prime_of_mem_primeFactors (hmem i)).odd_of_ne_two
    (ne_of_gt (hp.trans_le (hleast i)))
  let b : ℚ := (p₁ : ℚ) + 1 / 2
  have hp' : (2 : ℚ) < p₁ := by exact_mod_cast hp
  have hb : 2 < b := by dsimp [b]; linarith only [hp']
  have hupper : abundancySup n ^ 2 ≤ (b + 2 * (n.primeFactors.card : ℚ) - 2) / (b - 2) := by
    rw [abundancySup_eq_prod_orderEmbOfFin rfl, ← Finset.prod_pow, ← prod_step_two _ hb]
    apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
    intro i _
    have hrank : (p₁ : ℚ) + 2 * (i.val : ℚ) ≤ (p i : ℚ) := by
      exact_mod_cast odd_rank_lower_bound hodd hleast i
    have hstart : 2 < b + 2 * (i.val : ℚ) := by
      linarith [Nat.cast_nonneg (α := ℚ) i.val]
    refine (sq_primeRatio_lt (hp.trans_le (hleast i))).le.trans
      (div_sub_antitone (by norm_num) hstart ?_)
    dsimp [b]
    linarith only [hrank]
  have hfour : (4 : ℚ) < abundancySup n ^ 2 := by
    nlinarith only [hH, sq_nonneg (abundancySup n - 2)]
  have h := (lt_div_iff₀ (sub_pos.mpr hb)).mp (hfour.trans_le hupper)
  have hcard : 6 * p₁ < 4 * n.primeFactors.card + 9 := by
    exact_mod_cast (show (6 : ℚ) * p₁ < 4 * (n.primeFactors.card : ℚ) + 9 by
      dsimp [b] at h
      linarith only [h])
  obtain ⟨a, ha⟩ := (Nat.prime_of_mem_primeFactors hp₁).odd_of_ne_two hp.ne'
  omega

-- Among odd integers starting at five, nine and fifteen must be skipped.
private theorem abundancySup_lt_two_of_card_eq_six {n : ℕ} (hk : n.primeFactors.card = 6)
    (hmin : ∀ q ∈ n.primeFactors, 5 ≤ q) : abundancySup n < 2 := by
  let p := n.primeFactors.orderEmbOfFin hk
  let firstSix : Fin 6 → ℕ := ![5, 7, 11, 13, 17, 19]
  have hmem (i : Fin 6) : p i ∈ n.primeFactors := n.primeFactors.orderEmbOfFin_mem hk i
  have hleast i := hmin (p i) (hmem i)
  have hprime i := Nat.prime_of_mem_primeFactors (hmem i)
  have hodd i := (hprime i).odd_of_ne_two (by have := hleast i; omega)
  have hgap {i j : Fin 6} (hij : i < j) := odd_gap hodd hij
  have h₁ := hgap (show (0 : Fin 6) < 1 by decide)
  have h₂ := hgap (show (1 : Fin 6) < 2 by decide)
  have h₃ := hgap (show (2 : Fin 6) < 3 by decide)
  have h₄ := hgap (show (3 : Fin 6) < 4 by decide)
  have h₅ := hgap (show (4 : Fin 6) < 5 by decide)
  have h9 : p 2 ≠ 9 := by rintro h; exact (by decide : ¬ Nat.Prime 9) (h ▸ hprime 2)
  have h15 : p 4 ≠ 15 := by rintro h; exact (by decide : ¬ Nat.Prime 15) (h ▸ hprime 4)
  obtain ⟨a, ha⟩ := hodd 2
  obtain ⟨b, hb⟩ := hodd 4
  have hrank (i : Fin 6) : firstSix i ≤ p i := by
    have h0 : 5 ≤ p 0 := hleast 0
    fin_cases i
    · exact h0
    · change 7 ≤ p 1
      omega
    · change 11 ≤ p 2
      omega
    · change 13 ≤ p 3
      omega
    · change 17 ≤ p 4
      omega
    · change 19 ≤ p 5
      omega
  rw [abundancySup_eq_prod_orderEmbOfFin hk]
  calc
    (∏ i : Fin 6, primeRatio (p i)) ≤ ∏ i : Fin 6, primeRatio (firstSix i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have h : (5 : ℚ) ≤ p i := by exact_mod_cast hleast i
        exact div_nonneg (by linarith) (by linarith)
      · intro i _
        have h : 1 < firstSix i := by fin_cases i <;> decide
        exact div_sub_antitone (by norm_num) (by exact_mod_cast h) (by exact_mod_cast hrank i)
    _ < 2 := by
      rw [Fin.prod_univ_six]
      change primeRatio 5 * primeRatio 7 * primeRatio 11 * primeRatio 13 * primeRatio 17 *
        primeRatio 19 < 2
      norm_num [primeRatio]

/-- **Grün's bound for non-deficient numbers.** Let $n$ be a non-deficient number with $k$
distinct prime factors, the least of which is $p_1$. Then $\tfrac{3}{2} p_1 - 2 < k$, and if
$p_1 \ge 5$ then $p_1 + 2 \le k$.

Source: Joshua Zelinsky, "Must a Primitive Non-Deficient Number
Always Have a Small Component?", Lemma 5 (label `Grun`). -/
public theorem grun_bounds_of_isNondeficient
    (n p₁ : ℕ) (hn : IsNondeficient n)
    (hp₁ : p₁ ∈ n.primeFactors)
    (hmin : ∀ q ∈ n.primeFactors, p₁ ≤ q) :
    (3 : ℚ) / 2 * (p₁ : ℚ) - 2 < (n.primeFactors.card : ℚ) ∧
      (5 ≤ p₁ → p₁ + 2 ≤ n.primeFactors.card) := by
  have hH := two_lt_abundancySup hn hp₁
  have hprime := Nat.prime_of_mem_primeFactors hp₁
  obtain heq | hp := hprime.two_le.eq_or_lt
  · subst p₁
    -- A power of two would have a singleton prime-factor set and supremum exactly two.
    have hk : 1 < n.primeFactors.card := by
      by_contra! hk
      have hsingle : n.primeFactors = {2} := by
        symm
        apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hp₁)
        simpa using hk
      norm_num [abundancySup, hsingle] at hH
    constructor
    · norm_num
      exact_mod_cast hk
    · omega
  · have hk := grun_bound_of_two_lt hp₁ hp hmin hH
    constructor
    · have hk' : (3 : ℚ) * p₁ < 2 * (n.primeFactors.card : ℚ) + 4 := by exact_mod_cast hk
      linarith only [hk']
    intro h5
    by_cases heq : p₁ = 5
    · subst p₁
      by_contra! h
      have hcard : n.primeFactors.card = 6 := by omega
      exact (not_lt_of_ge (abundancySup_lt_two_of_card_eq_six hcard hmin).le) hH
    · obtain ⟨a, ha⟩ := hprime.odd_of_ne_two hp.ne'
      omega

end MathlibExt.NumberTheory.PrimitiveNondeficientWanted
