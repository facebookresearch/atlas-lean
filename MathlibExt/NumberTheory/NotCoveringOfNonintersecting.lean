/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.ErdosGrahamCovering
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# No covering system of divisor form for a non-intersecting integer

The main result is `not_covering_of_nonintersecting`: if an integer admits a
congruence set of divisor form whose distinct classes overlap only at coprime
moduli, then no congruence set of divisor form covers the integers. This is
Theorem 3.2 of Adenwalla's paper on a question of Erdős and Graham, proved
following the paper through its Lemma 3.1, the reciprocal-sum estimate of its
Proposition 2.3, the covering estimate of its Lemma 2.2, and a direct count
for the remaining case of twice a prime power.

## References

* Sarosh Adenwalla, *A Question of Erdős and Graham on Covering Systems*,
  INTEGERS 26 (2026), Article A52.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosGrahamCoveringWanted

/-- The sum of the reciprocals of the divisors of `n` factors as a product
over its prime factors of finite geometric sums. -/
private theorem sum_inv_divisors_eq (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (1 : ℚ) / d =
      ∏ p ∈ n.primeFactors,
        ∑ j ∈ Finset.range (n.factorization p + 1), (1 : ℚ) / (p : ℚ) ^ j := by
  let invFun : ArithmeticFunction ℚ := ⟨fun d => (1 : ℚ) / d, by simp⟩
  have hmul : invFun.IsMultiplicative := by
    constructor
    · simp [invFun]
    · intro m k _
      simp only [invFun, ArithmeticFunction.coe_mk]
      rw [Nat.cast_mul, one_div, one_div, one_div, mul_inv]
  have hH : (invFun * (↑ArithmeticFunction.zeta : ArithmeticFunction ℚ)).IsMultiplicative :=
    hmul.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hfact := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    (invFun * (↑ArithmeticFunction.zeta : ArithmeticFunction ℚ)) hH (n := n) hn
  have hHn : (invFun * (↑ArithmeticFunction.zeta : ArithmeticFunction ℚ)) n =
      ∑ d ∈ n.divisors, (1 : ℚ) / d := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    refine Finset.sum_congr rfl fun d _ => rfl
  rw [← hHn, hfact]
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpprime := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rw [Nat.divisors_prime_pow hpprime, Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : invFun (p ^ j) = (1 : ℚ) / (p : ℚ) ^ j := by
    change (1 : ℚ) / ((p ^ j : ℕ) : ℚ) = (1 : ℚ) / (p : ℚ) ^ j
    rw [Nat.cast_pow]
  exact h1

/-- The function `q ↦ q / (q - 1)` is antitone on integers at least `2`. -/
private theorem f_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b : ℚ) / ((b : ℚ) - 1) ≤ (a : ℚ) / ((a : ℚ) - 1) := by
  have ha' : (1 : ℚ) < a := by exact_mod_cast ha
  have hb' : (1 : ℚ) < b := by exact_mod_cast (le_trans ha hab)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hcast : (a : ℚ) ≤ b := by exact_mod_cast hab
  nlinarith

/-- The function `q ↦ q / (q - 1)` is nonnegative on integers at least `2`. -/
private theorem f_nonneg {q : ℕ} (hq : 2 ≤ q) :
    (0 : ℚ) ≤ (q : ℚ) / ((q : ℚ) - 1) := by
  apply div_nonneg (Nat.cast_nonneg _)
  exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ q by omega))

/-- The function `q ↦ q / (q - 1)` is positive on integers at least `2`. -/
private theorem f_pos {q : ℕ} (hq : 2 ≤ q) :
    (0 : ℚ) < (q : ℚ) / ((q : ℚ) - 1) := by
  apply div_pos (by exact_mod_cast (show 0 < q by omega))
  have h1 : (1 : ℚ) < q := by exact_mod_cast hq
  linarith

/-- A finite geometric sum with ratio `1 / p` is less than `p / (p - 1)`. -/
private theorem geom_sum_inv_lt {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (1 : ℚ) / (p : ℚ) ^ j < (p : ℚ) / ((p : ℚ) - 1) := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hp)
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp
  set x : ℚ := 1 / p with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx]; exact (div_lt_one hp0).mpr (by exact_mod_cast hp)
  have hsum : ∑ j ∈ Finset.range (k + 1), (1 : ℚ) / (p : ℚ) ^ j =
      ∑ j ∈ Finset.range (k + 1), x ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx, div_pow, one_pow]
  rw [hsum]
  have hgeom := geom_sum_mul x (k + 1)
  have hxp : x ^ (k + 1) < 1 := pow_lt_one₀ hx0.le hx1 (by norm_num)
  have hxp0 : 0 < x ^ (k + 1) := pow_pos hx0 _
  have hkey : (∑ j ∈ Finset.range (k + 1), x ^ j) * (1 - x) < 1 := by
    have hEq : (∑ j ∈ Finset.range (k + 1), x ^ j) * (1 - x) = 1 - x ^ (k + 1) := by
      linear_combination -hgeom
    rw [hEq]; linarith
  have h1x : (0 : ℚ) < 1 - x := by linarith
  have hlt : (∑ j ∈ Finset.range (k + 1), x ^ j) < 1 / (1 - x) := by
    rw [lt_div_iff₀ h1x]; linarith [hkey]
  have heq : (1 : ℚ) / (1 - x) = (p : ℚ) / ((p : ℚ) - 1) := by
    rw [hx]; field_simp
  rwa [heq] at hlt

/-- If every element of `T` is at least `L ≥ 2`, then the product of
`q / (q - 1)` over `T` is at most the product over the smallest possible
values `L, L + 1, …`. -/
private theorem prod_f_le {T : Finset ℕ} {L : ℕ} (hL2 : 2 ≤ L)
    (hT : ∀ q ∈ T, L ≤ q) :
    ∏ q ∈ T, (q : ℚ) / ((q : ℚ) - 1) ≤
      ∏ i ∈ Finset.range T.card, ((L + i : ℕ) : ℚ) / (((L + i : ℕ) : ℚ) - 1) := by
  classical
  have key : ∀ k (hk : k < T.card),
      L + k ≤ T.orderEmbOfFin rfl ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hmem := hT _ (Finset.orderEmbOfFin_mem T (rfl : T.card = T.card) ⟨0, hk⟩)
      simpa using hmem
    | succ k ih =>
      intro hk
      have hk' : k < T.card := by omega
      have hlt : T.orderEmbOfFin rfl ⟨k, hk'⟩ < T.orderEmbOfFin rfl ⟨k + 1, hk⟩ :=
        (T.orderEmbOfFin rfl).strictMono (by simp [Fin.lt_def])
      have hih := ih hk'
      omega
  have hprod : (∏ i : Fin T.card,
        ((T.orderEmbOfFin rfl i : ℕ) : ℚ) / ((((T.orderEmbOfFin rfl i : ℕ) : ℚ)) - 1)) =
      ∏ q ∈ T, (q : ℚ) / ((q : ℚ) - 1) := by
    refine Finset.prod_bij (fun i _ => T.orderEmbOfFin rfl i)
      (fun i _ => Finset.orderEmbOfFin_mem T rfl i)
      (fun a _ b _ h => (T.orderEmbOfFin rfl).injective h) ?_ (fun i _ => rfl)
    intro q hq
    have hrange : q ∈ Set.range (T.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hq
    obtain ⟨i, hi⟩ := hrange
    exact ⟨i, Finset.mem_univ i, hi⟩
  rw [← hprod]
  have hle : ∏ i : Fin T.card,
        ((T.orderEmbOfFin rfl i : ℕ) : ℚ) / ((((T.orderEmbOfFin rfl i : ℕ) : ℚ)) - 1) ≤
      ∏ i : Fin T.card,
        ((L + (i : ℕ) : ℕ) : ℚ) / ((((L + (i : ℕ) : ℕ) : ℚ)) - 1) := by
    refine Finset.prod_le_prod₀ (fun i _ => f_nonneg (q := T.orderEmbOfFin rfl i) ?_)
      fun i _ => ?_
    · exact Nat.le_trans hL2 (hT _ (Finset.orderEmbOfFin_mem T (rfl : T.card = T.card) i))
    · apply f_antitone (by omega : 2 ≤ L + (i : ℕ))
      have hk := key (i : ℕ) i.isLt
      simpa using hk
  rw [Fin.prod_univ_eq_prod_range
    (fun i => ((L + i : ℕ) : ℚ) / (((L + i : ℕ) : ℚ) - 1)) T.card] at hle
  exact hle

/-- The telescoping product `∏_{i < t} (L + i) / (L + i - 1)`. -/
private theorem prod_f_range {L : ℕ} (hL : 2 ≤ L) : ∀ t : ℕ,
    ∏ i ∈ Finset.range t, ((L + i : ℕ) : ℚ) / (((L + i : ℕ) : ℚ) - 1) =
      (((L + t : ℕ) : ℚ) - 1) / ((L : ℚ) - 1) := by
  have hg0 : ((L : ℚ) - 1) ≠ 0 := by
    have h2 : (2 : ℚ) ≤ (L : ℚ) := by exact_mod_cast hL
    linarith
  intro t
  induction t with
  | zero => exact (div_self hg0).symm
  | succ t ih =>
    rw [Finset.prod_range_succ, ih]
    have hgt : (((L + t : ℕ) : ℚ) - 1) ≠ 0 := by
      have h2 : (2 : ℚ) ≤ ((L + t : ℕ) : ℚ) := by exact_mod_cast (by omega)
      linarith
    have hgt1 : (((L + (t + 1) : ℕ) : ℚ) - 1) ≠ 0 := by
      have h2 : (2 : ℚ) ≤ ((L + (t + 1) : ℕ) : ℚ) := by exact_mod_cast (by omega)
      linarith
    field_simp
    push_cast
    ring

/-- The Chinese remainder theorem for integers: two congruences that agree
modulo the greatest common divisor of their moduli have a common solution. -/
private theorem exists_int_modEq_of_modEq_gcd {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A B : ℤ} (h : A ≡ B [ZMOD (Nat.gcd m n : ℤ)]) :
    ∃ x : ℤ, x ≡ A [ZMOD (m : ℤ)] ∧ x ≡ B [ZMOD (n : ℤ)] := by
  classical
  set a' := (A % (m : ℤ)).toNat with ha'
  set b' := (B % (n : ℤ)).toNat with hb'
  have ha'nn : (0 : ℤ) ≤ A % (m : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hm.ne')
  have hb'nn : (0 : ℤ) ≤ B % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have hcastA : ((a' : ℤ)) = A % (m : ℤ) := Int.toNat_of_nonneg ha'nn
  have hcastB : ((b' : ℤ)) = B % (n : ℤ) := Int.toNat_of_nonneg hb'nn
  have hmod : a' ≡ b' [MOD Nat.gcd m n] := by
    rw [← Int.natCast_modEq_iff]
    have hA : ((a' : ℤ)) ≡ A [ZMOD (Nat.gcd m n : ℤ)] := by
      rw [hcastA]
      exact (Int.mod_modEq A (m : ℤ)).of_dvd (by exact_mod_cast Nat.gcd_dvd_left m n)
    have hB : ((b' : ℤ)) ≡ B [ZMOD (Nat.gcd m n : ℤ)] := by
      rw [hcastB]
      exact (Int.mod_modEq B (n : ℤ)).of_dvd (by exact_mod_cast Nat.gcd_dvd_right m n)
    exact hA.trans (h.trans hB.symm)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hmod
  refine ⟨(k : ℤ), ?_, ?_⟩
  · have h1 : (k : ℤ) ≡ (a' : ℤ) [ZMOD (m : ℤ)] := Int.natCast_modEq_iff.mpr hk1
    exact h1.trans (by rw [hcastA]; exact Int.mod_modEq A (m : ℤ))
  · have h1 : (k : ℤ) ≡ (b' : ℤ) [ZMOD (n : ℤ)] := Int.natCast_modEq_iff.mpr hk2
    exact h1.trans (by rw [hcastB]; exact Int.mod_modEq B (n : ℤ))

/-- **Lemma 3.1**: if `n > 1` admits a congruence set of divisor form whose
distinct classes overlap only at coprime moduli, then `n / n.minFac` has
fewer than `n.minFac` distinct prime divisors. -/
private theorem card_primeFactors_div_minFac_lt_of_cd {n : ℕ} (hn : 1 < n)
    (a : ℕ → ℤ)
    (ha : ∀ d d' : ℕ, d ∣ n → d' ∣ n → 1 < d → 1 < d' → d ≠ d' →
      (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧ x ≡ a d' [ZMOD (d' : ℤ)]) →
        Nat.Coprime d d') :
    (n / n.minFac).primeFactors.card < n.minFac := by
  set p := n.minFac with hpdef
  by_contra hcon
  have hle : p ≤ (n / p).primeFactors.card := Nat.not_lt.mp hcon
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hp2 : 2 ≤ p := hp.two_le
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hNe : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hle
  set e := T.orderEmbOfFin hTcard with hedef
  have hqmem : ∀ i, e i ∈ (n / p).primeFactors :=
    fun i => hTsub (Finset.orderEmbOfFin_mem T hTcard i)
  have hqprime : ∀ i, (e i).Prime := fun i => (Nat.mem_primeFactors.mp (hqmem i)).1
  have hqdvd : ∀ i, e i ∣ n / p := fun i => (Nat.mem_primeFactors.mp (hqmem i)).2.1
  have hdiv : ∀ i, p * e i ∣ n := fun i => by
    have h1 : p * e i ∣ p * (n / p) := Nat.mul_dvd_mul_left p (hqdvd i)
    rwa [Nat.mul_div_cancel' hpdvd] at h1
  have h1lt : ∀ i, 1 < p * e i := fun i => by
    have hq2 := (hqprime i).two_le
    calc 1 < 2 * 2 := by norm_num
      _ ≤ p * e i := Nat.mul_le_mul hp2 hq2
  set f : Fin p → ZMod p := fun i => (a (p * e i) : ZMod p) with hfdef
  have hcop_false : ∀ d d' : ℕ, p ∣ d → p ∣ d' → ¬ Nat.Coprime d d' := by
    intro d d' hd hd' hcop
    have h1 : p ∣ Nat.gcd d d' := Nat.dvd_gcd hd hd'
    rw [hcop] at h1
    exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
  by_cases hinj : Function.Injective f
  · have himg : Finset.univ.image f = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injective _ hinj]
      simp [ZMod.card]
    have hmem : (a p : ZMod p) ∈ Finset.univ.image f := by
      rw [himg]; exact Finset.mem_univ _
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have heq : ((a (p * e i) : ℤ) : ZMod p) = ((a p : ℤ) : ZMod p) := hi
    have hmodeq : a (p * e i) ≡ a p [ZMOD (p : ℤ)] :=
      ZMod.intCast_eq_intCast_iff _ _ _ |>.mp heq
    have hne : p ≠ p * e i := by
      intro hEq
      have h2 : e i = 1 :=
        Nat.eq_of_mul_eq_mul_left hp.pos (by rw [mul_one]; exact hEq.symm)
      have hq2 := (hqprime i).two_le
      omega
    have hcop := ha p (p * e i) hpdvd (hdiv i) (by omega) (h1lt i) hne
      ⟨a (p * e i), hmodeq, Int.ModEq.refl _⟩
    exact hcop_false p (p * e i) (dvd_refl p) (Dvd.dvd.mul_right (dvd_refl p) _) hcop
  · rw [Function.not_injective_iff] at hinj
    obtain ⟨i, j, hij, hine⟩ := hinj
    have hmodeq : a (p * e i) ≡ a (p * e j) [ZMOD (p : ℤ)] :=
      ZMod.intCast_eq_intCast_iff _ _ _ |>.mp hij
    have hgcd : Nat.gcd (p * e i) (p * e j) = p := by
      rw [Nat.gcd_mul_left, (Nat.coprime_primes (hqprime i) (hqprime j)).mpr
        (fun h => hine (e.injective h)), mul_one]
    have hmodgcd : a (p * e i) ≡ a (p * e j)
        [ZMOD (Nat.gcd (p * e i) (p * e j) : ℤ)] := by
      rw [hgcd]; exact hmodeq
    obtain ⟨x, hx1, hx2⟩ := exists_int_modEq_of_modEq_gcd
      (Nat.mul_pos hp.pos (hqprime i).pos) (Nat.mul_pos hp.pos (hqprime j).pos) hmodgcd
    have hcop := ha (p * e i) (p * e j) (hdiv i) (hdiv j) (h1lt i) (h1lt j) (by
      intro hEq
      exact hine (e.injective (Nat.mul_left_cancel (by omega : 0 < p) hEq)))
      ⟨x, hx1, hx2⟩
    exact hcop_false _ _ (Dvd.dvd.mul_right (dvd_refl p) _)
      (Dvd.dvd.mul_right (dvd_refl p) _) hcop

/-- At most `N / d` naturals below `N` lie in a given residue class modulo
`d`, when `d ∣ N`: `x ↦ x / d` maps them injectively into `[0, N / d)`. -/
private theorem card_filter_range_modEq_le {d N : ℕ} (hd : 0 < d) (hdN : d ∣ N)
    (v : ℤ) :
    ((Finset.range N).filter fun x : ℕ => (x : ℤ) ≡ v [ZMOD (d : ℤ)]).card ≤ N / d := by
  calc _ ≤ (Finset.range (N / d)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x / d) (fun x hx => ?_)
          fun x hx y hy hxy => ?_
        · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx
          simp only [Finset.mem_coe, Finset.mem_range]
          rw [Nat.div_lt_iff_lt_mul hd, Nat.div_mul_cancel hdN]
          exact hx.1
        · rw [Finset.mem_coe, Finset.mem_filter] at hx hy
          have hmod : x % d = y % d := Int.natCast_modEq_iff.mp (hx.2.trans hy.2.symm)
          have hdiv : x / d = y / d := hxy
          rw [← Nat.div_add_mod x d, ← Nat.div_add_mod y d, hmod, hdiv]
    _ = N / d := Finset.card_range _

/-- Twice a partial geometric sum is less than the next power, for ratio
at least `3`. -/
private theorem two_mul_sum_pow_lt {q α : ℕ} (hq : 3 ≤ q) (hα : 1 ≤ α) :
    2 * ∑ j ∈ Finset.range α, q ^ j < q ^ α := by
  induction α with
  | zero => omega
  | succ α ih =>
    rcases eq_or_ne α 0 with rfl | hα0
    · simp; omega
    · have ih' := ih (by omega)
      rw [Finset.sum_range_succ]
      have h3 : 3 * q ^ α ≤ q ^ (α + 1) := by
        rw [pow_succ, mul_comm]
        gcongr
      calc 2 * (∑ j ∈ Finset.range α, q ^ j + q ^ α)
          = 2 * ∑ j ∈ Finset.range α, q ^ j + 2 * q ^ α := by ring
        _ < q ^ α + 2 * q ^ α := by omega
        _ = 3 * q ^ α := by ring
        _ ≤ q ^ (α + 1) := h3

/-- The divisors of twice a prime power are the prime powers and twice
the prime powers. -/
private theorem dvd_two_mul_prime_pow {q α d : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hd : d ∣ 2 * q ^ α) : ∃ i ≤ α, d = q ^ i ∨ d = 2 * q ^ i := by
  have hqpos : 0 < q := hq.pos
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by positivity)
  have hd0 : d ≠ 0 := hdpos.ne'
  have hn0 : (2 * q ^ α) ≠ 0 := by positivity
  have h2prime : Nat.Prime 2 := Nat.prime_two
  have hfac2 : d.factorization 2 ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have h4 : (2 : ℕ) ^ 2 ∣ d := (h2prime.pow_dvd_iff_le_factorization hd0).mpr (by omega)
    have h4' : (2 : ℕ) ^ 2 ∣ 2 * q ^ α := dvd_trans h4 hd
    have h2q : (2 : ℕ) ∣ q ^ α := by
      have h := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp
        (by simpa [pow_two] using h4' : 2 * 2 ∣ 2 * q ^ α)
      exact h
    have h2q' : (2 : ℕ) ∣ q := h2prime.dvd_of_dvd_pow h2q
    exact hq2 ((Nat.prime_dvd_prime_iff_eq h2prime hq).mp h2q' |>.symm)
  have hfacq : d.factorization q ≤ α := by
    by_contra hcon
    push Not at hcon
    have h1 : q ^ (α + 1) ∣ d := (hq.pow_dvd_iff_le_factorization hd0).mpr (by omega)
    have h2 : q ^ (α + 1) ∣ 2 * q ^ α := dvd_trans h1 hd
    rw [pow_succ, mul_comm (2 : ℕ) (q ^ α)] at h2
    have hq2' : q ∣ 2 := (Nat.mul_dvd_mul_iff_left (pow_pos hq.pos α)).mp h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq h2prime).mp hq2')
  have hfac0 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ q → d.factorization r = 0 := by
    intro r hr hr2 hrq
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hrdvd
    have hrdvd2 : r ∣ 2 * q ^ α := dvd_trans hrdvd hd
    rcases (hr.dvd_mul.mp hrdvd2) with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr h2prime).mp h)
    · have hrq' : r ∣ q := hr.dvd_of_dvd_pow h
      exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrq')
  set i := d.factorization q with hi_def
  set e := d.factorization 2 with he_def
  have hprod : (∏ r ∈ d.primeFactors, r ^ d.factorization r) = d :=
    Nat.prod_factorization_pow_eq_self hd0
  have hsub : d.primeFactors ⊆ {2, q} := by
    intro r hr
    have hpr := (Nat.mem_primeFactors.mp hr).1
    have hrdvd := (Nat.mem_primeFactors.mp hr).2.1
    by_contra hcon
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
    have h0 := hfac0 r hpr hcon.1 hcon.2
    have hpos := hpr.factorization_pos_of_dvd hd0 hrdvd
    omega
  have hprod3 : (∏ r ∈ d.primeFactors, r ^ d.factorization r) =
      (∏ r ∈ ({2, q} : Finset ℕ), r ^ d.factorization r) := by
    apply Finset.prod_subset hsub
    intro r hr hrnot
    have hpr : r.Prime := by
      rcases Finset.mem_insert.mp hr with rfl | hr'
      · exact h2prime
      · rw [Finset.mem_singleton.mp hr']; exact hq
    rw [Nat.factorization_eq_zero_of_not_dvd
      (fun h => hrnot (Nat.mem_primeFactors.mpr ⟨hpr, h, hd0⟩))]
    simp
  have hprod4 : (∏ r ∈ ({2, q} : Finset ℕ), r ^ d.factorization r) =
      2 ^ d.factorization 2 * q ^ d.factorization q := by
    rw [Finset.prod_insert
      (by simp only [Finset.mem_singleton]; exact fun h => hq2 h.symm),
      Finset.prod_singleton]
  have hd_eq : d = 2 ^ e * q ^ i := hprod.symm.trans (hprod3.trans hprod4)
  refine ⟨i, hfacq, ?_⟩
  rw [hd_eq]
  rcases (by omega : e = 0 ∨ e = 1) with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

/-- No congruence set of divisor form covers the integers when the integer
is twice a power of an odd prime: projecting to residues modulo `q ^ α`,
each residue class modulo a divisor contributes at most two classes modulo
a power of `q`, whose total size is less than `q ^ α`. -/
private theorem not_covering_of_two_mul_prime_pow {q α : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hα : 1 ≤ α) (b : ℕ → ℤ)
    (hcov : Int.IsCoveringSystem
      (((2 * q ^ α).divisors.filter (fun d => 1 < d)).image (fun d => (b d, d)))) :
    False := by
  have hqpos : 0 < q := hq.pos
  have hq3 : 3 ≤ q := by
    have h2 := hq.two_le
    omega
  set M := q ^ α with hMdef
  have hMpos : 0 < M := pow_pos hqpos α
  have h2M : ¬ (2 : ℕ) ∣ M := by
    intro h
    have h2q : (2 : ℕ) ∣ q := Nat.prime_two.dvd_of_dvd_pow h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q |>.symm)
  have hqpow_dvd : ∀ i ≤ α, q ^ i ∣ M := fun i hi => pow_dvd_pow q hi
  have hsub : Finset.range M ⊆
      (Finset.range α).biUnion (fun j =>
        ((Finset.range M).filter (fun y : ℕ =>
          (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])) ∪
        ((Finset.range M).filter (fun y : ℕ =>
          (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)]))) := by
    intro y hy
    rw [Finset.mem_range] at hy
    by_cases hpar : (y : ℤ) ≡ b 2 [ZMOD (2 : ℤ)]
    · set z : ℤ := (y : ℤ) + M with hzdef
      have hzM : z ≡ (y : ℤ) [ZMOD (M : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        simp [hzdef]
      have hz2 : ¬ z ≡ b 2 [ZMOD (2 : ℤ)] := by
        intro hz
        have hMdvd : ((2 : ℕ) : ℤ) ∣ (M : ℤ) := by
          have h1 : z ≡ (y : ℤ) [ZMOD (2 : ℤ)] := hz.trans hpar.symm
          rw [Int.modEq_iff_dvd] at h1
          have h3 : ((2 : ℕ) : ℤ) ∣ -(↑y - z) := dvd_neg.mpr h1
          rw [neg_sub] at h3
          have hzsub : z - (y : ℤ) = (M : ℤ) := by simp [hzdef]
          rwa [hzsub] at h3
        exact h2M (by exact_mod_cast hMdvd)
      have hz := hcov z
      obtain ⟨c, hc, hcz⟩ := hz
      rw [Finset.mem_image] at hc
      obtain ⟨d, hdD, rfl⟩ := hc
      rw [Finset.mem_filter, Nat.mem_divisors] at hdD
      obtain ⟨⟨hddiv, _⟩, hd1⟩ := hdD
      rw [hMdef] at hddiv
      have hd2 : d ≠ 2 := by
        intro hd2eq
        apply hz2
        rw [hd2eq] at hcz
        exact hcz
      obtain ⟨i, hiα, hdi⟩ := dvd_two_mul_prime_pow hq hq2 hddiv
      have hi1 : 1 ≤ i := by
        by_contra hcon
        have hi0 : i = 0 := by omega
        subst hi0
        rcases hdi with h | h <;> simp_all
      have hqdvd : q ^ i ∣ d := by
        rcases hdi with h | h
        · rw [← h]
        · rw [h]; exact dvd_mul_left (q ^ i) 2
      have hzy : z ≡ (y : ℤ) [ZMOD (q ^ i : ℤ)] :=
        Int.ModEq.of_dvd (by exact_mod_cast hqpow_dvd i hiα) hzM
      have hzb : z ≡ b d [ZMOD (q ^ i : ℤ)] :=
        Int.ModEq.of_dvd (by exact_mod_cast hqdvd) hcz
      have hyb : (y : ℤ) ≡ b d [ZMOD (q ^ i : ℤ)] := hzy.symm.trans hzb
      refine Finset.mem_biUnion.mpr ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
      have hii : i - 1 + 1 = i := by omega
      rw [Finset.mem_union]
      rcases hdi with h | h
      · left
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr hy, ?_⟩
        rw [hii]
        exact h ▸ hyb
      · right
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr hy, ?_⟩
        rw [hii]
        exact h ▸ hyb
    · set z : ℤ := (y : ℤ) with hzdef
      have hzM : z ≡ (y : ℤ) [ZMOD (M : ℤ)] := Int.ModEq.refl _
      have hz2 : ¬ z ≡ b 2 [ZMOD (2 : ℤ)] := hpar
      have hz := hcov z
      obtain ⟨c, hc, hcz⟩ := hz
      rw [Finset.mem_image] at hc
      obtain ⟨d, hdD, rfl⟩ := hc
      rw [Finset.mem_filter, Nat.mem_divisors] at hdD
      obtain ⟨⟨hddiv, _⟩, hd1⟩ := hdD
      rw [hMdef] at hddiv
      have hd2 : d ≠ 2 := by
        intro hd2eq
        apply hz2
        rw [hd2eq] at hcz
        exact hcz
      obtain ⟨i, hiα, hdi⟩ := dvd_two_mul_prime_pow hq hq2 hddiv
      have hi1 : 1 ≤ i := by
        by_contra hcon
        have hi0 : i = 0 := by omega
        subst hi0
        rcases hdi with h | h <;> simp_all
      have hqdvd : q ^ i ∣ d := by
        rcases hdi with h | h
        · rw [← h]
        · rw [h]; exact dvd_mul_left (q ^ i) 2
      have hzy : z ≡ (y : ℤ) [ZMOD (q ^ i : ℤ)] :=
        Int.ModEq.of_dvd (by exact_mod_cast hqpow_dvd i hiα) hzM
      have hzb : z ≡ b d [ZMOD (q ^ i : ℤ)] :=
        Int.ModEq.of_dvd (by exact_mod_cast hqdvd) hcz
      have hyb : (y : ℤ) ≡ b d [ZMOD (q ^ i : ℤ)] := hzy.symm.trans hzb
      refine Finset.mem_biUnion.mpr ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
      have hii : i - 1 + 1 = i := by omega
      rw [Finset.mem_union]
      rcases hdi with h | h
      · left
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr hy, ?_⟩
        rw [hii]
        exact h ▸ hyb
      · right
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_range.mpr hy, ?_⟩
        rw [hii]
        exact h ▸ hyb
  have hcard : M ≤ ∑ j ∈ Finset.range α,
      (((Finset.range M).filter (fun y : ℕ =>
        (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card +
      ((Finset.range M).filter (fun y : ℕ =>
        (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card) := by
    calc M = (Finset.range M).card := (Finset.card_range M).symm
      _ ≤ ((Finset.range α).biUnion (fun j =>
          ((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])) ∪
          ((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ j ∈ Finset.range α, (((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])) ∪
          ((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)]))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range α,
          (((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card +
          ((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card) :=
        Finset.sum_le_sum fun j _ => Finset.card_union_le _ _
  have hbound : ∑ j ∈ Finset.range α,
      (((Finset.range M).filter (fun y : ℕ =>
        (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card +
      ((Finset.range M).filter (fun y : ℕ =>
        (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card) < M := by
    have hstep : ∀ j ∈ Finset.range α,
        ((Finset.range M).filter (fun y : ℕ =>
          (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card +
        ((Finset.range M).filter (fun y : ℕ =>
          (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card ≤
        2 * q ^ (α - (j + 1)) := by
      intro j hj
      have hjα : j + 1 ≤ α := by
        rw [Finset.mem_range] at hj; omega
      have h1 := card_filter_range_modEq_le (show 0 < q ^ (j + 1) from pow_pos hqpos _)
        (hqpow_dvd (j + 1) hjα) (b (q ^ (j + 1)))
      have h2 := card_filter_range_modEq_le (show 0 < q ^ (j + 1) from pow_pos hqpos _)
        (hqpow_dvd (j + 1) hjα) (b (2 * q ^ (j + 1)))
      rw [Nat.cast_pow] at h1 h2
      have hdiv : M / q ^ (j + 1) = q ^ (α - (j + 1)) := by
        rw [hMdef, Nat.pow_div hjα hqpos]
      omega
    calc ∑ j ∈ Finset.range α,
          (((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card +
          ((Finset.range M).filter (fun y : ℕ =>
            (y : ℤ) ≡ b (2 * q ^ (j + 1)) [ZMOD (q ^ (j + 1) : ℤ)])).card)
        ≤ ∑ j ∈ Finset.range α, 2 * q ^ (α - (j + 1)) := Finset.sum_le_sum hstep
      _ = 2 * ∑ j ∈ Finset.range α, q ^ (α - (j + 1)) := by rw [Finset.mul_sum]
      _ = 2 * ∑ j ∈ Finset.range α, q ^ j := by
        congr 1
        have hrew : ∀ j ∈ Finset.range α, q ^ (α - (j + 1)) = q ^ (α - 1 - j) := by
          intro j hj; rw [Finset.mem_range] at hj; congr 1; omega
        rw [Finset.sum_congr rfl hrew]
        exact Finset.sum_range_reflect (fun j => q ^ j) α
      _ < q ^ α := two_mul_sum_pow_lt hq3 hα
      _ = M := hMdef.symm
  omega

/-- If the smallest prime factor of `n` does not divide `n` twice, then the
prime factors of `n / n.minFac` are the prime factors of `n` other than the
smallest one. -/
private theorem primeFactors_div_of_not_sq_dvd {n : ℕ} (hn : 1 < n)
    (h2 : ¬ n.minFac ^ 2 ∣ n) :
    (n / n.minFac).primeFactors = n.primeFactors.erase n.minFac := by
  classical
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hn0 : n ≠ 0 := by omega
  have hnp0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos).ne'
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_erase]
  constructor
  · rintro ⟨hqprime, hqdiv, -⟩
    have hqn : q ∣ n := by
      have h1 : q ∣ p * (n / p) := dvd_mul_of_dvd_right hqdiv p
      rwa [Nat.mul_div_cancel' hpdvd] at h1
    refine ⟨?_, hqprime, hqn, hn0⟩
    intro hqp
    subst hqp
    apply h2
    have h2' : p * p ∣ p * (n / p) := Nat.mul_dvd_mul_left p hqdiv
    rwa [Nat.mul_div_cancel' hpdvd, ← pow_two] at h2'
  · rintro ⟨hqne, hqprime, hqdiv, -⟩
    refine ⟨hqprime, ?_, hnp0⟩
    have h1 : q ∣ p * (n / p) := by rwa [Nat.mul_div_cancel' hpdvd]
    rcases (hqprime.dvd_mul.mp h1) with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp h) hqne
    · exact h

/-- If the smallest prime factor of `n` divides `n` twice, then dividing
by it does not change the set of prime factors. -/
private theorem primeFactors_div_of_sq_dvd {n : ℕ} (hn : 1 < n)
    (h2 : n.minFac ^ 2 ∣ n) :
    (n / n.minFac).primeFactors = n.primeFactors := by
  classical
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ n := Nat.minFac_dvd n
  have hn0 : n ≠ 0 := by omega
  have hnp0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) hp.pos).ne'
  ext q
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hqprime, hqdiv, -⟩
    refine ⟨hqprime, ?_, hn0⟩
    have h1 : q ∣ p * (n / p) := dvd_mul_of_dvd_right hqdiv p
    rwa [Nat.mul_div_cancel' hpdvd] at h1
  · rintro ⟨hqprime, hqdiv, -⟩
    refine ⟨hqprime, ?_, hnp0⟩
    by_cases hqp : q = p
    · subst hqp
      have ht : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' h2
      have hnp : n / p = p * (n / p ^ 2) := by
        have h1 : n / p = (p ^ 2 * (n / p ^ 2)) / p := by rw [ht]
        rw [h1, pow_two, mul_assoc]
        exact Nat.mul_div_cancel_left _ hp.pos
      rw [hnp]
      exact dvd_mul_right p _
    · have h1 : q ∣ p * (n / p) := by rwa [Nat.mul_div_cancel' hpdvd]
      rcases (hqprime.dvd_mul.mp h1) with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp h) hqp
      · exact h

/-- **Lemma 2.2** in divisor form: if the residue classes of divisor form
cover the integers, then the sum of the reciprocals of the divisors
greater than `1` is at least `1`. -/
private theorem one_le_sum_inv_divisors_of_covering {n : ℕ} (b : ℕ → ℤ)
    (hcov : Int.IsCoveringSystem
      ((n.divisors.filter (fun d => 1 < d)).image (fun d => (b d, d)))) :
    (1 : ℚ) ≤ ∑ d ∈ n.divisors.filter (fun d => 1 < d), (1 : ℚ) / d := by
  classical
  have hpos : ∀ i : Fin (n.divisors.filter (fun d => 1 < d)).card,
      0 < (n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i := by
    intro i
    have hmem := Finset.orderEmbOfFin_mem _ rfl i
    rw [Finset.mem_filter, Nat.mem_divisors] at hmem
    omega
  have hcov' : Int.IsCoveringSystem
      (Int.indexedCoveringClasses
        (fun i => (n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i)
        (fun i => b ((n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i))) := by
    rw [Int.indexedCoveringClasses_isCoveringSystem_iff]
    intro z
    obtain ⟨c, hc, hcz⟩ := hcov z
    rw [Finset.mem_image] at hc
    obtain ⟨d, hdD, rfl⟩ := hc
    have hrange : d ∈
        Set.range ((n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hdD
    obtain ⟨i, hi⟩ := hrange
    exact ⟨i, hi ▸ hcz⟩
  have hle := MathlibExt.NumberTheory.ErdosGrahamCoveringWanted.one_le_sum_inv_moduli
    (fun i => (n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i)
    (fun i => b ((n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i)) hpos hcov'
  have hsum : (∑ i, (1 : ℚ) /
        (((n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i : ℕ) : ℚ)) =
      ∑ d ∈ n.divisors.filter (fun d => 1 < d), (1 : ℚ) / d := by
    refine Finset.sum_bij
      (fun i _ => (n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl i)
      (fun i _ => Finset.orderEmbOfFin_mem _ rfl i)
      (fun a _ b _ h =>
        ((n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl).injective h) ?_
      (fun i _ => rfl)
    intro d hd
    have hrange : d ∈
        Set.range ((n.divisors.filter (fun d => 1 < d)).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hd
    obtain ⟨i, hi⟩ := hrange
    exact ⟨i, Finset.mem_univ i, hi⟩
  rwa [hsum] at hle

/-- The sum over divisors greater than `1` is the sum over all divisors
minus the term `1 / 1`. -/
private theorem sum_inv_divisors_filter_eq {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => 1 < d), (1 : ℚ) / d =
      (∑ d ∈ n.divisors, (1 : ℚ) / d) - 1 := by
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn
  have herase : n.divisors.filter (fun d => 1 < d) = n.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hd, h1d⟩
      exact ⟨by omega, hd⟩
    · rintro ⟨hne, hd⟩
      refine ⟨hd, ?_⟩
      have hpos := Nat.pos_of_mem_divisors hd
      omega
  have h := Finset.add_sum_erase n.divisors (fun d => (1 : ℚ) / d) h1
  rw [herase]
  simp only [Nat.cast_one, div_one] at h
  linarith

/-- A product with a strict factor is strict, when all factors are
nonnegative and the other side is positive. -/
private theorem prod_lt_of_exists_strict {S : Finset ℕ} {f g : ℕ → ℚ}
    (hf : ∀ q ∈ S, 0 ≤ f q) (hg : ∀ q ∈ S, 0 < g q) (hle : ∀ q ∈ S, f q ≤ g q)
    (h : ∃ q0 ∈ S, f q0 < g q0) : ∏ q ∈ S, f q < ∏ q ∈ S, g q := by
  obtain ⟨q0, hq0, hlt⟩ := h
  rw [← Finset.mul_prod_erase S f hq0, ← Finset.mul_prod_erase S g hq0]
  have hle' : ∏ q ∈ S.erase q0, f q ≤ ∏ q ∈ S.erase q0, g q :=
    Finset.prod_le_prod₀ (fun q hq => hf q (Finset.mem_of_mem_erase hq))
      (fun q hq => hle q (Finset.mem_of_mem_erase hq))
  have hpos : 0 < ∏ q ∈ S.erase q0, g q :=
    Finset.prod_pos (fun q hq => hg q (Finset.mem_of_mem_erase hq))
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle' (hf q0 hq0))
    (mul_lt_mul_of_pos_right hlt hpos)

/-- The reciprocal sum over the divisors of a non-intersecting integer is
less than `2`, except in the case where the smallest prime factor is `2`
and does not divide the integer twice, which is handled separately. The
proof is the paper's Theorem 3.2, Cases 1a and 2: the divisor sum factors
into geometric sums, each less than `q / (q - 1)`, and Lemma 3.1 bounds
the number of distinct prime factors so that the product of the
`q / (q - 1)` telescopes to at most `2`. -/
private theorem sum_inv_divisors_lt_two {n : ℕ} (hn : 1 < n)
    (hcard : (n / n.minFac).primeFactors.card < n.minFac)
    (hcase : n.minFac ^ 2 ∣ n ∨ (n.minFac ≠ 2 ∧ ¬ n.minFac ^ 2 ∣ n)) :
    ∑ d ∈ n.divisors, (1 : ℚ) / d < 2 := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hp2 : 2 ≤ n.minFac := hp.two_le
  have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hpP : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hn0⟩
  have hgeom_pos : ∀ q ∈ n.primeFactors,
      0 < ∑ j ∈ Finset.range (n.factorization q + 1), (1 : ℚ) / (q : ℚ) ^ j := by
    intro q hq
    have hqpos : (0 : ℚ) < q := by
      exact_mod_cast (Nat.mem_primeFactors.mp hq).1.pos
    apply Finset.sum_pos
    · intro j _
      exact div_pos one_pos (pow_pos hqpos _)
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hgeom_lt : ∀ q ∈ n.primeFactors,
      (∑ j ∈ Finset.range (n.factorization q + 1), (1 : ℚ) / (q : ℚ) ^ j) <
        (q : ℚ) / ((q : ℚ) - 1) := fun q hq =>
    geom_sum_inv_lt (Nat.mem_primeFactors.mp hq).1.two_le _
  have hsum_eq := sum_inv_divisors_eq n hn0
  rcases hcase with hsq | ⟨hpne, hnsq⟩
  · -- The smallest prime factor occurs at least twice.
    have hPeq : (n / n.minFac).primeFactors = n.primeFactors :=
      primeFactors_div_of_sq_dvd hn hsq
    have hcardP : n.primeFactors.card < n.minFac := by
      rw [← hPeq]; exact hcard
    have hcardE : (n.primeFactors.erase n.minFac).card + 1 = n.primeFactors.card := by
      have h := Finset.card_erase_of_mem hpP
      have hpos : 1 ≤ n.primeFactors.card := Finset.card_pos.mpr ⟨n.minFac, hpP⟩
      omega
    have hboundE : ∏ q ∈ n.primeFactors.erase n.minFac,
        (q : ℚ) / ((q : ℚ) - 1) ≤
          ((n.minFac : ℚ) + ((n.primeFactors.erase n.minFac).card : ℚ)) /
            (n.minFac : ℚ) := by
      have h1 := prod_f_le (T := n.primeFactors.erase n.minFac)
        (L := n.minFac + 1) (by omega) (fun q hq => by
          have hqmem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
          have hqne : q ≠ n.minFac := (Finset.mem_erase.mp hq).1
          have hqge : n.minFac ≤ q := Nat.minFac_le_of_dvd
            (Nat.mem_primeFactors.mp hqmem).1.two_le (Nat.mem_primeFactors.mp hqmem).2.1
          omega)
      have h2 := prod_f_range (L := n.minFac + 1) (by omega)
        ((n.primeFactors.erase n.minFac).card)
      rw [h2] at h1
      refine le_trans h1 ?_
      have heq : (((n.minFac + 1 + (n.primeFactors.erase n.minFac).card : ℕ) : ℚ) - 1) /
            (((n.minFac + 1 : ℕ) : ℚ) - 1) =
          ((n.minFac : ℚ) + ((n.primeFactors.erase n.minFac).card : ℚ)) /
            (n.minFac : ℚ) := by
        congr 1 <;> push_cast <;> ring
      exact le_of_eq heq
    have hboundP : ∏ q ∈ n.primeFactors, (q : ℚ) / ((q : ℚ) - 1) ≤ 2 := by
      have hsplit := (Finset.mul_prod_erase n.primeFactors
        (fun q => (q : ℚ) / ((q : ℚ) - 1)) hpP).symm
      rw [hsplit]
      have hle := mul_le_mul_of_nonneg_left hboundE (f_nonneg hp2)
      refine le_trans hle ?_
      have heq : (n.minFac : ℚ) / ((n.minFac : ℚ) - 1) *
            (((n.minFac : ℚ) + ((n.primeFactors.erase n.minFac).card : ℚ)) /
              (n.minFac : ℚ)) =
          ((n.minFac : ℚ) + ((n.primeFactors.erase n.minFac).card : ℚ)) /
            ((n.minFac : ℚ) - 1) := by
        have hp0 : (n.minFac : ℚ) ≠ 0 := by
          exact_mod_cast (show n.minFac ≠ 0 by omega)
        have hpm1 : ((n.minFac : ℚ) - 1) ≠ 0 := by
          have h2 : (2 : ℚ) ≤ n.minFac := by exact_mod_cast hp2
          linarith
        field_simp
      rw [heq]
      rw [div_le_iff₀ (by
        have h2 : (2 : ℚ) ≤ n.minFac := by exact_mod_cast hp2
        linarith)]
      have hs : ((n.primeFactors.erase n.minFac).card : ℚ) ≤ (n.minFac : ℚ) - 2 := by
        have hsc : (n.primeFactors.erase n.minFac).card ≤ n.minFac - 2 := by omega
        exact_mod_cast hsc
      linarith
    have hlt : (∏ q ∈ n.primeFactors,
          ∑ j ∈ Finset.range (n.factorization q + 1), (1 : ℚ) / (q : ℚ) ^ j) <
        ∏ q ∈ n.primeFactors, (q : ℚ) / ((q : ℚ) - 1) :=
      prod_lt_of_exists_strict (fun q hq => (hgeom_pos q hq).le)
        (fun q hq => f_pos (Nat.mem_primeFactors.mp hq).1.two_le)
        (fun q hq => (hgeom_lt q hq).le) ⟨n.minFac, hpP, hgeom_lt n.minFac hpP⟩
    rw [hsum_eq]
    exact lt_of_lt_of_le hlt hboundP
  · -- The smallest prime factor occurs once, and is odd.
    have hPeq : (n / n.minFac).primeFactors = n.primeFactors.erase n.minFac :=
      primeFactors_div_of_not_sq_dvd hn hnsq
    have hcardE : (n.primeFactors.erase n.minFac).card < n.minFac := by
      rw [← hPeq]; exact hcard
    have hpodd : Odd n.minFac := hp.odd_of_ne_two hpne
    have hfacp : n.factorization n.minFac = 1 := by
      have hge : 1 ≤ n.factorization n.minFac :=
        (hp.pow_dvd_iff_le_factorization hn0).mp (by rwa [pow_one])
      have hlt : n.factorization n.minFac < 2 := by
        by_contra hcon
        push Not at hcon
        exact hnsq ((hp.pow_dvd_iff_le_factorization hn0).mpr hcon)
      omega
    have hgeomp : (∑ j ∈ Finset.range (n.factorization n.minFac + 1),
          (1 : ℚ) / (n.minFac : ℚ) ^ j) = 1 + 1 / (n.minFac : ℚ) := by
      rw [hfacp]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
        div_one, zero_add]
    have hqge : ∀ q ∈ n.primeFactors.erase n.minFac, n.minFac + 2 ≤ q := by
      intro q hq
      have hqmem : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
      have hqne : q ≠ n.minFac := (Finset.mem_erase.mp hq).1
      have hqp := (Nat.mem_primeFactors.mp hqmem).1
      have hqdiv := (Nat.mem_primeFactors.mp hqmem).2.1
      have hqge1 : n.minFac ≤ q := Nat.minFac_le_of_dvd hqp.two_le hqdiv
      have hqodd : Odd q := by
        rcases Nat.even_or_odd q with h | h
        · obtain ⟨r, hr⟩ := h
          have h2n : (2 : ℕ) ∣ n := dvd_trans ⟨r, by omega⟩ hqdiv
          have hle2 : n.minFac ≤ 2 := Nat.minFac_le_of_dvd (by norm_num) h2n
          omega
        · exact h
      have hqne1 : q ≠ n.minFac + 1 := by
        intro h
        rw [h] at hqodd
        exact (Nat.not_even_iff_odd.mpr hqodd) (hpodd.add_one)
      omega
    have hboundE : ∏ q ∈ n.primeFactors.erase n.minFac,
        (q : ℚ) / ((q : ℚ) - 1) ≤
          (((n.minFac : ℚ) + 1 +
            ((n.primeFactors.erase n.minFac).card : ℚ))) / ((n.minFac : ℚ) + 1) := by
      have h1 := prod_f_le (T := n.primeFactors.erase n.minFac)
        (L := n.minFac + 2) (by omega) hqge
      have h2 := prod_f_range (L := n.minFac + 2) (by omega)
        ((n.primeFactors.erase n.minFac).card)
      rw [h2] at h1
      refine le_trans h1 ?_
      have heq : (((n.minFac + 2 + (n.primeFactors.erase n.minFac).card : ℕ) : ℚ) - 1) /
            (((n.minFac + 2 : ℕ) : ℚ) - 1) =
          ((n.minFac : ℚ) + 1 + ((n.primeFactors.erase n.minFac).card : ℚ)) /
            ((n.minFac : ℚ) + 1) := by
        congr 1 <;> push_cast <;> ring
      exact le_of_eq heq
    have hboundG : (1 + 1 / (n.minFac : ℚ)) *
        ∏ q ∈ n.primeFactors.erase n.minFac, (q : ℚ) / ((q : ℚ) - 1) ≤ 2 := by
      have hnonneg : (0 : ℚ) ≤ 1 + 1 / (n.minFac : ℚ) := by
        have hp0 : (0 : ℚ) < n.minFac := by exact_mod_cast hp.pos
        exact add_nonneg zero_le_one (div_nonneg zero_le_one hp0.le)
      have hle : (1 + 1 / (n.minFac : ℚ)) *
          ∏ q ∈ n.primeFactors.erase n.minFac, (q : ℚ) / ((q : ℚ) - 1) ≤
          (1 + 1 / (n.minFac : ℚ)) *
            (((n.minFac : ℚ) + 1 +
              ((n.primeFactors.erase n.minFac).card : ℚ)) / ((n.minFac : ℚ) + 1)) :=
        mul_le_mul_of_nonneg_left hboundE hnonneg
      refine le_trans hle ?_
      have heq : (1 + 1 / (n.minFac : ℚ)) *
            (((n.minFac : ℚ) + 1 + ((n.primeFactors.erase n.minFac).card : ℚ)) /
              ((n.minFac : ℚ) + 1)) =
          ((n.minFac : ℚ) + 1 + ((n.primeFactors.erase n.minFac).card : ℚ)) /
            (n.minFac : ℚ) := by
        have hp0 : (n.minFac : ℚ) ≠ 0 := by
          exact_mod_cast (show n.minFac ≠ 0 by omega)
        have hp1 : ((n.minFac : ℚ) + 1) ≠ 0 := by
          have h2 : (0 : ℚ) < n.minFac := by exact_mod_cast hp.pos
          linarith
        field_simp
      rw [heq]
      rw [div_le_iff₀ (by exact_mod_cast hp.pos)]
      have hs : ((n.primeFactors.erase n.minFac).card : ℚ) ≤ (n.minFac : ℚ) - 1 := by
        have hsc : ((n.primeFactors.erase n.minFac).card : ℚ) ≤
            ((n.minFac - 1 : ℕ) : ℚ) := by
          exact_mod_cast (show (n.primeFactors.erase n.minFac).card ≤ n.minFac - 1 by omega)
        rwa [Nat.cast_sub (show 1 ≤ n.minFac by omega), Nat.cast_one] at hsc
      have h3 : (2 : ℚ) ≤ n.minFac := by exact_mod_cast hp2
      linarith
    have hsplit := (Finset.mul_prod_erase n.primeFactors
      (fun q => ∑ j ∈ Finset.range (n.factorization q + 1), (1 : ℚ) / (q : ℚ) ^ j)
      hpP).symm
    rw [hsum_eq, hsplit]
    by_cases hempty : (n.primeFactors.erase n.minFac) = ∅
    · rw [hempty, Finset.prod_empty, mul_one, hgeomp]
      have hlt1 : (1 : ℚ) / (n.minFac : ℚ) < 1 := by
        rw [div_lt_one (by exact_mod_cast hp.pos)]
        exact_mod_cast (show 1 < n.minFac by omega)
      linarith
    · have hne : (n.primeFactors.erase n.minFac).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨q0, hq0⟩ := hne
      have hlt : (∏ q ∈ n.primeFactors.erase n.minFac,
            ∑ j ∈ Finset.range (n.factorization q + 1), (1 : ℚ) / (q : ℚ) ^ j) <
          ∏ q ∈ n.primeFactors.erase n.minFac, (q : ℚ) / ((q : ℚ) - 1) :=
        prod_lt_of_exists_strict (fun q hq => (hgeom_pos q (Finset.mem_of_mem_erase hq)).le)
          (fun q hq => f_pos (Nat.mem_primeFactors.mp
            (Finset.mem_of_mem_erase hq)).1.two_le)
          (fun q hq => (hgeom_lt q (Finset.mem_of_mem_erase hq)).le)
          ⟨q0, hq0, hgeom_lt q0 (Finset.mem_of_mem_erase hq0)⟩
      calc (∑ j ∈ Finset.range (n.factorization n.minFac + 1),
              (1 : ℚ) / (n.minFac : ℚ) ^ j) *
            ∏ q ∈ n.primeFactors.erase n.minFac,
              ∑ j ∈ Finset.range (n.factorization q + 1), (1 : ℚ) / (q : ℚ) ^ j
          < (∑ j ∈ Finset.range (n.factorization n.minFac + 1),
              (1 : ℚ) / (n.minFac : ℚ) ^ j) *
            ∏ q ∈ n.primeFactors.erase n.minFac, (q : ℚ) / ((q : ℚ) - 1) :=
          mul_lt_mul_of_pos_left hlt (hgeom_pos n.minFac hpP)
        _ = (1 + 1 / (n.minFac : ℚ)) *
            ∏ q ∈ n.primeFactors.erase n.minFac, (q : ℚ) / ((q : ℚ) - 1) := by
          rw [hgeomp]
        _ ≤ 2 := hboundG

/-- The remaining case of Theorem 3.2: the smallest prime factor is `2`,
it occurs once, and Lemma 3.1 leaves at most one other prime factor. Then
`n` is `2` or twice a prime power, and neither admits a covering system
of divisor form. -/
private theorem not_covering_of_minFac_two {n : ℕ} (hn : 1 < n)
    (hp2 : n.minFac = 2) (hsq : ¬ n.minFac ^ 2 ∣ n)
    (hcard : (n / n.minFac).primeFactors.card < n.minFac) (b : ℕ → ℤ)
    (hcov : Int.IsCoveringSystem
      ((n.divisors.filter (fun d => 1 < d)).image (fun d => (b d, d)))) : False := by
  have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
  rw [hp2] at hpdvd hsq hcard
  have hn2 : 2 * (n / 2) = n := Nat.mul_div_cancel' hpdvd
  set m := n / 2 with hmdef
  have hmpos : 0 < m := by omega
  have hm0 : m ≠ 0 := by omega
  have h2m : ¬ (2 : ℕ) ∣ m := by
    intro h
    apply hsq
    have h4 : (2 : ℕ) * 2 ∣ 2 * m := Nat.mul_dvd_mul_left 2 h
    rw [hn2, ← pow_two] at h4
    exact h4
  have hcardm : m.primeFactors.card < 2 := hcard
  rcases eq_or_ne m.primeFactors.card 0 with h0 | h0
  · have hmem : m.primeFactors = ∅ := Finset.card_eq_zero.mp h0
    have hm1 : m = 1 := by
      by_contra hcon
      have hmem2 : m.minFac ∈ m.primeFactors := Nat.mem_primeFactors.mpr
        ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, hm0⟩
      rw [hmem] at hmem2
      exact Finset.notMem_empty _ hmem2
    have hn_eq : n = 2 := by omega
    rw [hn_eq] at hcov
    have hD : (2 : ℕ).divisors.filter (fun d => 1 < d) = {2} := by
      ext d
      simp only [Nat.Prime.divisors Nat.prime_two, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton]
      omega
    have hge := one_le_sum_inv_divisors_of_covering b hcov
    rw [hD, Finset.sum_singleton] at hge
    norm_num at hge
  · have h1 : m.primeFactors.card = 1 := by omega
    obtain ⟨q, hqS⟩ := Finset.card_eq_one.mp h1
    have hqmem : q ∈ m.primeFactors := by rw [hqS]; exact Finset.mem_singleton_self q
    have hqp : q.Prime := (Nat.mem_primeFactors.mp hqmem).1
    have hqdiv : q ∣ m := (Nat.mem_primeFactors.mp hqmem).2.1
    have hq2 : q ≠ 2 := by
      intro h
      rw [h] at hqdiv
      exact h2m hqdiv
    have hfac : 1 ≤ m.factorization q := (hqp.pow_dvd_iff_le_factorization hm0).mp
      (by rwa [pow_one])
    have hm_eq : m = q ^ (m.factorization q) := by
      have h : (∏ r ∈ m.primeFactors, r ^ m.factorization r) = m :=
        Nat.prod_factorization_pow_eq_self hm0
      rw [hqS, Finset.prod_singleton] at h
      exact h.symm
    have hn_eq : n = 2 * q ^ (m.factorization q) := by omega
    rw [hn_eq] at hcov
    exact not_covering_of_two_mul_prime_pow hqp hq2 hfac b hcov

/-- **Theorem 3.2**: there does not exist any `n` such
that a congruence set of the form
`{a_d (mod d) : d ∣ n, d > 1}`, where `a_d (mod d)` and
`a_{d'} (mod d')` overlap only if `gcd d d' = 1`, is a
covering set. In the paper's terminology: a
non-intersecting integer (one admitting a congruence
set of divisor form whose distinct classes overlap
only at coprime moduli) admits no covering congruence
set of divisor form at all; the two witnesses are
quantified independently below.

Source: Sarosh Adenwalla, "A Question of Erdős and
Graham on Covering Systems", Theorem 3.2. -/
theorem not_covering_of_nonintersecting (n : ℕ)
    (hnonint : ∃ a : ℕ → ℤ,
      ∀ d d' : ℕ, d ∣ n → d' ∣ n → 1 < d → 1 < d' →
        d ≠ d' →
          (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧
            x ≡ a d' [ZMOD (d' : ℤ)]) →
          Nat.Coprime d d') :
    ¬ ∃ b : ℕ → ℤ, Int.IsCoveringSystem
        ((n.divisors.filter (fun d => 1 < d)).image
          (fun d => (b d, d))) := by
  rintro ⟨b, hcov⟩
  by_cases hn1 : 1 < n
  · obtain ⟨a, ha⟩ := hnonint
    have hcard := card_primeFactors_div_minFac_lt_of_cd hn1 a ha
    by_cases hsq : n.minFac ^ 2 ∣ n
    · have hsum2 := sum_inv_divisors_lt_two hn1 hcard (Or.inl hsq)
      have hge := one_le_sum_inv_divisors_of_covering b hcov
      have hlt : ∑ d ∈ n.divisors.filter (fun d => 1 < d), (1 : ℚ) / d < 1 := by
        rw [sum_inv_divisors_filter_eq (by omega)]
        linarith
      linarith
    · by_cases hp2 : n.minFac = 2
      · exact not_covering_of_minFac_two hn1 hp2 hsq hcard b hcov
      · have hsum2 := sum_inv_divisors_lt_two hn1 hcard (Or.inr ⟨hp2, hsq⟩)
        have hge := one_le_sum_inv_divisors_of_covering b hcov
        have hlt : ∑ d ∈ n.divisors.filter (fun d => 1 < d), (1 : ℚ) / d < 1 := by
          rw [sum_inv_divisors_filter_eq (by omega)]
          linarith
        linarith
  · obtain ⟨c, hc, -⟩ := hcov 0
    rw [Finset.mem_image] at hc
    obtain ⟨d, hd, -⟩ := hc
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, hn0⟩, hd1⟩ := hd
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
    omega

end MathlibExt.NumberTheory.ErdosGrahamCoveringWanted
