/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.Combinatorics.Enumerative.GeneralizedMotzkinCentralTrinomial
public import MathlibExt.Data.Set.Density
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Count
import Mathlib.Algebra.Field.ZMod
import MathlibExt.Combinatorics.Enumerative.GeneralizedMotzkinModP

/-!
# Zero density of OEIS A005717 modulo a prime

Let $T_m$ be the central trinomial coefficients, the constant terms of $(x^{-1} + 1 + x)^m$, and
let $a_n$ be the constant term of $x (x^{-1} + 1 + x)^n$ (OEIS A005717). For a prime $p$, the main
result `a005717_zero_density` gives the natural density of the set of $n$ with
$a_n \equiv 0 \pmod p$: it is $1$ when $p$ divides some $T_r$ with $r < p$; otherwise, for $p > 2$,
it is $(N_1 + p N_2) / ((p - 1)(p + 1)) \ge 1/(p - 1)$, where $N_1$ and $N_2$ count the $m < p - 1$
with $T_m \equiv T_{p-1} T_{m+1}$ and with $T_m \equiv T_{m+1} \pmod p$ respectively.

This is Proposition 14 of the arXiv version (arXiv:2411.03681v2) of N. Kohen, *Density and
Symmetry in the Generalized Motzkin Numbers mod p*. The proof here is self-contained. It uses
$2 a_n = T_{n+1} - T_n$, the digit congruence $T_{u p^K + v} \equiv T_u T_v \pmod p$ for
$v < p^K$, the congruence $T_{p-1} \in \{0, 1, -1\} \pmod p$ read off from the Frobenius identity
$(x^{-1} + 1 + x)^p \equiv x^{-p} + 1 + x^p \pmod p$, and $T_{p-3} \equiv -T_{p-2} \pmod p$, which
follows from the recurrence for $T_m$. The zero set is squeezed between sets that are periodic
modulo $p^K$, whose densities are counted exactly.
-/

namespace MetaMathlibExt

open LaurentPolynomial Filter Topology

namespace a005717_zero_density

/-! ### The sequence in terms of central trinomial coefficients -/

/-- Multiplication by the trinomial combines the three neighboring coefficients. -/
private theorem coeff_pow_succ (a b : ℤ) (n : ℕ) (k : ℤ) :
    (trinomialLaurent a b ^ (n + 1)).coeff k =
      (trinomialLaurent a b ^ n).coeff (k + 1) * a +
        (trinomialLaurent a b ^ n).coeff k * b +
        (trinomialLaurent a b ^ n).coeff (k - 1) * a := by
  rw [pow_succ]
  nth_rw 2 [trinomialLaurent]
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, ← single_eq_C]
  simp only [mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    AddMonoidAlgebra.coeff_mul_single_apply, neg_neg, neg_zero, add_zero, sub_eq_add_neg]

/-- Twice the sequence is the difference of two consecutive central trinomial coefficients. -/
private theorem two_mul_a005717 (n : ℕ) :
    2 * a005717 n = centralTrinomial 1 1 (n + 1) - centralTrinomial 1 1 n := by
  have hinv : invert (trinomialLaurent 1 1) = trinomialLaurent 1 1 := by
    simp [trinomialLaurent, add_comm, add_left_comm]
  have hsym : (trinomialLaurent 1 1 ^ n).coeff 1 = (trinomialLaurent 1 1 ^ n).coeff (-1) := by
    simpa only [map_pow, hinv] using invert_apply (trinomialLaurent 1 1 ^ n) 1
  have ha : a005717 n = (trinomialLaurent 1 1 ^ n).coeff (-1) := by
    simp only [a005717, T, AddMonoidAlgebra.coeff_mul_single_apply]
    norm_num
  rw [ha, centralTrinomial, centralTrinomial, coeff_pow_succ, zero_add, zero_sub, hsym]
  ring

/-! ### Central trinomial coefficients modulo `p` -/

/-- The central trinomial coefficient $T_n$ reduced modulo `p`. -/
private noncomputable def res (p n : ℕ) : ZMod p := (centralTrinomial 1 1 n : ZMod p)

private theorem centralTrinomial_zero : centralTrinomial 1 1 0 = 1 := by
  simpa using congrArg (fun l : List ℤ => l[0]!) centralTrinomial_one_one_values

private theorem centralTrinomial_one : centralTrinomial 1 1 1 = 1 := by
  simpa using congrArg (fun l : List ℤ => l[1]!) centralTrinomial_one_one_values

private theorem centralTrinomial_two : centralTrinomial 1 1 2 = 3 := by
  simpa using congrArg (fun l : List ℤ => l[2]!) centralTrinomial_one_one_values

private theorem res_zero (p : ℕ) : res p 0 = 1 := by
  simp [res, centralTrinomial_zero]

private theorem res_one (p : ℕ) : res p 1 = 1 := by
  simp [res, centralTrinomial_one]

private theorem res_eq_zero_iff (p n : ℕ) : res p n = 0 ↔ centralTrinomial 1 1 n ≡ 0 [ZMOD p] := by
  rw [res, ← Int.cast_zero, ZMod.intCast_eq_intCast_iff]

private theorem res_eq_res_iff (p m n : ℕ) :
    res p m = res p n ↔ centralTrinomial 1 1 m ≡ centralTrinomial 1 1 n [ZMOD p] :=
  ZMod.intCast_eq_intCast_iff _ _ _

variable {p : ℕ}

/-- The residue of $T_n$ is the product of the residues of $T_d$ over the base-`p` digits `d`. -/
private theorem res_digits (hp : p.Prime) (n : ℕ) :
    res p n = ((Nat.digits p n).map (res p)).prod := by
  have h := (ZMod.intCast_eq_intCast_iff _ _ p).2
    (constantTerm_linearLaurent_pow_digits 1 1 1 1 1 p n hp).2
  rw [res, h, Int.cast_list_prod, List.map_map]
  rfl

/-- Appending a base-`p` digit multiplies the residue by the residue of the digit. -/
private theorem res_mul_add (hp : p.Prime) (u d : ℕ) (hd : d < p) :
    res p (u * p + d) = res p u * res p d := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · simp [res_zero]
  · rw [res_digits hp, show u * p + d = d + p * u by ring,
      Nat.digits_add p hp.one_lt d u hd (Or.inr hu.ne'), List.map_cons, List.prod_cons,
      ← res_digits hp, mul_comm]

/-- Appending `K` base-`p` digits multiplies the residue by the residue of the appended number. -/
private theorem res_mul_pow_add (hp : p.Prime) (K u v : ℕ) (hv : v < p ^ K) :
    res p (u * p ^ K + v) = res p u * res p v := by
  induction K generalizing v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp [res_zero]
  | succ K ih =>
    have hdiv : v / p < p ^ K := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]
      simpa [pow_succ] using hv
    have hmod : v % p < p := Nat.mod_lt _ hp.pos
    have hv' : v / p * p + v % p = v := Nat.div_add_mod' v p
    calc res p (u * p ^ (K + 1) + v) = res p ((u * p ^ K + v / p) * p + v % p) := by
          congr 1
          rw [pow_succ]
          nth_rw 1 [← hv']
          ring
      _ = res p u * res p (v / p) * res p (v % p) := by rw [res_mul_add hp _ _ hmod, ih _ hdiv]
      _ = res p u * res p v := by rw [mul_assoc, ← res_mul_add hp _ _ hmod, hv']

/-- The residue of $T_{p^K - 1}$, whose base-`p` digits are all `p - 1`. -/
private theorem res_pow_sub_one (hp : p.Prime) (K : ℕ) :
    res p (p ^ K - 1) = res p (p - 1) ^ K := by
  induction K with
  | zero => simp [res_zero]
  | succ K ih =>
    have h1 : 1 ≤ p ^ K := Nat.one_le_pow _ _ hp.pos
    have h2 : 1 ≤ p := hp.one_le
    have h3 : 1 ≤ p ^ K * p := Nat.one_le_iff_ne_zero.2 (by positivity)
    have heq : p ^ (K + 1) - 1 = (p ^ K - 1) * p + (p - 1) := by
      rw [pow_succ]
      zify [h1, h2, h3]
      ring
    rw [heq, res_mul_add hp _ _ (Nat.sub_lt hp.pos one_pos), ih, pow_succ]

/-- If no $T_r$ with $r < p$ vanishes modulo `p`, then no $T_n$ does. -/
private theorem res_ne_zero (hp : p.Prime) (h : ∀ r < p, res p r ≠ 0) (n : ℕ) :
    res p n ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have : Fact p.Prime := ⟨hp⟩
    rcases lt_or_ge n p with hn | hn
    · exact h n hn
    · rw [← Nat.div_add_mod' n p, res_mul_add hp _ _ (Nat.mod_lt _ hp.pos)]
      exact mul_ne_zero (ih _ (Nat.div_lt_self (hp.pos.trans_le hn) hp.one_lt))
        (h _ (Nat.mod_lt _ hp.pos))

/-! ### The coefficient `T (p - 1)` modulo `p` -/

/-- Each multiplication by the trinomial moves an exponent by at most one. -/
private theorem coeff_pow_eq_zero (r : ℕ) (j : ℤ) (hj : r < j.natAbs) :
    (trinomialLaurent 1 1 ^ r).coeff j = 0 := by
  induction r generalizing j with
  | zero =>
    have hj' : (0 : ℤ) ≠ j := by omega
    simp [← T_zero, hj']
  | succ r ih =>
    rw [coeff_pow_succ, ih _ (by omega), ih _ (by omega), ih _ (by omega)]
    simp

/-- Frobenius: modulo `p`, the `p`-th power of the trinomial is $x^{-p} + 1 + x^p$. -/
private theorem coeff_pow_prime (hp : p.Prime) (j : ℤ) (hj : 0 < j) :
    (((trinomialLaurent 1 1 ^ p).coeff j : ℤ) : ZMod p) = if j = p then 1 else 0 := by
  have hP : trinomialLaurent 1 1 = T (-1) + T 0 + T 1 := by
    simp [trinomialLaurent]
  rw [hP, add_pow_prime_eq' hp, add_pow_prime_eq' hp, T_pow, T_pow, T_pow]
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_natCast_mul,
    T_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  have h1 : ¬((p : ℤ) * -1 = j) := by omega
  have h2 : ¬((p : ℤ) * 0 = j) := by omega
  simp only [h1, h2, ite_false, mul_one, eq_comm (a := (p : ℤ)), Int.cast_zero, zero_add]
  split_ifs <;> simp

/-- Modulo `p`, the central trinomial coefficient $T_{p-1}$ is $0$, $1$ or $-1$.

Write $c_j$ for the coefficients of $(x^{-1} + 1 + x)^{p-1}$ modulo `p`. Multiplying by
$x^{-1} + 1 + x$ and using the Frobenius identity gives $c_{j-1} + c_j + c_{j+1} = 0$ for
$0 < j < p$, so $c_j$ is periodic with period $3$ for $0 \le j \le p - 1$, while the end values are
$c_{p-1} = 1$, $c_{p-2} = -1$ and $c_{p-3} = 0$. -/
private theorem res_prime_sub_one (hp : p.Prime) (hp3 : 3 ≤ p) :
    res p (p - 1) = 0 ∨ res p (p - 1) = 1 ∨ res p (p - 1) = -1 := by
  set c : ℤ → ZMod p := fun j => ((trinomialLaurent 1 1 ^ (p - 1)).coeff j : ZMod p) with hc
  have hE (j : ℤ) (hj : 0 < j) : c (j + 1) + c j + c (j - 1) = if j = p then 1 else 0 := by
    have h := coeff_pow_succ 1 1 (p - 1) j
    rw [Nat.sub_add_cancel hp.one_le] at h
    rw [← coeff_pow_prime hp j hj, h]
    simp [hc]
  have hzero (j : ℤ) (hj : (p : ℤ) ≤ j) : c j = 0 := by
    simp only [hc, coeff_pow_eq_zero (p - 1) j (by omega), Int.cast_zero]
  have h1 : c (p - 1) = 1 := by
    have := hE p (by exact_mod_cast hp.pos)
    rw [ite_eq_left rfl, hzero (p + 1) (by omega), hzero p le_rfl] at this
    simpa using this
  have h2 : c (p - 2) = -1 := by
    have := hE (p - 1) (by omega)
    rw [ite_eq_right (by omega), show (p : ℤ) - 1 + 1 = p by ring, hzero p le_rfl, h1,
      show (p : ℤ) - 1 - 1 = p - 2 by ring] at this
    linear_combination this
  have h3 : c (p - 3) = 0 := by
    have := hE (p - 2) (by omega)
    rw [ite_eq_right (by omega), show (p : ℤ) - 2 + 1 = p - 1 by ring, h1, h2,
      show (p : ℤ) - 2 - 1 = p - 3 by ring] at this
    linear_combination this
  have hper (j : ℤ) (hj0 : 0 ≤ j) (hj3 : j + 3 ≤ p) : c (j + 3) = c j := by
    have e1 := hE (j + 1) (by omega)
    have e2 := hE (j + 2) (by omega)
    rw [ite_eq_right (by omega), show j + 1 + 1 = j + 2 by ring, show j + 1 - 1 = j by ring] at e1
    rw [ite_eq_right (by omega), show j + 2 + 1 = j + 3 by ring,
      show j + 2 - 1 = j + 1 by ring] at e2
    linear_combination e2 - e1
  have hk (k : ℕ) (hk : 3 * k ≤ p) : c (3 * k) = c 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℤ) = k + 1 by push_cast; ring,
        show (3 : ℤ) * (k + 1) = 3 * k + 3 by ring, hper _ (by positivity) (by omega)]
      exact ih (by omega)
  have hres : res p (p - 1) = c 0 := rfl
  have hdiv := Nat.div_add_mod (p - 1) 3
  have hmod := Nat.mod_lt (p - 1) (show 0 < 3 by norm_num)
  have h3k := hk ((p - 1) / 3) (by omega)
  rw [hres, ← h3k]
  interval_cases hr : (p - 1) % 3
  · refine Or.inr (Or.inl ?_)
    rw [show (3 : ℤ) * ((p - 1) / 3 : ℕ) = p - 1 by omega, h1]
  · refine Or.inr (Or.inr ?_)
    rw [show (3 : ℤ) * ((p - 1) / 3 : ℕ) = p - 2 by omega, h2]
  · refine Or.inl ?_
    rw [show (3 : ℤ) * ((p - 1) / 3 : ℕ) = p - 3 by omega, h3]

/-- Two steps of the recurrence below `p` give $T_{p-3} \equiv -T_{p-2} \pmod p$. -/
private theorem res_sub_three_add_res_sub_two (hp : p.Prime) (hp5 : 5 ≤ p) :
    res p (p - 3) + res p (p - 2) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((6 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    rcases hp.dvd_mul.1 (show p ∣ 2 * 3 by simpa using h') with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
  have hq : ((q : ℕ) : ZMod (q + 3)) = -3 := by
    have h := ZMod.natCast_self (q + 3)
    push_cast at h
    linear_combination h
  have r1 := congrArg (Int.cast : ℤ → ZMod (q + 3)) (centralTrinomial_recurrence 1 1 q)
  have r2 := congrArg (Int.cast : ℤ → ZMod (q + 3)) (centralTrinomial_recurrence 1 1 (q + 1))
  simp only [show q + 1 + 2 = q + 3 by ring, show q + 1 + 1 = q + 2 by ring] at r2
  push_cast at r1 r2
  rw [hq] at r1 r2
  simp only [show q + 3 - 3 = q by omega, show q + 3 - 2 = q + 1 by omega, res]
  have key : (6 : ZMod (q + 3)) *
      ((centralTrinomial 1 1 q : ZMod (q + 3)) + centralTrinomial 1 1 (q + 1)) = 0 := by
    linear_combination r1 + r2
  exact (mul_eq_zero.1 key).resolve_left h6

/-- For odd `p`, the sequence vanishes modulo `p` exactly when $T_{n+1} \equiv T_n$. -/
private theorem a005717_modEq_zero_iff (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
    a005717 n ≡ 0 [ZMOD p] ↔ res p (n + 1) = res p n := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  have key := congrArg (Int.cast : ℤ → ZMod p) (two_mul_a005717 n)
  push_cast at key
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_zero, res, res]
  constructor
  · intro h
    rw [h, mul_zero] at key
    linear_combination -key
  · intro h
    rw [h, sub_self] at key
    exact (mul_eq_zero.1 key).resolve_left h2

/-! ### Densities of periodic sets -/

/-- Partial densities are monotone in the set. -/
private theorem partialDensity_mono {S T : Set ℕ} (h : S ⊆ T) (N : ℕ) :
    S.partialDensity Set.univ N ≤ T.partialDensity Set.univ N := by
  unfold Set.partialDensity
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard
    (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left _ h))
    ((Set.finite_Iio N).subset Set.inter_subset_right)

/-- A set squeezed between sets whose densities are arbitrarily close to `α` has density `α`. -/
private theorem hasDensity_of_squeeze {S : Set ℕ} {α : ℝ}
    (h : ∀ ε > 0, ∃ L U : Set ℕ, ∃ ℓ u : ℝ, L ⊆ S ∧ S ⊆ U ∧ L.HasDensity ℓ ∧ U.HasDensity u ∧
      α - ε ≤ ℓ ∧ u ≤ α + ε) :
    S.HasDensity α := by
  rw [Set.HasDensity, tendsto_order]
  constructor
  · intro a ha
    obtain ⟨L, -, ℓ, -, hL, -, hLd, -, hℓ, -⟩ := h ((α - a) / 2) (by linarith)
    filter_upwards [(tendsto_order.1 hLd).1 a (by linarith)] with N hN
    exact hN.trans_le (partialDensity_mono hL N)
  · intro a ha
    obtain ⟨-, U, -, u, -, hU, -, hUd, -, hu⟩ := h ((a - α) / 2) (by linarith)
    filter_upwards [(tendsto_order.1 hUd).2 a (by linarith)] with N hN
    exact (partialDensity_mono hU N).trans_lt hN

/-- Counts below `N` only depend on the predicate below `N`. -/
private theorem count_congr {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] {N : ℕ}
    (h : ∀ n < N, P n ↔ Q n) : Nat.count P N = Nat.count Q N := by
  simp only [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr fun n hn => h n (Finset.mem_range.1 hn))

/-- Splitting off the last number below a positive bound. -/
private theorem count_eq_count_pred_add {P : ℕ → Prop} [DecidablePred P] {N : ℕ} (hN : 0 < N) :
    Nat.count P N = Nat.count P (N - 1) + if P (N - 1) then 1 else 0 := by
  conv_lhs => rw [show N = N - 1 + 1 by omega]
  exact Nat.count_succ P (N - 1)

/-- Counting below `m * L` block by block. -/
private theorem count_mul_eq_sum (P : ℕ → Prop) [DecidablePred P] (L m : ℕ) :
    Nat.count P (m * L) = ∑ d ∈ Finset.range m, Nat.count (fun w => P (d * L + w)) L := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ← ih, add_mul, one_mul, Nat.count_add]

/-- A set of natural numbers defined by a condition on the residue modulo `M` has density equal
to the proportion of residues below `M` that satisfy the condition. -/
private theorem hasDensity_mod {M : ℕ} (hM : 0 < M) (Q : ℕ → Prop) [DecidablePred Q] :
    {n | Q (n % M)}.HasDensity ((Nat.count Q M : ℝ) / M) := by
  set A := Nat.count Q M with hA
  have hblock (k : ℕ) : Nat.count (fun n => Q (n % M)) (k * M) = k * A := by
    rw [count_mul_eq_sum]
    have hd : ∀ d ∈ Finset.range k, Nat.count (fun w => Q ((d * M + w) % M)) M = A := by
      intro d _
      rw [hA]
      apply count_congr
      intro w hw
      rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]
    rw [Finset.sum_congr rfl hd, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hcount (N : ℕ) : (({n | Q (n % M)} ∩ Set.univ) ∩ Set.Iio N).ncard =
      Nat.count (fun n => Q (n % M)) N := by
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext n
    simp [and_comm]
  have hlow (N : ℕ) : N / M * A ≤ Nat.count (fun n => Q (n % M)) N := by
    rw [← hblock]
    exact Nat.count_monotone _ (Nat.div_mul_le_self N M)
  have hup (N : ℕ) : Nat.count (fun n => Q (n % M)) N ≤ (N / M + 1) * A := by
    rw [← hblock]
    apply Nat.count_monotone
    have h1 := Nat.div_add_mod' N M
    have h2 := Nat.mod_lt N hM
    rw [add_mul, one_mul]
    omega
  rw [Set.HasDensity]
  simp only [Set.partialDensity, hcount, Set.univ_inter, Set.ncard_Iio_nat]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun N : ℕ => (A : ℝ) / M - A / N)
    (h := fun N : ℕ => (A : ℝ) / M + A / N)
  · simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (A : ℝ))
  · simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (A : ℝ))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : ((N / M : ℕ) : ℝ) * A ≤ Nat.count (fun n => Q (n % M)) N := by
      exact_mod_cast hlow N
    have h2 : (N : ℝ) / M - 1 ≤ (N / M : ℕ) := by
      have e : (N : ℝ) = (N / M : ℕ) * M + (N % M : ℕ) := by
        exact_mod_cast (Nat.div_add_mod' N M).symm
      have e2 : ((N % M : ℕ) : ℝ) < M := by exact_mod_cast Nat.mod_lt N hM
      rw [div_sub_one hMr.ne', div_le_iff₀ hMr]
      linarith
    have h3 : (A : ℝ) / M - A / N = (A * ((N : ℝ) / M - 1)) / N := by
      field_simp
    rw [h3]
    apply div_le_div_of_nonneg_right _ hNr.le
    calc (A : ℝ) * ((N : ℝ) / M - 1) ≤ A * (N / M : ℕ) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ ≤ _ := (mul_comm _ _).trans_le h1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (Nat.count (fun n => Q (n % M)) N : ℝ) ≤ ((N / M : ℕ) + 1) * A := by
      exact_mod_cast hup N
    have h2 : ((N / M : ℕ) : ℝ) ≤ N / M := Nat.cast_div_le
    have h3 : (A : ℝ) / M + A / N = (A * ((N : ℝ) / M + 1)) / N := by
      field_simp
    rw [h3]
    apply div_le_div_of_nonneg_right _ hNr.le
    calc _ ≤ ((N / M : ℕ) + 1) * (A : ℝ) := h1
      _ ≤ ((N : ℝ) / M + 1) * A := by gcongr
      _ = _ := by ring

/-! ### Density one when some `T r` with `r < p` vanishes -/

/-- If $T_r \equiv 0 \pmod p$ for a digit `r < p`, at most `(p - 1)^K` numbers below `p^K` have
$T_v \not\equiv 0 \pmod p$. -/
private theorem count_res_ne_zero_le (hp : p.Prime) {r : ℕ} (hr : r < p) (hr0 : res p r = 0)
    (K : ℕ) : Nat.count (fun v => res p v ≠ 0) (p ^ K) ≤ (p - 1) ^ K := by
  have : Fact p.Prime := ⟨hp⟩
  have hstep (m : ℕ) : Nat.count (fun v => res p v ≠ 0) (m * p) ≤
      (p - 1) * Nat.count (fun v => res p v ≠ 0) m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [add_mul, one_mul, Nat.count_add, Nat.count_succ, mul_add]
      refine add_le_add ih ?_
      by_cases hm : res p m = 0
      · rw [ite_eq_right (not_not.2 hm), mul_zero, nonpos_iff_eq_zero, Nat.count_iff_forall_not]
        intro d hd
        simp [res_mul_add hp _ _ hd, hm]
      · rw [ite_eq_left hm, mul_one]
        have hlt : Nat.count (fun d => res p (m * p + d) ≠ 0) p < p := by
          rw [Nat.count_eq_card_filter_range]
          calc _ < (Finset.range p).card :=
                Finset.card_lt_card (Finset.filter_ssubset.2
                  ⟨r, Finset.mem_range.2 hr, by simp [res_mul_add hp _ _ hr, hr0]⟩)
            _ = p := Finset.card_range p
        omega
  induction K with
  | zero =>
    rw [pow_zero, pow_zero, Nat.count_one]
    split_ifs <;> simp
  | succ K ih =>
    rw [pow_succ]
    calc _ ≤ (p - 1) * Nat.count (fun v => res p v ≠ 0) (p ^ K) := hstep _
      _ ≤ (p - 1) * (p - 1) ^ K := Nat.mul_le_mul_left _ ih
      _ = (p - 1) ^ (K + 1) := by ring

/-- If $T_r \equiv 0 \pmod p$ for some `r < p`, the sequence vanishes modulo `p` with density one:
for every `K`, both $T_n$ and $T_{n+1}$ vanish modulo `p` outside a set that is periodic modulo
$p^K$ and has density at most $3((p-1)/p)^K$. -/
private theorem hasDensity_one (hp : p.Prime)
    (hzero : ∃ r < p, centralTrinomial 1 1 r ≡ 0 [ZMOD p]) :
    ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1 := by
  obtain ⟨r, hr, hr0⟩ := hzero
  rw [← res_eq_zero_iff] at hr0
  have hp2 : p ≠ 2 := by
    rintro rfl
    interval_cases r
    · simp [res_zero] at hr0
    · simp [res_one] at hr0
  have hset : ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ) = {n | res p (n + 1) = res p n} := by
    ext n
    exact a005717_modEq_zero_iff hp hp2 n
  rw [hset]
  apply hasDensity_of_squeeze
  intro ε hε
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (((p : ℝ) - 1) / p) ^ K < ε / 3 :=
    exists_pow_lt_of_lt_one (by positivity) (by rw [div_lt_one hp0]; linarith)
  have hpK : 0 < p ^ K := pow_pos hp.pos K
  let Q : ℕ → Prop := fun v => res p v = 0 ∧ res p ((v + 1) % p ^ K) = 0
  refine ⟨{n | Q (n % p ^ K)}, Set.univ, (Nat.count Q (p ^ K) : ℝ) / (p ^ K : ℕ), 1, ?_,
    Set.subset_univ _, hasDensity_mod hpK Q, Set.HasDensity.univ, ?_, by linarith⟩
  · intro n hn
    obtain ⟨h1, h2⟩ := hn
    rw [Nat.mod_add_mod] at h2
    have e1 : res p n = 0 := by
      rw [← Nat.div_add_mod' n (p ^ K), res_mul_pow_add hp K _ _ (Nat.mod_lt _ hpK), h1,
        mul_zero]
    have e2 : res p (n + 1) = 0 := by
      rw [← Nat.div_add_mod' (n + 1) (p ^ K), res_mul_pow_add hp K _ _ (Nat.mod_lt _ hpK), h2,
        mul_zero]
    change res p (n + 1) = res p n
    rw [e1, e2]
  · -- Count the residues where `T v` or `T (v + 1)` does not vanish.
    have hB := count_res_ne_zero_le hp hr hr0 K
    have hR : Nat.count (fun w => res p (w % p ^ K) ≠ 0) (p ^ K) =
        Nat.count (fun v => res p v ≠ 0) (p ^ K) :=
      count_congr fun w hw => by rw [Nat.mod_eq_of_lt hw]
    have hshift : Nat.count (fun v => res p ((v + 1) % p ^ K) ≠ 0) (p ^ K) ≤
        Nat.count (fun v => res p v ≠ 0) (p ^ K) + 1 := by
      have h1 := Nat.count_succ' (fun w => res p (w % p ^ K) ≠ 0) (p ^ K)
      have h2 := Nat.count_succ (fun w => res p (w % p ^ K) ≠ 0) (p ^ K)
      split_ifs at h1 h2 <;> omega
    have hsplit : p ^ K ≤ Nat.count Q (p ^ K) + Nat.count (fun v => res p v ≠ 0) (p ^ K) +
        Nat.count (fun v => res p ((v + 1) % p ^ K) ≠ 0) (p ^ K) := by
      have htot : Nat.count Q (p ^ K) + Nat.count (fun v => ¬Q v) (p ^ K) = p ^ K := by
        simp only [Nat.count_eq_card_filter_range]
        rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
      have hnot : Nat.count (fun v => ¬Q v) (p ^ K) ≤
          Nat.count (fun v => res p v ≠ 0) (p ^ K) +
            Nat.count (fun v => res p ((v + 1) % p ^ K) ≠ 0) (p ^ K) := by
        simp only [Nat.count_eq_card_filter_range]
        refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_union, Q, not_and_or] at hv ⊢
        tauto
      omega
    have hcount : (p ^ K : ℕ) ≤ Nat.count Q (p ^ K) + 2 * (p - 1) ^ K + 1 := by omega
    have hcountR : (p : ℝ) ^ K - 2 * ((p : ℝ) - 1) ^ K - 1 ≤ Nat.count Q (p ^ K) := by
      have h := (Nat.cast_le (α := ℝ)).2 hcount
      push_cast [Nat.cast_sub hp.one_le] at h
      linarith
    have hone : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ K := one_le_pow₀ (by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith)
    have hpKr : (0 : ℝ) < (p : ℝ) ^ K := by positivity
    have hrat : ((p : ℝ) - 1) ^ K = (((p : ℝ) - 1) / p) ^ K * (p : ℝ) ^ K := by
      rw [div_pow, div_mul_cancel₀ _ hpKr.ne']
    push_cast
    rw [le_div_iff₀ hpKr]
    nlinarith

/-! ### The density formula when no `T r` with `r < p` vanishes -/

/-- The number of digits `d < p - 1` with $T_{d+1} \equiv e \, T_d \pmod p$. -/
private noncomputable def digitCount (p : ℕ) (e : ZMod p) : ℕ :=
  ((Finset.range (p - 1)).filter (fun d => res p (d + 1) = e * res p d)).card

/-- Splitting off the leading base-`p` digit: among the numbers `v < p^(K+1)` other than the last,
those with $T_{v+1} \equiv T_v$ are counted by `p` copies of the count below `p^K` and by the
carries into the leading digit. -/
private theorem count_succ_pow (hp : p.Prime) (hne : ∀ n, res p n ≠ 0) (K : ℕ) :
    Nat.count (fun v => v + 1 < p ^ (K + 1) ∧ res p (v + 1) = res p v) (p ^ (K + 1)) =
      p * Nat.count (fun v => v + 1 < p ^ K ∧ res p (v + 1) = res p v) (p ^ K) +
        digitCount p (res p (p - 1) ^ K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpK : 0 < p ^ K := pow_pos hp.pos K
  set f := Nat.count (fun v => v + 1 < p ^ K ∧ res p (v + 1) = res p v) (p ^ K) with hf
  have hf' : f = Nat.count (fun w => res p (w + 1) = res p w) (p ^ K - 1) := by
    rw [hf, count_eq_count_pred_add hpK, ite_eq_right (by omega), add_zero]
    exact count_congr fun w hw => ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have hblock (d : ℕ) (hd : d < p) :
      Nat.count (fun w => d * p ^ K + w + 1 < p * p ^ K ∧
          res p (d * p ^ K + w + 1) = res p (d * p ^ K + w)) (p ^ K) =
        f + if d + 1 < p ∧ res p (d + 1) = res p (p - 1) ^ K * res p d then 1 else 0 := by
    have hdK : (d + 1) * p ^ K ≤ p * p ^ K := Nat.mul_le_mul_right _ hd
    rw [count_eq_count_pred_add hpK]
    congr 1
    · rw [hf']
      apply count_congr
      intro w hw
      have hw' : w + 1 < p ^ K := by omega
      have hlt : d * p ^ K + w + 1 < p * p ^ K := by nlinarith
      rw [add_assoc, res_mul_pow_add hp K _ _ hw', res_mul_pow_add hp K _ _ (by omega)]
      exact ⟨fun h => mul_left_cancel₀ (hne d) h.2, fun h => ⟨by rwa [← add_assoc], by rw [h]⟩⟩
    · apply if_congr _ rfl rfl
      have e1 : d * p ^ K + (p ^ K - 1) + 1 = (d + 1) * p ^ K := by
        rw [add_assoc, Nat.sub_add_cancel hpK]
        ring
      rw [e1, res_mul_pow_add hp K _ _ (Nat.sub_lt hpK one_pos), res_pow_sub_one hp]
      have e2 : res p ((d + 1) * p ^ K) = res p (d + 1) := by
        simpa [res_zero] using res_mul_pow_add hp K (d + 1) 0 hpK
      rw [e2, Nat.mul_lt_mul_right hpK, mul_comm (res p d)]
  rw [pow_succ', count_mul_eq_sum, Finset.sum_congr rfl fun d hd => hblock d
    (Finset.mem_range.1 hd), Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, Finset.sum_boole, Nat.cast_id, digitCount]
  congr 2
  ext d
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega, h2⟩

/-- The count below an even power of `p`, in closed form. -/
private theorem count_even_pow (hp : p.Prime) (hne : ∀ n, res p n ≠ 0)
    (hτ : res p (p - 1) ^ 2 = 1) (J : ℕ) :
    ((p : ℝ) ^ 2 - 1) *
        (Nat.count (fun v => v + 1 < p ^ (2 * J) ∧ res p (v + 1) = res p v) (p ^ (2 * J)) : ℝ) =
      ((digitCount p (res p (p - 1)) : ℝ) + p * digitCount p 1) * ((p : ℝ) ^ (2 * J) - 1) := by
  induction J with
  | zero => simp [Nat.count_one]
  | succ J ih =>
    have h1 : res p (p - 1) ^ (2 * J + 1) = res p (p - 1) := by
      rw [pow_succ, pow_mul, hτ, one_pow, one_mul]
    have h2 : res p (p - 1) ^ (2 * J) = 1 := by
      rw [pow_mul, hτ, one_pow]
    rw [show 2 * (J + 1) = 2 * J + 1 + 1 by ring, count_succ_pow hp hne,
      count_succ_pow hp hne, h1, h2]
    push_cast
    rw [pow_succ, pow_succ]
    linear_combination (p : ℝ) ^ 2 * ih

/-- When no $T_n$ vanishes modulo `p` and $T_{p-1}^2 \equiv 1$, the set of `n` with
$T_{n+1} \equiv T_n \pmod p$ has the density given by the digit counts. -/
private theorem hasDensity_formula (hp : p.Prime) (hne : ∀ n, res p n ≠ 0)
    (hτ : res p (p - 1) ^ 2 = 1) :
    {n | res p (n + 1) = res p n}.HasDensity
      (((digitCount p (res p (p - 1)) : ℝ) + p * digitCount p 1) /
        (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ))) := by
  have : Fact p.Prime := ⟨hp⟩
  set D := ((digitCount p (res p (p - 1)) : ℝ) + p * digitCount p 1) /
    (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ)) with hD
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hden : ((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ) = (p : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub hp.one_le]
    push_cast
    ring
  have hden0 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hD0 : 0 ≤ D := by
    rw [hD, hden]
    positivity
  apply hasDensity_of_squeeze
  intro ε hε
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt ((D + 1) / ε) (show (1 : ℝ) < (p : ℝ) ^ 2 by
    nlinarith)
  have hpK : 0 < p ^ (2 * J) := pow_pos hp.pos _
  let H : ℕ → Prop := fun v => v + 1 < p ^ (2 * J) ∧ res p (v + 1) = res p v
  have hcountU : Nat.count (fun v => H v ∨ v = p ^ (2 * J) - 1) (p ^ (2 * J)) =
      Nat.count H (p ^ (2 * J)) + 1 := by
    rw [count_eq_count_pred_add hpK, count_eq_count_pred_add (P := H) hpK,
      ite_eq_left (Or.inr rfl), ite_eq_right (by simp only [H]; omega), add_zero]
    congr 1
    exact count_congr fun v hv => ⟨fun h => h.resolve_right (by omega), Or.inl⟩
  have hP : (0 : ℝ) < (p : ℝ) ^ (2 * J) := by positivity
  have hcount : (Nat.count H (p ^ (2 * J)) : ℝ) = D * ((p : ℝ) ^ (2 * J) - 1) := by
    rw [hD, hden, div_mul_eq_mul_div, eq_div_iff hden0.ne']
    linear_combination count_even_pow hp hne hτ J
  have hJ' : D + 1 < (p : ℝ) ^ (2 * J) * ε := by
    rw [← pow_mul] at hJ
    exact (div_lt_iff₀ hε).1 hJ
  refine ⟨{n | H (n % p ^ (2 * J))}, {n | H (n % p ^ (2 * J)) ∨ n % p ^ (2 * J) = p ^ (2 * J) - 1},
    (Nat.count H (p ^ (2 * J)) : ℝ) / (p ^ (2 * J) : ℕ),
    (Nat.count (fun v => H v ∨ v = p ^ (2 * J) - 1) (p ^ (2 * J)) : ℝ) / (p ^ (2 * J) : ℕ),
    ?_, ?_, hasDensity_mod hpK H, hasDensity_mod hpK (fun v => H v ∨ v = p ^ (2 * J) - 1), ?_,
    ?_⟩
  · intro n hn
    obtain ⟨h1, h2⟩ := hn
    change res p (n + 1) = res p n
    have hn' := Nat.div_add_mod' n (p ^ (2 * J))
    rw [← hn', add_assoc, res_mul_pow_add hp _ _ _ h1,
      res_mul_pow_add hp _ _ _ (Nat.mod_lt _ hpK), h2]
  · intro n hn
    change res p (n + 1) = res p n at hn
    have hmod := Nat.mod_lt n hpK
    by_cases h1 : n % p ^ (2 * J) + 1 < p ^ (2 * J)
    · left
      refine ⟨h1, ?_⟩
      have hn' := Nat.div_add_mod' n (p ^ (2 * J))
      rw [← hn', add_assoc, res_mul_pow_add hp _ _ _ h1,
        res_mul_pow_add hp _ _ _ (Nat.mod_lt _ hpK)] at hn
      exact mul_left_cancel₀ (hne _) hn
    · right
      show n % p ^ (2 * J) = p ^ (2 * J) - 1
      omega
  · push_cast
    rw [hcount, le_div_iff₀ hP]
    nlinarith
  · rw [hcountU]
    push_cast
    rw [hcount, div_le_iff₀ hP]
    nlinarith

end a005717_zero_density

open a005717_zero_density in
/-- **Zero density of A005717 modulo a prime.** Let $p$ be a prime, let $T_m$ be the central
trinomial coefficient, the constant term of $(x^{-1} + 1 + x)^m$, and let $a_n$ be the constant
term of $x (x^{-1} + 1 + x)^n$ (OEIS A005717). If $T_r \equiv 0 \pmod p$ for some $r < p$, then
the set of $n \in \mathbb{N}$ with $a_n \equiv 0 \pmod p$ has natural density $1$. If instead
$T_r \not\equiv 0 \pmod p$ for every $r < p$ and $p > 2$, let $N_1$ be the number of $m < p - 1$
with $T_m \equiv T_{p-1} T_{m+1} \pmod p$ and let $N_2$ be the number of $m < p - 1$ with
$T_m \equiv T_{m+1} \pmod p$. Then that set has natural density
$D_0 = (N_1 + p N_2) / ((p - 1)(p + 1))$, and $D_0 \ge 1/(p - 1)$.

Source: Nadav Kohen, *Density and Symmetry in the Generalized Motzkin Numbers Modulo p*,
INTEGERS 26 (2026), Article A22, Proposition 6. -/
public theorem a005717_zero_density
    (p : ℕ) (hp : p.Prime) :
    ((∃ r < p, centralTrinomial 1 1 r ≡ 0 [ZMOD p]) →
      ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity 1) ∧
    ((∀ r < p, ¬(centralTrinomial 1 1 r ≡ 0 [ZMOD p])) → 2 < p →
      let D₀ :=
        ((((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡
              centralTrinomial 1 1 (p - 1) * centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ) +
          p * (((Finset.range (p - 1)).filter (fun m =>
            centralTrinomial 1 1 m ≡ centralTrinomial 1 1 (m + 1)
              [ZMOD p])).card : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ))
      ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ).HasDensity D₀ ∧
        1 / ((p - 1 : ℕ) : ℝ) ≤ D₀) := by
  refine ⟨hasDensity_one hp, fun hnonzero hp2 => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hres : ∀ r < p, res p r ≠ 0 := fun r hr h => hnonzero r hr ((res_eq_zero_iff p r).1 h)
  have hne := res_ne_zero hp hres
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hnonzero 2 (by norm_num) (by rw [centralTrinomial_two]; exact Int.emod_self)
  have hp5 : 5 ≤ p := by
    by_contra h
    interval_cases p
    · exact hp3 rfl
    · exact absurd hp (by decide)
  have hτ : res p (p - 1) ^ 2 = 1 := by
    rcases res_prime_sub_one hp (by omega) with h | h | h
    · exact absurd h (hne _)
    · rw [h, one_pow]
    · rw [h]
      ring
  have hN₂ : ((Finset.range (p - 1)).filter (fun m =>
      centralTrinomial 1 1 m ≡ centralTrinomial 1 1 (m + 1) [ZMOD p])).card =
      digitCount p 1 := by
    unfold digitCount
    congr 1
    apply Finset.filter_congr
    intro m _
    rw [← res_eq_res_iff, one_mul, eq_comm]
  have hN₁ : ((Finset.range (p - 1)).filter (fun m =>
      centralTrinomial 1 1 m ≡
        centralTrinomial 1 1 (p - 1) * centralTrinomial 1 1 (m + 1) [ZMOD p])).card =
      digitCount p (res p (p - 1)) := by
    unfold digitCount
    congr 1
    apply Finset.filter_congr
    intro m _
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_mul]
    change res p m = res p (p - 1) * res p (m + 1) ↔ _
    constructor
    · intro h
      rw [h, ← mul_assoc, ← sq, hτ, one_mul]
    · intro h
      rw [h, ← mul_assoc, ← sq, hτ, one_mul]
  have hset : ({n | a005717 n ≡ 0 [ZMOD p]} : Set ℕ) = {n | res p (n + 1) = res p n} := by
    ext n
    exact a005717_modEq_zero_iff hp (by omega) n
  intro D₀
  have hD : D₀ = ((digitCount p (res p (p - 1)) : ℝ) + p * digitCount p 1) /
      (((p - 1 : ℕ) : ℝ) * (p + 1 : ℝ)) := by
    simp only [D₀, hN₁, hN₂]
  rw [hset, hD]
  refine ⟨hasDensity_formula hp hne hτ, ?_⟩
  -- Both counts are positive: `m = 0` always counts, and so does `m = p - 3` when `T (p - 1) = -1`.
  have ha : 1 ≤ digitCount p 1 := by
    unfold digitCount
    apply Finset.card_pos.2
    exact ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
      by rw [zero_add, res_one, res_zero, one_mul]⟩⟩
  have hb : 1 ≤ digitCount p (res p (p - 1)) := by
    unfold digitCount
    apply Finset.card_pos.2
    rcases mul_self_eq_one_iff.1 (show res p (p - 1) * res p (p - 1) = 1 by rw [← sq, hτ])
      with h | h
    · exact ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
        by rw [h, zero_add, res_one, res_zero, one_mul]⟩⟩
    · refine ⟨p - 3, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩⟩
      rw [h, show p - 3 + 1 = p - 2 by omega]
      linear_combination res_sub_three_add_res_sub_two hp hp5
  have hpm1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p - 1 by omega)
  have har : (1 : ℝ) ≤ digitCount p 1 := by exact_mod_cast ha
  have hbr : (1 : ℝ) ≤ digitCount p (res p (p - 1)) := by exact_mod_cast hb
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [div_le_div_iff₀ hpm1 (by positivity)]
  nlinarith [mul_nonneg hpm1.le (sub_nonneg.2 hbr),
    mul_nonneg (mul_nonneg hpm1.le hp0) (sub_nonneg.2 har)]

end MetaMathlibExt
