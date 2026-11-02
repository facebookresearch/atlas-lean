/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The birthday bound

Choose `q` elements of a finite set `α` of size `N` uniformly and independently, i.e. a uniform
function `Fin q → α`. `collisionGame α q : PMF Bool` outputs whether two of them coincide, and
`collisionProb α q` is the probability of a collision.

* `collisionProb_eq`: `collisionProb α q = 1 - N (N - 1) ⋯ (N - q + 1) / N ^ q`, by counting
  injective functions (`Fintype.card_embedding_eq`).
* `collisionProb_le` (**birthday upper bound**): `collisionProb α q ≤ q (q - 1) / (2 N)`. This
  slightly strengthens Katz and Lindell's Lemma A.15, which states the bound `q ^ 2 / (2 N)`.
* `one_sub_exp_le_collisionProb`: `1 - exp (-q (q - 1) / (2 N)) ≤ collisionProb α q`, and
  `div_one_add_le_collisionProb`: with `x = q (q - 1) / (2 N)`, `x / (1 + x) ≤ collisionProb α q`.
* `collisionProb_ge` (**birthday lower bound**): if `q (q - 1) ≤ 2 N`, then
  `q (q - 1) / (4 N) ≤ collisionProb α q`. `collisionProb_ge_of_le_sqrt` is the statement of
  Katz and Lindell's Lemma A.16 in the 2nd edition, whose hypothesis is `q ≤ √(2 N)`;
  `collisionProb_ge_of_le_sqrt_card` is the weaker form with `q ≤ √N`.
  `half_le_collisionProb`: if `2 N ≤ q (q - 1)`, a collision has probability at least `1/2`.

So `Θ(√N)` samples are necessary and sufficient for a constant collision probability, which is the
generic bound behind the birthday attack on hash functions. The general inequalities used in the
proofs (the Weierstrass product inequality, the count of injective functions) are private here;
they can be promoted to MathlibExt later.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed., CRC Press, 2020,
  Appendix A.4.
-/

@[expose] public section

namespace Cslib.Crypto.Birthday

open Finset

variable (α : Type*) [Fintype α] [Nonempty α] (q : ℕ)

open Classical in
/-- **The collision experiment.** For a nonempty finite set $\alpha$ and a natural number $q$, the
collision experiment is the probability distribution on $\{\mathrm{true}, \mathrm{false}\}$
obtained by drawing a function $s \colon \{0, \dots, q - 1\} \to \alpha$ uniformly at random
(equivalently, $q$ independent uniform samples $s(0), \dots, s(q - 1)$ from $\alpha$) and
outputting true exactly when $s$ is not injective, that is, when $s(i) = s(j)$ for some
$i \ne j$. -/
noncomputable def collisionGame : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin q → α)).map fun s => !decide (Function.Injective s)

/-- **Collision probability.** For a nonempty finite set $\alpha$ and a natural number $q$, the
collision probability is the probability, as a real number, that the collision experiment with
$q$ samples from $\alpha$ outputs true, that is, that $q$ independent uniform samples from
$\alpha$ contain two equal samples at distinct positions. -/
noncomputable def collisionProb : ℝ := (collisionGame α q true).toReal

omit [Nonempty α] in
private theorem map_uniform_apply {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → Bool)
    (b : Bool) :
    (Cslib.Probability.PMF.uniformOfFintype Ω).map f b =
      (univ.filter fun ω => f ω = b).card * (Fintype.card Ω : ENNReal)⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 3
  ext ω
  simp [eq_comm]

omit [Nonempty α] in
/-- The number of injective functions `Fin q → α` is `N (N - 1) ⋯ (N - q + 1)`. -/
private theorem card_filter_injective [DecidableEq α] :
    (univ.filter fun s : Fin q → α => Function.Injective s).card =
      (Fintype.card α).descFactorial q := by
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _),
    Fintype.card_embedding_eq, Fintype.card_fin]

/-- **The exact collision probability.** Let $\alpha$ be a nonempty finite set with $N$ elements
and $q$ a natural number. The probability that $q$ independent uniform samples from $\alpha$
contain a collision equals $1 - N (N - 1) \cdots (N - q + 1) / N^q$, where the product
$N (N - 1) \cdots (N - q + 1)$ has $q$ factors (it is $1$ for $q = 0$ and $0$ for $q > N$). -/
theorem collisionProb_eq :
    collisionProb α q =
      1 - ((Fintype.card α).descFactorial q : ℝ) / (Fintype.card α : ℝ) ^ q := by
  classical
  have hN : 0 < Fintype.card α := Fintype.card_pos
  have hcard : Fintype.card (Fin q → α) = Fintype.card α ^ q := by simp
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin q → α)))
    (fun s => Function.Injective s)
  rw [card_filter_injective, card_univ, hcard] at hsplit
  have hle : (Fintype.card α).descFactorial q ≤ Fintype.card α ^ q := Nat.descFactorial_le_pow _ _
  rw [collisionProb, collisionGame, map_uniform_apply, hcard]
  have hset : (univ.filter fun s : Fin q → α => (!decide (Function.Injective s)) = true) =
      univ.filter fun s => ¬Function.Injective s := by
    ext s
    simp
  rw [hset, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, ← div_eq_mul_inv, eq_sub_iff_add_eq, Nat.cast_pow, ← add_div,
    div_eq_one_iff_eq (by positivity), ← Nat.cast_pow]
  exact_mod_cast (show (univ.filter fun s : Fin q → α => ¬Function.Injective s).card +
    (Fintype.card α).descFactorial q = Fintype.card α ^ q by omega)

/-- For `q ≤ N`, `N (N - 1) ⋯ (N - q + 1) / N ^ q = ∏_{i < q} (1 - i / N)`. -/
private theorem descFactorial_div_pow (hq : q ≤ Fintype.card α) :
    ((Fintype.card α).descFactorial q : ℝ) / (Fintype.card α : ℝ) ^ q =
      ∏ i ∈ range q, (1 - (i : ℝ) / Fintype.card α) := by
  have hN : (Fintype.card α : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := α)
    positivity
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show (Fintype.card α : ℝ) ^ q = ∏ _i ∈ range q, (Fintype.card α : ℝ) by
      rw [prod_const, card_range], ← prod_div_distrib]
  refine prod_congr rfl fun i hi => ?_
  rw [Nat.cast_sub (by have := mem_range.mp hi; omega), sub_div, div_self hN]

/-- Mathlib's Gauss sum `Finset.sum_range_id_mul_two`, cast to the reals. -/
private theorem sum_range_cast (q : ℕ) : ∑ i ∈ range q, (i : ℝ) = q * (q - 1) / 2 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_range_id_mul_two q)
  push_cast [Nat.cast_sub hq] at h
  linarith

/-- `1 - ∑ x_i ≤ ∏ (1 - x_i)` for `x_i ∈ [0, 1]` (the Weierstrass product inequality). -/
private theorem one_sub_sum_le_prod (x : ℕ → ℝ) (n : ℕ) (h0 : ∀ i < n, 0 ≤ x i)
    (h1 : ∀ i < n, x i ≤ 1) : 1 - ∑ i ∈ range n, x i ≤ ∏ i ∈ range n, (1 - x i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, prod_range_succ]
    have hS : 0 ≤ ∑ i ∈ range n, x i :=
      sum_nonneg fun i hi => h0 i (by have := mem_range.mp hi; omega)
    have := mul_le_mul_of_nonneg_right (ih (fun i hi => h0 i (by omega))
      (fun i hi => h1 i (by omega))) (sub_nonneg.mpr (h1 n (by omega)))
    nlinarith [h0 n (by omega)]

private theorem collisionProb_le_one : collisionProb α q ≤ 1 := by
  rw [collisionProb_eq, sub_le_self_iff]
  positivity

/-- **Birthday upper bound.** Let $\alpha$ be a nonempty finite set with $N$ elements and $q$ a
natural number. The probability that $q$ independent uniform samples from $\alpha$ contain a
collision is at most $q (q - 1) / (2 N)$.

This implies Katz and Lindell's Lemma A.15, which states the bound $q^2 / (2 N)$. -/
theorem collisionProb_le :
    collisionProb α q ≤ q * (q - 1) / (2 * Fintype.card α) := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rcases le_or_gt q (Fintype.card α) with hq | hq
  · rw [collisionProb_eq, descFactorial_div_pow α q hq, sub_le_comm]
    have h := one_sub_sum_le_prod (fun i => (i : ℝ) / Fintype.card α) q
      (fun i _ => by positivity) (fun i hi => by
        rw [div_le_one hN]
        exact_mod_cast (hi.trans_le hq).le)
    have hsum : ∑ i ∈ range q, (i : ℝ) / Fintype.card α = q * (q - 1) / (2 * Fintype.card α) := by
      rw [← sum_div, sum_range_cast]
      field_simp
    rw [hsum] at h
    linarith
  · refine (collisionProb_le_one α q).trans ?_
    rw [le_div_iff₀ (by positivity), one_mul]
    have hq' : (Fintype.card α : ℝ) + 1 ≤ q := by exact_mod_cast hq
    have hN1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
    have hq1 : (Fintype.card α : ℝ) ≤ q - 1 := by linarith
    nlinarith [mul_le_mul hq' hq1 (by positivity) (by positivity)]

/-- **Birthday lower bound, exponential form.** Let $\alpha$ be a nonempty finite set with $N$
elements and $q$ a natural number. The probability that $q$ independent uniform samples from
$\alpha$ contain a collision is at least $1 - \exp(-q (q - 1) / (2 N))$. -/
theorem one_sub_exp_le_collisionProb :
    1 - Real.exp (-(q * (q - 1) / (2 * Fintype.card α))) ≤ collisionProb α q := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rcases le_or_gt q (Fintype.card α) with hq | hq
  · rw [collisionProb_eq, descFactorial_div_pow α q hq, sub_le_sub_iff_left]
    have hsum : -(q * (q - 1) / (2 * Fintype.card α)) =
        ∑ i ∈ range q, -((i : ℝ) / Fintype.card α) := by
      rw [sum_neg_distrib, ← sum_div, sum_range_cast]
      field_simp
    rw [hsum, Real.exp_sum]
    refine prod_le_prod₀ (fun i hi => ?_) (fun i _ => ?_)
    · rw [sub_nonneg, div_le_one hN]
      exact_mod_cast (mem_range.mp hi).le.trans hq
    · linarith [Real.add_one_le_exp (-((i : ℝ) / Fintype.card α))]
  · have hD : (Fintype.card α).descFactorial q = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hq
    rw [collisionProb_eq, hD, Nat.cast_zero, zero_div, sub_zero]
    linarith [Real.exp_pos (-(q * (q - 1) / (2 * Fintype.card α)))]

/-- **Birthday lower bound, rational form.** Let $\alpha$ be a nonempty finite set with $N$
elements, $q$ a natural number, and $x = q (q - 1) / (2 N)$. The probability that $q$ independent
uniform samples from $\alpha$ contain a collision is at least $x / (1 + x)$. -/
theorem div_one_add_le_collisionProb :
    (q * (q - 1) / (2 * Fintype.card α)) / (1 + q * (q - 1) / (2 * Fintype.card α)) ≤
      collisionProb α q := by
  set x : ℝ := q * (q - 1) / (2 * Fintype.card α)
  have hx : 0 ≤ x := by
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [x, h]
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h
      have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
      positivity
  refine le_trans ?_ (one_sub_exp_le_collisionProb α q)
  have hexp : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith [Real.add_one_le_exp x])
  have : x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
  linarith

/-- **Birthday lower bound.** Let $\alpha$ be a nonempty finite set with $N$ elements and $q$ a
natural number with $q (q - 1) \le 2 N$. The probability that $q$ independent uniform samples
from $\alpha$ contain a collision is at least $q (q - 1) / (4 N)$.

This strengthens Katz and Lindell's Lemma A.16, whose hypothesis $q \le \sqrt{2 N}$ implies
$q (q - 1) \le 2 N$. -/
theorem collisionProb_ge (h : (q : ℝ) * (q - 1) ≤ 2 * Fintype.card α) :
    q * (q - 1) / (4 * Fintype.card α) ≤ collisionProb α q := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine le_trans ?_ (div_one_add_le_collisionProb α q)
  set x : ℝ := q * (q - 1) / (2 * Fintype.card α)
  have hx0 : 0 ≤ x := by
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [x, h]
    · have : (1 : ℝ) ≤ q := by exact_mod_cast h
      positivity
  have hx1 : x ≤ 1 := by rw [div_le_one (by positivity)]; exact h
  have h4 : (q : ℝ) * (q - 1) / (4 * Fintype.card α) = x / 2 := by
    simp only [x]
    field_simp
    ring
  rw [h4, div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

omit [Nonempty α] in
/-- `q ≤ √(2 N)` implies the hypothesis `q (q - 1) ≤ 2 N` of `collisionProb_ge`. -/
private theorem mul_sub_one_le_of_le_sqrt (h : (q : ℝ) ≤ Real.sqrt (2 * Fintype.card α)) :
    (q : ℝ) * (q - 1) ≤ 2 * Fintype.card α := by
  have h2 : (q : ℝ) ^ 2 ≤ 2 * Fintype.card α :=
    (Real.le_sqrt (by positivity) (by positivity)).mp h
  nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]

/-- **Birthday lower bound as stated in Katz and Lindell.** Let $\alpha$ be a nonempty finite set
with $N$ elements and $q$ a natural number with $q \le \sqrt{2 N}$. The probability that $q$
independent uniform samples from $\alpha$ contain a collision is at least $q (q - 1) / (4 N)$.

This is Lemma A.16 of Katz and Lindell (2nd ed.): "say $q \le \sqrt{2N}$ elements are chosen
uniformly and independently ... at least $q (q - 1) / (4N)$". -/
theorem collisionProb_ge_of_le_sqrt (h : (q : ℝ) ≤ Real.sqrt (2 * Fintype.card α)) :
    q * (q - 1) / (4 * Fintype.card α) ≤ collisionProb α q :=
  collisionProb_ge α q (mul_sub_one_le_of_le_sqrt α q h)

/-- **Birthday lower bound for at most square-root many samples.** Let $\alpha$ be a nonempty
finite set with $N$ elements and $q$ a natural number with $q \le \sqrt{N}$. The probability that
$q$ independent uniform samples from $\alpha$ contain a collision is at least
$q (q - 1) / (4 N)$. -/
theorem collisionProb_ge_of_le_sqrt_card (h : (q : ℝ) ≤ Real.sqrt (Fintype.card α)) :
    q * (q - 1) / (4 * Fintype.card α) ≤ collisionProb α q :=
  collisionProb_ge_of_le_sqrt α q (h.trans (Real.sqrt_le_sqrt (by
    have : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
    linarith)))

/-- **Even odds of a collision.** Let $\alpha$ be a nonempty finite set with $N$ elements and $q$ a
natural number with $2 N \le q (q - 1)$. The probability that $q$ independent uniform samples from
$\alpha$ contain a collision is at least $1/2$. -/
theorem half_le_collisionProb (h : 2 * (Fintype.card α : ℝ) ≤ q * (q - 1)) :
    1 / 2 ≤ collisionProb α q := by
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine le_trans ?_ (div_one_add_le_collisionProb α q)
  set x : ℝ := q * (q - 1) / (2 * Fintype.card α)
  have hx1 : 1 ≤ x := by rw [le_div_iff₀ (by positivity), one_mul]; exact h
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  linarith

end Cslib.Crypto.Birthday
