/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Horadam recurrence for composition sums

We obtain the recurrence by clearing the denominator in the generating function of the
weighted composition sums and comparing coefficients of degree at least three.
-/

namespace MetaMathlibExt

open scoped BigOperators

namespace horadam_composition_sum_recurrence

open PowerSeries

private def prepend (n : ℕ) (p : Σ i : Fin (n + 1), Composition (n - i.val)) :
    Composition (n + 1) :=
  ((Composition.single (p.1.val + 1) (Nat.succ_pos _)).append p.2).cast (by
    have := p.1.isLt
    omega)

-- Splitting off the first block gives the composition/series identity, as in
-- `MathlibExt.NumberTheory.GibonacciCompositionSum`.
private lemma prepend_bijective (n : ℕ) : Function.Bijective (prepend n) := by
  constructor
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    have hblocks := congrArg Composition.blocks h
    change (i.val + 1) :: c.blocks = (j.val + 1) :: d.blocks at hblocks
    obtain ⟨hij, hcd⟩ := List.cons.inj hblocks
    have : i = j := Fin.ext (by omega)
    subst j
    rw [Composition.ext hcd]
  · rintro ⟨l, hpos, hsum⟩
    obtain _ | ⟨b, l⟩ := l
    · simp at hsum
    cases b with
    | zero => simp at hpos
    | succ i =>
      simp only [List.sum_cons] at hsum
      let c : Composition (n - i) :=
        ⟨l, fun h => hpos (List.mem_cons_of_mem _ h), by omega⟩
      exact ⟨⟨⟨i, by omega⟩, c⟩, rfl⟩

private noncomputable def compositionSum (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ c : Composition n, (c.blocks.map w).prod

private lemma compositionSeries (w : ℕ → ℂ) :
    mk (compositionSum w) = 1 + X * (mk (fun j => w (j + 1)) * mk (compositionSum w)) := by
  ext n
  cases n with
  | zero => simp [compositionSum, (Composition.blocks_eq_nil _).mpr rfl, composition_card]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, coeff_mk, coeff_one, ite_eq_right (Nat.succ_ne_zero _),
      zero_add, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (mk fun k => w (k + 1)) * coeff j (mk (compositionSum w)))]
    simp only [coeff_mk]
    let e := Equiv.ofBijective (prepend n) (prepend_bijective n)
    unfold compositionSum
    rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    change (((i.val + 1) :: c.blocks).map w).prod = _
    rw [List.map_cons, List.prod_cons]

private def blockWeight (q d e : ℂ) (j : ℕ) : ℂ := ((q + e) * j - e) * d ^ (j - 1)

private lemma compositionSum_eq (q d e : ℂ) (n : ℕ) :
    compositionSum (blockWeight q d e) n =
      ∑ c : Composition n, d ^ (n - c.length) *
        ∏ i : Fin c.length, ((q + e) * (c.blocksFun i : ℂ) - e) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have hsum : ∑ i : Fin c.length, (c.blocksFun i - 1) = n - c.length := by
    rw [Finset.sum_tsub_distrib _ (fun i _ => c.one_le_blocksFun i), c.sum_blocksFun]
    simp
  rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, blockWeight, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hsum, mul_comm]

-- The block series is X * W. Its geometric denominator is (1 - dX)^2.
private lemma weightedSeries (q d e : ℂ) :
    mk (compositionSum (blockWeight q d e)) *
        (1 - C (2 * d + q) * X - C (e * d - d ^ 2) * X ^ 2) =
      1 - C (2 * d) * X + C (d ^ 2) * X ^ 2 := by
  let S := mk (compositionSum (blockWeight q d e))
  let W := mk (fun j => blockWeight q d e (j + 1))
  let T : ℂ⟦X⟧ := 1 - C d * X
  change S * _ = _
  have hT : T ^ 2 = 1 - C (2 * d) * X + C (d ^ 2) * X ^ 2 := by
    rw [show 2 * d = d + d by ring, map_add, map_pow]
    dsimp [T]
    ring
  have hW : W * T ^ 2 = C q + C (e * d) * X := by
    rw [hT, mul_add, mul_sub, mul_one, ← mul_assoc, ← mul_assoc, pow_two X, ← mul_assoc]
    ext n
    rcases n with _ | _ | n
    · simp [W, blockWeight]
    · simp [W, blockWeight]
      ring
    · simp only [map_add (coeff _), map_sub (coeff _), coeff_mk, coeff_succ_mul_X, coeff_mul_C,
        coeff_C, Nat.succ_ne_zero, ite_false, W, blockWeight, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_one, pow_succ]
      ring
  have hS : S - X * (W * S) = 1 := sub_eq_iff_eq_add.mpr (compositionSeries _)
  have hden : (1 - C (2 * d + q) * X - C (e * d - d ^ 2) * X ^ 2 : ℂ⟦X⟧) =
      T ^ 2 - X * (C q + C (e * d) * X) := by
    simp only [hT, map_add, map_sub]
    ring
  calc
    S * _ = (S - X * (W * S)) * T ^ 2 := by rw [hden, ← hW]; ring
    _ = _ := by rw [hS, one_mul, hT]

private lemma weightedSum_recurrence (q d e : ℂ) (n : ℕ) (hn : 3 ≤ n) :
    let S := compositionSum (blockWeight q d e)
    S n = (2 * d + q) * S (n - 1) + (e * d - d ^ 2) * S (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  dsimp only
  have h := weightedSeries q d e
  rw [mul_sub, mul_sub, mul_one, ← mul_assoc, ← mul_assoc] at h
  have hrec := congrArg (coeff (k + 3)) h
  simp (disch := omega) only [map_add (coeff _), map_sub (coeff _), coeff_mk,
    coeff_succ_mul_X, coeff_mul_C, coeff_mul_X_pow', coeff_one, coeff_C, Nat.succ_ne_zero,
    ite_false, zero_sub, neg_zero, zero_add, ite_eq_left (show 2 ≤ k + 3 by omega),
    show k + 3 - 2 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega] at hrec ⊢
  linear_combination hrec

end horadam_composition_sum_recurrence

open horadam_composition_sum_recurrence in
/-- **Horadam composition sums satisfy the Horadam recurrence.** Let $p, q, r, s$ be complex
numbers with $(q - r)^2 = 4s(p - 1)$ and $4s(p - 1) \ne 0$, put $e = 2ps/(r - q)$, and for every
natural number $m$ let
$$w_m = \sum_c \bigl((r - q)/2\bigr)^{m - \ell(c)} \prod_{j \in c} \bigl((q + e) j - e\bigr),$$
where $c$ runs over the compositions of $m$ (ordered tuples of positive integers with sum $m$),
$\ell(c)$ is the number of parts of $c$ and the product runs over the parts $j$ of $c$. Then
$w_n = r w_{n-1} + s w_{n-2}$ for every $n \ge 3$.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 1 (`integers-2025-A97-thm-1`). -/
public theorem horadam_composition_sum_recurrence (p q r s : ℂ)
    (h : (q - r) ^ 2 = 4 * s * (p - 1)) (h0 : 4 * s * (p - 1) ≠ 0) (n : ℕ) (hn : 3 ≤ n) :
    ∑ c : Composition n, ((r - q) / 2) ^ (n - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) =
      r * ∑ c : Composition (n - 1), ((r - q) / 2) ^ (n - 1 - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) +
      s * ∑ c : Composition (n - 2), ((r - q) / 2) ^ (n - 2 - c.length) *
        ∏ i : Fin c.length,
          ((q + 2 * p * s / (r - q)) * (c.blocksFun i : ℂ) - 2 * p * s / (r - q)) := by
  let d := (r - q) / 2
  let e := 2 * p * s / (r - q)
  have hne : r - q ≠ 0 := by
    intro hz
    have hqr := sub_eq_zero.mp hz
    exact h0 (by simpa [hqr] using h.symm)
  have hr : 2 * d + q = r := by
    dsimp [d]
    ring
  have he : e * d = p * s := by
    dsimp [e, d]
    field_simp [hne]
  have hd : d ^ 2 = s * (p - 1) := by
    dsimp [d]
    linear_combination (1 / 4 : ℂ) * h
  have hs : e * d - d ^ 2 = s := by
    rw [he, hd]
    ring
  have hrec := weightedSum_recurrence q d e n hn
  dsimp only at hrec
  rw [hr, hs] at hrec
  simpa only [compositionSum_eq, d, e] using hrec

end MetaMathlibExt
