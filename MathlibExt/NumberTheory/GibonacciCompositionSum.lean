/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import MathlibExt.NumberTheory.GibonacciNumber
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.GibonacciCassini

/-!
# Translates of Gibonacci sequences as composition sums

We prove that shifted Gibonacci numbers are weighted sums over ordered compositions.
-/

namespace MetaMathlibExt

open scoped BigOperators

namespace gibonacci_add_eq_composition_sum

open Finset PowerSeries

private def prepend (n : ℕ) (p : Σ i : Fin (n + 1), Composition (n - i.val)) :
    Composition (n + 1) :=
  ((Composition.single (p.1.val + 1) (Nat.succ_pos _)).append p.2).cast (by
    have := p.1.isLt
    omega)

-- A nonempty composition is determined by its first part and the remaining composition.
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

private lemma compositionSum_zero (w : ℕ → ℂ) : compositionSum w 0 = 1 := by
  simp [compositionSum, (Composition.blocks_eq_nil _).mpr rfl, composition_card]

private lemma compositionSum_succ (w : ℕ → ℂ) (n : ℕ) :
    compositionSum w (n + 1) =
      ∑ i ∈ range (n + 1), w (i + 1) * compositionSum w (n - i) := by
  let e := Equiv.ofBijective (prepend n) (prepend_bijective n)
  unfold compositionSum
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  change (((i.val + 1) :: c.blocks).map w).prod = _
  rw [List.map_cons, List.prod_cons]

private lemma compositionSeries (w : ℕ → ℂ) :
    mk (compositionSum w) = 1 + X * (mk (fun j => w (j + 1)) * mk (compositionSum w)) := by
  ext n
  cases n with
  | zero => simp [compositionSum_zero]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, coeff_mk, coeff_one, ite_eq_right (Nat.succ_ne_zero _),
      zero_add, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => coeff i (mk fun k => w (k + 1)) * coeff j (mk (compositionSum w)))]
    simpa only [coeff_mk] using compositionSum_succ w n

private def weight (a D x : ℂ) (j : ℕ) : ℂ := (D * j + a) * x ^ (j - 1)

-- Clearing the geometric denominators gives a quadratic equation for the composition series.
private lemma weightedSeries (a D x : ℂ) :
    let S := mk (compositionSum (weight a D x))
    S * (1 - C (2 * x + (a + D)) * X + C (x ^ 2 + a * x) * X ^ 2) =
      1 - C (2 * x) * X + C (x ^ 2) * X ^ 2 := by
  let S := mk (compositionSum (weight a D x))
  let W := mk (fun j => weight a D x (j + 1))
  let T : ℂ⟦X⟧ := 1 - C x * X
  change S * _ = _
  have hT : T ^ 2 = 1 - C (2 * x) * X + C (x ^ 2) * X ^ 2 := by
    rw [show 2 * x = x + x by ring, map_add, map_pow]
    dsimp [T]
    ring
  have hW : W * T ^ 2 = C (a + D) - C (a * x) * X := by
    rw [hT, mul_add, mul_sub, mul_one, ← mul_assoc, ← mul_assoc, pow_two X, ← mul_assoc]
    ext n
    rcases n with _ | _ | n
    · simp [W, weight]
      ring
    · simp [W, weight]
      ring
    · simp only [map_add (coeff _), map_sub (coeff _), coeff_mk, coeff_succ_mul_X, coeff_mul_C,
        coeff_C, Nat.succ_ne_zero, ite_false, W, weight, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_one, sub_zero, pow_succ]
      ring
  have hS : S - X * (W * S) = 1 := sub_eq_iff_eq_add.mpr (compositionSeries _)
  have hden : (1 - C (2 * x + (a + D)) * X + C (x ^ 2 + a * x) * X ^ 2 : ℂ⟦X⟧) =
      T ^ 2 - X * (C (a + D) - C (a * x) * X) := by
    simp only [hT, map_add]
    ring
  calc
    S * _ = (S - X * (W * S)) * T ^ 2 := by rw [hden, ← hW]; ring
    _ = _ := by rw [hS, one_mul, hT]

private lemma weightedSum (a D x : ℂ) :
    let S := compositionSum (weight a D x)
    S 1 = a + D ∧ S 2 = (a + D) ^ 2 + (a + 2 * D) * x ∧
      ∀ n : ℕ, S (n + 3) =
        (2 * x + (a + D)) * S (n + 2) - (x ^ 2 + a * x) * S (n + 1) := by
  let S := compositionSum (weight a D x)
  have h := weightedSeries a D x
  change mk S * _ = _ at h
  rw [mul_add, mul_sub, mul_one, ← mul_assoc, ← mul_assoc] at h
  have hs1 : S 1 = a + D := by
    change compositionSum (weight a D x) (0 + 1) = _
    rw [compositionSum_succ]
    simp [weight, compositionSum_zero, add_comm]
  refine ⟨hs1, ?_, fun n => ?_⟩
  · have h2 := congrArg (coeff 2) h
    simp (disch := omega) only [map_add (coeff _), map_sub (coeff _), coeff_mk,
      coeff_succ_mul_X, coeff_mul_C, coeff_mul_X_pow', coeff_one, coeff_C, hs1,
      show S 0 = 1 from compositionSum_zero _, Nat.sub_self, ite_true] at h2
    norm_num at h2
    linear_combination h2
  · have hrec := congrArg (coeff (n + 3)) h
    simp (disch := omega) only [map_add (coeff _), map_sub (coeff _), coeff_mk,
      coeff_succ_mul_X, coeff_mul_C, coeff_mul_X_pow', coeff_one, coeff_C, Nat.succ_ne_zero,
      ite_false, zero_sub, neg_zero, zero_add, ite_eq_left (show 2 ≤ n + 3 by omega),
      show n + 3 - 2 = n + 1 by omega] at hrec
    linear_combination hrec

private lemma weight_prod (a D x : ℂ) {n : ℕ} (c : Composition n) :
    (c.blocks.map (weight a D x)).prod =
      x ^ (n - c.length) * ∏ i : Fin c.length, (D * (c.blocksFun i : ℂ) + a) := by
  have hsum : ∑ i : Fin c.length, (c.blocksFun i - 1) = n - c.length := by
    rw [Finset.sum_tsub_distrib _ (fun i _ => c.one_le_blocksFun i), c.sum_blocksFun]
    simp
  rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_apply, weight, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, hsum, mul_comm]

private lemma cast_gibonacci_add_two (y z : ℤ) (k : ℕ) :
    (gibonacciNumber y z (k + 2) : ℂ) =
      (gibonacciNumber y z (k + 1) : ℂ) + gibonacciNumber y z k := by
  rw [gibonacciNumber, Int.cast_add]

private lemma gibonacci_succ_pos_and_lt (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (hm : 3 ≤ m) :
    0 < gibonacciNumber y z (m + 1) ∧
      gibonacciNumber y z m < gibonacciNumber y z (m + 1) := by
  have hnonneg (k : ℕ) : 0 ≤ gibonacciNumber y z k := by
    induction k using Nat.twoStepInduction with
    | zero => exact hy
    | one => exact hz
    | more _ ih₀ ih₁ => exact add_nonneg ih₁ ih₀
  have hpos (k : ℕ) : 0 < gibonacciNumber y z (k + 2) := by
    induction k with
    | zero =>
      change 0 < z + y
      omega
    | succ k ih => exact add_pos_of_pos_of_nonneg ih (hnonneg (k + 1))
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  exact ⟨hpos (k + 2), lt_add_of_pos_right _ (hpos k)⟩

-- Match the first two coefficients and the recurrence of the rescaled sequence.
private lemma scaledSum (a b D : ℂ) (hD : D ^ 2 = a ^ 2 + a * b - b ^ 2)
    (hb : b ≠ 0) (hA : b + 2 * (a + D) ≠ 0) (g : ℕ → ℂ)
    (hg₁ : g 1 = b) (hg₂ : g 2 = b + a)
    (hg : ∀ k, g (k + 2) = g (k + 1) + g k) (n : ℕ) (hn : 1 ≤ n) :
    let B := a + D
    let A := b + 2 * B
    compositionSum (weight a D (-B ^ 2 / A)) n =
      A / b ^ 2 * (b * B / A) ^ n * g n := by
  let B := a + D
  let A := b + 2 * B
  let x := -B ^ 2 / A
  let q := b * B / A
  let S := compositionSum (weight a D x)
  change S n = A / b ^ 2 * q ^ n * g n
  change A ≠ 0 at hA
  obtain ⟨hs₁, hs₂, hs⟩ := weightedSum a D x
  change S 1 = B at hs₁
  change S 2 = B ^ 2 + (a + 2 * D) * x at hs₂
  change ∀ k, S (k + 3) = (2 * x + B) * S (k + 2) -
    (x ^ 2 + a * x) * S (k + 1) at hs
  have hq : 2 * x + B = q := by
    dsimp only [x, q]
    field_simp [hA]
    dsimp only [A]
    ring
  have hq₂ : x ^ 2 + a * x = -(q ^ 2) := by
    dsimp only [x, q]
    field_simp [hA]
    dsimp only [A, B]
    linear_combination (a + D) ^ 2 * hD
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [hs₁, hg₁, pow_one]
    dsimp only [q, B]
    field_simp [hA, hb]
  | one =>
    change S 2 = A / b ^ 2 * q ^ 2 * g 2
    rw [hs₂, hg₂]
    dsimp only [x, q]
    rw [div_pow, mul_pow]
    field_simp [hA, hb]
    dsimp only [A, B]
    ring
  | more k ih₀ ih₁ =>
    rw [hs k, hq, hq₂, ih₁, ih₀, hg (k + 1)]
    simp only [pow_succ]
    ring

end gibonacci_add_eq_composition_sum

open gibonacci_add_eq_composition_sum in
/-- **Translates of a Gibonacci sequence as composition sums.** Let $y$ and $z$ be non-negative
integers, not both zero, and let $(G_k)$ be the Gibonacci sequence with $G_0 = y$ and $G_1 = z$.
Let $m \ge 3$ and $n \ge 1$, and let $D$ be a complex number with
$D^2 = (-1)^m (y^2 + yz - z^2)$. Then
$$G_{n+m} = \frac{(G_{m+2} + G_m + 2D)^{n-1}}{G_{m+1}^{n-2} (G_m + D)^n} \sum_c
\left(-\frac{(G_m + D)^2}{G_{m+2} + G_m + 2D}\right)^{n-r} \prod_{i=1}^{r} (D c_i + G_m),$$
where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

The two square roots $D$ give the two sign choices of identity (28) of the source.

Source: Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical
Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 2 (`integers-2025-A97-thm-2`). -/
public theorem gibonacci_add_eq_composition_sum (y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : y ≠ 0 ∨ z ≠ 0) (m : ℕ) (hm : 3 ≤ m) (D : ℂ)
    (hD : D ^ 2 = (-1) ^ m * ((y : ℂ) ^ 2 + y * z - z ^ 2)) (n : ℕ) (hn : 1 ≤ n) :
    (gibonacciNumber y z (n + m) : ℂ) =
      ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D) ^ (n - 1) /
        ((gibonacciNumber y z (m + 1) : ℂ) ^ ((n : ℤ) - 2) *
          ((gibonacciNumber y z m : ℂ) + D) ^ n) *
      ∑ c : Composition n,
        (-((gibonacciNumber y z m : ℂ) + D) ^ 2 /
          ((gibonacciNumber y z (m + 2) : ℂ) + gibonacciNumber y z m + 2 * D)) ^
            (n - c.length) *
        ∏ i : Fin c.length, (D * (c.blocksFun i : ℂ) + gibonacciNumber y z m) := by
  let g (k : ℕ) := (gibonacciNumber y z (k + m) : ℂ)
  let a := (gibonacciNumber y z m : ℂ)
  let b := (gibonacciNumber y z (m + 1) : ℂ)
  let B := a + D
  let A := b + 2 * B
  let x := -B ^ 2 / A
  have hnext : (gibonacciNumber y z (m + 2) : ℂ) = b + a :=
    cast_gibonacci_add_two y z m
  have hg (k : ℕ) : g (k + 2) = g (k + 1) + g k := by
    simpa only [g, add_right_comm k] using cast_gibonacci_add_two y z (k + m)
  obtain ⟨hbpos, hablt⟩ := gibonacci_succ_pos_and_lt y z hy hz hyz m hm
  have hab : a ≠ b := by
    dsimp only [a, b]
    exact_mod_cast hablt.ne
  have hb : b ≠ 0 := by
    dsimp only [b]
    exact_mod_cast hbpos.ne'
  have hCassini : (gibonacciNumber y z (m + 2) : ℂ) * a - b ^ 2 =
      (-1 : ℂ) ^ (m + 1) * ((z : ℂ) ^ 2 - y * z - y ^ 2) := by
    have h := gibonacci_cassini_of_pos y z (m + 1) (by omega)
    rw [Nat.add_sub_cancel] at h
    dsimp only [a, b]
    exact_mod_cast h
  have hD' : D ^ 2 = a ^ 2 + a * b - b ^ 2 := by
    rw [hnext, pow_succ] at hCassini
    linear_combination hD - hCassini
  have hB : B ≠ 0 := by
    intro h
    change a + D = 0 at h
    have hDa : D = -a := by linear_combination h
    rw [hDa] at hD'
    exact mul_ne_zero hb (sub_ne_zero.mpr hab) (by linear_combination -hD')
  have hA : A ≠ 0 := by
    intro h
    change b + 2 * (a + D) = 0 at h
    have hDa : D = -(b + 2 * a) / 2 := by
      linear_combination (1 / 2 : ℂ) * h
    rw [hDa] at hD'
    exact mul_ne_zero hb hb (by linear_combination (4 / 5 : ℂ) * hD')
  have hscaled := scaledSum a b D hD' hb hA g (by simp only [g, b, add_comm 1 m])
    (by simpa only [g, add_comm 2 m] using hnext) hg n hn
  change compositionSum (weight a D x) n = A / b ^ 2 * (b * B / A) ^ n * g n at hscaled
  have hnorm :
      A ^ (n - 1) / (b ^ ((n : ℤ) - 2) * B ^ n) * (A / b ^ 2 * (b * B / A) ^ n) =
        1 := by
    rw [zpow_sub₀ hb, zpow_natCast, zpow_ofNat, div_pow, mul_pow]
    conv in A ^ n => rw [show A ^ n = A ^ (n - 1) * A by
      rw [← pow_succ, Nat.sub_add_cancel hn]]
    field_simp [hb, hA, hB]
  have hsum :
      (∑ c : Composition n, x ^ (n - c.length) *
        ∏ i : Fin c.length, (D * (c.blocksFun i : ℂ) + a)) =
      compositionSum (weight a D x) n :=
    Finset.sum_congr rfl fun c _ => (weight_prod a D x c).symm
  rw [hnext, show b + a + a + 2 * D = A by dsimp only [A, B]; ring]
  change g n = A ^ (n - 1) / (b ^ ((n : ℤ) - 2) * B ^ n) * _
  rw [hsum, hscaled, ← mul_assoc, hnorm, one_mul]

end MetaMathlibExt
