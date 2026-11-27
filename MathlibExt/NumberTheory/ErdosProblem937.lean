/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/937.lean` (Formal Conjectures), for the definitions and statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.KFull
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Powerful numbers in arithmetic progression

`conjecture_holds` proves Erdős Problem 937. Starting from one explicit progression, a polynomial
transformation gives a progression with larger maximum term. Each term is multiplied by a square,
and a polynomial identity controls common prime factors.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem937Wanted

/-- **Four-term progressions of pairwise coprime powerful numbers.** For natural numbers $a$ and
$d$, the numbers $a$, $a + d$, $a + 2d$, $a + 3d$ form a four-term arithmetic progression of
pairwise coprime powerful numbers when $d > 0$, each of the four numbers is powerful (that is,
$2$-full: nonzero and divisible by $p^2$ for every prime $p$ dividing it), and any two of the
four numbers are coprime. -/
def IsCoprimePowerfulAP4 (a d : ℕ) : Prop :=
  0 < d ∧
  Nat.IsKFull 2 a ∧ Nat.IsKFull 2 (a + d) ∧ Nat.IsKFull 2 (a + 2 * d) ∧
  Nat.IsKFull 2 (a + 3 * d) ∧
  a.Coprime (a + d) ∧ a.Coprime (a + 2 * d) ∧ a.Coprime (a + 3 * d) ∧
  (a + d).Coprime (a + 2 * d) ∧ (a + d).Coprime (a + 3 * d) ∧
  (a + 2 * d).Coprime (a + 3 * d)

/-- **Statement of Erdős Problem 937.** There are infinitely many pairs of natural numbers
$(a, d)$ with $d > 0$ such that the four numbers $a$, $a + d$, $a + 2d$, $a + 3d$ are powerful
(each is nonzero and divisible by $p^2$ for every prime $p$ dividing it) and pairwise coprime;
that is, infinitely many four-term arithmetic progressions of pairwise coprime powerful numbers. -/
def conjecture : Prop :=
  {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite

-- We write the common difference as 2b to keep the transformation integral.
private def term {R : Type*} [CommRing R] (a b : R) (i : Fin 4) : R :=
  a + 2 * (i : ℕ) * b

-- These quartics give the square multipliers for tripling on the double cover
-- branched at the four zeros of the progression.
private def weight {R : Type*} [CommRing R] (a b : R) : Fin 4 → R :=
  ![a ^ 4 + 18 * a ^ 3 * b + 108 * a ^ 2 * b ^ 2 + 264 * a * b ^ 3 + 216 * b ^ 4,
    a ^ 4 + 14 * a ^ 3 * b + 72 * a ^ 2 * b ^ 2 + 144 * a * b ^ 3 + 72 * b ^ 4,
    a ^ 4 + 10 * a ^ 3 * b + 36 * a ^ 2 * b ^ 2 + 72 * a * b ^ 3 + 72 * b ^ 4,
    a ^ 4 + 6 * a ^ 3 * b - 48 * a * b ^ 3 - 72 * b ^ 4]

private def nextStart {R : Type*} [CommRing R] (a b : R) : R :=
  a * weight a b 0 ^ 2

private def nextHalfStep {R : Type*} [CommRing R] (a b : R) : R :=
  b * (weight a b 1 ^ 2 -
    2 * a * (weight a b 1 + weight a b 0) * (a ^ 3 + 9 * a ^ 2 * b + 30 * a * b ^ 2 + 36 * b ^ 3))

private theorem transform_term {R : Type*} [CommRing R] (a b : R) (i : Fin 4) :
    term (nextStart a b) (nextHalfStep a b) i = term a b i * weight a b i ^ 2 := by
  fin_cases i <;> simp [term, nextStart, nextHalfStep, weight] <;> ring

-- A prime dividing the first three transformed terms divides each corresponding
-- product of a term and its weight. This identity then forces it to divide 288 b⁶.
private theorem certificate {R : Type*} [CommRing R] (a b : R) :
    (2 * a + 18 * b) * (term a b 0 * weight a b 0) -
      (7 * a + 26 * b) * (term a b 1 * weight a b 1) +
      (5 * a + 14 * b) * (term a b 2 * weight a b 2) = 288 * b ^ 6 := by
  simp [term, weight]
  ring

private theorem cast_weight (a b : ℤ) (p : ℕ) (i : Fin 4) :
    ((weight a b i : ℤ) : ZMod p) = weight (a : ZMod p) b i := by
  fin_cases i <;> simp [weight]

private theorem cast_start (a b : ℤ) (p : ℕ) :
    ((nextStart a b : ℤ) : ZMod p) = nextStart (a : ZMod p) b := by
  simp [nextStart, cast_weight]

private theorem cast_step (a b : ℤ) (p : ℕ) :
    ((nextHalfStep a b : ℤ) : ZMod p) = nextHalfStep (a : ZMod p) b := by
  simp [nextHalfStep, cast_weight]

private theorem full_mul_sq {x y : ℕ} (hx : Nat.IsKFull 2 x) (hy : y ≠ 0) :
    Nat.IsKFull 2 (x * y ^ 2) := by
  refine ⟨mul_ne_zero hx.1 (pow_ne_zero _ hy), fun p hp h => ?_⟩
  rcases hp.dvd_mul.mp h with h | h
  · exact dvd_mul_of_dvd_left (hx.2 p hp h) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h) 2) _

-- Primitivity rules out a prime dividing every term. The residue conditions handle
-- the primes 2 and 3, which can divide a difference between two indices.
private structure Valid (a b : ℤ) : Prop where
  full : ∀ i, Nat.IsKFull 2 (term a b i).natAbs
  primitive : ∀ p : ℕ, p.Prime → (a : ZMod p) = 0 → (b : ZMod p) ≠ 0
  oddStart : (a : ZMod 2) = 1
  startModThree : (a : ZMod 3) = 1
  stepModThree : (b : ZMod 3) ≠ 0

private theorem transform_primitive {a b : ℤ} (h : Valid a b) (p : ℕ) (hp : p.Prime) :
    ((nextStart a b : ℤ) : ZMod p) = 0 → ((nextHalfStep a b : ℤ) : ZMod p) ≠ 0 := by
  rw [cast_start, cast_step]
  intro hA hB
  have h2 : ∀ y : ZMod 2, nextStart 1 y ≠ 0 := by decide
  have h3 : ∀ y : ZMod 3, nextStart 1 y ≠ 0 := by decide
  let : Fact p.Prime := ⟨hp⟩
  have hprod (i : Fin 4) : term (a : ZMod p) b i * weight (a : ZMod p) b i = 0 := by
    have hz := (transform_term (a : ZMod p) b i).symm
    rw [hA, hB] at hz
    simpa [term, mul_eq_zero, or_comm] using hz
  have hc := certificate (a : ZMod p) b
  rw [hprod, hprod, hprod] at hc
  have hz : (288 : ZMod p) * (b : ZMod p) ^ 6 = 0 := by simpa using hc.symm
  rcases mul_eq_zero.mp hz with hc | hb
  · have hd := (ZMod.natCast_eq_zero_iff 288 p).mp hc
    change p ∣ 2 ^ 5 * 3 ^ 2 at hd
    have he : p = 2 ∨ p = 3 := (hp.dvd_mul.mp hd).imp
      (fun h => (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
      (fun h => (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
    rcases he with rfl | rfl
    · rw [h.oddStart] at hA
      exact h2 _ hA
    · rw [h.startModThree] at hA
      exact h3 _ hA
  · have hb' : (b : ZMod p) = 0 := (pow_eq_zero_iff (by decide)).mp hb
    exact h.primitive p hp (by simpa [nextStart, weight, hb'] using hA) hb'

private theorem Valid.transform {a b : ℤ} (h : Valid a b) :
    Valid (nextStart a b) (nextHalfStep a b) := by
  refine ⟨fun i => ?_, transform_primitive h, ?_, ?_, ?_⟩
  · rw [transform_term, Int.natAbs_mul, Int.natAbs_pow]
    apply full_mul_sq (h.full i)
    intro hz
    have hw := congrArg (fun x : ℤ => (x : ZMod 2)) (Int.natAbs_eq_zero.mp hz)
    rw [cast_weight, h.oddStart] at hw
    exact (by decide : ∀ (y : ZMod 2) (j : Fin 4), weight 1 y j ≠ 0) _ _ hw
  · rw [cast_start, h.oddStart]
    exact (by decide : ∀ y : ZMod 2, nextStart 1 y = 1) _
  · rw [cast_start, h.startModThree]
    exact (by decide : ∀ y : ZMod 3, nextStart 1 y = 1) _
  · rw [cast_step, h.startModThree]
    exact (by decide : ∀ y : ZMod 3, y ≠ 0 → nextHalfStep 1 y ≠ 0) _ h.stepModThree

private theorem Valid.reverse {a b : ℤ} (h : Valid a b) : Valid (a + 6 * b) (-b) := by
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · have he : term (a + 6 * b) (-b) i = term a b i.rev := by
      fin_cases i <;> simp [term, Fin.rev] <;> ring
    rw [he]
    exact h.full _
  · intro p hp ha hb
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_neg, neg_eq_zero] at ha hb
    exact h.primitive p hp (by simpa [hb] using ha) hb
  · push_cast
    simp [h.oddStart, show (6 : ZMod 2) = 0 by decide]
  · push_cast
    simp [h.startModThree, show (6 : ZMod 3) = 0 by decide]
  · simpa using h.stepModThree

private theorem Valid.larger {a b : ℤ} (h : Valid a b) (ha : 0 < a) (hb : 0 < b) :
    ∃ x y : ℤ, Valid x y ∧ 0 < x ∧ 0 < y ∧ a + 6 * b < x + 6 * y := by
  let A := nextStart a b
  let B := nextHalfStep a b
  have h' : Valid A B := h.transform
  have hg : a + 6 * b < A := by
    have h₁ : 1 ≤ a := by omega
    have h₂ : 1 ≤ b := by omega
    have hw : a + 6 * b < weight a b 0 := by
      simp [weight]
      nlinarith only [le_self_pow₀ h₁ (by decide : 4 ≠ 0), le_self_pow₀ h₂ (by decide : 4 ≠ 0),
        hb, show 0 ≤ a ^ 3 * b by positivity, show 0 ≤ a ^ 2 * b ^ 2 by positivity,
        show 0 ≤ a * b ^ 3 by positivity]
    exact hw.trans_le ((le_self_pow₀ (by omega) (by decide : 2 ≠ 0)).trans
      (le_mul_of_one_le_left (sq_nonneg _) h₁))
  have hB : B ≠ 0 := fun he => h'.stepModThree (by simp [he])
  rcases lt_or_gt_of_ne hB with hneg | hpos
  · have hlast : 0 < A + 6 * B := by
      have hn : 0 ≤ term A B 3 := by
        rw [show term A B 3 = _ from transform_term a b 3]
        apply mul_nonneg _ (sq_nonneg _)
        dsimp [term]
        positivity
      norm_num [term] at hn
      have hne : A + 6 * B ≠ 0 := by
        intro he
        simpa [he] using h'.reverse.oddStart
      omega
    exact ⟨A + 6 * B, -B, h'.reverse, hlast, by omega, by omega⟩
  · exact ⟨A, B, h', by omega, hpos, by omega⟩

private theorem Valid.pairwise_mod {a b : ℤ} (h : Valid a b) (p : ℕ) (hp : p.Prime)
    {i j : Fin 4} (hij : i ≠ j) :
    term (a : ZMod p) b i = 0 → term (a : ZMod p) b j ≠ 0 := by
  have h₂ : ∀ (y : ZMod 2) (k : Fin 4), term 1 y k ≠ 0 := by decide
  have h₃ : ∀ (y : ZMod 3) (k l : Fin 4), k ≠ l → term 1 y k = 0 → term 1 y l ≠ 0 := by
    decide
  by_cases hp2 : p = 2
  · subst p
    rw [h.oddStart]
    exact fun hi => (h₂ _ _ hi).elim
  by_cases hp3 : p = 3
  · subst p
    rw [h.startModThree]
    exact h₃ _ _ _ hij
  let : Fact p.Prime := ⟨hp⟩
  have hlt : 4 ≤ p := by have := hp.two_le; omega
  have hdiff : ((i : ℕ) : ZMod p) ≠ (j : ℕ) := by
    intro he
    apply hij
    apply Fin.ext
    simpa [ZMod.val_natCast_of_lt (i.isLt.trans_le hlt),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hlt)] using congrArg ZMod.val he
  have htwo : (2 : ZMod p) ≠ 0 := fun he =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp he))
  intro hi hj
  have hz : 2 * (((i : ℕ) : ZMod p) - (j : ℕ)) * (b : ZMod p) = 0 := by
    unfold term at hi hj
    linear_combination hi - hj
  have hb := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero htwo (sub_ne_zero.mpr hdiff))
  exact h.primitive p hp (by simpa [term, hb] using hi) hb

private theorem Valid.progression {a b : ℕ} (h : Valid a b) (hb : 0 < b) :
    IsCoprimePowerfulAP4 a (2 * b) := by
  let n (i : Fin 4) := a + 2 * (i : ℕ) * b
  have full (i : Fin 4) : Nat.IsKFull 2 (n i) := by
    have he : term (a : ℤ) b i = (n i : ℕ) := by simp [term, n]
    simpa [he] using h.full i
  have cop (i j : Fin 4) (hij : i ≠ j) : (n i).Coprime (n j) := by
    by_contra hn
    obtain ⟨p, hp, hi, hj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have cast (k : Fin 4) : (n k : ZMod p) = term (a : ZMod p) b k := by simp [n, term]
    apply h.pairwise_mod p hp hij
    · simpa only [Int.cast_natCast, ← cast] using (ZMod.natCast_eq_zero_iff _ _).mpr hi
    · simpa only [Int.cast_natCast, ← cast] using (ZMod.natCast_eq_zero_iff _ _).mpr hj
  have h0 : n 0 = a := by simp [n]
  have h1 : n 1 = a + 2 * b := by simp [n]
  have h2 : n 2 = a + 2 * (2 * b) := by simp [n, mul_assoc]
  have h3 : n 3 = a + 3 * (2 * b) := by simp [n]; ring
  unfold IsCoprimePowerfulAP4
  refine ⟨by omega, h0 ▸ full 0, h1 ▸ full 1, h2 ▸ full 2, h3 ▸ full 3,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h0, h1] using cop 0 1 (by decide)
  · simpa only [h0, h2] using cop 0 2 (by decide)
  · simpa only [h0, h3] using cop 0 3 (by decide)
  · simpa only [h1, h2] using cop 1 2 (by decide)
  · simpa only [h1, h3] using cop 1 3 (by decide)
  · simpa only [h2, h3] using cop 2 3 (by decide)

-- Start with 1, 9, 17, 25. Writing u for the ratio of step to start gives
-- (1 + u)(1 + 2u)(1 + 3u) = 17 v² with (u,v) = (8,15).
-- In coordinates (x,y) = (102u,1734v) this is y² = x³ + 187x² + 10404x + 176868.
-- Taking the x-coordinate of 17 times (816,26010) gives a seed in which the third
-- term is 17³ times a square. Only the resulting integer identities are needed below.
private def seed : ℕ × ℕ :=
  let double (P : ℚ × ℚ) :=
    let (x, y) := P
    let m := (3 * x ^ 2 + 374 * x + 10404) / (2 * y)
    let t := m ^ 2 - 187 - 2 * x
    (t, m * (x - t) - y)
  let (x, y) := double (double (double (double (816, 26010))))
  let m := (y - 26010) / (x - 816)
  let u := (m ^ 2 - 187 - x - 816) / 102
  (u.den, u.num.toNat / 2)

private theorem seed_valid : Valid seed.1 seed.2 := by
  refine ⟨fun i => ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · let k (j : Fin 4) : ℕ := if j = 2 then 17 ^ 3 else 1
    let n (j : Fin 4) := (term (seed.1 : ℤ) seed.2 j).natAbs
    let r (j : Fin 4) := Nat.sqrt (n j / k j)
    have eqn : ∀ j, n j = k j * r j ^ 2 := by decide +kernel
    have pos : ∀ j, r j ≠ 0 := by decide +kernel
    have full : Nat.IsKFull 2 (17 ^ 3) := by
      refine ⟨by decide, fun p hp hd => ?_⟩
      have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp
        (hp.dvd_of_dvd_pow hd)
      subst p
      decide
    change Nat.IsKFull 2 (n i)
    rw [eqn]
    apply full_mul_sq _ (pos i)
    by_cases hi : i = 2
    · simpa [k, hi] using full
    · simpa [k, hi] using Nat.isKFull_one 2
  · intro p hp ha
    let : Fact p.Prime := ⟨hp⟩
    have hc : seed.1.Coprime seed.2 := by decide +kernel
    simp only [Int.cast_natCast] at ha ⊢
    exact (ne_zero_or_ne_zero_of_nat_coprime (A := ZMod p) hc).resolve_left (not_not.mpr ha)

private theorem unbounded (m : ℕ) :
    ∃ a b : ℤ, Valid a b ∧ 0 < a ∧ 0 < b ∧ m ≤ a + 6 * b := by
  induction m with
  | zero =>
    have ha : 0 < seed.1 := by decide +kernel
    have hb : 0 < seed.2 := by decide +kernel
    exact ⟨_, _, seed_valid, by exact_mod_cast ha, by exact_mod_cast hb, by positivity⟩
  | succ m ih =>
    obtain ⟨a, b, h, ha, hb, hm⟩ := ih
    obtain ⟨x, y, hxy, hx, hy, hg⟩ := h.larger ha hb
    exact ⟨x, y, hxy, hx, hy, by omega⟩

/--
**Erdős Problem 937 holds (Bajpai–Bennett–Chan).** There are infinitely many pairs of natural
numbers $(a, d)$ with $d > 0$ such that the four numbers $a$, $a + d$, $a + 2d$, $a + 3d$ are
powerful (each is nonzero and divisible by $p^2$ for every prime $p$ dividing it) and pairwise
coprime. That is, there are infinitely many four-term arithmetic progressions of pairwise coprime
powerful numbers.

Source: Prajeet Bajpai, Michael A. Bennett, and Tsz Ho Chan, Arithmetic
progressions in squarefull numbers, International Journal of Number Theory 20 (2024), 19–45,
https://mathscinet.ams.org/mathscinet-getitem?mr=4688726. Moved from
`OpenConjectures/NumberTheory/ErdosProblem937`. Resolved true: Resolved true by
Bajpai–Bennett–Chan; a proof is available in an external Lean development.
-/
public theorem conjecture_holds : conjecture := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image (fun p : ℕ × ℕ => p.1 + 3 * p.2)).bddAbove
  obtain ⟨a, b, h, ha, hb, hg⟩ := unbounded (M + 1)
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  have hmem : (a, 2 * b) ∈ {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2} :=
    h.progression (by omega)
  have hle := hM (Set.mem_image_of_mem (fun p : ℕ × ℕ => p.1 + 3 * p.2) hmem)
  dsimp at hle
  omega

end MathlibExt.NumberTheory.ErdosProblem937Wanted
