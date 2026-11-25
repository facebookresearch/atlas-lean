/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.FactorisationProperties
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Reciprocals of primitive pseudoperfect numbers

`conjecture_holds` proves that the reciprocals of primitive pseudoperfect numbers are summable.

Write σ(a) for the sum of the divisors of a. If ma is primitive pseudoperfect with m > 1,
a representation of ma must use summands whose sum is at least m outside the multiples of m.
Counting those summands gives (1 + σ(a)) ∑_{p ∣ m} 1/p ≥ 1, over distinct primes p.

We bound finite sums of 1/m for which ma is primitive pseudoperfect and every prime factor
of m is at least y. At a prime y, separating the multiples of y gives two sums, with parameters
(a, y + 1) and (ya, y). The majorant for these sums uses the product of (1 − 1/p) over p < y
and the sum of log(p)/(p − 1) over the same primes. When y reaches 4096a + 1, the cofactor
inequality lets us bound the sum by smaller cofactors using the tail estimate
∑_{p ≥ y} log(p)/p² ≤ 4 log(4)/y. Taking a = 1 and y = 2 gives a uniform bound.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted

/-- **Primitive pseudoperfect numbers.** A natural number $n$ lies in $A$, the set of primitive
pseudoperfect numbers, when $n > 0$, $n$ is pseudoperfect (it is positive and equal to the sum of
some set of distinct proper divisors of itself), and no proper divisor of $n$ (a divisor
$m \mid n$ with $m < n$) is pseudoperfect. -/
def InA (n : Nat) : Prop :=
  0 < n ∧ Nat.Pseudoperfect n ∧
    ∀ m, m ∣ n → m < n → ¬Nat.Pseudoperfect m

/-- **Erdős Problem 469 (statement).** The proposition that the reciprocals of the primitive
pseudoperfect numbers have finite sum: the family $(1/n)$, indexed by the natural numbers $n$
that are primitive pseudoperfect, is summable in $\mathbb{R}$. Here $n$ is pseudoperfect if
$n > 0$ and $n$ is the sum of some set of distinct proper divisors of $n$, and primitive
pseudoperfect if moreover no proper divisor of $n$ is pseudoperfect.

Source: [EP-469]. -/
def conjecture : Prop :=
  Summable (fun a : {n : Nat // InA n} => (1 : Real) / (a.val : Real))

open Finset Real

private def sigma (a : ℕ) := ∑ d ∈ a.divisors, d

private theorem quotient_summands {m : ℕ} {s : Finset ℕ}
    (h : ∀ d ∈ s, m ∣ d) :
    m * (∑ d ∈ s.image (· / m), d) = ∑ d ∈ s, d := by
  rw [sum_image]
  · rw [mul_sum]
    exact sum_congr rfl fun d hd ↦ Nat.mul_div_cancel' (h d hd)
  · intro x hx y hy hxy
    simpa only [Nat.mul_div_cancel' (h x hx), Nat.mul_div_cancel' (h y hy)] using
      congrArg (m * ·) hxy

private theorem extension_prime {a m d : ℕ} (hm : 0 < m) (hd : d ∣ m * a) (h : ¬m ∣ d) :
    ∃ p ∈ m.primeFactors, p * d ∣ m * a := by
  obtain ⟨e, f, ⟨k, rfl⟩, hf, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  have hk : k ≠ 1 := by rintro rfl; simp at h
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk
  refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_right hpk _, hm.ne'⟩, ?_⟩
  simpa [mul_left_comm, mul_assoc, mul_comm] using
    Nat.mul_dvd_mul (Nat.mul_dvd_mul_left e hpk) hf

/-- Every divisor of ma outside the multiples of m divides ma/p for some prime p dividing m.
Multiplication by p embeds those divisors back into the divisors of ma. -/
private theorem complementary_sum {a m : ℕ} (hm : 0 < m) (ha : 0 < a) {s : Finset ℕ}
    (hs : s ⊆ (m * a).divisors) :
    (∑ d ∈ s with ¬m ∣ d, (d : ℝ)) ≤
      (sigma (m * a) : ℝ) * ∑ p ∈ m.primeFactors, (1 : ℝ) / p := by
  classical
  let t := s.filter (fun d ↦ ¬m ∣ d)
  let F (p d : ℕ) : ℝ := if p * d ∣ m * a then d else 0
  have hF (p d : ℕ) : 0 ≤ F p d := by dsimp [F]; split <;> positivity
  calc
    ∑ d ∈ t, (d : ℝ) ≤ ∑ d ∈ t, ∑ p ∈ m.primeFactors, F p d := by
      refine sum_le_sum fun d hd ↦ ?_
      obtain ⟨hd, hmd⟩ := mem_filter.mp hd
      obtain ⟨p, hp, hpd⟩ := extension_prime hm (Nat.mem_divisors.mp (hs hd)).1 hmd
      simpa [F, hpd] using
        (single_le_sum (s := m.primeFactors) (f := fun p ↦ F p d) (fun p _ ↦ hF p d) hp)
    _ = ∑ p ∈ m.primeFactors, ∑ d ∈ t, F p d := sum_comm
    _ ≤ ∑ p ∈ m.primeFactors, (sigma (m * a) : ℝ) * (1 / p) := by
      refine sum_le_sum fun p hp ↦ ?_
      have hp0 := (Nat.mem_primeFactors.mp hp).1.pos
      have hR : (0 : ℝ) < p := by positivity
      let u := t.filter (fun d ↦ p * d ∣ m * a)
      have hu : u.image (p * ·) ⊆ (m * a).divisors := by
        intro d hd
        obtain ⟨e, he, rfl⟩ := mem_image.mp hd
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp he).2, Nat.mul_ne_zero hm.ne' ha.ne'⟩
      have hle := (sum_le_sum_of_subset hu (f := id) :
        ∑ d ∈ u.image (p * ·), id d ≤ sigma (m * a))
      rw [sum_image (fun _ _ _ _ hxy ↦ Nat.eq_of_mul_eq_mul_left hp0 hxy)] at hle
      change ∑ d ∈ u, p * d ≤ sigma (m * a) at hle
      rw [← mul_sum] at hle
      rw [← div_eq_mul_one_div, le_div_iff₀ hR, mul_comm]
      change (p : ℝ) * ∑ d ∈ t, (if p * d ∣ m * a then (d : ℝ) else 0) ≤ _
      rw [← sum_filter]
      change (p : ℝ) * ∑ e ∈ u, (e : ℝ) ≤ _
      rw [← Nat.cast_sum, ← Nat.cast_mul]
      exact Nat.cast_le.mpr hle
    _ = _ := (mul_sum ..).symm

private theorem bound_common {a m : ℕ} (hm : 0 < m) (ha : 0 < a) {s : Finset ℕ}
    (hs : s ⊆ (m * a).divisors) :
    ∑ d ∈ s with m ∣ d, d ≤ m * sigma a := by
  let t := s.filter (fun d ↦ m ∣ d)
  have ht : t.image (· / m) ⊆ a.divisors := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := mem_image.mp hd
    obtain ⟨he, hme⟩ := mem_filter.mp he
    apply Nat.mem_divisors.mpr
    refine ⟨Nat.dvd_of_mul_dvd_mul_left hm ?_, ha.ne'⟩
    rw [Nat.mul_div_cancel' hme]
    exact (Nat.mem_divisors.mp (hs he)).1
  change ∑ d ∈ t, d ≤ _
  rw [← quotient_summands (fun d (hd : d ∈ t) ↦ (mem_filter.mp hd).2)]
  exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset ht)

/-- A divisor representation of ma gives a lower bound on the prime reciprocal sum of m. -/
private theorem cofactor_bound {a m : ℕ} (hn : InA (m * a)) (hm : 1 < m) :
    1 ≤ ((sigma a : ℝ) + 1) * ∑ p ∈ m.primeFactors, (1 : ℝ) / p := by
  have ha := Nat.pos_of_mul_pos_left hn.1
  have hm0 := Nat.zero_lt_of_lt hm
  obtain ⟨_, s, hs, he⟩ := hn.2.1
  let t := s.filter (fun d ↦ m ∣ d)
  have ht : t.image (· / m) ⊆ a.properDivisors := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := mem_image.mp hd
    obtain ⟨he, hm'⟩ := mem_filter.mp he
    have ⟨hle, hlt⟩ := Nat.mem_properDivisors.mp (hs he)
    apply Nat.mem_properDivisors.mpr
    constructor
    · apply Nat.dvd_of_mul_dvd_mul_left hm0
      rwa [Nat.mul_div_cancel' hm']
    · apply (Nat.mul_lt_mul_left hm0).mp
      rwa [Nat.mul_div_cancel' hm']
  have hne : ∑ d ∈ t.image (· / m), d ≠ a :=
    fun h ↦ hn.2.2 a (dvd_mul_left a m) (lt_mul_of_one_lt_left ha hm) ⟨ha, _, ht, h⟩
  have heq := quotient_summands (fun d (hd : d ∈ t) ↦ (mem_filter.mp hd).2)
  have hsplit := sum_filter_add_sum_filter_not s (fun d ↦ m ∣ d) id
  simp only [id_eq, he] at hsplit
  have hmle : m ≤ ∑ d ∈ s with ¬m ∣ d, d := by
    change (∑ d ∈ t, d) + _ = _ at hsplit
    have hlt : ∑ d ∈ t.image (· / m), d < a := lt_of_le_of_ne
      ((Nat.le_of_mul_le_mul_left (heq.trans_le (Nat.le.intro hsplit)) hm0)) hne
    have hmul := Nat.mul_le_mul_left m (Nat.succ_le_iff.mpr hlt)
    rw [Nat.mul_succ, heq] at hmul
    omega
  let S := ∑ p ∈ m.primeFactors, (1 : ℝ) / p
  have h1 : (m : ℝ) ≤ (sigma (m * a) : ℝ) * S :=
    le_trans (by rw [← Nat.cast_sum]; exact Nat.cast_le.mpr hmle)
      (complementary_sum hm0 ha (hs.trans Nat.properDivisors_subset_divisors))
  have h2 : (sigma (m * a) : ℝ) ≤ (m : ℝ) * sigma a + sigma (m * a) * S := by
    have h := sum_filter_add_sum_filter_not (m * a).divisors (fun d ↦ m ∣ d) (fun d ↦ (d : ℝ))
    calc
      (sigma (m * a) : ℝ) = _ := (Nat.cast_sum ..).trans h.symm
      _ ≤ _ := add_le_add (by
        rw [← Nat.cast_sum, ← Nat.cast_mul]
        exact Nat.cast_le.mpr (bound_common hm0 ha (Finset.Subset.refl _)))
        (complementary_sum hm0 ha (Finset.Subset.refl _))
  have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ by positivity
  have hmR : (0 : ℝ) < m := by positivity
  by_cases hs1 : 1 ≤ S
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (sigma a)) hS]
  · apply le_of_mul_le_mul_left (a := (m : ℝ)) _ hmR
    nlinarith only [mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr (le_of_not_ge hs1)),
      mul_le_mul_of_nonneg_right h2 hS]

/-! ## Estimates for sums and products over primes -/

private noncomputable def primeTail (s : Finset ℕ) :=
  ∑ p ∈ s, Real.log p / (p : ℝ) ^ 2

private theorem primeTail_block {y : ℕ} (hy : 0 < y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ y ≤ p ∧ p < 2 * y) :
    primeTail s ≤ (2 * Real.log 4) / y := by
  have hy' : (0 : ℝ) < y := by positivity
  have hθ : ∑ p ∈ s, Real.log p ≤ Chebyshev.theta ((2 * y : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hprime, _, hlt⟩ := hs p hp
      exact Nat.mem_primesLE.mpr ⟨hlt.le, hprime⟩
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  calc
    primeTail s ≤ ∑ p ∈ s, Real.log p / (y : ℝ) ^ 2 := by
      refine sum_le_sum fun p hp ↦ ?_
      have h := hs p hp
      have hn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast h.1.one_le)
      exact div_le_div_of_nonneg_left hn (by positivity) (by gcongr; exact_mod_cast h.2.1)
    _ = (∑ p ∈ s, Real.log p) / (y : ℝ) ^ 2 := (sum_div ..).symm
    _ ≤ _ := by
      have h := hθ.trans (Chebyshev.theta_le_log4_mul_x (by positivity))
      push_cast at h
      rw [div_le_div_iff₀ (by positivity) hy']
      nlinarith [mul_le_mul_of_nonneg_right h hy'.le]

/-- Sum the Chebyshev bounds for the intervals [y, 2y), [2y, 4y), and so on. -/
private theorem primeTail_bound {y : ℕ} (hy : 0 < y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ y ≤ p) :
    primeTail s ≤ 4 * Real.log 4 / y := by
  suffices h : ∀ k y : ℕ, 0 < y → ∀ s : Finset ℕ,
      (∀ p ∈ s, p.Prime ∧ y ≤ p ∧ p < 2 ^ k * y) →
      primeTail s ≤ (4 * Real.log 4 / y) * (1 - (1 / 2 : ℝ) ^ k) by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (s.sup id) (by decide : 1 < (2 : ℕ))
    apply (h k y hy s (fun p hp ↦ ⟨(hs p hp).1, (hs p hp).2, ?_⟩)).trans
    · exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))
    · exact (Finset.le_sup (f := id) hp).trans_lt (hk.trans_le (Nat.le_mul_of_pos_right _ hy))
  intro k
  induction k with
  | zero =>
    intro y hy s hs
    have : s = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp ↦ by
      have := hs p hp
      simp at this
      omega
    simp [this, primeTail]
  | succ k ih =>
    intro y hy s hs
    let u := s.filter (fun p ↦ p < 2 * y)
    let v := s.filter (fun p ↦ ¬p < 2 * y)
    have hu := primeTail_block hy u (fun p hp ↦ by
      obtain ⟨hp, hp'⟩ := mem_filter.mp hp
      exact ⟨(hs p hp).1, (hs p hp).2.1, hp'⟩)
    have hv := ih (2 * y) (by omega) v (fun p hp ↦ by
      obtain ⟨hp, hp'⟩ := mem_filter.mp hp
      refine ⟨(hs p hp).1, by omega, ?_⟩
      simpa [pow_succ, mul_assoc] using (hs p hp).2.2)
    have hsum : primeTail u + primeTail v = primeTail s :=
      sum_filter_add_sum_filter_not s _ _
    rw [← hsum]
    apply (add_le_add hu hv).trans_eq
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring

private noncomputable def primeMoment (y : ℕ) :=
  ∑ p ∈ y.primesBelow, Real.log p / ((p : ℝ) - 1)

/-- Mertens’ estimate at modulus one bounds the first logarithmic moment. -/
private theorem primeMoment_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℕ, 2 ≤ y → primeMoment y ≤ Real.log y + C := by
  obtain ⟨B, hB⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le
    (q := 1) 1 isUnit_one
  use |B| + 4 * Real.log 4
  refine ⟨by positivity, fun y hy ↦ ?_⟩
  have h := le_trans (le_abs_self _) (hB y (by exact_mod_cast (by omega : 1 ≤ y)))
  simp only [Nat.floor_natCast, Nat.totient_one, Nat.cast_one, div_one,
    ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply,
    Set.mem_ofPred_eq, Subsingleton.elim (_ : ZMod 1) 1, ite_true] at h
  have hsum : ∑ p ∈ y.primesBelow, Real.log p / p ≤
      ∑ n ∈ Ioc 0 y, ArithmeticFunction.vonMangoldt n / n := by
    calc _ = ∑ p ∈ y.primesBelow, ArithmeticFunction.vonMangoldt p / p := by
              refine sum_congr rfl fun p hp ↦ ?_
              rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesBelow hp)]
         _ ≤ _ := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro p hp
                exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesBelow hp).pos,
                  (Nat.lt_of_mem_primesBelow hp).le⟩
              · intro n _ _
                exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hterm (p : ℕ) (hp : p ∈ y.primesBelow) :
      Real.log p / ((p : ℝ) - 1) ≤ Real.log p / p + 2 * (Real.log p / (p : ℝ) ^ 2) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have h0 : 0 < (p : ℝ) - 1 := by linarith
    field_simp [h0]
    nlinarith [mul_nonneg hlog (sub_nonneg.mpr hp2)]
  have hadd := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hadd
  have ht := primeTail_bound (y := 2) (by decide) y.primesBelow
    (fun p hp ↦ ⟨Nat.prime_of_mem_primesBelow hp, (Nat.prime_of_mem_primesBelow hp).two_le⟩)
  unfold primeTail at ht
  unfold primeMoment
  norm_num at ht
  linarith [le_abs_self B]

private def primeProduct (s : Finset ℕ) : ℕ := ∏ p ∈ s, p

private noncomputable def squarefreeMass (s : Finset ℕ) :=
  ∑ t ∈ s.powerset, ((primeProduct t : ℝ))⁻¹

private noncomputable def logMass (s : Finset ℕ) :=
  ∑ t ∈ s.powerset, Real.log (primeProduct t) / (primeProduct t : ℝ)

private theorem primeProduct_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    0 < primeProduct s := prod_pos fun p hp ↦ (hs p hp).pos

private theorem mass_eq_prod (s : Finset ℕ) :
    squarefreeMass s = ∏ p ∈ s, (1 + (p : ℝ)⁻¹) := by
  simp [squarefreeMass, prod_one_add, primeProduct]

private theorem logMass_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    logMass s ≤ squarefreeMass s * ∑ p ∈ s, Real.log p / ((p : ℝ) - 1) := by
  induction s using Finset.induction_on with
  | empty => simp [logMass, primeProduct]
  | insert p s hp ih =>
    have hpr := hs p (mem_insert_self ..)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq ↦ hs q (mem_insert_of_mem hq)
    have hpos : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
    have hrec : logMass (insert p s) =
        logMass s + (logMass s + Real.log p * squarefreeMass s) / p := by
      unfold logMass squarefreeMass
      rw [sum_powerset_insert hp]
      congr 1
      rw [mul_sum, ← sum_add_distrib, sum_div]
      apply sum_congr rfl
      intro t ht
      have ht' := mem_powerset.mp ht
      have hn : (0 : ℝ) < primeProduct t := by
        exact_mod_cast primeProduct_pos (fun q hq ↦ hs' q (ht' hq))
      rw [show primeProduct (insert p t) = p * primeProduct t from prod_insert (fun h ↦ hp (ht' h)),
        Nat.cast_mul, Real.log_mul hpos.ne' hn.ne']
      ring
    have hmass : squarefreeMass (insert p s) = (1 + (p : ℝ)⁻¹) * squarefreeMass s := by
      rw [mass_eq_prod, prod_insert hp, ← mass_eq_prod]
    have hnon : 0 ≤ squarefreeMass s := sum_nonneg fun _ _ ↦ by positivity
    have hg : Real.log p / p ≤ (1 + (p : ℝ)⁻¹) * (Real.log p / ((p : ℝ) - 1)) := by
      have h0 : 0 < (p : ℝ) - 1 := by linarith
      field_simp [h0, hpos]
      linarith
    rw [hrec, hmass, sum_insert hp]
    simp only [div_eq_mul_inv] at hg ⊢
    have h₁ := mul_le_mul_of_nonneg_left (ih hs') (show 0 ≤ 1 + (p : ℝ)⁻¹ by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hg hnon
    simp only [div_eq_mul_inv] at h₁
    linarith only [h₁, h₂]

private theorem primeMoment_nonneg (y : ℕ) : 0 ≤ primeMoment y := by
  refine sum_nonneg fun p hp ↦ div_nonneg ?_ ?_
  all_goals have h : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le
  · exact Real.log_nonneg h
  · linarith

/-- At least half of the reciprocal mass of the squarefree products lies below exp(T),
by the bound on its logarithmic moment. There the ordinary harmonic sum bounds it. -/
private theorem mass_bound (y : ℕ) :
    squarefreeMass y.primesBelow ≤ 2 + 4 * (1 + primeMoment y) := by
  let s := y.primesBelow
  let T := 2 * (1 + primeMoment y)
  have hT : 0 < T := by dsimp [T]; linarith [primeMoment_nonneg y]
  let u := s.powerset.filter (fun t ↦ (primeProduct t : ℝ) ≤ Real.exp T)
  have hu : u.image primeProduct ⊆ Icc 1 ⌊Real.exp T⌋₊ := by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
    obtain ⟨ht, hle⟩ := mem_filter.mp ht
    have hpos := primeProduct_pos (fun _ hq ↦ Nat.prime_of_mem_primesBelow (mem_powerset.mp ht hq))
    exact mem_Icc.mpr ⟨hpos, Nat.le_floor hle⟩
  have hinj : Set.InjOn primeProduct (↑u) := by
    intro t ht v hv h
    have facts {t : Finset ℕ} (ht : t ∈ u) : (primeProduct t).primeFactors = t :=
      Nat.primeFactors_prod fun _ hq ↦
        Nat.prime_of_mem_primesBelow (mem_powerset.mp (mem_filter.mp ht).1 hq)
    simpa only [facts ht, facts hv] using congrArg Nat.primeFactors h
  have hsmall : ∑ t ∈ u, (primeProduct t : ℝ)⁻¹ ≤ 1 + T := by
    rw [← sum_image (f := fun d : ℕ ↦ (d : ℝ)⁻¹) hinj]
    apply (sum_le_sum_of_subset_of_nonneg hu (fun _ _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))).trans
    have hh := harmonic_floor_le_one_add_log (Real.exp T) (Real.one_le_exp hT.le)
    simpa [harmonic_eq_sum_Icc] using hh
  have hmajor : ∀ t ∈ s.powerset, T * (primeProduct t : ℝ)⁻¹ ≤
      (if (primeProduct t : ℝ) ≤ Real.exp T then T * (primeProduct t : ℝ)⁻¹ else 0) +
        Real.log (primeProduct t) / (primeProduct t : ℝ) := by
    intro t ht
    have hd := primeProduct_pos (fun _ hq ↦ Nat.prime_of_mem_primesBelow (mem_powerset.mp ht hq))
    split_ifs with h
    · have hlog := Real.log_nonneg (x := (primeProduct t : ℝ)) (by exact_mod_cast hd)
      exact le_add_of_nonneg_right (div_nonneg hlog (Nat.cast_nonneg _))
    · rw [zero_add, div_eq_mul_inv]
      gcongr
      simpa using (Real.log_le_log (Real.exp_pos T) (le_of_not_ge h))
  have he := sum_le_sum hmajor
  rw [← mul_sum, sum_add_distrib, ← sum_filter, ← mul_sum] at he
  change T * squarefreeMass s ≤ T * (∑ t ∈ u, (primeProduct t : ℝ)⁻¹) + logMass s at he
  have hm : logMass s ≤ squarefreeMass s * primeMoment y :=
    logMass_le fun _ hp ↦ Nat.prime_of_mem_primesBelow hp
  have hz : 0 ≤ squarefreeMass s := sum_nonneg fun _ _ ↦ by positivity
  change squarefreeMass s ≤ _
  suffices hz' : squarefreeMass s ≤ 2 * (1 + T) by
    dsimp only [T] at hz'
    linarith
  apply le_of_mul_le_mul_left (a := T / 2) _ (by positivity)
  have h₁ := mul_le_mul_of_nonneg_left hsmall hT.le
  have h₂ : primeMoment y ≤ T / 2 := by dsimp [T]; linarith
  linarith only [he, h₁, hm, mul_le_mul_of_nonneg_right h₂ hz]

private noncomputable def sieveWeight (y : ℕ) := ∏ p ∈ y.primesBelow, (1 - (p : ℝ)⁻¹)

private theorem sieveWeight_pos (y : ℕ) : 0 < sieveWeight y := by
  refine prod_pos fun p hp ↦ sub_pos.mpr ?_
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt)

/-- The product on the right is the product of 1 − 1/p² for primes p < y. Extending the
product to every integer from 2 to y − 1 gives the telescoping lower bound on the left. -/
private theorem weight_mul_mass {y : ℕ} (hy : 2 ≤ y) :
    (y : ℝ) / (2 * (y - 1 : ℝ)) ≤ sieveWeight y * squarefreeMass y.primesBelow := by
  induction y, hy using Nat.le_induction with
  | base => norm_num [sieveWeight, mass_eq_prod, show Nat.primesBelow 2 = ∅ by decide]
  | succ y hy ih =>
    have h : (2 : ℝ) ≤ y := by exact_mod_cast hy
    have h1 : 0 < (y : ℝ) - 1 := by linarith
    have h0 : 0 < (y : ℝ) := by linarith
    have heq : (y + 1 : ℝ) / (2 * y) =
        ((1 - (y : ℝ)⁻¹) * (1 + (y : ℝ)⁻¹)) * ((y : ℝ) / (2 * (y - 1))) := by
      field_simp
    have hprod : sieveWeight (y + 1) * squarefreeMass (y + 1).primesBelow =
        (if y.Prime then (1 - (y : ℝ)⁻¹) * (1 + (y : ℝ)⁻¹) else 1) *
          (sieveWeight y * squarefreeMass y.primesBelow) := by
      simp only [sieveWeight, mass_eq_prod, Nat.primesBelow_succ]
      have hnot : y ∉ y.primesBelow := fun h ↦ (Nat.lt_of_mem_primesBelow h).false
      split_ifs <;> simp [hnot, mul_mul_mul_comm]
    rw [hprod, Nat.cast_add_one, add_sub_cancel_right, heq]
    have hpos : 0 < 1 - (y : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
    refine (mul_le_mul_of_nonneg_left ih (mul_nonneg hpos.le (by positivity))).trans ?_
    apply mul_le_mul_of_nonneg_right _
      (mul_nonneg (sieveWeight_pos _).le (sum_nonneg fun _ _ ↦ by positivity))
    split_ifs <;> nlinarith [sq_nonneg (y : ℝ)⁻¹]

/-! ## A bound for the reciprocal sums with fixed divisor and prime cutoff -/

private noncomputable def abundancy (a : ℕ) : ℝ := sigma a / (a : ℝ)

private theorem one_le_abundancy {a : ℕ} (ha : 0 < a) : 1 ≤ abundancy a := by
  rw [abundancy, one_le_div (by positivity)]
  exact_mod_cast (single_le_sum (f := id) (fun _ _ ↦ Nat.zero_le _)
    (Nat.mem_divisors_self a ha.ne') :
    a ≤ sigma a)

private theorem sigma_eq_mul {a : ℕ} (ha : 0 < a) : (sigma a : ℝ) = (a : ℝ) * abundancy a := by
  unfold abundancy
  field_simp

private theorem abundancy_le {a : ℕ} (ha : 0 < a) : abundancy a ≤ 1 + Real.log a := by
  have heq : abundancy a = ∑ d ∈ a.divisors, (d : ℝ)⁻¹ := by
    rw [abundancy, sigma, ← Nat.sum_div_divisors a, Nat.cast_sum, Finset.sum_div]
    refine sum_congr rfl fun d hd ↦ ?_
    have hh := (Nat.mem_divisors.mp hd).1
    have hd0 := Nat.pos_of_mem_divisors hd
    rw [Nat.cast_div hh (by positivity)]
    field_simp
  rw [heq]
  apply le_trans _ (harmonic_le_one_add_log a)
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact sum_le_sum_of_subset_of_nonneg (fun d hd ↦ mem_Icc.mpr
    ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd ha (Nat.mem_divisors.mp hd).1⟩)
    (fun _ _ _ ↦ by positivity)

private theorem abundancy_mul_prime {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    abundancy (p * a) ≤ (1 + (p : ℝ)⁻¹) * abundancy a := by
  have hsub : {d ∈ (p * a).divisors | ¬p ∣ d} ⊆ a.divisors := by
    intro d hd
    obtain ⟨hd, hpd⟩ := mem_filter.mp hd
    exact Nat.mem_divisors.mpr ⟨(hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_left
      (Nat.mem_divisors.mp hd).1, ha.ne'⟩
  have hle : sigma (p * a) ≤ p * sigma a + sigma a :=
    (sum_filter_add_sum_filter_not (p * a).divisors (fun d ↦ p ∣ d) id).symm.trans_le
      (Nat.add_le_add (bound_common hp.pos ha (Subset.refl _)) (sum_le_sum_of_subset hsub))
  have hcast : (sigma (p * a) : ℝ) ≤ p * (sigma a : ℝ) + sigma a := by exact_mod_cast hle
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  simp only [abundancy, Nat.cast_mul]
  field_simp
  linarith

/-- This bounded decreasing factor absorbs the possible increase of the abundancy at ap. -/
private noncomputable def correction (y : ℕ) : ℝ :=
  if y = 2 then 10 else 1 + 4 / ((y : ℝ) - 1)

private theorem correction_bounds {y : ℕ} (hy : 2 ≤ y) : 1 ≤ correction y ∧ correction y ≤ 10 := by
  have h : (2 : ℝ) ≤ y := by exact_mod_cast hy
  unfold correction
  split_ifs
  · norm_num
  · constructor
    · linarith [div_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (show 0 ≤ (y : ℝ) - 1 by linarith)]
    · have hh : 4 / ((y : ℝ) - 1) ≤ 9 := (div_le_iff₀ (by linarith)).mpr (by linarith)
      linarith

private theorem correction_step {p : ℕ} (hp : 2 ≤ p) :
    (1 - (p : ℝ)⁻¹) * correction (p + 1) +
        (p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) * correction p ≤ correction p := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · norm_num [correction]
  have h : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h₀ : 0 < (p : ℝ) := by linarith
  have h₁ : 0 < (p : ℝ) - 1 := by linarith
  simp [correction, show p + 1 ≠ 2 by omega, show p ≠ 2 by omega]
  field_simp [h₀, h₁]
  nlinarith

private theorem correction_anti {p : ℕ} (hp : 2 ≤ p) : correction (p + 1) ≤ correction p := by
  by_cases h : p = 2
  · subst p; norm_num [correction]
  suffices 4 / (p : ℝ) ≤ 4 / ((p : ℝ) - 1) by
    simpa [correction, h, show p + 1 ≠ 2 by omega] using this
  have h' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  gcongr
  · linarith
  · linarith

/-- Multiplying this expression by the sieve weight gives the majorant for the induction. -/
private noncomputable def allowance (A : ℝ) (a y : ℕ) : ℝ :=
  Real.log a - primeMoment y + A * abundancy a * correction y

private theorem allowance_lower {A C : ℝ} (hC : ∀ y : ℕ, 2 ≤ y → primeMoment y ≤ Real.log y + C)
    (hA : 2 * (Real.log 4097 + C) ≤ A) (hA0 : 0 ≤ A)
    {a y : ℕ} (ha : 0 < a) (hy : 2 ≤ y) (hya : y ≤ 4096 * a + 1) :
    A * abundancy a / 2 ≤ allowance A a y := by
  have hlog : Real.log y ≤ Real.log 4097 + Real.log a := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show y ≤ 4097 * a by omega)
  have hD := one_le_abundancy ha
  have hpos : 0 ≤ A * abundancy a := mul_nonneg hA0 (by linarith)
  unfold allowance
  linarith only [hlog, hC y hy, hA, mul_le_mul_of_nonneg_left hD hA0,
    mul_le_mul_of_nonneg_left (correction_bounds hy).1 hpos]

private theorem allowance_upper {A : ℝ} (hA : 1 ≤ A) {p a y : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hap : a ≤ p) (hy : 2 ≤ y) :
    allowance A (p * a) y ≤ (62 * A) * Real.log p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp2
  have hhalf : 1 / 2 ≤ Real.log (p : ℝ) := by linarith [Real.log_two_gt_d9]
  have halog := Real.log_le_log (by positivity : (0 : ℝ) < a)
    (show (a : ℝ) ≤ p by exact_mod_cast hap)
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hD : abundancy (p * a) ≤ 6 * Real.log p := calc
    _ ≤ (1 + (p : ℝ)⁻¹) * abundancy a := abundancy_mul_prime hp ha
    _ ≤ 2 * (1 + Real.log a) := mul_le_mul (by linarith) (abundancy_le ha)
      (zero_le_one.trans (one_le_abundancy ha)) (by norm_num)
    _ ≤ _ := by linarith
  have hbound : A * abundancy (p * a) * correction y ≤ A * (6 * Real.log p) * 10 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hD (by linarith)) (correction_bounds hy).2
      (by linarith [(correction_bounds hy).1]) (by positivity)
  rw [allowance, Nat.cast_mul, Real.log_mul hp0.ne' (by positivity)]
  linarith only [hbound, halog, primeMoment_nonneg y,
    mul_le_mul_of_nonneg_right hA (show 0 ≤ Real.log (p : ℝ) by linarith)]

private theorem weight_pos_bound {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : ℕ, 2 ≤ y → primeMoment y ≤ Real.log y + C) {y : ℕ} (hy : 2 ≤ y) :
    1 ≤ (12 + 8 * C) * sieveWeight y * (1 + Real.log y) := by
  have hy' : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hw := sieveWeight_pos y
  have hl : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hm := weight_mul_mass hy
  have hhalf : (1 / 2 : ℝ) ≤ y / (2 * ((y : ℝ) - 1)) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hmass : squarefreeMass y.primesBelow ≤ (6 + 4 * C) * (1 + Real.log y) := by
    nlinarith only [mass_bound y, hC y hy, hl, mul_nonneg hC0 hl]
  nlinarith only [hhalf.trans hm, mul_le_mul_of_nonneg_left hmass hw.le]

private theorem allowance_at_member {C A : ℝ} (hC : ∀ y : ℕ, 2 ≤ y → primeMoment y ≤ Real.log y + C)
    (hA : C + 2 ≤ A) (hA0 : 0 ≤ A) {a y : ℕ} (ha : InA a) (hy : 2 ≤ y)
    (hw : ∃ p ∈ a.primeFactors, y ≤ p) :
    (1 + Real.log y) / 2 ≤ allowance A a y := by
  obtain ⟨p, hp, hyp⟩ := hw
  obtain ⟨hpr, ⟨d, rfl⟩, _⟩ := Nat.mem_primeFactors.mp hp
  have hd : 0 < d := Nat.pos_of_mul_pos_left ha.1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  have hd0 : (0 : ℝ) < d := by positivity
  have hp_le := cofactor_bound ha hpr.one_lt
  rw [hpr.primeFactors, sum_singleton] at hp_le
  have h1 : (p : ℝ) ≤ (sigma d : ℝ) + 1 := by
    rwa [← div_eq_mul_one_div, le_div_iff₀ hp0, one_mul] at hp_le
  have h2 : (sigma d : ℝ) ≤ d * (d : ℝ) := by
    rw [sigma_eq_mul hd]
    exact mul_le_mul_of_nonneg_left ((abundancy_le hd).trans
      (by linarith [Real.log_le_sub_one_of_pos hd0])) hd0.le
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (p : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by nlinarith
  have hlog := Real.log_le_log hp0 h3
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  norm_num at hlog
  have hlog' := Real.log_le_log (by positivity : (0 : ℝ) < y)
    (show (y : ℝ) ≤ p by exact_mod_cast hyp)
  have hD := one_le_abundancy ha.1
  have hcor : 1 ≤ abundancy (p * d) * correction y :=
    one_le_mul_of_one_le_of_one_le hD (correction_bounds hy).1
  rw [allowance, Nat.cast_mul, Real.log_mul hp0.ne' hd0.ne', mul_assoc]
  linarith only [hlog, hlog', hC y hy, hA, Real.log_two_lt_d9, mul_le_mul_of_nonneg_left hcor hA0]

private theorem weight_prime_step {y : ℕ} (hy : y.Prime) :
    sieveWeight (y + 1) = (1 - (y : ℝ)⁻¹) * sieveWeight y := by
  simp [sieveWeight, Nat.primesBelow_succ, hy, Nat.notMem_primesBelow]

/-- At a prime p the logarithmic terms balance exactly, and the correction bounds both branches. -/
private theorem weighted_step {A : ℝ} (hA : 0 ≤ A) {a p : ℕ} (ha : 0 < a) (hp : p.Prime) :
    sieveWeight (p + 1) * allowance A a (p + 1) +
        (p : ℝ)⁻¹ * (sieveWeight p * allowance A (p * a) p) ≤
      sieveWeight p * allowance A a p := by
  have h0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have h1 : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hD := abundancy_mul_prime hp ha
  have hmoment : primeMoment (p + 1) = Real.log p / ((p : ℝ) - 1) + primeMoment p := by
    simp [primeMoment, Nat.primesBelow_succ, hp, Nat.notMem_primesBelow]
  have hbal : (1 - (p : ℝ)⁻¹) * (Real.log a - primeMoment (p + 1)) +
      (p : ℝ)⁻¹ * (Real.log (p * a : ℕ) - primeMoment p) = Real.log a - primeMoment p := by
    rw [hmoment, Nat.cast_mul, Real.log_mul h0.ne' (by positivity)]
    field_simp [show ((p : ℝ) - 1) ≠ 0 by linarith]
    ring
  have hcor : (1 - (p : ℝ)⁻¹) * (abundancy a * correction (p + 1)) +
      (p : ℝ)⁻¹ * (abundancy (p * a) * correction p) ≤ abundancy a * correction p := by
    have hmul := mul_le_mul_of_nonneg_left (correction_step hp.two_le)
      (zero_le_one.trans (one_le_abundancy ha))
    have hcorrect : 0 ≤ correction p := zero_le_one.trans (correction_bounds hp.two_le).1
    nlinarith only [hmul,
      mul_le_mul_of_nonneg_right hD (mul_nonneg (inv_nonneg.mpr h0.le) hcorrect)]
  have h : (1 - (p : ℝ)⁻¹) * allowance A a (p + 1) +
      (p : ℝ)⁻¹ * allowance A (p * a) p ≤ allowance A a p := by
    unfold allowance
    linarith only [hbal, mul_le_mul_of_nonneg_left hcor hA]
  rw [weight_prime_step hp]
  linarith only [mul_le_mul_of_nonneg_left h (sieveWeight_pos p).le]

private theorem weighted_skip {A : ℝ} (hA : 0 ≤ A) {a y : ℕ} (ha : 0 < a)
    (hy : 2 ≤ y) (hp : ¬y.Prime) :
    sieveWeight (y + 1) * allowance A a (y + 1) ≤ sieveWeight y * allowance A a y := by
  simp only [sieveWeight, allowance, primeMoment, Nat.primesBelow_succ, hp, ↓reduceIte]
  apply mul_le_mul_of_nonneg_left _ (sieveWeight_pos y).le
  exact add_le_add_right (mul_le_mul_of_nonneg_left (correction_anti hy)
    (mul_nonneg hA (zero_le_one.trans (one_le_abundancy ha)))) _

private noncomputable def recipMass (s : Finset ℕ) := ∑ m ∈ s, (m : ℝ)⁻¹

private def quotients (p : ℕ) (s : Finset ℕ) := (s.filter (p ∣ ·)).image (· / p)

private theorem mem_quotients {p : ℕ} (hp : 0 < p) {s : Finset ℕ} {d : ℕ} :
    d ∈ quotients p s ↔ p * d ∈ s := by
  constructor
  · intro hd
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hd
    obtain ⟨hm, hpm⟩ := mem_filter.mp hm
    rwa [Nat.mul_div_cancel' hpm]
  · intro hd
    exact mem_image.mpr ⟨p * d, mem_filter.mpr ⟨hd, dvd_mul_right ..⟩, Nat.mul_div_cancel_left _ hp⟩

private theorem recip_quotients {p : ℕ} (hp : 0 < p) (s : Finset ℕ) :
    recipMass (s.filter (p ∣ ·)) = (p : ℝ)⁻¹ * recipMass (quotients p s) := by
  unfold recipMass quotients
  rw [sum_image, mul_sum]
  · refine sum_congr rfl fun m hm ↦ ?_
    have h := (mem_filter.mp hm).2
    rw [Nat.cast_div h (by positivity)]
    field_simp
  · intro m hm n hn he
    simpa only [Nat.mul_div_cancel' (mem_filter.mp hm).2, Nat.mul_div_cancel' (mem_filter.mp hn).2]
      using congrArg (p * ·) he

/-- Charge each reciprocal to the primes dividing its cofactor, then remove each charged prime. -/
private theorem rough_mass_le {a : ℕ} {s : Finset ℕ} (hs : ∀ m ∈ s, InA (m * a)) (hne : 1 ∉ s) :
    recipMass s ≤ ((sigma a : ℝ) + 1) *
      ∑ p ∈ s.biUnion Nat.primeFactors, (p : ℝ)⁻¹ ^ 2 * recipMass (quotients p s) := by
  let P := s.biUnion Nat.primeFactors
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    obtain ⟨_, _, hp⟩ := mem_biUnion.mp hp
    exact (Nat.mem_primeFactors.mp hp).1
  have hgo (m : ℕ) (hm : m ∈ s) :
      (m : ℝ)⁻¹ ≤ ((sigma a : ℝ) + 1) * ∑ p ∈ P, (if p ∣ m then (p : ℝ)⁻¹ * (m : ℝ)⁻¹ else 0) := by
    have hmpos := Nat.pos_of_mul_pos_right (hs m hm).1
    have he : m.primeFactors = P.filter (· ∣ m) := by
      ext p
      constructor
      · intro hp
        exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨m, hm, hp⟩, (Nat.mem_primeFactors.mp hp).2.1⟩
      · intro hp
        obtain ⟨hp, hpm⟩ := mem_filter.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hpm, hmpos.ne'⟩
    have hm1 : 1 < m := by
      have : m ≠ 1 := fun h ↦ hne (h ▸ hm)
      omega
    have hh := mul_le_mul_of_nonneg_right (cofactor_bound (hs m hm) hm1)
      (inv_nonneg.mpr (Nat.cast_nonneg m (α := ℝ)))
    rw [← sum_filter, ← he, ← sum_mul]
    simpa only [one_mul, one_div, mul_assoc] using hh
  unfold recipMass
  calc
    _ ≤ _ := sum_le_sum hgo
    _ = ((sigma a : ℝ) + 1) * ∑ p ∈ P, ∑ m ∈ s, (if p ∣ m then (p : ℝ)⁻¹ * (m : ℝ)⁻¹ else 0) := by
      rw [← mul_sum, sum_comm]
    _ = _ := by
      congr 1
      refine sum_congr rfl fun p hp ↦ ?_
      rw [← sum_filter, ← mul_sum]
      change (p : ℝ)⁻¹ * recipMass (s.filter (p ∣ ·)) = _
      rw [recip_quotients (hprime p hp).pos, sq, mul_assoc]
      rfl

/-- Uniform bound for finite sets of cofactors m of primitive pseudoperfect products ma.
The last hypothesis records the prime just removed when m reaches 1. -/
private theorem mass_bound_rough {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y : ℕ, 2 ≤ y → primeMoment y ≤ Real.log y + C)
    (N a y : ℕ) (s : Finset ℕ) (ha : 0 < a) (hy : 2 ≤ y) (hya : y ≤ 4096 * a + 1)
    (hN : ∀ m ∈ s, m ≤ N) (hs : ∀ m ∈ s, InA (m * a))
    (hrough : ∀ m ∈ s, ∀ p ∈ m.primeFactors, y ≤ p)
    (hunit : 1 ∈ s → ∃ p ∈ a.primeFactors, y ≤ p) :
    recipMass s ≤ (24 + 16 * C) *
      (sieveWeight y * allowance (2 * (Real.log 4097 + C + 2)) a y) := by
  let A := 2 * (Real.log 4097 + C + 2)
  let L := 24 + 16 * C
  have hlog : 0 ≤ Real.log 4097 := Real.log_nonneg (by norm_num)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hA0 := zero_le_one.trans hA
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hW := sieveWeight_pos y
  have hlower := allowance_lower hC (A := A) (by dsimp [A]; linarith) hA0 ha hy hya
  change recipMass s ≤ L * (sieveWeight y * allowance A a y)
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [recipMass, sum_empty]
    exact mul_nonneg hL (mul_nonneg hW.le (le_trans (by
      have := one_le_abundancy ha
      positivity) hlower))
  -- Once a itself is primitive pseudoperfect, no larger multiple can be primitive.
  by_cases h1 : 1 ∈ s
  · have haA : InA a := by simpa using hs 1 h1
    have he : s = {1} := by
      apply eq_singleton_iff_unique_mem.mpr
      refine ⟨h1, fun m hm ↦ ?_⟩
      have hh := hs m hm
      have hmpos := Nat.pos_of_mul_pos_right hh.1
      by_contra h
      exact hh.2.2 a (dvd_mul_left ..) (lt_mul_of_one_lt_left ha (by omega)) haA.2.1
    have ht := allowance_at_member hC (A := A) (by dsimp [A]; linarith) hA0 haA hy (hunit h1)
    have hw := weight_pos_bound hC0 hC hy
    simp only [he, recipMass, sum_singleton, Nat.cast_one, inv_one]
    have hh := mul_le_mul_of_nonneg_left ht (mul_nonneg hL hW.le)
    dsimp [L] at hh ⊢
    linarith only [hw, hh]
  have hNpos : 0 < N := by
    obtain ⟨m, hm⟩ := hne
    exact (Nat.pos_of_mul_pos_right (hs m hm).1).trans_le (hN m hm)
  have ihp (p : ℕ) (hp : p.Prime) (hyp : y ≤ p) :
      recipMass (quotients p s) ≤ L * (sieveWeight y * allowance A (p * a) y) := by
    have hp0 := hp.pos
    refine mass_bound_rough hC0 hC (N - 1) (p * a) y _ (Nat.mul_pos hp0 ha) hy ?_ ?_ ?_ ?_ ?_
    · exact hya.trans (by nlinarith [Nat.le_mul_of_pos_left a hp0])
    · intro m hm
      have hm' := (mem_quotients hp0).mp hm
      have hmp := Nat.pos_of_mul_pos_right (hs (p * m) hm').1
      have hm0 := Nat.pos_of_mul_pos_left hmp
      have := lt_mul_of_one_lt_left hm0 hp.one_lt
      have := hN _ hm'
      omega
    · intro m hm
      simpa [mul_left_comm, mul_assoc] using hs (p * m) ((mem_quotients hp0).mp hm)
    · intro m hm q hq
      have hpm := (mem_quotients hp0).mp hm
      exact hrough _ hpm q (Nat.primeFactors_mono (dvd_mul_left ..)
        (Nat.pos_of_mul_pos_right (hs _ hpm).1).ne' hq)
    · intro _
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right .., (Nat.mul_pos hp0 ha).ne'⟩, hyp⟩
  -- Below the cutoff we separate the multiples of the next prime.
  by_cases hcut : y < 4096 * a + 1
  · let u := s.filter (fun m ↦ ¬ (y.Prime ∧ y ∣ m))
    have ihu : recipMass u ≤ L * (sieveWeight (y + 1) * allowance A a (y + 1)) := by
      refine mass_bound_rough hC0 hC N a (y + 1) u ha (by omega) hcut ?_ ?_ ?_ ?_
      · exact fun m hm ↦ hN _ (mem_filter.mp hm).1
      · exact fun m hm ↦ hs _ (mem_filter.mp hm).1
      · intro m hm p hp
        obtain ⟨hm, hnd⟩ := mem_filter.mp hm
        have hle := hrough _ hm _ hp
        have hneq : y ≠ p := by
          rintro rfl
          exact hnd ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1⟩
        omega
      · exact fun hm ↦ (h1 (mem_filter.mp hm).1).elim
    by_cases hp : y.Prime
    · have hsum : recipMass s = recipMass u + (y : ℝ)⁻¹ * recipMass (quotients y s) := by
        rw [← recip_quotients hp.pos]
        simpa [recipMass, u, hp, add_comm] using
          (sum_filter_add_sum_filter_not s (fun m ↦ y ∣ m) (fun m ↦ (m : ℝ)⁻¹)).symm
      rw [hsum]
      have hdiv := mul_le_mul_of_nonneg_left (ihp y hp le_rfl)
        (inv_nonneg.mpr (Nat.cast_nonneg y (α := ℝ)))
      linarith only [ihu, hdiv, mul_le_mul_of_nonneg_left (weighted_step hA0 ha hp) hL]
    · have hu : u = s := by simp [u, hp]
      rw [← hu]
      exact ihu.trans (mul_le_mul_of_nonneg_left (weighted_skip hA0 ha hy hp) hL)
  · -- At the cutoff the cofactor inequality supplies a second factor of 1/p.
    let P := s.biUnion Nat.primeFactors
    have hpy (p : ℕ) (hp : p ∈ P) : p.Prime ∧ y ≤ p := by
      obtain ⟨m, hm, hp⟩ := mem_biUnion.mp hp
      exact ⟨(Nat.mem_primeFactors.mp hp).1, hrough _ hm _ hp⟩
    have htail := primeTail_bound (show 0 < y by omega) P hpy
    have hterm (p : ℕ) (hp : p ∈ P) :
        (p : ℝ)⁻¹ ^ 2 * recipMass (quotients p s) ≤
          (L * sieveWeight y * (62 * A)) * (Real.log p / (p : ℝ) ^ 2) := by
      obtain ⟨hp, hyp⟩ := hpy _ hp
      have h := (ihp p hp hyp).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (allowance_upper hA hp ha (by omega) hy) hW.le) hL)
      calc
        _ ≤ (p : ℝ)⁻¹ ^ 2 * (L * (sieveWeight y * ((62 * A) * Real.log p))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
        _ = _ := by rw [div_eq_mul_inv, inv_pow]; ring
    have hsum := sum_le_sum hterm
    rw [← mul_sum] at hsum
    have hconst : 0 ≤ L * sieveWeight y * (62 * A) := by positivity
    have h' := (rough_mass_le hs h1).trans
      (mul_le_mul_of_nonneg_left (hsum.trans (mul_le_mul_of_nonneg_left htail hconst))
        (by positivity))
    have hyR : (4096 : ℝ) * a ≤ y := by exact_mod_cast (show 4096 * a ≤ y by omega)
    have hD := one_le_abundancy ha
    have h1σ : (sigma a : ℝ) + 1 ≤ 2 * a * abundancy a := by
      rw [sigma_eq_mul ha]
      have ha1 : 1 ≤ (a : ℝ) := by exact_mod_cast ha
      nlinarith [one_le_mul_of_one_le_of_one_le ha1 hD]
    have hsmall : ((sigma a : ℝ) + 1) * (62 * (4 * Real.log 4) / y) ≤ abundancy a / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      have hpos : 0 ≤ abundancy a := by linarith
      nlinarith only [mul_le_mul_of_nonneg_left hlog4
        (show (0 : ℝ) ≤ sigma a + 1 by positivity), h1σ, mul_le_mul_of_nonneg_right hyR hpos]
    calc
      recipMass s ≤ _ := h'
      _ = L * sieveWeight y * A *
          (((sigma a : ℝ) + 1) * (62 * (4 * Real.log 4) / y)) := by ring
      _ ≤ L * sieveWeight y * A * (abundancy a / 2) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hlower (mul_nonneg hL hW.le)]
termination_by (N, 4096 * a + 1 - y)
decreasing_by
  all_goals first | exact Prod.Lex.left _ _ (by omega) | exact Prod.Lex.right _ (by omega)

/--
**Reciprocals of primitive pseudoperfect numbers have finite sum.** Call a natural number
$n$ pseudoperfect if $n > 0$ and $n$ is the sum of some set of distinct proper divisors of $n$,
and primitive pseudoperfect if moreover no proper divisor of $n$ is pseudoperfect. Then the
family $(1/n)$, indexed by the primitive pseudoperfect numbers $n$, is summable in $\mathbb{R}$,
that is, the sum of $1/n$ over all primitive pseudoperfect numbers $n$ is finite.

This is Erdős Problem 469, resolved true.

Source: plby/lean-proofs, Erdos469.lean, commit 68da20b96673899166e94638f5a7fffeb7231d35 (2026),
https://github.com/plby/lean-proofs/blob/68da20b96673899166e94638f5a7fffeb7231d35/src/latest/ErdosProblems/Erdos469.lean.
Moved from `OpenConjectures/NumberTheory/DivisorSumReciprocalConvergence`.
-/
theorem conjecture_holds : conjecture := by
  obtain ⟨C, hC0, hC⟩ := primeMoment_bound
  apply summable_of_sum_le (c := (24 + 16 * C) * (sieveWeight 2 *
    allowance (2 * (Real.log 4097 + C + 2)) 1 2)) (fun _ ↦ by positivity)
  intro u
  let s := u.image Subtype.val
  have hs (m : ℕ) (hm : m ∈ s) : InA (m * 1) := by
    obtain ⟨x, _, rfl⟩ := mem_image.mp hm
    simpa using x.property
  have hh := mass_bound_rough hC0 hC (s.sup id) 1 2 s (by decide) (by decide) (by decide)
    (fun m hm ↦ le_sup (f := id) hm) hs
    (fun _ _ _ hp ↦ (Nat.mem_primeFactors.mp hp).1.two_le) (fun h ↦ by
      have hh := (hs 1 h).2.1
      exact absurd hh (by decide))
  simpa [recipMass, s, sum_image Subtype.val_injective.injOn, one_div] using hh

end MathlibExt.NumberTheory.DivisorSumReciprocalConvergenceWanted
