/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPolynomial.BernsteinBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coordinatewise Bernstein degree elevation

Degree elevation preserves the polynomial and forms convex combinations of
neighbouring coefficients. Reference: A. P. Smith, *Enclosure Methods for
Systems of Polynomial Equations and Inequalities* (2012), §3.3.3, equation (3.28),
https://d-nb.info/1028327854/34. The tensor recurrence applies this identity
in one coordinate, leaving the other binomial factors unchanged.
-/

@[expose] public section

namespace MvPolynomial

private theorem choose_ratio_elevate (n j d : ℕ) (hd : d ≤ n) (hj : j ≤ n) :
    ((j + 1).choose d : ℝ) / (n + 1).choose d =
      ((j + 1 : ℕ) : ℝ) / (n + 1) * ((j.choose d : ℝ) / n.choose d) +
      ((n - j : ℕ) : ℝ) / (n + 1) * (((j + 1).choose d : ℝ) / n.choose d) := by
  by_cases hdj : d ≤ j + 1
  · have hn : (n.choose d : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hd)
    have hn1 : ((n + 1).choose d : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : d ≤ n + 1))
    have hN' := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq n d)
    have hJ' := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq j d)
    simp only [Nat.cast_mul, Nat.cast_sub (show d ≤ n + 1 by omega),
      Nat.cast_add, Nat.cast_one] at hN'
    simp only [Nat.cast_mul, Nat.cast_sub hdj, Nat.cast_add, Nat.cast_one] at hJ'
    rw [Nat.cast_sub hj]
    push_cast
    field_simp
    nlinarith [congrArg (fun x : ℝ => x * ((j + 1).choose d : ℝ)) hN',
      congrArg (fun x : ℝ => x * ((n + 1).choose d : ℝ)) hJ']
  · have h1 : (j + 1).choose d = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h0 : j.choose d = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h0]

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem prod_choose_update (n k : ι → ℕ) (r : ι) (j : ℕ) (d : ι →₀ ℕ) :
    (∏ i, ((Function.update k r j i).choose (d i) : ℝ) / (n i).choose (d i)) =
      ((j.choose (d r) : ℝ) / (n r).choose (d r)) *
        ∏ i ∈ univ.erase r, ((k i).choose (d i) : ℝ) / (n i).choose (d i) := by
  rw [← mul_prod_erase _ _ (mem_univ r)]
  congr 1
  · simp
  · apply prod_congr rfl
    intro i hi
    simp [Function.update_of_ne (ne_of_mem_erase hi)]

/-- For a real polynomial in finitely many variables, raising a single
coordinate degree preserves the coefficient at its lower endpoint. No degree
bound on the polynomial is required; indices and degrees in the other
coordinates are arbitrary. -/
theorem bernsteinCoeff_elevate_zero {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    {r : ι} (k : ι → ℕ) :
    bernsteinCoeff (Function.update n r (n r + 1)) p (Function.update k r 0) =
      bernsteinCoeff n p (Function.update k r 0) := by
  simp only [bernsteinCoeff, sum_def]
  apply sum_congr rfl
  intro d hd
  rw [prod_choose_update, prod_choose_update]
  by_cases hdr : d r = 0
  · simp only [hdr, Nat.choose_zero_right, Nat.cast_one, div_one, one_mul]
    congr 1
    apply prod_congr rfl
    intro i hi
    simp [Function.update_of_ne (ne_of_mem_erase hi)]
  · simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hdr)]

/-- For a real polynomial in finitely many variables, raising one coordinate
degree by one forms the usual weighted combination of adjacent coefficients.
For `j ≤ n r`, the new coefficient at `j+1` has
weights `(j+1)/(n r+1)` and `(n r-j)/(n r+1)`. At the upper endpoint the second
weight is zero, so its out-of-range coefficient contributes nothing. Only the
polynomial degree in coordinate `r` needs to be at most `n r`. -/
theorem bernsteinCoeff_elevate_succ {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    {r : ι} (k : ι → ℕ) (j : ℕ) (hp : p.degreeOf r ≤ n r) (hj : j ≤ n r) :
    bernsteinCoeff (Function.update n r (n r + 1)) p (Function.update k r (j + 1)) =
      ((j + 1 : ℕ) : ℝ) / (n r + 1) * bernsteinCoeff n p (Function.update k r j) +
      ((n r - j : ℕ) : ℝ) / (n r + 1) *
        bernsteinCoeff n p (Function.update k r (j + 1)) := by
  simp only [bernsteinCoeff, sum_def, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [prod_choose_update, prod_choose_update, prod_choose_update]
  have heq : (∏ i ∈ univ.erase r, ((k i).choose (d i) : ℝ) /
      ((Function.update n r (n r + 1)) i).choose (d i)) =
      ∏ i ∈ univ.erase r, ((k i).choose (d i) : ℝ) / (n i).choose (d i) := by
    apply prod_congr rfl
    intro i hi
    simp [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [heq, Function.update_self,
    choose_ratio_elevate (n r) j (d r) ((degreeOf_le_iff.mp hp) d hd) hj]
  ring

/-- For a real polynomial in finitely many variables, raising one coordinate
degree preserves its upper endpoint coefficient. The polynomial degree in
that coordinate must not exceed the original degree. -/
theorem bernsteinCoeff_elevate_top {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    {r : ι} (k : ι → ℕ) (hp : p.degreeOf r ≤ n r) :
    bernsteinCoeff (Function.update n r (n r + 1)) p
        (Function.update k r (n r + 1)) =
      bernsteinCoeff n p (Function.update k r (n r)) := by
  have hn : (n r : ℝ) + 1 ≠ 0 := by positivity
  simpa [hn] using bernsteinCoeff_elevate_succ k (n r) hp le_rfl

/-- For a real polynomial in finitely many variables with `p.degreeOf r ≤ n r`,
if every valid degree-`n` Bernstein coefficient lies in `[L,U]`, then every
valid coefficient after raising degree `n r` by one also lies in `[L,U]`.
Original indices satisfy `k i ≤ n i`; elevated indices satisfy `k r ≤ n r+1`
and `k i ≤ n i` elsewhere. Both endpoints of the elevated coordinate are included. -/
theorem bernsteinCoeff_elevate_mem_Icc {n : ι → ℕ} {p : MvPolynomial ι ℝ}
    {r : ι} {L U : ℝ} (hp : p.degreeOf r ≤ n r)
    (hb : ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → bernsteinCoeff n p k ∈ Set.Icc L U)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ Function.update n r (n r + 1) i) :
    bernsteinCoeff (Function.update n r (n r + 1)) p k ∈ Set.Icc L U := by
  have hupdate (j : ℕ) (hj : j ≤ n r) : ∀ i, Function.update k r j i ≤ n i := by
    intro i
    by_cases hi : i = r
    · subst i
      simpa using hj
    · simpa [Function.update_of_ne hi] using hk i
  have hkr : k r ≤ n r + 1 := by simpa using hk r
  rcases hj : k r with _ | j
  · have heq : Function.update k r 0 = k := by
      simp [← hj]
    rw [← heq, bernsteinCoeff_elevate_zero]
    exact hb _ (hupdate 0 (Nat.zero_le _))
  · have heq : Function.update k r (j + 1) = k := by
      simp [← hj]
    have hjn : j ≤ n r := by omega
    by_cases htop : j = n r
    · rw [← heq, htop, bernsteinCoeff_elevate_top k hp]
      exact hb _ (hupdate _ le_rfl)
    · have hj1 : j + 1 ≤ n r := by omega
      have hleft := hb _ (hupdate j hjn)
      have hright := hb _ (hupdate (j + 1) hj1)
      have hpos : (0 : ℝ) < n r + 1 := by positivity
      have hweights : ((j + 1 : ℕ) : ℝ) / (n r + 1) +
          ((n r - j : ℕ) : ℝ) / (n r + 1) = 1 := by
        rw [← add_div, Nat.cast_sub hjn]
        push_cast
        field_simp
        ring
      rw [← heq, bernsteinCoeff_elevate_succ k j hp hjn]
      constructor
      · have h1 := mul_le_mul_of_nonneg_left hleft.1
          (show (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) / (n r + 1) by positivity)
        have h2 := mul_le_mul_of_nonneg_left hright.1
          (show (0 : ℝ) ≤ ((n r - j : ℕ) : ℝ) / (n r + 1) by positivity)
        nlinarith [congrArg (fun a : ℝ => a * L) hweights]
      · have h1 := mul_le_mul_of_nonneg_left hleft.2
          (show (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) / (n r + 1) by positivity)
        have h2 := mul_le_mul_of_nonneg_left hright.2
          (show (0 : ℝ) ≤ ((n r - j : ℕ) : ℝ) / (n r + 1) by positivity)
        nlinarith [congrArg (fun a : ℝ => a * U) hweights]

omit [DecidableEq ι] in
/-- For a real polynomial in finitely many variables with coordinate degrees
at most `n`, increasing the bound to any `m ≥ n` preserves every interval
containing all valid degree-`n` Bernstein coefficients: every coefficient
with index `k i ≤ m i` lies in that same interval. Degrees may be zero, and
the variable type may be empty. -/
theorem bernsteinCoeff_mem_Icc_of_le {n m : ι → ℕ} {p : MvPolynomial ι ℝ}
    {L U : ℝ} (hp : ∀ i, p.degreeOf i ≤ n i) (hnm : ∀ i, n i ≤ m i)
    (hb : ∀ k : ι → ℕ, (∀ i, k i ≤ n i) → bernsteinCoeff n p k ∈ Set.Icc L U)
    (k : ι → ℕ) (hk : ∀ i, k i ≤ m i) : bernsteinCoeff m p k ∈ Set.Icc L U := by
  classical
  generalize hs : ∑ i, m i = s
  induction s using Nat.strong_induction_on generalizing m k with
  | ind s ih =>
    by_cases heq : n = m
    · subst m
      exact hb k hk
    · obtain ⟨r, hr⟩ : ∃ r, n r < m r := by
        by_contra! h
        exact heq (funext fun i => Nat.le_antisymm (hnm i) (h i))
      let m' := Function.update m r (m r - 1)
      have hn' : ∀ i, n i ≤ m' i := by
        intro i
        by_cases hi : i = r
        · subst i
          simp only [m', Function.update_self]
          omega
        · simpa [m', Function.update_of_ne hi] using hnm i
      have hm' : ∀ i, m' i ≤ m i := by
        intro i
        by_cases hi : i = r
        · subst i
          simp [m']
        · simp [m', Function.update_of_ne hi]
      have hsum : ∑ i, m' i < s := by
        rw [← hs]
        apply sum_lt_sum (fun i _ => hm' i)
        exact ⟨r, mem_univ r, by simp only [m', Function.update_self]; omega⟩
      have hrecover : Function.update m' r (m' r + 1) = m := by
        have hrpos : 0 < m r := by omega
        simp [m', Nat.sub_add_cancel hrpos]
      rw [← hrecover]
      exact bernsteinCoeff_elevate_mem_Icc ((hp r).trans (hn' r))
        (fun l hl => ih (∑ i, m' i) hsum hn' l hl rfl) k (by simpa [hrecover] using hk)

end MvPolynomial
