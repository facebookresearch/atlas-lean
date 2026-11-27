/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.TaylorCoefficientComposition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Tests for Faà di Bruno's formula for Taylor coefficients

At order `0`, the right-hand side reduces to `f (g a)`.
The first-order case is the chain rule, and the second-order case is checked
numerically for `f x = x ^ 3` and `g x = x ^ 2` at `1`, where the two
partitions of `2` contribute `3` and `12`. A direct computation of the second
derivative of the composite `x ^ 6`, which does not use the formula, gives the
same Taylor coefficient `15`.
-/

@[expose] public section

namespace MetaMathlibExt.TaylorCoefficientCompositionTests

open MetaMathlibExt

private theorem parts_two (π : Nat.Partition 2) : π.parts = {2} ∨ π.parts = {1, 1} := by
  obtain ⟨l, hl⟩ : ∃ l : List ℕ, (↑l : Multiset ℕ) = π.parts :=
    ⟨π.parts.toList, Multiset.coe_toList _⟩
  rw [← hl]
  have hsum : l.sum = 2 := by
    have h := π.parts_sum
    rw [← hl, Multiset.sum_coe] at h
    exact h
  have hpos : ∀ i ∈ l, 0 < i := by
    intro i hi
    exact π.parts_pos (by rw [← hl]; exact Multiset.mem_coe.mpr hi)
  match l with
  | [] => simp at hsum
  | [a] =>
    simp only [List.sum_cons, List.sum_nil] at hsum
    left
    have h1 : (↑[a] : Multiset ℕ) = {a} := by simp
    have ha2 : a = 2 := by omega
    rw [h1, ha2]
  | a :: b :: t =>
    simp only [List.sum_cons] at hsum
    have hapos : 0 < a := hpos a (by simp)
    have hbpos : 0 < b := hpos b (by simp)
    have ht : t = [] := by
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil t hne
      have hxpos := hpos x (by simp [List.mem_cons, hx])
      have hx0 : x = 0 := by
        have h0 : t.sum = 0 := by omega
        exact (List.sum_eq_zero_iff.mp h0) x hx
      omega
    subst ht
    simp only [List.sum_nil] at hsum
    right
    have hab : a = 1 ∧ b = 1 := by omega
    obtain ⟨rfl, rfl⟩ := hab
    rfl

private def part11 : Nat.Partition 2 :=
  ⟨{1, 1}, by
    intro i hi
    have h1 : i = 1 := by simpa using hi
    omega, by decide⟩

/-- The zeroth-order case: the empty partition is the only partition of `0` and
`Finset.Icc 1 0` is empty, so the right-hand side reduces to `f (g a)`. -/
example (f g : ℝ → ℝ) (a : ℝ) (hf : ContDiffAt ℝ 0 f (g a)) (hg : ContDiffAt ℝ 0 g a) :
    iteratedDeriv 0 (f ∘ g) a / (Nat.factorial 0 : ℝ) = f (g a) := by
  rw [taylorCoeff_comp_eq_sum_partitions f g a 0 hf hg]
  simp

/-- The first-order case is the chain rule. -/
example (f g : ℝ → ℝ) (a : ℝ) (hf : ContDiffAt ℝ 1 f (g a)) (hg : ContDiffAt ℝ 1 g a) :
    deriv (f ∘ g) a = deriv f (g a) * deriv g a := by
  have h := taylorCoeff_comp_eq_sum_partitions f g a 1 hf hg
  rw [iteratedDeriv_one] at h
  simp only [Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [Fintype.sum_unique] at h
  simp only [Nat.Partition.partition_one_parts, Multiset.card_singleton,
    Multiset.count_singleton, Finset.Icc_self, Finset.prod_singleton, iteratedDeriv_one,
    Nat.factorial_one, Nat.cast_one, div_one, pow_one, ite_true] at h
  simpa using h

/-- The second-order case for `x ^ 3` composed with `x ^ 2` at `1`: the
partitions `{2}` and `{1, 1}` contribute `3` and `12`. -/
example : iteratedDeriv 2 ((fun x : ℝ => x ^ 3) ∘ (fun x : ℝ => x ^ 2)) 1
      / (Nat.factorial 2 : ℝ) = 15 := by
  have hf3 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ 3) ((fun x : ℝ => x ^ 2) 1) :=
    ContDiff.contDiffAt (ContDiff.pow contDiff_id 3)
  have hg2 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ 2) 1 :=
    ContDiff.contDiffAt (ContDiff.pow contDiff_id 2)
  have h := taylorCoeff_comp_eq_sum_partitions (fun x : ℝ => x ^ 3) (fun x : ℝ => x ^ 2) 1 2 hf3 hg2
  have huniv : (Finset.univ : Finset (Nat.Partition 2))
      = {Nat.Partition.indiscrete 2, part11} := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro _
      rcases parts_two π with h2 | h11
      · left
        apply Nat.Partition.ext
        rw [h2]
        simp [Nat.Partition.indiscrete_parts]
      · right
        apply Nat.Partition.ext
        rw [h11]
        rfl
    · rintro (rfl | rfl) <;> simp
  rw [h]
  rw [huniv]
  have hne : Nat.Partition.indiscrete 2 ≠ part11 := by
    intro hcon
    have := congrArg Nat.Partition.parts hcon
    simp [Nat.Partition.indiscrete_parts, part11] at this
  rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hne), Finset.sum_singleton]
  simp only [part11]
  have e1 : iteratedDeriv 2 (fun x : ℝ => x ^ 3) 1 = 6 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hd : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 :=
      funext fun x => (hasDerivAt_pow 3 x).deriv
    rw [hd]
    have h6 : deriv (fun x : ℝ => 3 * x ^ 2) 1 = 6 := by
      have h := (HasDerivAt.const_mul (3 : ℝ) (hasDerivAt_pow 2 (1 : ℝ))).deriv
      convert h using 1
      norm_num
    exact h6
  have e2 : iteratedDeriv 1 (fun x : ℝ => x ^ 2) 1 = 2 := by
    rw [iteratedDeriv_one]
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) 2 1 := by
      have h := hasDerivAt_pow 2 (1 : ℝ)
      norm_num at h ⊢
      exact h
    exact h2.deriv
  have e3 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) 1 = 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hd : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x :=
      funext fun x => by simp
    rw [hd]
    exact (hasDerivAt_const_mul (2 : ℝ)).deriv
  have e4 : deriv (fun x : ℝ => x ^ 3) 1 = 3 := by
    have h := (hasDerivAt_pow 3 (1 : ℝ)).deriv
    convert h using 1
    norm_num
  rw [show Finset.Icc (1 : ℕ) 2 = {1, 2} from by decide,
    Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2)]
  rw [Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
    Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
    Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
    Nat.Partition.indiscrete_parts (show (2 : ℕ) ≠ 0 by norm_num)]
  simp only [Multiset.count_singleton, Multiset.card_singleton, iteratedDeriv_one, one_pow,
    e2, e3, e4]
  norm_num [e1]

/-- A cross-check of the previous example that does not use the formula: the
composite is `x ^ 6`, whose second derivative at `1` is `6 * 5 = 30`, so the
left-hand side is `15` as well. -/
example : iteratedDeriv 2 ((fun x : ℝ => x ^ 3) ∘ (fun x : ℝ => x ^ 2)) 1
      / (Nat.factorial 2 : ℝ) = 15 := by
  have hcomp : (fun x : ℝ => x ^ 3) ∘ (fun x : ℝ => x ^ 2) = fun x : ℝ => x ^ 6 := by
    funext x
    simp only [Function.comp_apply, ← pow_mul]
  rw [hcomp, iteratedDeriv_pow]
  norm_num [Nat.descFactorial, Nat.factorial]

end MetaMathlibExt.TaylorCoefficientCompositionTests
