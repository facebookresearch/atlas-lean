/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# Restricted sumsets and restricted signed sumsets of integer finsets

`restrictedSumset h A` is `h^∧ A`, the sums of `h` distinct elements of `A` (defined for
finsets of any additive commutative monoid), and
`restrictedSignedSumset h A` is `h^∧_± A`, the sums `Σ λ_a a` with `λ_a ∈ {-1, 0, 1}` and
`Σ |λ_a| = h`. Both are computable, and the membership lemmas recover the coefficient
definitions.

## Main statements

* `MetaMathlibExt.mem_restrictedSumset_iff`
* `MetaMathlibExt.mem_restrictedSignedSumset_iff`
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Restricted sumset.** For a natural number $h$ and a finite subset $A$ of an additive
commutative monoid $G$, the restricted sumset $h^{\wedge} A$ is the set of all sums
$\sum_{a \in B} a$ with $B$ an $h$-element subset of $A$, that is, the sums of $h$ distinct
elements of $A$. In particular $0^{\wedge} A = \{0\}$.

The source works in the integers; here $G$ is an arbitrary additive commutative monoid.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of restricted sumset. -/
public def restrictedSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] (h : ℕ)
    (A : Finset G) : Finset G :=
  (A.powersetCard h).image (fun B => ∑ a ∈ B, a)

/-- **Restricted signed sumset.** For a natural number $h$ and a finite set $A$ of integers, the
restricted signed sumset $h^{\wedge}_{\pm} A$ is the set of all integers
$\sum_{a \in B} a - 2 \sum_{a \in N} a$, where $B$ ranges over the $h$-element subsets of $A$ and
$N$ ranges over the subsets of $B$. These are the sums of the elements of $B$ in which the
elements of $N$ are given a negative sign.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of restricted signed sumset. -/
public def restrictedSignedSumset (h : ℕ) (A : Finset ℤ) : Finset ℤ :=
  ((A.powersetCard h).sigma (fun B => B.powerset)).image
    (fun p => ∑ a ∈ p.1, a - 2 * ∑ a ∈ p.2, a)


/-- **Coefficient description of the restricted sumset.** For a natural number $h$, a finite set
$A$ of integers and an integer $x$, $x$ lies in the restricted sumset $h^{\wedge} A$ if and only
if there is a function $c : \mathbb{Z} \to \mathbb{Z}$ with $c(a) \in \{0, 1\}$ for every
$a \in A$, $\sum_{a \in A} c(a) = h$ and $x = \sum_{a \in A} c(a)\, a$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of restricted sumset. -/
public theorem mem_restrictedSumset_iff (h : ℕ) (A : Finset ℤ) (x : ℤ) :
    x ∈ restrictedSumset h A ↔
      ∃ c : ℤ → ℤ,
        (∀ a ∈ A, c a = 0 ∨ c a = 1) ∧
        ∑ a ∈ A, c a = (h : ℤ) ∧
        x = ∑ a ∈ A, c a * a := by
  constructor
  · simp only [restrictedSumset, Finset.mem_image, Finset.mem_powersetCard]
    rintro ⟨B, ⟨hBA, hcard⟩, rfl⟩
    refine ⟨fun a => if a ∈ B then 1 else 0, ?_, ?_, ?_⟩
    · intro a ha
      by_cases hab : a ∈ B <;> simp [hab]
    · have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      simp [hAB, hcard]
    · have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      simp [hAB]
  · rintro ⟨c, hc, hsum, rfl⟩
    let B := A.filter fun a => c a = 1
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have hcoeff (a : ℤ) (ha : a ∈ A) : c a = if a ∈ B then 1 else 0 := by
      have := hc a ha
      simp only [B, Finset.mem_filter]
      rcases this with h0 | h1
      · simp [h0]
      · simp [h1, ha]
    have hcardZ : (B.card : ℤ) = h := by
      have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      calc
        (B.card : ℤ) = ∑ a ∈ A, c a := by
          rw [Finset.sum_congr rfl fun a ha => hcoeff a ha]
          simp [hAB]
        _ = h := hsum
    have hcard : B.card = h := by exact_mod_cast hcardZ
    refine Finset.mem_image.mpr ⟨B, Finset.mem_powersetCard.mpr ⟨hBA, hcard⟩, ?_⟩
    have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
    symm
    rw [Finset.sum_congr rfl fun a ha => congrArg (fun z => z * a) (hcoeff a ha)]
    simp [hAB]

/-- **Coefficient description of the restricted signed sumset.** For a natural number $h$, a
finite set $A$ of integers and an integer $x$, $x$ lies in the restricted signed sumset
$h^{\wedge}_{\pm} A$ if and only if there is a function $c : \mathbb{Z} \to \mathbb{Z}$ with
$c(a) \in \{-1, 0, 1\}$ for every $a \in A$, $\sum_{a \in A} |c(a)| = h$ and
$x = \sum_{a \in A} c(a)\, a$.

Source: Mohan, Raj Kumar Mistri, Ram Krishna Pandey, *Some Direct and Inverse Problems for the Restricted Signed Sumset in the Set of Integers*, INTEGERS 24 (2024), Article A81, Definition of restricted signed sumset. -/
public theorem mem_restrictedSignedSumset_iff (h : ℕ) (A : Finset ℤ) (x : ℤ) :
    x ∈ restrictedSignedSumset h A ↔
      ∃ c : ℤ → ℤ,
        (∀ a ∈ A, c a = -1 ∨ c a = 0 ∨ c a = 1) ∧
        ∑ a ∈ A, |c a| = (h : ℤ) ∧
        x = ∑ a ∈ A, c a * a := by
  constructor
  · simp only [restrictedSignedSumset, Finset.mem_image, Finset.mem_sigma,
      Finset.mem_powersetCard, Finset.mem_powerset]
    rintro ⟨⟨B, N⟩, ⟨⟨hBA, hcard⟩, hNB⟩, rfl⟩
    let c : ℤ → ℤ := fun a => if a ∈ B then if a ∈ N then -1 else 1 else 0
    refine ⟨c, ?_, ?_, ?_⟩
    · intro a ha
      by_cases hab : a ∈ B
      · by_cases han : a ∈ N <;> simp [c, hab, han]
      · simp [c, hab]
    · have hone (a : ℤ) (ha : a ∈ B) : |c a| = 1 := by
        by_cases han : a ∈ N <;> simp [c, ha, han]
      have hzero (a : ℤ) (haA : a ∈ A) (haB : a ∉ B) : |c a| = 0 := by
        simp [c, haB]
      calc
        ∑ a ∈ A, |c a| = ∑ a ∈ B, |c a| :=
          (Finset.sum_subset hBA hzero).symm
        _ = ∑ _a ∈ B, (1 : ℤ) := Finset.sum_congr rfl hone
        _ = h := by simp [hcard]
    · have hcformula (a : ℤ) (ha : a ∈ B) :
          c a * a = a - 2 * (if a ∈ N then a else 0) := by
        by_cases han : a ∈ N
        · simp [c, ha, han]
          ring
        · simp [c, ha, han]
      have hout (a : ℤ) (haA : a ∈ A) (haB : a ∉ B) : c a * a = 0 := by
        simp [c, haB]
      have hNB' : B ∩ N = N := Finset.inter_eq_right.mpr hNB
      symm
      calc
        ∑ a ∈ A, c a * a = ∑ a ∈ B, c a * a :=
          (Finset.sum_subset hBA hout).symm
        _ = ∑ a ∈ B, (a - 2 * (if a ∈ N then a else 0)) :=
          Finset.sum_congr rfl hcformula
        _ = ∑ a ∈ B, a - 2 * ∑ a ∈ N, a := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          simp [hNB']
  · rintro ⟨c, hc, hsum, rfl⟩
    let B := A.filter fun a => c a ≠ 0
    let N := B.filter fun a => c a = -1
    have hBA : B ⊆ A := Finset.filter_subset _ _
    have hNB : N ⊆ B := Finset.filter_subset _ _
    have hcB (a : ℤ) (ha : a ∈ A) : |c a| = if a ∈ B then 1 else 0 := by
      rcases hc a ha with hm | h0 | h1
      · simp [B, ha, hm]
      · simp [B, ha, h0]
      · simp [B, ha, h1]
    have hcardZ : (B.card : ℤ) = h := by
      have hAB : A ∩ B = B := Finset.inter_eq_right.mpr hBA
      calc
        (B.card : ℤ) = ∑ a ∈ A, |c a| := by
          rw [Finset.sum_congr rfl fun a ha => hcB a ha]
          simp [hAB]
        _ = h := hsum
    have hcard : B.card = h := by exact_mod_cast hcardZ
    refine Finset.mem_image.mpr ⟨⟨B, N⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨hBA, hcard⟩,
        Finset.mem_powerset.mpr hNB⟩
    · have hcformula (a : ℤ) (ha : a ∈ B) :
          c a * a = a - 2 * (if a ∈ N then a else 0) := by
        have haA := hBA ha
        rcases hc a haA with hm | h0 | h1
        · simp [N, ha, hm]
          ring
        · have : a ∉ B := by simp [B, haA, h0]
          exact (this ha).elim
        · simp [N, ha, h1]
      have hout (a : ℤ) (haA : a ∈ A) (haB : a ∉ B) : c a * a = 0 := by
        have hzero : c a = 0 := by
          simpa only [B, Finset.mem_filter, haA, true_and, not_not] using haB
        simp [hzero]
      have hNB' : B ∩ N = N := Finset.inter_eq_right.mpr hNB
      symm
      calc
        ∑ a ∈ A, c a * a = ∑ a ∈ B, c a * a :=
          (Finset.sum_subset hBA hout).symm
        _ = ∑ a ∈ B, (a - 2 * (if a ∈ N then a else 0)) :=
          Finset.sum_congr rfl hcformula
        _ = ∑ a ∈ B, a - 2 * ∑ a ∈ N, a := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          simp [hNB']

end

end MetaMathlibExt
