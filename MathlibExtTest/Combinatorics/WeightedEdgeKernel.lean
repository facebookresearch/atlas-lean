/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.WeightedEdgeKernel
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WeightedEdgeKernelTest

open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Independent adjacency test, used for both natural and integer kernels. -/
def overlap {ι : Type*} [DecidableEq ι] (p q : ι × ι) : Prop :=
  q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2

instance {ι : Type*} [DecidableEq ι] (p q : ι × ι) : Decidable (overlap p q) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def complete : Matrix (Fin 6) (Fin 6) ℕ := fun a b => if a = b then 0 else 1

def overlapKernel {ι : Type*} [DecidableEq ι] : Matrix (ι × ι) (ι × ι) ℕ :=
  fun p q => if overlap p q then 1 else 0

def total {ι R : Type*} [Fintype ι] [AddCommMonoid R] (c : Matrix ι ι R) : R :=
  ∑ a, ∑ b, c a b

def quadratic {ι R : Type*} [Fintype ι] [CommSemiring R]
    (c : Matrix ι ι R) (κ : Matrix (ι × ι) (ι × ι) R) : R :=
  ∑ p, ∑ q, c p.1 p.2 * c q.1 q.2 * κ p q

example : total complete = 30 := by decide
example : quadratic complete overlapKernel = 540 := by decide
example : 4 * 5 * total complete = 600 := by decide
example : quadratic complete (fun _ _ => 1) = 900 := by decide

/-- Five disjoint undirected edges, rather than another dense graph. -/
def matching : Matrix (Fin 10) (Fin 10) ℕ := fun a b =>
  if a ≠ b ∧ a.val / 2 = b.val / 2 then 1 else 0

example : total matching = 10 := by decide
example : ∀ a, ∑ b, matching a b ≤ 1 := by decide
example : quadratic matching overlapKernel = 20 := by decide
example : 4 * 1 * total matching = 40 := by decide
example : quadratic matching (fun _ _ => 1) = 100 := by decide
example : ¬quadratic matching (fun _ _ => 1) ≤ 4 * 1 * total matching := by decide

/-- Every leaf points to the center; bounded rows alone do not control columns. -/
def directedStar : Matrix (Fin 6) (Fin 6) ℕ := fun a b =>
  if a ≠ 0 ∧ b = 0 then 1 else 0

example : total directedStar = 5 := by decide
example : directedStar 0 1 ≠ directedStar 1 0 := by decide
example : ∀ a, ∑ b, directedStar a b ≤ 1 := by decide
example : quadratic directedStar overlapKernel = 25 := by decide
example : ¬quadratic directedStar overlapKernel ≤ 4 * 1 * total directedStar := by decide

/-- The path has undirected edge weights one, two, and three. -/
def pathWeight : Matrix (Fin 4) (Fin 4) ℤ := fun a b =>
  if a.val + 1 = b.val then b.val else if b.val + 1 = a.val then a.val else 0

/-- A signed kernel whose sign depends on its first pair, so it is nonsymmetric. -/
def signedKernel : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℤ := fun p q =>
  if overlap p q then (if p.1.val ≤ 1 then 1 else -1) else 0

example : total pathWeight = 12 := by decide
example : ∀ a, ∑ b, pathWeight a b ≤ 5 := by decide
example : quadratic pathWeight signedKernel = -48 := by decide
example : 4 * 5 * total pathWeight * 1 = 240 := by decide
example : signedKernel (0, 1) (1, 2) ≠ signedKernel (1, 2) (0, 1) ∨
    signedKernel (1, 2) (2, 3) ≠ signedKernel (2, 3) (1, 2) := by decide

/-- A populated natural-number client consumes all hypotheses of the generic theorem. -/
example : quadratic complete overlapKernel ≤ 4 * 5 * total complete * 1 := by
  apply Matrix.sum_mul_mul_kernel_le complete 5 (fun _ _ => Nat.zero_le _)
    (by intro a b; simp [complete, eq_comm]) (by decide) overlapKernel 1 (by decide)
    (by intro p q; simp [overlapKernel]; split_ifs <;> decide)
  intro p q h₁ h₂ h₃ h₄
  simp [overlapKernel, overlap, h₁, h₂, h₃, h₄]

/-- Sparse weights exercise the same API with a strictly smaller row bound. -/
example : quadratic matching overlapKernel ≤ 4 * 1 * total matching * 1 := by
  apply Matrix.sum_mul_mul_kernel_le matching 1 (fun _ _ => Nat.zero_le _)
    (by intro a b; simp [matching, eq_comm, and_comm]) (by decide) overlapKernel 1 (by decide)
    (by intro p q; simp [overlapKernel]; split_ifs <;> decide)
  intro p q h₁ h₂ h₃ h₄
  simp [overlapKernel, overlap, h₁, h₂, h₃, h₄]

/-- The integer client has negative overlapping entries and an asymmetric kernel. -/
example : quadratic pathWeight signedKernel ≤ 4 * 5 * total pathWeight * 1 := by
  apply Matrix.sum_mul_mul_kernel_le pathWeight 5
    (by intro a b; unfold pathWeight; split_ifs <;> simp)
    (by intro a b; simp [pathWeight]; split_ifs <;> omega) (by decide)
    signedKernel 1 (by decide) (by intro p q; unfold signedKernel; split_ifs <;> decide)
  intro p q h₁ h₂ h₃ h₄
  simp [signedKernel, overlap, h₁, h₂, h₃, h₄]

example (p : Fin 6 × Fin 6) :
    (∑ q ∈ (univ.filter fun q : Fin 6 × Fin 6 => overlap p q), complete q.1 q.2) ≤
      4 * 5 :=
  Matrix.sum_weights_shared_endpoint_le complete 5 (fun _ _ => Nat.zero_le _)
    (by intro a b; simp [complete, eq_comm]) (by decide) p

/-- The all-pair theorem admits a nonzero loop. -/
example : quadratic (fun _ _ : Fin 1 => (2 : ℕ)) (fun _ _ => 1) ≤
    4 * 2 * total (fun _ _ : Fin 1 => (2 : ℕ)) * 1 := by
  apply Matrix.sum_mul_mul_kernel_le (fun _ _ : Fin 1 => (2 : ℕ)) 2 (fun _ _ => Nat.zero_le _)
    (fun _ _ => rfl) (by intro a; simp) _ 1 (by decide) (fun _ _ => le_refl _)
  intro p q h
  exact False.elim (h (Subsingleton.elim _ _))

example : quadratic (fun _ _ : Fin 1 => (2 : ℕ)) (fun _ _ => 1) = 4 ∧
    4 * 2 * total (fun _ _ : Fin 1 => (2 : ℕ)) = 16 := by decide

/-- With no indices, the row condition places no restriction on a negative `P`. -/
example (c : Matrix Empty Empty ℤ) (κ : Matrix (Empty × Empty) (Empty × Empty) ℤ) :
    quadratic c κ ≤ 4 * (-5) * total c * 1 :=
  Matrix.sum_mul_mul_kernel_le c (-5) (fun a => a.elim) (fun a => a.elim)
    (fun a => a.elim) κ 1 (by decide) (fun p => p.1.elim) (fun p => p.1.elim)

example (c : Matrix Empty Empty ℤ) (κ : Matrix (Empty × Empty) (Empty × Empty) ℤ) :
    quadratic c κ = 0 ∧ total c = 0 := by
  simp [quadratic, total]

/-- Zero bounds are permitted, including zero weights and zero kernel. -/
example : quadratic (fun _ _ : Fin 3 => (0 : ℤ)) (fun _ _ => 0) ≤
    4 * 0 * total (fun _ _ : Fin 3 => (0 : ℤ)) * 0 := by
  apply Matrix.sum_mul_mul_kernel_le (fun _ _ : Fin 3 => (0 : ℤ)) 0
    (fun _ _ => le_refl _) (fun _ _ => rfl)
    (by intro a; simp) _ 0 (le_refl _) (fun _ _ => le_refl _) (fun _ _ _ _ _ _ => rfl)

def negativeKernel : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℤ :=
  fun p q => if overlap p q then -1 else 0

example : quadratic pathWeight negativeKernel ≤ 4 * 5 * total pathWeight * 0 := by
  apply Matrix.sum_mul_mul_kernel_le pathWeight 5
    (by intro a b; unfold pathWeight; split_ifs <;> simp)
    (by intro a b; simp [pathWeight]; split_ifs <;> omega) (by decide)
    negativeKernel 0 (le_refl _) (by intro p q; unfold negativeKernel; split_ifs <;> decide)
  intro p q h₁ h₂ h₃ h₄
  simp [negativeKernel, overlap, h₁, h₂, h₃, h₄]

example : quadratic pathWeight negativeKernel = -120 := by decide

/-- The scalar generality includes the real numbers. -/
example (c : Matrix (Fin 2) (Fin 2) ℝ) (P m : ℝ)
    (hc : ∀ a b, 0 ≤ c a b) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b, c a b ≤ P) (hm : 0 ≤ m)
    (κ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (h1 : ∀ p q, κ p q ≤ m)
    (h0 : ∀ p q, q.1 ≠ p.1 → q.1 ≠ p.2 → q.2 ≠ p.1 → q.2 ≠ p.2 → κ p q = 0) :
    quadratic c κ ≤ 4 * P * total c * m :=
  Matrix.sum_mul_mul_kernel_le c P hc hs hP κ m hm h1 h0

/-- The index type lives in a higher universe, independently of the scalar. -/
example (c : Matrix (ULift.{1} (Fin 2)) (ULift.{1} (Fin 2)) ℕ) (P m : ℕ)
    (hs : ∀ a b, c a b = c b a) (hP : ∀ a, ∑ b, c a b ≤ P)
    (κ : Matrix (ULift.{1} (Fin 2) × ULift.{1} (Fin 2))
      (ULift.{1} (Fin 2) × ULift.{1} (Fin 2)) ℕ) (h1 : ∀ p q, κ p q ≤ m)
    (h0 : ∀ p q, q.1 ≠ p.1 → q.1 ≠ p.2 → q.2 ≠ p.1 → q.2 ≠ p.2 → κ p q = 0) :
    quadratic c κ ≤ 4 * P * total c * m :=
  Matrix.sum_mul_mul_kernel_le c P (fun _ _ => Nat.zero_le _) hs hP κ m (Nat.zero_le _) h1 h0

example (p q : Fin 6 × Fin 6) :
    ¬overlap p q ↔ q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2 := by
  simp only [overlap, not_or]

/-- The source accepts arbitrary diagonal weights, here all equal to one. -/
def sourceWeight : Matrix (Fin 6) (Fin 6) ℕ := fun _ _ => 1

/-- Inactive source entries are negative, making an unmasked extension invalid. -/
def sourceKernel : Matrix (Fin 6 × Fin 6) (Fin 6 × Fin 6) ℤ := fun p q =>
  if p.1 ≠ p.2 ∧ q.1 ≠ q.2 then (if overlap p q then 1 else 0) else -100

def sourceQuadratic {g : ℕ} (c : Matrix (Fin g) (Fin g) ℕ)
    (κ : Matrix (Fin g × Fin g) (Fin g × Fin g) ℤ) : ℤ :=
  ∑ p ∈ (univ.filter fun p : Fin g × Fin g => p.1 ≠ p.2),
    ∑ q ∈ (univ.filter fun q : Fin g × Fin g => q.1 ≠ q.2),
      (c p.1 p.2 : ℤ) * (c q.1 q.2 : ℤ) * κ p q

example : sourceQuadratic sourceWeight sourceKernel = 540 := by decide
example : quadratic (fun _ _ : Fin 6 => (1 : ℤ)) sourceKernel = -39060 := by decide
example : quadratic (fun a b : Fin 6 => if a = b then (0 : ℤ) else 1)
    (fun p q => if p.1 ≠ p.2 ∧ q.1 ≠ q.2 then sourceKernel p q else 0) = 540 := by
  decide

/-- The exact source theorem retains the erased row sums and arbitrary input diagonals. -/
example : sourceQuadratic sourceWeight sourceKernel ≤
    ((4 * 5 * (∑ a, ∑ b ∈ univ.erase a, sourceWeight a b) : ℕ) : ℤ) * 1 := by
  apply Matrix.sum_ordered_nat_int_kernel_le 6 5 sourceWeight
    (fun _ _ => rfl) (by decide) sourceKernel 1 (by decide)
  · intro p hp q hq h₁ h₂ h₃ h₄
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    rw [sourceKernel, ite_eq_left ⟨hp', hq'⟩]
    simp [overlap, h₁, h₂, h₃, h₄]
  · intro p q
    unfold sourceKernel
    split_ifs <;> decide

/-- Even an arbitrarily large positive diagonal contributes zero to the source domain. -/
example (d : ℕ) : sourceQuadratic (fun _ _ : Fin 1 => d + 1) (fun _ _ => (-3 : ℤ)) ≤
    ((4 * 0 * (∑ a : Fin 1, ∑ _b ∈ univ.erase a, d + 1) : ℕ) : ℤ) * 0 := by
  apply Matrix.sum_ordered_nat_int_kernel_le 1 0 (fun _ _ : Fin 1 => d + 1)
    (fun _ _ => rfl) (by
      intro a
      have hu : (univ : Finset (Fin 1)) = {a} := by
        ext b
        constructor
        · intro _
          exact mem_singleton.mpr (Subsingleton.elim _ _)
        · intro _
          exact mem_univ _
      rw [hu]
      simp) (fun _ _ => (-3 : ℤ)) 0 (le_refl _)
  · intro p hp
    exact False.elim ((mem_filter.mp hp).2 (Subsingleton.elim _ _))
  · intro p q
    decide

example (d : ℕ) : sourceQuadratic (fun _ _ : Fin 1 => d + 1) (fun _ _ => (-3 : ℤ)) = 0 := by
  unfold sourceQuadratic
  have he : (univ.filter fun p : Fin 1 × Fin 1 => p.1 ≠ p.2) = ∅ := by
    ext p
    simp [Subsingleton.elim p.1 p.2]
  rw [he]
  simp

def pathNat : Matrix (Fin 4) (Fin 4) ℕ := fun a b =>
  if a.val + 1 = b.val then b.val else if b.val + 1 = a.val then a.val else 0

example : sourceQuadratic pathNat signedKernel = -48 := by decide

/-- A second original Nat/Int source client exercises signed overlapping entries. -/
example : sourceQuadratic pathNat signedKernel ≤
    ((4 * 5 * (∑ a, ∑ b ∈ univ.erase a, pathNat a b) : ℕ) : ℤ) * 1 := by
  apply Matrix.sum_ordered_nat_int_kernel_le 4 5 pathNat
    (by intro a b; simp [pathNat]; split_ifs <;> omega) (by decide) signedKernel 1 (by decide)
  · intro p _ q _ h₁ h₂ h₃ h₄
    simp [signedKernel, overlap, h₁, h₂, h₃, h₄]
  · intro p q
    unfold signedKernel
    split_ifs <;> decide

#print axioms Matrix.sum_ordered_nat_int_kernel_le

#reduce (sourceQuadratic sourceWeight sourceKernel,
  quadratic (fun _ _ : Fin 6 => (1 : ℤ)) sourceKernel,
  quadratic (fun a b : Fin 6 => if a = b then (0 : ℤ) else 1)
    (fun p q => if p.1 ≠ p.2 ∧ q.1 ≠ q.2 then sourceKernel p q else 0))

#reduce (quadratic (fun _ _ : Fin 1 => (2 : ℕ)) (fun _ _ => 1),
  4 * 2 * total (fun _ _ : Fin 1 => (2 : ℕ)), quadratic pathWeight negativeKernel)
#print axioms Matrix.sum_weights_shared_endpoint_le
#print axioms Matrix.sum_mul_mul_kernel_le

#reduce (total complete, quadratic complete overlapKernel,
  4 * 5 * total complete, quadratic complete (fun _ _ => 1))
#reduce (total matching, quadratic matching overlapKernel,
  4 * 1 * total matching, quadratic matching (fun _ _ => 1))
#reduce (total directedStar, quadratic directedStar overlapKernel,
  4 * 1 * total directedStar)
#reduce (total pathWeight, quadratic pathWeight signedKernel,
  4 * 5 * total pathWeight * 1)

end WeightedEdgeKernelTest
