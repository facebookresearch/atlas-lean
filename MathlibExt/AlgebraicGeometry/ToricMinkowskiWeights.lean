/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
public import Mathlib.GroupTheory.Index

/-!
# Integral Minkowski weights and the literal fan displacement sum

Weights belong to a subgroup of functions on actual fan cones. Balancing
uses primitive quotient-lattice normals, not Euclidean unit vectors.
The product is initially a raw integer weight function: its independence
and balancing are proof goals, not assumptions in the construction.

Source: Fulton--Sturmfels, *Intersection Theory on Toric Varieties*,
alg-geom/9403002v1, Theorems 2.1 and 3.2. The integral operational-Chow
comparison is separate from ordinary rational Chow homology.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights

open FiniteToricCoordinates
open scoped BigOperators

variable {n : ℕ} (F : FiniteFan n)

local instance : Fintype F.Face := inferInstance

/-- A positive primitive normal in the actual quotient lattice. -/
structure FaceNormal (σ τ : F.Face) where
  vector : Lattice n
  in_lattice : vector ∈ coneLattice σ.val
  nonzero : (QuotientAddGroup.mk' (coneLattice τ.val)) vector ≠ 0
  primitive : (coneLattice σ.val).map (QuotientAddGroup.mk' (coneLattice τ.val)) =
    AddSubgroup.zmultiples ((QuotientAddGroup.mk' (coneLattice τ.val)) vector)
  positive : ∃ x ∈ σ.val, ∃ y ∈ coneSpan τ.val, latticeCast n vector = x + y

/-- The normal catalogue is characterized geometrically; representatives
may vary only by the actual face lattice. -/
structure NormalData where
  normal : ∀ (σ τ : F.Face), τ.val.IsFaceOf σ.val →
    coneDimension τ.val + 1 = coneDimension σ.val → FaceNormal F σ τ

variable (N : NormalData F)

def balanceAt (w : F.Face → ℤ) (k : ℕ) (τ : F.Face) :
    Lattice n ⧸ coneLattice τ.val := by
  classical
  exact ∑ σ : F.Face,
    if h : τ.val.IsFaceOf σ.val ∧ coneDimension τ.val + 1 = coneDimension σ.val ∧
        coneDimension σ.val + k = n then
      w σ • (QuotientAddGroup.mk' (coneLattice τ.val)) (N.normal σ τ h.1 h.2.1).vector
    else 0

@[simp]
theorem balanceAt_zero (k : ℕ) (τ : F.Face) : balanceAt F N 0 k τ = 0 := by
  classical
  simp [balanceAt]

theorem balanceAt_add (w v : F.Face → ℤ) (k : ℕ) (τ : F.Face) :
    balanceAt F N (w + v) k τ = balanceAt F N w k τ + balanceAt F N v k τ := by
  classical
  simp only [balanceAt, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp [add_zsmul]

theorem balanceAt_neg (w : F.Face → ℤ) (k : ℕ) (τ : F.Face) :
    balanceAt F N (-w) k τ = -balanceAt F N w k τ := by
  classical
  simp only [balanceAt, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

/-- The actual subgroup of codimension-k balanced integer weights. -/
def weights (k : ℕ) : AddSubgroup (F.Face → ℤ) where
  carrier := {w | (∀ σ : F.Face, coneDimension σ.val + k ≠ n → w σ = 0) ∧
    ∀ τ : F.Face, coneDimension τ.val + k + 1 = n → balanceAt F N w k τ = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro w v ⟨hw, hb⟩ ⟨hv, hc⟩
    refine ⟨fun σ h ↦ by simp [hw σ h, hv σ h], fun τ h ↦ ?_⟩
    rw [balanceAt_add, hb τ h, hc τ h, add_zero]
  neg_mem' := by
    rintro w ⟨hw, hb⟩
    refine ⟨fun σ h ↦ by simp [hw σ h], fun τ h ↦ ?_⟩
    rw [balanceAt_neg, hb τ h, neg_zero]

def GenericDisplacement (v : RealSpace n) : Prop :=
  ∀ σ τ : F.Face, coneSpan σ.val ⊔ coneSpan τ.val ≠ ⊤ →
    v ∉ coneSpan σ.val ⊔ coneSpan τ.val

def DisplacedMeet (σ τ : F.Face) (v : RealSpace n) : Prop :=
  ∃ x ∈ σ.val, ∃ y ∈ τ.val, x = y + v

/-- The coefficient is the actual finite lattice index when the spans fill
the lattice. Infinite-index pairs have index zero in the raw formula. -/
def latticeCoefficient (σ τ : F.Face) : ℤ :=
  ((coneLattice σ.val ⊔ coneLattice τ.val).index : ℤ)

def displacementProduct (k l : ℕ) (w v : F.Face → ℤ) (a : RealSpace n) : F.Face → ℤ := by
  classical
  exact fun γ ↦ ∑ σ : F.Face, ∑ τ : F.Face,
    if γ.val.IsFaceOf σ.val ∧ γ.val.IsFaceOf τ.val ∧
      coneDimension σ.val + k = n ∧ coneDimension τ.val + l = n ∧
      coneDimension γ.val + k + l = n ∧ DisplacedMeet F σ τ a then
      latticeCoefficient F σ τ * w σ * v τ
    else 0

end MathlibExt.AlgebraicGeometry.ToricMinkowskiWeights
