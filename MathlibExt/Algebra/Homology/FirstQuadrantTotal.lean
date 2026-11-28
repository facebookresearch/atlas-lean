/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.TotalComplexDownNat
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite antidiagonal presentations of first-quadrant totals

For a nonnegative homological bicomplex, total degree n consists of
the bidegrees (p,q) with p+q=n. They are canonically indexed by
p∈Fin(n+1), with q=n−p.

Horizontal stage k retains p≤k. Once n≤k every total-degree n
coordinate is retained, so the filtered and full indexing fibers
are equivalent. In a preadditive category with finite coproducts,
these finite antidiagonals define the total complex and give
Tot(K)_n ≅ ⨁_(p=0)^n K_(p,n−p).
The object and morphism worlds of the target category are independent.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

/-- For n∈ℕ, the total-degree fiber is the set of pairs
(p,q)∈ℕ² satisfying p+q=n.
These are the bidegrees contributing to degree n of a first-quadrant
homological total complex. -/
abbrev DownNatTotalFiber (n : ℕ) :=
  (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' {n}

@[simp]
theorem downNatTotalFiber_mem (n : ℕ) (x : DownNatTotalFiber n) :
    x.val.1 + x.val.2 = n :=
  x.property

/-- For a pair (p,q) of nonnegative integers with p+q=n,
the horizontal coordinate p belongs to Fin(n+1), since p≤n.
This defines the map from the total-degree fiber to Fin(n+1). -/
def downNatTotalFiberToFin (n : ℕ) : DownNatTotalFiber n → Fin (n + 1) :=
  fun x => ⟨x.val.1, by
    have hx := x.property
    change x.val.1 + x.val.2 = n at hx
    omega⟩

theorem downNatTotalFiberToFin_injective (n : ℕ) :
    Function.Injective (downNatTotalFiberToFin n) := by
  rintro ⟨⟨xp, xq⟩, hx⟩ ⟨⟨yp, yq⟩, hy⟩ hxy
  change xp + xq = n at hx
  change yp + yq = n at hy
  dsimp [downNatTotalFiberToFin] at hxy
  have hp : xp = yp := congrArg Fin.val hxy
  subst yp
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Nat.add_left_cancel (hx.trans hy.symm)

theorem downNatTotalFiber_finite (n : ℕ) :
    Finite (DownNatTotalFiber n) :=
  inferInstance

/-- For p∈Fin(n+1), the pair (p,n−p) belongs to the
nonnegative total-degree fiber at n.
The subtraction is justified by p≤n and recovers its unique
vertical coordinate. -/
def finToDownNatTotalFiber (n : ℕ) : Fin (n + 1) → DownNatTotalFiber n :=
  fun p => ⟨(p.val, n - p.val), by
    change p.val + (n - p.val) = n
    omega⟩

/-- For n∈ℕ, the antidiagonal pairs (p,q) with p+q=n are
equivalent to Fin(n+1). The forward map takes p, and the inverse
sends p to (p,n−p). -/
def downNatTotalFiberEquivFin (n : ℕ) :
    DownNatTotalFiber n ≃ Fin (n + 1) where
  toFun := downNatTotalFiberToFin n
  invFun := finToDownNatTotalFiber n
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hx := x.property
      change x.val.1 + x.val.2 = n at hx
      dsimp [finToDownNatTotalFiber, downNatTotalFiberToFin]
      omega
  right_inv _ := rfl

/-- For n,k∈ℕ, the horizontal filtered fiber consists of
pairs (p,q)∈ℕ² with p+q=n and p≤k.
It indexes the retained finite summands in stage k of total degree n. -/
abbrev DownNatHorizontalFilteredFiber (n k : ℕ) :=
  {pq : DownNatTotalFiber n // pq.val.1 ≤ k}

instance downNatHorizontalFilteredFiber_finite (n k : ℕ) :
    Finite (DownNatHorizontalFilteredFiber n k) :=
  inferInstance

/-- For a pair (p,q)∈ℕ² with p+q=n, the inequality p≤n holds.
It supplies the degreewise horizontal support bound for the
first-quadrant total. -/
theorem downNatTotalFiber_fst_le (n : ℕ) (pq : DownNatTotalFiber n) :
    pq.val.1 ≤ n := by
  have hpq := pq.property
  change pq.val.1 + pq.val.2 = n at hpq
  omega

/-- For n,k∈ℕ with n≤k, forgetting the horizontal-bound
proof gives an equivalence from the filtered fiber
{(p,q) | p+q=n, p≤k} to the full total fiber.
Every total-degree coordinate already satisfies p≤n≤k. -/
def downNatHorizontalFilteredFiberEquiv (n k : ℕ) (h : n ≤ k) :
    DownNatHorizontalFilteredFiber n k ≃ DownNatTotalFiber n where
  toFun pq := pq.1
  invFun pq := ⟨pq, (downNatTotalFiber_fst_le n pq).trans h⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, its direct-sum total exists.
Each degree n uses only the finite antidiagonal p+q=n,
so no infinite coproduct assumption is required. -/
theorem firstQuadrantHasTotal
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := by
  intro n
  change HasCoproduct (fun pq : DownNatTotalFiber n =>
    (K.X pq.val.1).X pq.val.2)
  infer_instance

/-- For a nonnegative homological bicomplex K in a preadditive
category with finite coproducts, there is an isomorphism
Tot(K)_n ≅ ⨁_(p=0)^n K_(p,n−p).
It is the reindexing of the total-degree fiber by Fin(n+1). -/
noncomputable def firstQuadrantTotalXIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ≅
      ∐ fun p : Fin (n + 1) => (K.X p.val).X (n - p.val) :=
  Sigma.whiskerEquiv
    (f := fun pq : DownNatTotalFiber n =>
      (K.X pq.val.1).X pq.val.2)
    (g := fun p : Fin (n + 1) =>
      (K.X p.val).X (n - p.val))
    (downNatTotalFiberEquivFin n)
    (fun pq => eqToIso (by
      have he : ((downNatTotalFiberEquivFin n) pq).val = pq.val.1 := rfl
      rw [he]
      congr 1
      have hpq := pq.property
      change pq.val.1 + pq.val.2 = n at hpq
      omega))

end HomologicalComplex₂

end
