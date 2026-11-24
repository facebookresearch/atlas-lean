/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.TotalComplexDownNat
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Finite first-quadrant total complexes

In total degree `n`, a first-quadrant chain bicomplex has exactly the
bidegrees `(p,n-p)` for `0 ≤ p ≤ n`.  This file identifies that indexing
fiber with `Fin (n+1)`, obtains totalization from finite coproducts, and
records the finite horizontal filtration's degreewise exhaustiveness.

These are boundedness ingredients only; no spectral object or convergence
theorem is asserted here.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

/-- Bidegrees contributing to total degree `n` in a first-quadrant chain
bicomplex. -/
abbrev DownNatTotalFiber (n : ℕ) :=
  (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' {n}

@[simp]
theorem downNatTotalFiber_mem (n : ℕ) (x : DownNatTotalFiber n) :
    x.val.1 + x.val.2 = n :=
  x.property

/-- First horizontal coordinate of a total bidegree. -/
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

/-- Every `p ≤ n` gives the unique bidegree `(p,n-p)` in total degree
`n`. -/
def finToDownNatTotalFiber (n : ℕ) : Fin (n + 1) → DownNatTotalFiber n :=
  fun p => ⟨(p.val, n - p.val), by
    change p.val + (n - p.val) = n
    omega⟩

/-- The bidegrees in total degree `n` are canonically `Fin (n+1)`. -/
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

/-- Bidegrees in total degree `n` whose horizontal coordinate is at most
`k`. -/
abbrev DownNatHorizontalFilteredFiber (n k : ℕ) :=
  {pq : DownNatTotalFiber n // pq.val.1 ≤ k}

instance downNatHorizontalFilteredFiber_finite (n k : ℕ) :
    Finite (DownNatHorizontalFilteredFiber n k) :=
  inferInstance

/-- Every bidegree in total degree `n` has horizontal coordinate at most
`n`. -/
theorem downNatTotalFiber_fst_le (n : ℕ) (pq : DownNatTotalFiber n) :
    pq.val.1 ≤ n := by
  have hpq := pq.property
  change pq.val.1 + pq.val.2 = n at hpq
  omega

/-- The horizontal filtration is exhaustive in total degree `n` by stage
`n` (and hence by every later stage). -/
def downNatHorizontalFilteredFiberEquiv (n k : ℕ) (h : n ≤ k) :
    DownNatHorizontalFilteredFiber n k ≃ DownNatTotalFiber n where
  toFun pq := pq.1
  invFun pq := ⟨pq, (downNatTotalFiber_fst_le n pq).trans h⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

/-- A first-quadrant chain bicomplex has a direct-sum total complex using
only finite coproducts. -/
theorem firstQuadrantHasTotal
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := by
  intro n
  change HasCoproduct (fun pq : DownNatTotalFiber n =>
    (K.X pq.val.1).X pq.val.2)
  infer_instance

/-- Explicit finite-coproduct presentation of total degree `n`. -/
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
