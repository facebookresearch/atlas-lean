/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Author: @toskua
Copyright (c) 2023 Joël Riou. All rights reserved.
Copyright (c) 2026 @junekim623, Muse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The total-symmetry proof was promoted from the Hartshorne development by
Joël Riou, @junekim623, and Muse. It adapts
`Mathlib/Algebra/Homology/ComplexShapeSigns.lean` at pinned Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
-/
module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import MathlibExt.Algebra.Homology.TensorSignsUpNat
public import MathlibExt.Algebra.Homology.TotalComplexExact

/-!
# Total complexes of nonnegative cochain bicomplexes

For the nonnegative cochain shape, the total degree of a bidegree (p,q) is p+q. Each
antidiagonal p+q=n is finite, so finite coproducts in a preadditive category suffice to form the
direct-sum total. Interchanging the two directions of the bicomplex uses the symmetry sign
(−1)^{pq}. The same totalization applies to the unit-step nonnegative cochain shape.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape

set_option backward.isDefEq.respectTransparency.types false in
/-- For nonnegative cochain bicomplexes, transposition of bidegrees (p,q) ↦ (q,p) preserves the
total degree p+q and uses the unit sign σ(p,q) = (−1)^{pq}. These signs satisfy the
compatibility equations with the two cochain total-differential signs, giving the total-shape
symmetry. -/
instance upNatTotalComplexShapeSymmetry :
    TotalComplexShapeSymmetry (up ℕ) (up ℕ) (up ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, Nat.add_mul, one_mul, pow_add, ← mul_assoc,
      mul_comm ((-1 : ℤˣ) ^ q) ((-1 : ℤˣ) ^ (p * q)), mul_assoc,
      Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, Nat.mul_add, mul_one, pow_add]

/-- The unit-step cochain shape on the natural numbers, with relation p+1=q, admits the
total-complex shape taking (p,q) to p+q in the nonnegative cochain shape. It uses the canonical
total-differential signs for the two cochain directions. -/
instance totalComplexShapeUp'Nat :
    TotalComplexShape (up' (1 : ℕ)) (up' (1 : ℕ)) (up ℕ) :=
  inferInstanceAs (TotalComplexShape (up ℕ) (up ℕ) (up ℕ))

/-- For every natural number n, the set of bidegrees (p,q) ∈ ℕ² satisfying p+q=n is finite. This is
the fiber over n of the total-shape projection for two nonnegative cochain directions. -/
theorem upNatTotalFiberSetFinite (n : ℕ) :
    (ComplexShape.π (up ℕ) (up ℕ) (up ℕ) ⁻¹' ({n} : Set ℕ)).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))))
  intro x hx
  have hx' : x.1 + x.2 = n := Set.mem_singleton_iff.mp hx
  exact Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩)

/-- For n ∈ ℕ, the fiber of the nonnegative cochain total projection (p,q) ↦ p+q over {n} is a
finite type. Thus total degree n has finitely many bidegree summands. -/
instance upNatTotalFiberFinite (n : ℕ) :
    Finite ((ComplexShape.π (up ℕ) (up ℕ) (up ℕ)) ⁻¹' {n}) := by
  let _ := (upNatTotalFiberSetFinite n).fintype
  infer_instance

/-- The total-shape projection ℕ² → ℕ, (p,q) ↦ p+q, for two nonnegative cochain directions has
finite fibers in every total degree. -/
instance upNatTotalFiniteFibers :
    GradedObject.FiniteFibers
      (ComplexShape.π (up ℕ) (up ℕ) (up ℕ)) :=
  fun _ => inferInstance

/-- The total projection for two unit-step nonnegative cochain shapes, taking (p,q) to p+q in the
nonnegative cochain shape, has finite fibers in every natural-number degree. -/
instance up'NatTotalFiniteFibers :
    GradedObject.FiniteFibers
      (ComplexShape.π (up' (1 : ℕ)) (up' (1 : ℕ)) (up ℕ)) := by
  intro n
  change Finite ((ComplexShape.π (up ℕ) (up ℕ) (up ℕ)) ⁻¹' {n})
  infer_instance

end ComplexShape

namespace HomologicalComplex₂

/-- Let C be preadditive with finite coproducts and B a bicomplex with both cochain directions
indexed by ℕ. Then B has a total cochain complex with degree-n term the finite coproduct of
B_{p,q} over p+q=n and differential the sum of the two signed total contributions. -/
theorem hasTotalUpNat
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]
    (B : HomologicalComplex₂ C (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)) :
    B.HasTotal (ComplexShape.up ℕ) :=
  inferInstance

/-- Let C be preadditive with finite coproducts and B a bicomplex whose two shapes are the unit-step
cochain shape on ℕ. It has a nonnegative total cochain complex with degree-n term ⨁_{p+q=n}
B_{p,q} and the canonical signed total differential. -/
theorem hasTotalUp'Nat
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]
    (B : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) :
    B.HasTotal (ComplexShape.up ℕ) :=
  inferInstance

end HomologicalComplex₂

end
