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
# Total complexes of natural cochain bicomplexes

The fibers of `(p, q) ↦ p + q` are finite for nonnegative cochain shapes.
This supplies totalization from finite coproducts for both the canonical
`up ℕ` shape and its definitionally equal `up' 1` spelling. The file also
provides the canonical symmetry signs for these first-quadrant totals.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape

set_option backward.isDefEq.respectTransparency.types false in
/-- Symmetry signs for totals of nonnegative cochain bicomplexes. -/
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

/-- The `up' 1` spelling of the nonnegative cochain shape uses the canonical
`up ℕ` total-complex structure. -/
instance totalComplexShapeUp'Nat :
    TotalComplexShape (up' (1 : ℕ)) (up' (1 : ℕ)) (up ℕ) :=
  inferInstanceAs (TotalComplexShape (up ℕ) (up ℕ) (up ℕ))

/-- The fiber of `(p, q) ↦ p + q` over a natural cochain total degree is a
finite set. -/
theorem upNatTotalFiberSetFinite (n : ℕ) :
    (ComplexShape.π (up ℕ) (up ℕ) (up ℕ) ⁻¹' ({n} : Set ℕ)).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))))
  intro x hx
  have hx' : x.1 + x.2 = n := Set.mem_singleton_iff.mp hx
  exact Finset.mem_coe.mpr (Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩)

/-- The fiber of the nonnegative cochain total-shape projection is finite. -/
instance upNatTotalFiberFinite (n : ℕ) :
    Finite ((ComplexShape.π (up ℕ) (up ℕ) (up ℕ)) ⁻¹' {n}) := by
  let _ := (upNatTotalFiberSetFinite n).fintype
  infer_instance

/-- The nonnegative cochain total-shape projection has finite fibers. -/
instance upNatTotalFiniteFibers :
    GradedObject.FiniteFibers
      (ComplexShape.π (up ℕ) (up ℕ) (up ℕ)) :=
  fun _ => inferInstance

/-- The `up' 1` spelling of the nonnegative cochain total-shape projection
has finite fibers. -/
instance up'NatTotalFiniteFibers :
    GradedObject.FiniteFibers
      (ComplexShape.π (up' (1 : ℕ)) (up' (1 : ℕ)) (up ℕ)) := by
  intro n
  change Finite ((ComplexShape.π (up ℕ) (up ℕ) (up ℕ)) ⁻¹' {n})
  infer_instance

end ComplexShape

namespace HomologicalComplex₂

/-- Every nonnegative cochain bicomplex in a category with finite coproducts
has a total complex. -/
theorem hasTotalUpNat
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]
    (B : HomologicalComplex₂ C (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)) :
    B.HasTotal (ComplexShape.up ℕ) :=
  inferInstance

/-- Every bicomplex using the `up' 1` spelling in a category with finite
coproducts has a nonnegative cochain total complex. -/
theorem hasTotalUp'Nat
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]
    (B : HomologicalComplex₂ C (ComplexShape.up' (1 : ℕ))
      (ComplexShape.up' (1 : ℕ))) :
    B.HasTotal (ComplexShape.up ℕ) :=
  inferInstance

end HomologicalComplex₂

end
