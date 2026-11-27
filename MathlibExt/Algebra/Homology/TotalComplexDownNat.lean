/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.TotalComplexExact

/-!
# Total complexes of natural first-quadrant bicomplexes

The fibers of `(p,q) ↦ p+q` are finite. Consequently every bicomplex indexed
by `ComplexShape.down ℕ` in both directions has a direct-sum total complex in
a preadditive category with finite coproducts.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape

/-- The fiber of `(i,j) ↦ i+j` over a natural total degree is finite. -/
instance downNatTotalFiberFinite (n : ℕ) :
    Finite ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n}) := by
  have hπ : ∀ x : ℕ × ℕ, ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) x = x.1 + x.2 :=
    fun _ => rfl
  apply Finite.of_injective
    (f := fun x : (ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)) ⁻¹' {n} =>
      (⟨x.val.1, by
        have hmem : ComplexShape.π (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (ComplexShape.down ℕ) x.val = n :=
          x.property
        rw [hπ] at hmem
        omega⟩ : Fin (n + 1)))
  intro a b hab
  have h1 : a.val.1 = b.val.1 := congrArg Fin.val hab
  have ha : ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) a.val = n := a.property
  have hb : ComplexShape.π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) b.val = n := b.property
  rw [hπ] at ha hb
  have h2 : a.val.2 = b.val.2 := by omega
  exact Subtype.ext (Prod.ext h1 h2)

/-- The natural chain total-shape projection has finite fibers. -/
instance downNatTotalFiniteFibers :
    GradedObject.FiniteFibers
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) :=
  fun _ => inferInstance

end ComplexShape

namespace HomologicalComplex₂

/-- Every natural first-quadrant bicomplex in a category with finite
coproducts has a total complex. The corresponding instance is supplied by
`GradedObject.hasMap_of_finiteFibers`. -/
theorem hasTotalDownNat
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C]
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    B.HasTotal (ComplexShape.down ℕ) :=
  fun _ => inferInstance

end HomologicalComplex₂

end
