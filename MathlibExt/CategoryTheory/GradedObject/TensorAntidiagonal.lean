/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.Kunneth.Edge
public import Mathlib.CategoryTheory.GradedObject.Monoidal

/-!
# Actual graded tensor fibres and finite antidiagonal biproducts

This is the native addition-fibre coproduct comparison for arbitrary graded
objects, not just homology of same-world module complexes. Both directions
are native injections/descent maps. It reuses the existing finite natural
antidiagonal type and supplies no comparison certificate.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.GradedObject.TensorAntidiagonal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasFiniteBiproducts C]

/-- The finite antidiagonal indexing pairs of nonnegative degrees. -/
abbrev Index (n : ℕ) := HomologicalComplex.KunnethTensorIndex n

variable (X Y : GradedObject ℕ C) [GradedObject.HasTensor X Y]

/-- The canonical map from the actual tensor coproduct to its finite biproduct. -/
def toBiproduct (n : ℕ) : GradedObject.Monoidal.tensorObj X Y n ⟶
    ⨁ fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2 :=
  GradedObject.Monoidal.tensorObjDesc fun p q h =>
    biproduct.ι (fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2)
      ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩

/-- The canonical inverse map from the antidiagonal biproduct. -/
def fromBiproduct (n : ℕ) : (⨁ fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2) ⟶
    GradedObject.Monoidal.tensorObj X Y n :=
  biproduct.desc fun ij => GradedObject.Monoidal.ιTensorObj X Y ij.val.1 ij.val.2 n
    (Finset.mem_antidiagonal.mp ij.property)

@[reassoc (attr := simp)]
theorem ι_toBiproduct (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj X Y p q n h ≫ toBiproduct X Y n =
      biproduct.ι (fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2)
        ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩ :=
  GradedObject.Monoidal.ι_tensorObjDesc _ p q h

@[reassoc (attr := simp)]
theorem ι_fromBiproduct (n : ℕ) (ij : Index n) :
    biproduct.ι (fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2) ij ≫ fromBiproduct X Y n =
      GradedObject.Monoidal.ιTensorObj X Y ij.val.1 ij.val.2 n
        (Finset.mem_antidiagonal.mp ij.property) :=
  biproduct.ι_desc _ _

/-- The earned canonical antidiagonal coproduct-to-biproduct isomorphism. -/
def iso (n : ℕ) : GradedObject.Monoidal.tensorObj X Y n ≅
    ⨁ fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2 where
  hom := toBiproduct X Y n
  inv := fromBiproduct X Y n
  hom_inv_id := by
    apply GradedObject.Monoidal.tensorObj_ext
    intro p q h
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ fromBiproduct X Y n) (ι_toBiproduct X Y p q n h)).trans
        ((ι_fromBiproduct X Y n _).trans (Category.comp_id _).symm))
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro ij
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ toBiproduct X Y n) (ι_fromBiproduct X Y n ij)).trans
        ((ι_toBiproduct X Y _ _ n _).trans (Category.comp_id _).symm))

end CategoryTheory.GradedObject.TensorAntidiagonal
