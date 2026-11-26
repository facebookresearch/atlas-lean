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
# Graded tensor terms as finite antidiagonal biproducts

Let C be a preadditive monoidal category with finite biproducts, and X,Y be ℕ-graded objects
whose graded tensor exists. In degree n, the tensor coproduct over p+q=n is canonically
isomorphic to the finite biproduct ⊕_{p+q=n}(X_p⊗Y_q).

The forward map sends each graded tensor coproduct injection to the corresponding biproduct
injection, and the inverse sends each biproduct injection to the graded tensor injection. The
comparison uses the finite natural antidiagonal and imposes no additional additivity condition
on the tensor functor.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.GradedObject.TensorAntidiagonal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasFiniteBiproducts C]

/-- For n ∈ ℕ, let Index(n) be the finite type of pairs (p,q) ∈ ℕ×ℕ satisfying p+q=n. It is the
subtype of the natural-number antidiagonal of n, used to index the degree-n tensor biproduct. -/
abbrev Index (n : ℕ) := HomologicalComplex.KunnethTensorIndex n

variable (X Y : GradedObject ℕ C) [GradedObject.HasTensor X Y]

/-- Let C be a preadditive monoidal category with finite biproducts, X,Y ℕ-graded objects with
HasTensor X Y, and n ∈ ℕ. Define (X⊗Y)_n → ⊕_{p+q=n}(X_p⊗Y_q) by coproduct descent, sending
each graded tensor injection from X_p⊗Y_q to the biproduct injection indexed by (p,q). The
target is the finite biproduct over the antidiagonal p+q=n. -/
def toBiproduct (n : ℕ) : GradedObject.Monoidal.tensorObj X Y n ⟶
    ⨁ fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2 :=
  GradedObject.Monoidal.tensorObjDesc fun p q h =>
    biproduct.ι (fun ij : Index n => X ij.val.1 ⊗ Y ij.val.2)
      ⟨(p, q), Finset.mem_antidiagonal.mpr h⟩

/-- Let C be a preadditive monoidal category with finite biproducts, X,Y ℕ-graded objects with
HasTensor X Y, and n ∈ ℕ. Define ⊕_{p+q=n}(X_p⊗Y_q) → (X⊗Y)_n by biproduct descent. On the
summand indexed by (p,q), its composite with the biproduct injection is the canonical graded
tensor coproduct injection for p+q=n. -/
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

/-- Let C be a preadditive monoidal category with finite biproducts and X,Y ℕ-graded objects whose
graded tensor exists. For n ∈ ℕ, the injection-preserving maps define an isomorphism (X⊗Y)_n ≅
⊕_{p+q=n}(X_p⊗Y_q). Its forward and inverse maps are respectively coproduct and biproduct
descent using the same antidiagonal summand injections. -/
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
