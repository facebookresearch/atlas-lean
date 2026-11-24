/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGSourceMore.AlexanderWhitney
public import MathlibExt.CategoryTheory.DGModelContracts
public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Native normalized Alexander–Whitney and tensor degree comparisons

The normalization map is the actual inclusion, Alexander–Whitney
front/back cuts, and normalized Moore projections. Tensor extension
and shifting comparisons fix every homogeneous summand, including
their native integer degrees. No unrelated tensor isomorphism is used.

References: Eilenberg–Zilber; PTVV arXiv:1111.3209v4, §2.1.
The completed Alexander–Whitney source port retains its Tau Ceti credits.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.NegativeTensorNormalizations

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicTopology
open _root_.AlgebraicTopology.DoldKan
open MathlibExt.CategoryTheory.DGModelContracts

universe u
variable {R : Type u} [CommRing R]

/-- The actual normalized Moore Alexander–Whitney chain map. -/
def normalizedAlexanderWhitney (A B : SimplicialObject (ModuleCat.{u} R)) :
    (normalizedMooreComplex (ModuleCat.{u} R)).obj (A ⊗ B) ⟶
      (normalizedMooreComplex (ModuleCat.{u} R)).obj A ⊗
        (normalizedMooreComplex (ModuleCat.{u} R)).obj B :=
  inclusionOfMooreComplexMap (A ⊗ B) ≫ SimplicialObject.alexanderWhitney A B ≫
    (PInftyToNormalizedMooreComplex A ⊗ₘ PInftyToNormalizedMooreComplex B)

/-- The literal extension of a chain complex into nonpositive cochain degrees. -/
def negativeExtension (A : ChainComplex (ModuleCat.{u} R) ℕ) : Cochains R :=
  A.extend (ComplexShape.embeddingUpIntLE 0)

/-- Its homogeneous coefficient remains the actual native chain coefficient. -/
def negativeCoefficient (A : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (a : A.X n) : (negativeExtension A).X (-(n : ℤ)) :=
  (A.extendXIso (ComplexShape.embeddingUpIntLE 0) (by simp)).inv a

/-- Tensor extension is fixed on every original homogeneous chain summand. -/
structure TensorExtensionModel (A B : ChainComplex (ModuleCat.{u} R) ℕ) where
  comparison : negativeExtension (A ⊗ B) ≅ negativeExtension A ⊗ negativeExtension B
  normalized : ∀ (m n : ℕ) (a : A.X m) (b : B.X n),
    (comparison.hom.f (-((m + n : ℕ) : ℤ))).hom
      (negativeCoefficient (A ⊗ B) (m + n)
        ((HomologicalComplex.ιTensorObj A B m n (m + n) rfl).hom
          (TensorProduct.tmul R a b))) =
    (HomologicalComplex.ιTensorObj (negativeExtension A) (negativeExtension B)
      (-(m : ℤ)) (-(n : ℤ)) (-((m + n : ℕ) : ℤ)) (by omega)).hom
        (TensorProduct.tmul R (negativeCoefficient A m a) (negativeCoefficient B n b))

/-- Shifting the first tensor factor has the native sign-free pure-generator formula. -/
structure LeftShiftTensorModel (A B : Cochains R) (t : ℤ) where
  comparison : (A ⊗ B)⟦t⟧ ≅ A⟦t⟧ ⊗ B
  normalized : ∀ (p q : ℤ) (a : A.X p) (b : B.X q),
    (comparison.hom.f (p + q - t)).hom
      (((A ⊗ B).shiftFunctorObjXIso t (p + q - t) (p + q) (by omega)).inv
        ((HomologicalComplex.ιTensorObj A B p q (p + q) rfl).hom
          (TensorProduct.tmul R a b))) =
    (HomologicalComplex.ιTensorObj (A⟦t⟧) B (p - t) q (p + q - t) (by omega)).hom
      (TensorProduct.tmul R
        ((A.shiftFunctorObjXIso t (p - t) p (by omega)).inv a) b)

end MathlibExt.Algebra.Homology.NegativeTensorNormalizations
