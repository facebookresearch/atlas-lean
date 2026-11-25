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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.HomTensorCoordinates
public import MathlibExt.Algebra.Category.ModuleCat.TensorHomFiniteFactor
public import MathlibExt.Algebra.Category.ModuleCat.TensorIntegerProductFiniteFactor

/-!
# Product cochains and finite-projective tensor factors

Cochains use `HomComplex.Triplet a`, whose diagonal coordinates are the
integer product of module Hom spaces. Product and coefficient comparisons
give the signed tensor-factor comparison with an arbitrary first Hom
source. At source coordinate s, the sign is (-1)^(s*b), where b is the
right tensor degree.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

/-- Diagonal coordinates of the original native product cochain. The inverse
uses the native degree Iso to retain every Triplet presentation. -/
def cochainDiagonalLinearEquiv (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ) :
    Cochain P J a ≃ₗ[R] ∀ s : ℤ, P.X s →ₗ[R] J.X (s + a) where
  toFun f s := (f.v s (s + a) rfl).hom
  invFun g := Cochain.mk (fun s t hst =>
    ModuleCat.ofHom (g s) ≫ (HomologicalComplex.XIsoOfEq J hst).hom)
  left_inv f := by
    apply Cochain.ext
    intro s t hst
    subst t
    change ModuleCat.ofHom ((f.v s (s + a) rfl).hom) ≫
      (HomologicalComplex.XIsoOfEq J rfl).hom = f.v s (s + a) rfl
    simp only [ModuleCat.ofHom_hom, HomologicalComplex.XIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Category.comp_id]
  right_inv g := by
    funext s
    change (ModuleCat.ofHom (g s) ≫
      (HomologicalComplex.XIsoOfEq J rfl).hom).hom = g s
    simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom,
      Category.comp_id, ModuleCat.hom_ofHom]
  map_add' f g := by
    funext s
    exact ModuleCat.hom_add _ _
  map_smul' r f := by
    funext s
    exact ModuleCat.hom_smul _ _

/-- The original cochain evaluation is the forward diagonal coordinate. -/
theorem cochainDiagonalLinearEquiv_apply
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (f : Cochain P J a) (s : ℤ) :
    cochainDiagonalLinearEquiv R P J a f s = (f.v s (s + a) rfl).hom := rfl

/-- Every original off-diagonal Triplet uses the same native degree transport. -/
theorem cochainDiagonalLinearEquiv_symm_apply_v
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (g : ∀ s : ℤ, P.X s →ₗ[R] J.X (s + a))
    (s t : ℤ) (hst : s + a = t) :
    ((cochainDiagonalLinearEquiv R P J a).symm g).v s t hst =
      ModuleCat.ofHom (g s) ≫ (HomologicalComplex.XIsoOfEq J hst).hom := rfl

/-- Original source-degree signs on an actual integer product. Applying the
same signs twice is the identity, including in characteristic two. -/
def integerProductSignsLinearEquiv (F : ℤ → ModuleCat.{v} R) (b : ℤ) :
    (∀ s : ℤ, F s) ≃ₗ[R] ∀ s : ℤ, F s where
  toFun f s := (s * b).negOnePow • f s
  invFun f s := (s * b).negOnePow • f s
  left_inv f := by
    funext s
    change (s * b).negOnePow • ((s * b).negOnePow • f s) = f s
    rw [smul_smul, Int.units_mul_self, one_smul]
  right_inv f := by
    funext s
    change (s * b).negOnePow • ((s * b).negOnePow • f s) = f s
    rw [smul_smul, Int.units_mul_self, one_smul]
  map_add' f g := by
    funext s
    exact smul_add _ _ _
  map_smul' r f := by
    funext s
    simpa only [RingHom.id_apply, Pi.smul_apply, Units.smul_def] using
      (smul_comm ((s * b).negOnePow : ℤ) r (f s))

/-- The original full Hom product, tensored on the right by the original
finite categorical-projective factor, has its actual signed coefficient Iso.
Neither P nor J has a bound or finiteness hypothesis. -/
def cochainTensorFiniteFactorEquiv
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    (V : ModuleCat.{v} R) [CategoryTheory.Projective V] [Module.Finite R V] :
    Cochain P J a ⊗[R] V ≃ₗ[R] ∀ s : ℤ, P.X s →ₗ[R] J.X (s + a) ⊗[R] V :=
  ((cochainDiagonalLinearEquiv R P J a).rTensor V).trans
    ((ModuleCat.integerProductRightTensorIso R
      (fun s => ModuleCat.of R (P.X s →ₗ[R] J.X (s + a))) V).toLinearEquiv.trans
      ((LinearEquiv.piCongrRight (fun s =>
        (ModuleCat.finiteProjectiveTensorFactorHomTensorIso R
          (P.X s) (J.X (s + a)) V).toLinearEquiv)).trans
        (integerProductSignsLinearEquiv R
          (fun s => ModuleCat.of R (P.X s →ₗ[R] J.X (s + a) ⊗[R] V)) b)))

/-- Its forward map is exactly the original signed coefficient map at every
original source degree, on the actual unrestricted cochain family. -/
theorem cochainTensorFiniteFactorEquiv_tmul
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    (V : ModuleCat.{v} R) [CategoryTheory.Projective V] [Module.Finite R V]
    (f : Cochain P J a) (u : V) (s : ℤ) :
    cochainTensorFiniteFactorEquiv R P J a b V (f ⊗ₜ[R] u) s =
      (s * b).negOnePow •
        TensorProduct.rTensorHomToHomRTensor (.id R) (P.X s) (J.X (s + a)) V
          ((f.v s (s + a) rfl).hom ⊗ₜ[R] u) := rfl

end CochainComplex.ModuleTensor
