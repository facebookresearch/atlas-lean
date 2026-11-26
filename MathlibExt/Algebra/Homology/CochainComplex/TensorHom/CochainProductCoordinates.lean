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
# Full cochain products and a finite projective tensor factor

Let R be a commutative ring and P,J integer cochain complexes of R-modules. Degree-a cochains
identify R-linearly with the full product ∏_s Hom_R(P^s,J^{s+a}), using target-degree
transports for every presentation of s+a.

If V is a finite projective object of the same module category, tensoring this full cochain
product on the right by V gives the product of Hom_R(P^s,J^{s+a}⊗V). A chosen right tensor
degree b introduces the sign (−1)^{sb} at source degree s. Neither P nor J requires support
bounds, finite generation, or projectivity.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]

/-- For a commutative ring R, integer R-module cochain complexes P,J in universe v, and a ∈ ℤ,
there is an R-linear equivalence C^a(P,J) ≃ ∏_{s∈ℤ} Hom_R(P^s,J^{s+a}). It sends f to its
coordinate f_{s,s+a}. The inverse uses the canonical target-term isomorphism to define every
coordinate with s+a=t. -/
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

/-- Let R be a commutative ring, P,J integer R-module cochain complexes, a ∈ ℤ, and f ∈ C^a(P,J).
The source-degree-s coordinate of cochainDiagonalLinearEquiv(f) is the underlying R-linear map
of f_{s,s+a}. -/
theorem cochainDiagonalLinearEquiv_apply
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (f : Cochain P J a) (s : ℤ) :
    cochainDiagonalLinearEquiv R P J a f s = (f.v s (s + a) rfl).hom := rfl

/-- For a commutative ring R, P,J integer R-module cochain complexes, and a family g_s : P^s →ₗ[R]
J^{s+a}, the reconstructed degree-a cochain has coordinate at s+a=t equal to g_s followed by
the canonical isomorphism J^{s+a} ≅ J^t. This formula holds for every presentation of the
target degree. -/
theorem cochainDiagonalLinearEquiv_symm_apply_v
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a : ℤ)
    (g : ∀ s : ℤ, P.X s →ₗ[R] J.X (s + a))
    (s t : ℤ) (hst : s + a = t) :
    ((cochainDiagonalLinearEquiv R P J a).symm g).v s t hst =
      ModuleCat.ofHom (g s) ≫ (HomologicalComplex.XIsoOfEq J hst).hom := rfl

/-- Let R be a commutative ring, F : ℤ → ModuleCat.{v} R a family, and b ∈ ℤ. The map on ∏_s F_s
given by x_s ↦ (−1)^{sb}·x_s is an R-linear equivalence with itself as inverse. The integer
sign is (s*b).negOnePow, whose square is one in every characteristic. -/
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

/-- Let R be a commutative ring, P,J integer cochain complexes in ModuleCat.{v} R, and V a finite
R-module that is projective as an object of ModuleCat.{v} R. For a,b ∈ ℤ there is an R-linear
equivalence C^a(P,J)⊗_R V ≃ ∏_s Hom_R(P^s,J^{s+a}⊗_R V). It combines the full-product tensor
comparison, the finite-projective Hom–tensor comparison in each source degree, and the signs
(−1)^{sb}. The modules in P and J are unrestricted. -/
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

/-- For a commutative ring R, integer module cochain complexes P,J, a finite
categorical-projective module V, f ∈ C^a(P,J), u ∈ V, and a,b,s ∈ ℤ, the s-coordinate of
cochainTensorFiniteFactorEquiv(f⊗u) is the R-linear map x ↦ (−1)^{sb}·(f_{s,s+a}(x)⊗u). The
projectivity and finiteness assumptions are on V, not on either Hom input. -/
theorem cochainTensorFiniteFactorEquiv_tmul
    (P J : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)
    (V : ModuleCat.{v} R) [CategoryTheory.Projective V] [Module.Finite R V]
    (f : Cochain P J a) (u : V) (s : ℤ) :
    cochainTensorFiniteFactorEquiv R P J a b V (f ⊗ₜ[R] u) s =
      (s * b).negOnePow •
        TensorProduct.rTensorHomToHomRTensor (.id R) (P.X s) (J.X (s + a)) V
          ((f.v s (s + a) rfl).hom ⊗ₜ[R] u) := rfl

end CochainComplex.ModuleTensor
