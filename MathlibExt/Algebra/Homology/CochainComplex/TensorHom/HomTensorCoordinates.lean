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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Curry
public import MathlibExt.Algebra.Category.ModuleCat.TensorHomFinite

/-!
# Original coordinates of the Hom–tensor comparison

The degree component is the native sum desc into the original full product Hom.
On a pure summand `(f : Hom(P,J)^a) ⊗ (u : U^b)`, its original P-degree p
component is `(-1)^(p*b) f_p(-) ⊗ u` in the actual tensor total degree.
This owner records the constructed components, independently of the separate
differential law and finite-support inverse.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CochainComplex.HomComplex
open scoped TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]
  (P J U : CochainComplex (ModuleCat.{v} R) ℤ)

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- The original signed summand map, assembled from native evaluation, tensor Hom
and the original tensor coprojection, without a comparison input. -/
def homTensorPairLinear (n a b : ℤ) (hab : a + b = n) :
    Cochain P J a ⊗[R] U.X b →ₗ[R] Cochain P (complexAt R J U) n :=
  LinearMap.pi (fun T : Triplet n => by
    let qJ := T.p + a
    let hq : qJ + b = T.q := by
      change (T.p + a) + b = T.q
      rw [add_assoc, hab, T.hpq]
    let i : ModuleCat.tensorObjAt R (J.X qJ) (U.X b) ⟶ (complexAt R J U).X T.q :=
      HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        qJ b T.q hq
    let ev : Cochain P J a →ₗ[R] (P.X T.p →ₗ[R] J.X qJ) :=
      (ModuleCat.homLinearEquiv (R := R) (S := R)
        (M := P.X T.p) (N := J.X qJ)).toLinearMap.comp
          (productEval R P J a T.p qJ rfl)
    let t : Cochain P J a ⊗[R] U.X b →ₗ[R]
        (P.X T.p →ₗ[R] J.X qJ ⊗[R] U.X b) :=
      (TensorProduct.rTensorHomToHomRTensor (.id R) (P.X T.p) (J.X qJ) (U.X b)).comp
        (TensorProduct.map ev (LinearMap.id : U.X b →ₗ[R] U.X b))
    let post : (P.X T.p →ₗ[R] J.X qJ ⊗[R] U.X b) →ₗ[R]
        (P.X T.p →ₗ[R] (complexAt R J U).X T.q) :=
      LinearMap.llcomp R (P.X T.p) (J.X qJ ⊗[R] U.X b)
        ((complexAt R J U).X T.q) i.hom
    exact (ModuleCat.homLinearEquiv (R := R) (S := R)
      (M := P.X T.p) (N := (complexAt R J U).X T.q)).symm.toLinearMap.comp
        ((T.p * b).negOnePow • (post.comp t)))

/-- Actual pure values characterize every signed original coordinate. -/
theorem homTensorPairLinear_v (n a b : ℤ) (hab : a + b = n)
    (f : Cochain P J a) (u : U.X b) (p q : ℤ) (hpq : p + n = q) (x : P.X p) :
    (((homTensorPairLinear R P J U n a b hab) (f ⊗ₜ[R] u)).v p q hpq).hom x =
      (p * b).negOnePow • mkAt R J U (p + a) b q (by omega)
        ((f.v p (p + a) rfl).hom x) u := rfl

/-- The actual degree component of `Hom(P,J) ⊗ U → Hom(P,J ⊗ U)`. -/
def homTensorDegree (n : ℤ) :
    (complexAt R (linearComplex R P J) U).X n ⟶
      (linearComplex R P (complexAt R J U)).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := linearComplex R P J) (K₂ := U)
    (F := ModuleCat.tensorBifunctorAt R) (c := .up ℤ)
      (fun a b hab => ModuleCat.ofHom (homTensorPairLinear R P J U n a b hab))

/-- The native total desc retains each original Hom cochain/tensor value and sign. -/
theorem homTensorDegree_mk_v (n a b : ℤ) (hab : a + b = n)
    (f : Cochain P J a) (u : U.X b) (p q : ℤ) (hpq : p + n = q) (x : P.X p) :
    ((((homTensorDegree R P J U n).hom
        (mkAt R (linearComplex R P J) U a b n hab f u)).v p q hpq).hom x) =
      (p * b).negOnePow • mkAt R J U (p + a) b q (by omega)
        ((f.v p (p + a) rfl).hom x) u := by
  have h := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := linearComplex R P J) (K₂ := U)
    (F := ModuleCat.tensorBifunctorAt R) (c := .up ℤ)
      (fun a b hab => ModuleCat.ofHom (homTensorPairLinear R P J U n a b hab)) a b hab
  have hv := congrArg (fun m : ModuleCat.tensorObjAt R
      ((linearComplex R P J).X a) (U.X b) ⟶ (linearComplex R P (complexAt R J U)).X n =>
        ((m.hom (f ⊗ₜ[R] u)).v p q hpq).hom x) h
  change ((((homTensorDegree R P J U n).hom
      (mkAt R (linearComplex R P J) U a b n hab f u)).v p q hpq).hom x) =
    (((homTensorPairLinear R P J U n a b hab (f ⊗ₜ[R] u)).v p q hpq).hom x) at hv
  exact hv.trans (homTensorPairLinear_v R P J U n a b hab f u p q hpq x)

/-- A supported original J coordinate can be substituted before evaluating the row. -/
theorem homTensorDegree_mk_v' (n a b : ℤ) (hab : a + b = n)
    (f : Cochain P J a) (u : U.X b) (p j q : ℤ)
    (hpj : p + a = j) (hpq : p + n = q) (x : P.X p) :
    ((((homTensorDegree R P J U n).hom
        (mkAt R (linearComplex R P J) U a b n hab f u)).v p q hpq).hom x) =
      (p * b).negOnePow • mkAt R J U j b q (by omega)
        ((f.v p j hpj).hom x) u := by
  subst j
  exact homTensorDegree_mk_v R P J U n a b hab f u p q hpq x

end CochainComplex.ModuleTensor
