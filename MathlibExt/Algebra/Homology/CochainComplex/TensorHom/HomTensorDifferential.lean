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
public meta import Mathlib.Tactic.Abel

/-!
# Differential compatibility of the signed Hom–tensor map

For cochains `f ∈ Hom_R(P,J)^a` and `u ∈ U^b`, put `n = a + b`. The signed comparison has
source-degree-`p` factor `(-1)^(p*b)`. Taking its differential gives the three contributions
from `d_J`, `d_U`, and precomposition with `d_P`.

Their signs are respectively `(-1)^(p*b)`, `(-1)^(p*b+p+a)`, and `(-1)^(n+1+(p+1)*b)`. The
last two agree with the signs obtained by taking the source tensor differential first. Thus
the degree maps define a cochain morphism for arbitrary integer complexes `P`, `J`, and `U`.
-/

@[expose] public section
noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]
  (P J U : CochainComplex (ModuleCat.{v} R) ℤ)

/-- Cochain tensor-total generator is additive in its first factor.

For `p + q = n`, the tensor-total class of `(x + x') ⊗ y` is the sum of the classes of `x ⊗ y`
and `x' ⊗ y`. -/
theorem mkAt_add_fst (p q n : ℤ) (h : p + q = n)
    (x x' : J.X p) (y : U.X q) :
    mkAt R J U p q n h (x + x') y =
      mkAt R J U p q n h x y + mkAt R J U p q n h x' y := by
  let i : ModuleCat.tensorObjAt R (J.X p) (U.X q) ⟶ (complexAt R J U).X n :=
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ) p q n h
  change i.hom ((x + x') ⊗ₜ[R] y) = i.hom (x ⊗ₜ[R] y) + i.hom (x' ⊗ₜ[R] y)
  rw [TensorProduct.add_tmul]
  exact i.hom.map_add _ _

/-- Integer units pass through the first tensor-total factor.

For an integer unit `s : ℤˣ`, the tensor-total class of `(s • x) ⊗ y` equals `s` times the
tensor-total class of `x ⊗ y`. -/
theorem mkAt_units_smul_fst (p q n : ℤ) (h : p + q = n)
    (s : ℤˣ) (x : J.X p) (y : U.X q) :
    mkAt R J U p q n h (s • x) y = s • mkAt R J U p q n h x y := by
  let i : ModuleCat.tensorObjAt R (J.X p) (U.X q) ⟶ (complexAt R J U).X n :=
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ) p q n h
  change i.hom ((s • x) ⊗ₜ[R] y) = s • i.hom (x ⊗ₜ[R] y)
  simp only [Units.smul_def]
  rw [← TensorProduct.smul_tmul']
  exact map_zsmul i.hom _ _

/-- Integer scalar multiplication passes through the first tensor-total factor.

For an integer `s`, the tensor-total class of `(s • x) ⊗ y` equals `s` times the class of `x ⊗
y`. -/
theorem mkAt_zsmul_fst (p q n : ℤ) (h : p + q = n)
    (s : ℤ) (x : J.X p) (y : U.X q) :
    mkAt R J U p q n h (s • x) y = s • mkAt R J U p q n h x y := by
  let i : ModuleCat.tensorObjAt R (J.X p) (U.X q) ⟶ (complexAt R J U).X n :=
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ) p q n h
  change i.hom ((s • x) ⊗ₜ[R] y) = s • i.hom (x ⊗ₜ[R] y)
  rw [← TensorProduct.smul_tmul']
  exact map_zsmul i.hom _ _

/-- Differential after the Hom–tensor comparison on a pure cell.

For `a + b = n`, evaluate the differential of the image of `f ⊗ u` at source degree `p`. Its
three terms are the `J` differential with sign `(-1)^(p*b)`, the `U` differential with sign
`(-1)^(p*b+p+a)`, and precomposition by `P.d p (p+1)` with sign `(-1)^(n+1+(p+1)*b)`, in
target total degree `p + n + 1`. -/
theorem delta_homTensorDegree_mk (n a b : ℤ) (hab : a + b = n)
    (f : Cochain P J a) (u : U.X b) (p : ℤ) (x : P.X p) :
    ((δ n (n + 1) ((homTensorDegree R P J U n).hom
      (mkAt R (linearComplex R P J) U a b n hab f u))).v p (p + n + 1)
        (by omega)).hom x =
      (p * b).negOnePow • mkAt R J U (p + a + 1) b (p + n + 1) (by omega)
        ((J.d (p + a) (p + a + 1)).hom ((f.v p (p + a) rfl).hom x)) u +
      ((p * b).negOnePow * (p + a).negOnePow) •
        mkAt R J U (p + a) (b + 1) (p + n + 1) (by omega)
          ((f.v p (p + a) rfl).hom x) ((U.d b (b + 1)).hom u) +
      ((n + 1).negOnePow * ((p + 1) * b).negOnePow) •
        mkAt R J U (p + a + 1) b (p + n + 1) (by omega)
          ((f.v (p + 1) (p + a + 1) (by omega)).hom
            ((P.d p (p + 1)).hom x)) u := by
  let T := complexAt R J U
  let w := (homTensorDegree R P J U n).hom
    (mkAt R (linearComplex R P J) U a b n hab f u)
  have hd := δ_v n (n + 1) rfl w p (p + n + 1) (by omega)
    (p + n) (p + 1) (by omega) rfl
  have hv := congrArg (fun k : P.X p ⟶ T.X (p + n + 1) => k.hom x) hd
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, Units.smul_def, ModuleCat.hom_smul, LinearMap.smul_apply] at hv
  dsimp only [w, T] at hv
  rw [homTensorDegree_mk_v' R P J U n a b hab f u p (p + a) (p + n)
    rfl (by omega) x,
    homTensorDegree_mk_v' R P J U n a b hab f u (p + 1) (p + a + 1)
      (p + n + 1) (by omega) (by omega) ((P.d p (p + 1)).hom x)] at hv
  simp only [Units.smul_def, map_zsmul] at hv
  rw [d_mkAt] at hv
  simpa only [Units.smul_def, Units.val_mul, smul_add, smul_smul, add_assoc] using hv

/-- Hom–tensor comparison after the tensor differential on a pure cell.

For a cell in degrees `(a, b)`, take its source tensor differential and then the comparison in
degree `n + 1`. At source degree `p`, the `J`, `P`, and `U` terms have signs `(-1)^(p*b)`,
`(-1)^(p*b+a+1)`, and `(-1)^(a+p*(b+1))`, respectively. -/
theorem homTensorDegree_d_mk (n a b : ℤ) (hab : a + b = n)
    (f : Cochain P J a) (u : U.X b) (p : ℤ) (x : P.X p) :
    (((homTensorDegree R P J U (n + 1)).hom
      (((complexAt R (linearComplex R P J) U).d n (n + 1)).hom
        (mkAt R (linearComplex R P J) U a b n hab f u))).v p (p + n + 1)
          (by omega)).hom x =
      (p * b).negOnePow • mkAt R J U (p + a + 1) b (p + n + 1) (by omega)
        ((J.d (p + a) (p + a + 1)).hom ((f.v p (p + a) rfl).hom x)) u +
      ((p * b).negOnePow * (a + 1).negOnePow) •
        mkAt R J U (p + a + 1) b (p + n + 1) (by omega)
          ((f.v (p + 1) (p + a + 1) (by omega)).hom
            ((P.d p (p + 1)).hom x)) u +
      (a.negOnePow * (p * (b + 1)).negOnePow) •
        mkAt R J U (p + a) (b + 1) (p + n + 1) (by omega)
          ((f.v p (p + a) rfl).hom x) ((U.d b (b + 1)).hom u) := by
  have hd := d_mkAt R (linearComplex R P J) U a b n hab f u
  let E : Cochain P (complexAt R J U) (n + 1) →ₗ[R]
      (complexAt R J U).X (p + n + 1) :=
    { toFun := fun w => (w.v p (p + n + 1) (by omega)).hom x
      map_add' := fun w w' => by
        rw [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
      map_smul' := fun r w => by
        rw [RingHom.id_apply, Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply] }
  let H : (complexAt R (linearComplex R P J) U).X (n + 1) →ₗ[R]
      (complexAt R J U).X (p + n + 1) :=
    E.comp (homTensorDegree R P J U (n + 1)).hom
  have hv := congrArg H hd
  simp only [Units.smul_def, map_add, map_zsmul] at hv
  have hδ : ((linearComplex R P J).d a (a + 1)).hom f = δ a (a + 1) f := rfl
  rw [hδ] at hv
  change (((homTensorDegree R P J U (n + 1)).hom
      (((complexAt R (linearComplex R P J) U).d n (n + 1)).hom
        (mkAt R (linearComplex R P J) U a b n hab f u))).v p (p + n + 1)
          (by omega)).hom x =
    (((homTensorDegree R P J U (n + 1)).hom
      (mkAt R (linearComplex R P J) U (a + 1) b (n + 1) (by omega)
        (δ a (a + 1) f) u)).v p (p + n + 1) (by omega)).hom x +
      (a.negOnePow : ℤ) • (((homTensorDegree R P J U (n + 1)).hom
        (mkAt R (linearComplex R P J) U a (b + 1) (n + 1) (by omega)
          f ((U.d b (b + 1)).hom u))).v p (p + n + 1) (by omega)).hom x at hv
  rw [homTensorDegree_mk_v' R P J U (n + 1) (a + 1) b (by omega)
      (δ a (a + 1) f) u p (p + a + 1) (p + n + 1) (by omega) (by omega) x,
    homTensorDegree_mk_v' R P J U (n + 1) a (b + 1) (by omega)
      f ((U.d b (b + 1)).hom u) p (p + a) (p + n + 1) rfl (by omega) x] at hv
  have hf := δ_v a (a + 1) rfl f p (p + a + 1) (by omega)
    (p + a) (p + 1) (by omega) rfl
  have hfx := congrArg (fun k : P.X p ⟶ J.X (p + a + 1) => k.hom x) hf
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, Units.smul_def, ModuleCat.hom_smul, LinearMap.smul_apply] at hfx
  rw [hfx] at hv
  simpa only [Units.smul_def, Units.val_mul, mkAt_add_fst, mkAt_zsmul_fst,
    smul_add, smul_smul, add_assoc] using hv

/-- Hom-source sign identity for the tensor comparison.

For integers with `a + b = n`, `(n + 1).negOnePow * ((p + 1)*b).negOnePow = (p*b).negOnePow *
(a + 1).negOnePow`. This identifies the two precomposition signs. -/
theorem homTensor_sign_P (n a b p : ℤ) (hab : a + b = n) :
    (n + 1).negOnePow * ((p + 1) * b).negOnePow =
      (p * b).negOnePow * (a + 1).negOnePow := by
  have h : n + 1 + (p + 1) * b = (p * b + (a + 1)) + (b + b) := by
    rw [add_mul, one_mul]
    omega
  calc
    _ = (n + 1 + (p + 1) * b).negOnePow := (Int.negOnePow_add _ _).symm
    _ = ((p * b + (a + 1)) + (b + b)).negOnePow := congrArg Int.negOnePow h
    _ = ((p * b).negOnePow * (a + 1).negOnePow) * (b.negOnePow * b.negOnePow) := by
      simp only [Int.negOnePow_add]
    _ = _ := by rw [Int.units_mul_self, mul_one]

/-- Tensor-factor sign identity for the Hom comparison.

For arbitrary integers `a`, `b`, and `p`, `(p*b).negOnePow * (p + a).negOnePow = a.negOnePow *
(p*(b+1)).negOnePow`. -/
theorem homTensor_sign_U (a b p : ℤ) :
    (p * b).negOnePow * (p + a).negOnePow =
      a.negOnePow * (p * (b + 1)).negOnePow := by
  have h : p * b + (p + a) = a + p * (b + 1) := by
    rw [mul_add, mul_one]
    omega
  calc
    _ = (p * b + (p + a)).negOnePow := (Int.negOnePow_add _ _).symm
    _ = (a + p * (b + 1)).negOnePow := congrArg Int.negOnePow h
    _ = _ := Int.negOnePow_add _ _

/-- Signed Hom–tensor degree maps commute with differentials.

For every integer `n`, the degree-`n` comparison followed by the target differential equals
the source differential followed by the degree-`n + 1` comparison. -/
theorem homTensorDegree_comm (n : ℤ) :
    homTensorDegree R P J U n ≫ (linearComplex R P (complexAt R J U)).d n (n + 1) =
      (complexAt R (linearComplex R P J) U).d n (n + 1) ≫
        homTensorDegree R P J U (n + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f u
  apply Cochain.ext
  intro p q hpq
  have hq : q = p + n + 1 := by omega
  subst hq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((δ n (n + 1) ((homTensorDegree R P J U n).hom
      (mkAt R (linearComplex R P J) U a b n hab f u))).v p (p + n + 1)
        (by omega)).hom x =
    (((homTensorDegree R P J U (n + 1)).hom
      (((complexAt R (linearComplex R P J) U).d n (n + 1)).hom
        (mkAt R (linearComplex R P J) U a b n hab f u))).v p (p + n + 1)
          (by omega)).hom x
  rw [delta_homTensorDegree_mk, homTensorDegree_d_mk,
    homTensor_sign_P n a b p hab, homTensor_sign_U]
  abel

/-- Signed Hom–tensor cochain morphism.

The degree maps `homTensorDegree R P J U n` and their differential compatibility define a
morphism `Hom_R(P,J) ⊗_R U ⟶ Hom_R(P,J ⊗_R U)` of cochain complexes. -/
def homTensorComparison :
    complexAt R (linearComplex R P J) U ⟶ linearComplex R P (complexAt R J U) where
  f n := homTensorDegree R P J U n
  comm' := by
    intro n m hnm
    change n + 1 = m at hnm
    subst m
    exact homTensorDegree_comm R P J U n

end CochainComplex.ModuleTensor
