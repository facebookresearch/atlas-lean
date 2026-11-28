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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.CochainProductCoordinates
public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.TensorFiniteDecomposition

/-!
# Inverting Hom–tensor coordinates with a bounded finite projective factor

Let `R : Type u` be a commutative ring and `P`, `J`, and `U` integer cochain complexes in
`ModuleCat.{v} R`. The comparison `Hom_R(P,J) ⊗_R U → Hom_R(P,J ⊗_R U)` sends a tensor from
degrees `(a, b)` to the source-degree-`s` coordinate with sign `(-1)^(s*b)`.

When every `U^b` is finite and categorically projective, project the target Hom coordinates to
the tensor cells of `U`-degree `b`, invert the signed coefficient and integer-product
comparison, and include the resulting element in the source cell `(n - b, b)`.

Summing these inverse pieces over `b ∈ [L, N]` gives a two-sided inverse in degree `n` if
`U^b` is zero below `L` and above `N`. The Hom source `P` and target `J` are unrestricted, and
the scalar and carrier universes are independent.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
open scoped BigOperators TensorProduct

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]
  (P J U : CochainComplex (ModuleCat.{v} R) ℤ)
  [∀ b : ℤ, CategoryTheory.Projective (U.X b)] [∀ b : ℤ, Module.Finite R (U.X b)]

local instance (K L : CochainComplex (ModuleCat.{v} R) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (ModuleCat.tensorBifunctorAt R) (.up ℤ) := by
  intro n
  infer_instance

/-- Projection of a tensor-valued Hom cochain to one factor degree.

For a degree-`n` cochain `z : Hom_R(P, J ⊗ U)`, project its degree-`s` value to the cell
`J^(s+n-b) ⊗ U^b`. These maps form an integer-indexed family of linear maps from `P^s`. -/
def homTensorFiniteFactorProjected (n b : ℤ) :
    Cochain P (complexAt R J U) n →ₗ[R]
      ∀ s : ℤ, P.X s →ₗ[R] J.X (s + (n - b)) ⊗[R] U.X b :=
  LinearMap.pi (fun s =>
    (LinearMap.llcomp R (P.X s) ((complexAt R J U).X (s + n))
      (J.X (s + (n - b)) ⊗[R] U.X b)
      (tensorCellProjection R J U (s + (n - b)) b (s + n)).hom).comp
        ((LinearMap.proj s).comp
          (cochainDiagonalLinearEquiv R P (complexAt R J U) n).toLinearMap))

omit [∀ b : ℤ, CategoryTheory.Projective (U.X b)]
  [∀ b : ℤ, Module.Finite R (U.X b)] in
/-- Coordinate formula for one factor-degree Hom projection.

At source degree `s`, the projected family is the component `z_(s,s+n)` followed by the
tensor-cell projection onto `J^(s+n-b) ⊗ U^b`. -/
theorem homTensorFiniteFactorProjected_apply (n b : ℤ)
    (z : Cochain P (complexAt R J U) n) (s : ℤ) :
    homTensorFiniteFactorProjected R P J U n b z s =
      (tensorCellProjection R J U (s + (n - b)) b (s + n)).hom.comp
        (z.v s (s + n) rfl).hom := rfl

/-- Hom–tensor comparison on an arbitrary finite-factor summand tensor.

For `a + b = n` and any `t ∈ Hom_R(P,J)^a ⊗ U^b`, include `t` in the source total and apply
the Hom–tensor comparison. At source degree `s`, its value is the tensor-cell inclusion of the
signed coefficient-coordinate equivalence applied to `t` at `s` and evaluated on `x : P^s`. -/
theorem homTensorDegree_ι_finiteFactor_v
    (n a b : ℤ) (hab : a + b = n) (t : Cochain P J a ⊗[R] U.X b)
    (s q : ℤ) (hsq : s + n = q) (x : P.X s) :
    (((homTensorDegree R P J U n).hom
      ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
        (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)).v s q hsq).hom x =
      (HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        (s + a) b q (by change s + a + b = q; omega)).hom
          ((cochainTensorFiniteFactorEquiv R P J a b (U.X b) t s) x) := by
  let S := complexAt R (linearComplex R P J) U
  let T := complexAt R J U
  let iS : ModuleCat.tensorObjAt R ((linearComplex R P J).X a) (U.X b) ⟶ S.X n :=
    HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
      (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab
  let iT : ModuleCat.tensorObjAt R (J.X (s + a)) (U.X b) ⟶ T.X q :=
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
      (s + a) b q (by change s + a + b = q; omega)
  let E : Cochain P T n →ₗ[R] T.X q :=
    { toFun := fun w => (w.v s q hsq).hom x
      map_add' := fun w w' => by rw [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
      map_smul' := fun r w => by
        rw [RingHom.id_apply, Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply] }
  let EY : (∀ k : ℤ, P.X k →ₗ[R] J.X (k + a) ⊗[R] U.X b) →ₗ[R] T.X q :=
    { toFun := fun w => iT.hom (w s x)
      map_add' := fun w w' => by
        rw [Pi.add_apply, LinearMap.add_apply]
        exact iT.hom.map_add _ _
      map_smul' := fun r w => by
        rw [RingHom.id_apply, Pi.smul_apply, LinearMap.smul_apply]
        exact iT.hom.map_smul _ _ }
  let L : Cochain P J a ⊗[R] U.X b →ₗ[R] T.X q :=
    E.comp ((homTensorDegree R P J U n).hom.comp iS.hom)
  let M : Cochain P J a ⊗[R] U.X b →ₗ[R] T.X q :=
    EY.comp (cochainTensorFiniteFactorEquiv R P J a b (U.X b)).toLinearMap
  have h : L = M := by
    apply TensorProduct.ext'
    intro f u
    change ((((homTensorDegree R P J U n).hom
      (mkAt R (linearComplex R P J) U a b n hab f u)).v s q hsq).hom x) =
      iT.hom ((cochainTensorFiniteFactorEquiv R P J a b (U.X b) (f ⊗ₜ[R] u) s) x)
    rw [homTensorDegree_mk_v R P J U n a b hab f u s q hsq x,
      cochainTensorFiniteFactorEquiv_tmul]
    simp only [Units.smul_def, LinearMap.smul_apply,
      TensorProduct.rTensorHomToHomRTensor_apply]
    exact (map_zsmul iT.hom _ _).symm
  exact congrArg (fun h : Cochain P J a ⊗[R] U.X b →ₗ[R] T.X q => h t) h

/-- Projection recovers the matching signed coefficient coordinates.

Apply the degree-`n` comparison to the source cell `(n - b, b)` and project to factor degree
`b`. The result is `cochainTensorFiniteFactorEquiv` of the cell tensor, as a full integer
family of linear maps. -/
theorem homTensorFiniteFactorProjected_forward
    (n b : ℤ) (t : Cochain P J (n - b) ⊗[R] U.X b) :
    homTensorFiniteFactorProjected R P J U n b
      ((homTensorDegree R P J U n).hom
        ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - b) b n
            (by change n - b + b = n; omega)).hom t)) =
      cochainTensorFiniteFactorEquiv R P J (n - b) b (U.X b) t := by
  funext s
  apply LinearMap.ext
  intro x
  rw [homTensorFiniteFactorProjected_apply]
  change (tensorCellProjection R J U (s + (n - b)) b (s + n)).hom
    ((((homTensorDegree R P J U n).hom
      ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
        (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - b) b n
          (by change n - b + b = n; omega)).hom t)).v
          s (s + n) rfl).hom x) = _
  rw [homTensorDegree_ι_finiteFactor_v]
  have hi := tensorCellProjection_ι R J U (s + (n - b)) b (s + n)
    (by change s + (n - b) + b = s + n; omega)
  have hv := congrArg (fun f : ModuleCat.tensorObjAt R (J.X (s + (n - b))) (U.X b) ⟶
      ModuleCat.tensorObjAt R (J.X (s + (n - b))) (U.X b) =>
        f.hom ((cochainTensorFiniteFactorEquiv R P J (n - b) b (U.X b) t s) x)) hi
  exact hv

/-- Projection of a different factor degree vanishes.

For a tensor in source cell `(a, b)` with `a + b = n`, the forward Hom–tensor comparison has
zero projected family in factor degree `k` whenever `k ≠ b`. -/
theorem homTensorFiniteFactorProjected_forward_eq_zero
    (n a b k : ℤ) (hab : a + b = n) (hkb : k ≠ b)
    (t : Cochain P J a ⊗[R] U.X b) :
    homTensorFiniteFactorProjected R P J U n k
      ((homTensorDegree R P J U n).hom
        ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)) = 0 := by
  funext s
  apply LinearMap.ext
  intro x
  rw [homTensorFiniteFactorProjected_apply]
  change (tensorCellProjection R J U (s + (n - k)) k (s + n)).hom
    ((((homTensorDegree R P J U n).hom
      ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
        (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)).v
          s (s + n) rfl).hom x) = 0
  rw [homTensorDegree_ι_finiteFactor_v]
  have hi := tensorCellProjection_ι_eq_zero R J U (s + (n - k)) k (s + n)
    (s + a) b (by omega) (Or.inr hkb.symm)
  have hv := congrArg (fun f : ModuleCat.tensorObjAt R (J.X (s + a)) (U.X b) ⟶
      ModuleCat.tensorObjAt R (J.X (s + (n - k))) (U.X k) =>
        f.hom ((cochainTensorFiniteFactorEquiv R P J a b (U.X b) t s) x)) hi
  exact hv

/-- One factor-degree piece of the Hom–tensor inverse.

Project a target degree-`n` cochain to factor degree `b`, apply the inverse signed coefficient
equivalence, and include the result in source total cell `(n - b, b)`. Finite projectivity of
the factor terms supplies the coefficient equivalence. -/
def homTensorFiniteFactorInversePiece (n b : ℤ) :
    Cochain P (complexAt R J U) n →ₗ[R]
      (complexAt R (linearComplex R P J) U).X n :=
  (HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
    (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - b) b n (by change n - b + b = n; omega)).hom.comp
      ((cochainTensorFiniteFactorEquiv R P J (n - b) b (U.X b)).symm.toLinearMap.comp
        (homTensorFiniteFactorProjected R P J U n b))

/-- Finite sum of factor-degree inverse pieces.

For integer bounds `L` and `N`, sum the inverse pieces in factor degrees `b ∈ Finset.Icc L N`
to define a linear map from target degree-`n` Hom cochains to the source Hom–tensor total. -/
def homTensorFiniteFactorInverseDegree (L N n : ℤ) :
    Cochain P (complexAt R J U) n →ₗ[R]
      (complexAt R (linearComplex R P J) U).X n :=
  ∑ b ∈ Finset.Icc L N, homTensorFiniteFactorInversePiece R P J U n b

/-- Matching inverse piece recovers a source summand tensor.

For `a + b = n`, applying the forward comparison to any tensor in cell `(a, b)` and then the
inverse piece for degree `b` returns its source-total inclusion. -/
theorem homTensorFiniteFactorInversePiece_forward
    (n a b : ℤ) (hab : a + b = n) (t : Cochain P J a ⊗[R] U.X b) :
    homTensorFiniteFactorInversePiece R P J U n b
      ((homTensorDegree R P J U n).hom
        ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)) =
      (HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
        (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t := by
  have ha : a = n - b := by omega
  subst a
  change (HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
    (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - b) b n
      (by change n - b + b = n; omega)).hom
      ((cochainTensorFiniteFactorEquiv R P J (n - b) b (U.X b)).symm
        (homTensorFiniteFactorProjected R P J U n b
          ((homTensorDegree R P J U n).hom
            ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
              (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - b) b n
                (by change n - b + b = n; omega)).hom t)))) = _
  rw [homTensorFiniteFactorProjected_forward, LinearEquiv.symm_apply_apply]

/-- Nonmatching inverse piece vanishes on a source summand.

For a source cell `(a, b)`, the inverse piece in factor degree `k ≠ b` sends its forward image
to zero. -/
theorem homTensorFiniteFactorInversePiece_forward_eq_zero
    (n a b k : ℤ) (hab : a + b = n) (hkb : k ≠ b)
    (t : Cochain P J a ⊗[R] U.X b) :
    homTensorFiniteFactorInversePiece R P J U n k
      ((homTensorDegree R P J U n).hom
        ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)) = 0 := by
  change (HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
    (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - k) k n
      (by change n - k + k = n; omega)).hom
      ((cochainTensorFiniteFactorEquiv R P J (n - k) k (U.X k)).symm
        (homTensorFiniteFactorProjected R P J U n k
          ((homTensorDegree R P J U n).hom
            ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
              (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)))) = 0
  rw [homTensorFiniteFactorProjected_forward_eq_zero R P J U n a b k hab hkb t]
  simp only [map_zero]
  exact (HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
    (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - k) k n
      (by change n - k + k = n; omega)).hom.map_zero

/-- Bounded-factor inverse sum is a left inverse.

If every factor term `U^b` is zero for `b < L` and for `N < b`, the finite inverse sum
followed after the degree-`n` comparison is the identity on the source Hom–tensor total
degree. -/
theorem homTensorFiniteFactorInverseDegree_leftInverse (L N n : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) :
    Function.LeftInverse (homTensorFiniteFactorInverseDegree R P J U L N n)
      (homTensorDegree R P J U n).hom := by
  have h : homTensorDegree R P J U n ≫
      ModuleCat.ofHom (homTensorFiniteFactorInverseDegree R P J U L N n) =
      𝟙 ((complexAt R (linearComplex R P J) U).X n) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    by_cases hb : b ∈ Finset.Icc L N
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change homTensorFiniteFactorInverseDegree R P J U L N n
        ((homTensorDegree R P J U n).hom
          ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
            (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)) =
        (HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t
      let y : Cochain P (complexAt R J U) n := (homTensorDegree R P J U n).hom
        ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab).hom t)
      have hs : homTensorFiniteFactorInverseDegree R P J U L N n y =
          ∑ k ∈ Finset.Icc L N, homTensorFiniteFactorInversePiece R P J U n k y := by
        exact LinearMap.sum_apply _ _ _
      let i₀ : ModuleCat.tensorObjAt R ((linearComplex R P J).X a) (U.X b) ⟶
          (complexAt R (linearComplex R P J) U).X n :=
        HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
          (ModuleCat.tensorBifunctorAt R) (.up ℤ) a b n hab
      have hm : (∑ k ∈ Finset.Icc L N, homTensorFiniteFactorInversePiece R P J U n k y) =
          homTensorFiniteFactorInversePiece R P J U n b y := by
        apply Finset.sum_eq_single b
        · intro k hk hkb
          exact homTensorFiniteFactorInversePiece_forward_eq_zero R P J U n a b k hab hkb t
        · intro hbn
          exact False.elim (hbn hb)
      have hf : homTensorFiniteFactorInversePiece R P J U n b y = i₀.hom t :=
        homTensorFiniteFactorInversePiece_forward R P J U n a b hab t
      exact hs.trans (hm.trans hf)
    · have hz : IsZero (U.X b) := by
        by_cases h : b < L
        · exact hUlo b h
        · have h' : N < b := by
            simp only [Finset.mem_Icc] at hb
            omega
          exact hUhi b h'
      have hCell : IsZero (ModuleCat.tensorObjAt R ((linearComplex R P J).X a) (U.X b)) :=
        ((ModuleCat.tensorBifunctorAt R).obj ((linearComplex R P J).X a)).map_isZero hz
      exact hCell.eq_of_src _ _
  intro z
  have hv := congrArg (fun f : (complexAt R (linearComplex R P J) U).X n ⟶
      (complexAt R (linearComplex R P J) U).X n => f.hom z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.id_apply] using hv

/-- Forward image of one inverse piece is cell projection and reinclusion.

For a target cochain `z`, applying its factor-degree-`b` inverse piece and then the forward
comparison, at source degree `s`, gives the tensor-cell projection of `z_(s,s+n)(x)` onto
`J^(s+n-b) ⊗ U^b` followed by reinclusion. -/
theorem homTensorDegree_finiteFactorInversePiece_v (n b s : ℤ)
    (z : Cochain P (complexAt R J U) n) (x : P.X s) :
    (((homTensorDegree R P J U n).hom
      (homTensorFiniteFactorInversePiece R P J U n b z)).v s (s + n) rfl).hom x =
      (HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
        (s + (n - b)) b (s + n) (by change s + (n - b) + b = s + n; omega)).hom
          ((tensorCellProjection R J U (s + (n - b)) b (s + n)).hom
            ((z.v s (s + n) rfl).hom x)) := by
  unfold homTensorFiniteFactorInversePiece
  change (((homTensorDegree R P J U n).hom
    ((HomologicalComplex.ιMapBifunctor (linearComplex R P J) U
      (ModuleCat.tensorBifunctorAt R) (.up ℤ) (n - b) b n (by change n - b + b = n; omega)).hom
        ((cochainTensorFiniteFactorEquiv R P J (n - b) b (U.X b)).symm
          (homTensorFiniteFactorProjected R P J U n b z)))).v s (s + n) rfl).hom x = _
  rw [homTensorDegree_ι_finiteFactor_v, LinearEquiv.apply_symm_apply,
    homTensorFiniteFactorProjected_apply]
  rfl

/-- Bounded-factor inverse sum is a right inverse.

If `U` is zero below `L` and above `N`, the degree-`n` comparison applied after the finite
inverse sum is the identity on `Hom_R(P, J ⊗ U)^n`. -/
theorem homTensorFiniteFactorInverseDegree_rightInverse (L N n : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) :
    Function.RightInverse (homTensorFiniteFactorInverseDegree R P J U L N n)
      (homTensorDegree R P J U n).hom := by
  intro z
  apply Cochain.ext
  intro s q hsq
  have hq : q = s + n := hsq.symm
  subst q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let E : Cochain P (complexAt R J U) n →ₗ[R] (complexAt R J U).X (s + n) :=
    { toFun := fun f => (f.v s (s + n) rfl).hom x
      map_add' := fun f g => by
        rw [Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply]
      map_smul' := fun r f => by
        rw [RingHom.id_apply, Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply] }
  change E ((homTensorDegree R P J U n).hom
    (homTensorFiniteFactorInverseDegree R P J U L N n z)) = E z
  let H : (complexAt R (linearComplex R P J) U).X n →ₗ[R]
      (complexAt R J U).X (s + n) := E.comp (homTensorDegree R P J U n).hom
  have hs : homTensorFiniteFactorInverseDegree R P J U L N n z =
      ∑ b ∈ Finset.Icc L N, homTensorFiniteFactorInversePiece R P J U n b z := by
    exact LinearMap.sum_apply _ _ _
  let i (b : ℤ) : ModuleCat.tensorObjAt R (J.X (s + (n - b))) (U.X b) ⟶
      (complexAt R J U).X (s + n) :=
    HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
      (s + (n - b)) b (s + n) (by change s + (n - b) + b = s + n; omega)
  calc
    H (homTensorFiniteFactorInverseDegree R P J U L N n z) =
        ∑ b ∈ Finset.Icc L N, H (homTensorFiniteFactorInversePiece R P J U n b z) := by
      rw [hs]
      exact map_sum H _ _
    _ = ∑ b ∈ Finset.Icc L N,
        (i b).hom ((tensorCellProjection R J U (s + (n - b)) b (s + n)).hom
          ((z.v s (s + n) rfl).hom x)) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact homTensorDegree_finiteFactorInversePiece_v R P J U n b s z x
    _ = E z := by
      have hi := tensorDegree_id_eq_sum_of_bounded_right R J U L N (s + n) hUlo hUhi
      have hi' : 𝟙 ((complexAt R J U).X (s + n)) =
          ∑ b ∈ Finset.Icc L N, tensorCellProjection R J U (s + (n - b)) b (s + n) ≫ i b := by
        apply hi.trans
        apply Finset.sum_congr rfl
        intro b hb
        let V : {k : ℤ // k + b = s + n} →
            ((complexAt R J U).X (s + n) ⟶ (complexAt R J U).X (s + n)) := fun k =>
          tensorCellProjection R J U k.val b (s + n) ≫
            (HomologicalComplex.ιMapBifunctor J U (ModuleCat.tensorBifunctorAt R) (.up ℤ)
              k.val b (s + n) (by change k.val + b = s + n; exact k.property) :
                ModuleCat.tensorObjAt R (J.X k.val) (U.X b) ⟶ (complexAt R J U).X (s + n))
        let a₀ : {k : ℤ // k + b = s + n} := ⟨s + n - b, by omega⟩
        let a₁ : {k : ℤ // k + b = s + n} := ⟨s + (n - b), by omega⟩
        have ha : a₀ = a₁ := by
          apply Subtype.ext
          dsimp only [a₀, a₁]
          omega
        exact congrArg V ha
      let ev : ((complexAt R J U).X (s + n) ⟶ (complexAt R J U).X (s + n)) →+
          (complexAt R J U).X (s + n) :=
        { toFun := fun f => f.hom ((z.v s (s + n) rfl).hom x)
          map_zero' := by simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
          map_add' := fun f g => by simp only [ModuleCat.hom_add, LinearMap.add_apply] }
      have hv := congrArg ev hi'
      simp only [map_sum] at hv
      change E z = ∑ b ∈ Finset.Icc L N,
        (i b).hom ((tensorCellProjection R J U (s + (n - b)) b (s + n)).hom
          ((z.v s (s + n) rfl).hom x)) at hv
      exact hv.symm

end CochainComplex.ModuleTensor
