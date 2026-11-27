/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.AdditiveResolutionCondition
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Polynomial algebra lifts of augmented simplicial horns

Let `Q → const A` be an augmented simplicial algebra over a commutative ring `k`.
For dimension `n + 1 ≥ 1`, choose a missing face `i : Fin (n + 2)` and compatible
algebra maps `k[σ] → Q_n` on every other face, all with augmentation `α : k[σ] → A`.
There is an algebra map `k[σ] → Q_(n+1)` with those supplied faces and augmentation.

The underlying simplicial module maps fibrantly to its constant augmentation target,
so generators can be lifted across the horn and extended by polynomial evaluation.
For `n = 0` the overlap condition is empty. The polynomial-variable, ground-ring, and
target-carrier universes are independent; additive asphericity of the target is not
needed for this horn lift.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

universe u v w

namespace CommAlgCat.PolynomialHornLift

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)
  (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) (σ : Type w)

/--
The matching equations for the supplied faces of an `(n + 1)`-dimensional horn with
missing face `i`. For supplied indices `j < l` in positive boundary degree,
`d_(l-1) ∘ faces_j = d_j ∘ faces_l`; for `n = 0` there are no overlap conditions.
-/
def Compatible (n : ℕ) : (i : Fin (n + 2)) →
    (∀ j : Fin (n + 2), j ≠ i → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌)) → Prop :=
  match n with
  | 0 => fun _ _ => True
  | n + 1 => fun i faces => ∀ (j l : Fin (n + 3)) (hj : j ≠ i) (hl : l ≠ i) (hjl : j < l),
      (Q.left.δ (l.pred (Fin.ne_zero_of_lt hjl))).hom.comp (faces j hj) =
        (Q.left.δ (j.castPred (Fin.ne_last_of_lt hjl))).hom.comp (faces l hl)

/--
For a compatible horn whose supplied maps have common augmentation `α`, each
polynomial generator has a lift in `Q_(n+1)` with every supplied face value and the
prescribed augmentation value.
-/
theorem generator_lift (n : ℕ) (i : Fin (n + 2)) (α : MvPolynomial σ k →ₐ[k] A)
    (faces : ∀ j : Fin (n + 2), j ≠ i → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hc : Compatible k A Q σ n i faces)
    (ha : ∀ j hj, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j hj) = α) (x : σ) :
    ∃ y : Q.left.obj (op ⦋n + 1⦌),
      (∀ j hj, (Q.left.δ j).hom y = faces j hj (MvPolynomial.X x)) ∧
        (Q.hom.app (op ⦋n + 1⦌)).hom y = α (MvPolynomial.X x) := by
  let R := additiveAugmentedResolution k A Q
  let U := ModuleResolutionAsphericity.underlying R
  letI : Fibration U.hom := ModuleResolutionAsphericity.underlying_module_fibration R
  let faceMaps : ∀ j : Fin (n + 2), j ≠ i → ((SSet.stdSimplex.obj ⦋n⦌) ⟶ U.left) :=
    fun j hj => SSet.yonedaEquiv.symm (faces j hj (MvPolynomial.X x))
  have hface : SSet.horn.IsCompatible faceMaps := by
    cases n with
    | zero => trivial
    | succ n =>
        rw [SSet.horn.isCompatible_iff]
        intro j l hj hl hjl
        dsimp only [faceMaps]
        erw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
          SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
        exact congrArg SSet.yonedaEquiv.symm
          (AlgHom.congr_fun (hc j l hj hl hjl) (MvPolynomial.X x))
  let b : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶
      (SimplicialObject.const (Type (max u v))).obj U.right :=
    SSet.yonedaEquiv.symm (α (MvPolynomial.X x))
  have hcomm : ∀ j hj, faceMaps j hj ≫ U.hom = SSet.stdSimplex.δ j ≫ b := by
    intro j hj
    dsimp only [faceMaps, b]
    erw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (AlgHom.congr_fun (ha j hj) (MvPolynomial.X x))
  obtain ⟨φ, hφ, hφa⟩ := SSet.horn.IsCompatible.exists_lift hface U.hom b hcomm
  refine ⟨SSet.yonedaEquiv φ, ?_, ?_⟩
  · intro j hj
    have h := congrArg (SSet.yonedaEquiv (X := U.left) (n := ⦋n⦌)) (hφ j hj)
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp] at h
    have he := (SSet.yonedaEquiv (X := U.left) (n := ⦋n⦌)).apply_symm_apply
      (show U.left.obj (op ⦋n⦌) from faces j hj (MvPolynomial.X x))
    have hd : U.left.δ j (SSet.yonedaEquiv φ) = (Q.left.δ j).hom (SSet.yonedaEquiv φ) := rfl
    exact hd.symm.trans (h.trans he)
  · let Z := (SimplicialObject.const (Type (max u v))).obj U.right
    have h := congrArg (SSet.yonedaEquiv (X := Z) (n := ⦋n + 1⦌)) hφa
    rw [SSet.yonedaEquiv_comp] at h
    have he := (SSet.yonedaEquiv (X := Z) (n := ⦋n + 1⦌)).apply_symm_apply
      (show Z.obj (op ⦋n + 1⦌) from α (MvPolynomial.X x))
    have ha : U.hom.app (op ⦋n + 1⦌) (SSet.yonedaEquiv φ) =
        (Q.hom.app (op ⦋n + 1⦌)).hom (SSet.yonedaEquiv φ) := rfl
    exact ha.symm.trans (h.trans he)

/--
The algebra map `k[σ] → Q_(n+1)` obtained by evaluating polynomial variables at
chosen generator lifts of the compatible horn. It preserves every supplied face and
the common augmentation `α`.
-/
def lift (n : ℕ) (i : Fin (n + 2)) (α : MvPolynomial σ k →ₐ[k] A)
    (faces : ∀ j : Fin (n + 2), j ≠ i → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hc : Compatible k A Q σ n i faces)
    (ha : ∀ j hj, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j hj) = α) :
    MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n + 1⦌) :=
  MvPolynomial.aeval (fun x => Classical.choose (generator_lift k A Q σ n i α faces hc ha x))

/--
For every face index `j ≠ i`, the `j`-th face of the polynomial horn lift is the
prescribed algebra map `faces_j`.
-/
theorem lift_faces (n : ℕ) (i : Fin (n + 2)) (α : MvPolynomial σ k →ₐ[k] A)
    (faces : ∀ j : Fin (n + 2), j ≠ i → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hc : Compatible k A Q σ n i faces)
    (ha : ∀ j hj, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j hj) = α) (j : Fin (n + 2)) (hj : j ≠ i) :
    (Q.left.δ j).hom.comp (lift k A Q σ n i α faces hc ha) = faces j hj := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, lift, MvPolynomial.aeval_X]
  exact (Classical.choose_spec (generator_lift k A Q σ n i α faces hc ha x)).1 j hj

/--
The augmentation of the polynomial horn lift is the prescribed algebra map
`α : k[σ] → A`.
-/
theorem lift_augmentation (n : ℕ) (i : Fin (n + 2)) (α : MvPolynomial σ k →ₐ[k] A)
    (faces : ∀ j : Fin (n + 2), j ≠ i → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hc : Compatible k A Q σ n i faces)
    (ha : ∀ j hj, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j hj) = α) :
    (Q.hom.app (op ⦋n + 1⦌)).hom.comp (lift k A Q σ n i α faces hc ha) = α := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, lift, MvPolynomial.aeval_X]
  exact (Classical.choose_spec (generator_lift k A Q σ n i α faces hc ha x)).2

end CommAlgCat.PolynomialHornLift

end
