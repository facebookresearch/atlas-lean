/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.AdditiveResolutionCondition
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Polynomial algebra boundary lifts over an augmentation

Let `k` be a commutative ring and `Q → const A` an augmented simplicial `k`-algebra
whose normalized module augmentation is a quasi-isomorphism. For a polynomial algebra
`k[σ]`, suppose algebra maps `k[σ] → Q_n` satisfy all boundary matching equations and
have a common augmentation `α : k[σ] → A`. Then there is an algebra map
`k[σ] → Q_(n+1)` with exactly those faces and augmentation.

For `n = 0`, the overlap condition is empty. This gives an edge between two degree-zero
maps with common augmentation, oriented by `d₀(edge) = g` and `d₁(edge) = f`.
The variable-type universe is independent of the ground-ring and target-carrier universes.

For the polynomial comparison construction, see Loday, §3.5.2.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u v w

namespace CommAlgCat.PolynomialBoundaryComparison

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)
  (Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
  (σ : Type w)

/--
The boundary matching equations for a family of `n + 2` algebra maps `k[σ] → Q_n`.
For `n > 0` these are `d_(j-1) ∘ faces_i = d_i ∘ faces_j` when `i < j`; for
`n = 0` there are no overlap equations.
-/
def BoundaryCompatible (n : ℕ) :
    (Fin (n + 2) → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌)) → Prop :=
  match n with
  | 0 => fun _ => True
  | n + 1 => fun faces => ∀ (i j : Fin (n + 3)) (hij : i < j),
      (Q.left.δ (j.pred (Fin.ne_zero_of_lt hij))).hom.comp (faces i) =
        (Q.left.δ (i.castPred (Fin.ne_last_of_lt hij))).hom.comp (faces j)

/--
Under additive asphericity of the target, each generator `X x` has a lift in `Q_(n+1)`
with the prescribed faces and augmentation, provided the boundary maps match and
have the common augmentation `α`.
-/
theorem generator_boundary_lift (hQ : additiveResolutionCondition k A Q) (n : ℕ)
    (α : MvPolynomial σ k →ₐ[k] A)
    (faces : Fin (n + 2) → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hfaces : BoundaryCompatible k A Q σ n faces)
    (haug : ∀ j, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j) = α) (x : σ) :
    ∃ y : Q.left.obj (op ⦋n + 1⦌),
      (∀ j : Fin (n + 2), (Q.left.δ j).hom y = faces j (MvPolynomial.X x)) ∧
        (Q.hom.app (op ⦋n + 1⦌)).hom y = α (MvPolynomial.X x) := by
  let P := additiveAugmentedResolution k A Q
  letI : QuasiIso (ModuleResolutionAsphericity.augmentation P) := hQ
  let S := ModuleResolutionAsphericity.underlying P
  let f : Fin (n + 2) → ((SSet.stdSimplex.obj ⦋n⦌) ⟶ S.left) :=
    fun j => SSet.yonedaEquiv.symm (faces j (MvPolynomial.X x))
  have hf : SSet.boundary.IsCompatible f := by
    cases n with
    | zero => trivial
    | succ n =>
      rw [SSet.boundary.isCompatible_succ_iff]
      intro i j hij
      dsimp only [f]
      erw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
        SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm
        (AlgHom.congr_fun (hfaces i j hij) (MvPolynomial.X x))
  let b : (SSet.stdSimplex.obj ⦋n + 1⦌) ⟶
      (SimplicialObject.const (Type (max u v))).obj S.right :=
    SSet.yonedaEquiv.symm (α (MvPolynomial.X x))
  have hcomm : ∀ j : Fin (n + 2), f j ≫ S.hom = SSet.stdSimplex.δ j ≫ b := by
    intro j
    dsimp only [f, b]
    erw [SSet.yonedaEquiv_symm_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
    exact congrArg SSet.yonedaEquiv.symm (AlgHom.congr_fun (haug j) (MvPolynomial.X x))
  have hLift : HasLiftingProperty (SSet.boundary.{max u v} (n + 1)).ι S.hom :=
    ModuleResolutionAsphericity.hasLiftingProperty_boundary_of_quasiIso P (n + 1)
  obtain ⟨φ, hφ, hφaug⟩ := SSet.exists_simplex_lift_boundary hf hLift b hcomm
  refine ⟨SSet.yonedaEquiv φ, ?_, ?_⟩
  · intro j
    have h := congrArg (SSet.yonedaEquiv (X := S.left) (n := ⦋n⦌)) (hφ j)
    rw [SSet.stdSimplex.yonedaEquiv_δ_comp] at h
    have he := (SSet.yonedaEquiv (X := S.left) (n := ⦋n⦌)).apply_symm_apply
      (show S.left.obj (op ⦋n⦌) from faces j (MvPolynomial.X x))
    have hd : S.left.δ j (SSet.yonedaEquiv φ) = (Q.left.δ j).hom (SSet.yonedaEquiv φ) := rfl
    exact hd.symm.trans (h.trans he)
  · let Z := (SimplicialObject.const (Type (max u v))).obj S.right
    have h := congrArg (SSet.yonedaEquiv (X := Z) (n := ⦋n + 1⦌)) hφaug
    rw [SSet.yonedaEquiv_comp] at h
    have he := (SSet.yonedaEquiv (X := Z) (n := ⦋n + 1⦌)).apply_symm_apply
      (show Z.obj (op ⦋n + 1⦌) from α (MvPolynomial.X x))
    have ha : S.hom.app (op ⦋n + 1⦌) (SSet.yonedaEquiv φ) =
        (Q.hom.app (op ⦋n + 1⦌)).hom (SSet.yonedaEquiv φ) := rfl
    exact ha.symm.trans (h.trans he)

/--
The algebra map `k[σ] → Q_(n+1)` extending a compatible family of boundary maps with
common augmentation `α`, constructed by evaluating each variable at a generator lift.
-/
def boundaryLift (hQ : additiveResolutionCondition k A Q) (n : ℕ)
    (α : MvPolynomial σ k →ₐ[k] A)
    (faces : Fin (n + 2) → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hfaces : BoundaryCompatible k A Q σ n faces)
    (haug : ∀ j, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j) = α) :
    MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n + 1⦌) :=
  MvPolynomial.aeval (fun x => Classical.choose
    (generator_boundary_lift k A Q σ hQ n α faces hfaces haug x))

/--
Every face of `boundaryLift` is the corresponding prescribed algebra map `faces_j`.
-/
theorem boundaryLift_faces (hQ : additiveResolutionCondition k A Q) (n : ℕ)
    (α : MvPolynomial σ k →ₐ[k] A)
    (faces : Fin (n + 2) → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hfaces : BoundaryCompatible k A Q σ n faces)
    (haug : ∀ j, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j) = α) (j : Fin (n + 2)) :
    (Q.left.δ j).hom.comp (boundaryLift k A Q σ hQ n α faces hfaces haug) = faces j := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, boundaryLift, MvPolynomial.aeval_X]
  exact (Classical.choose_spec (generator_boundary_lift k A Q σ hQ n α faces hfaces haug x)).1 j

/--
The augmentation of the polynomial boundary lift is exactly the prescribed algebra
map `α : k[σ] → A`.
-/
theorem boundaryLift_augmentation (hQ : additiveResolutionCondition k A Q) (n : ℕ)
    (α : MvPolynomial σ k →ₐ[k] A)
    (faces : Fin (n + 2) → MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋n⦌))
    (hfaces : BoundaryCompatible k A Q σ n faces)
    (haug : ∀ j, (Q.hom.app (op ⦋n⦌)).hom.comp (faces j) = α) :
    (Q.hom.app (op ⦋n + 1⦌)).hom.comp
      (boundaryLift k A Q σ hQ n α faces hfaces haug) = α := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, boundaryLift, MvPolynomial.aeval_X]
  exact (Classical.choose_spec (generator_boundary_lift k A Q σ hQ n α faces hfaces haug x)).2

/--
The algebra edge `k[σ] → Q₁` between two maps `f, g : k[σ] → Q₀` with common
augmentation `α`, using additive asphericity of `Q`; its faces are `d₀ = g` and `d₁ = f`.
-/
def firstPrism (hQ : additiveResolutionCondition k A Q)
    (α : MvPolynomial σ k →ₐ[k] A)
    (f g : MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋0⦌))
    (hf : (Q.hom.app (op ⦋0⦌)).hom.comp f = α)
    (hg : (Q.hom.app (op ⦋0⦌)).hom.comp g = α) :
    MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋1⦌) :=
  boundaryLift k A Q σ hQ 0 α (fun j => Fin.cases g (fun _ => f) j) trivial
    (fun j => Fin.cases hg (fun _ => hf) j)

/--
The zero face of `firstPrism` is the second endpoint map `g`.
-/
@[simp]
theorem firstPrism_zero_face (hQ : additiveResolutionCondition k A Q)
    (α : MvPolynomial σ k →ₐ[k] A)
    (f g : MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋0⦌))
    (hf : (Q.hom.app (op ⦋0⦌)).hom.comp f = α)
    (hg : (Q.hom.app (op ⦋0⦌)).hom.comp g = α) :
    (Q.left.δ (0 : Fin 2)).hom.comp (firstPrism k A Q σ hQ α f g hf hg) = g :=
  boundaryLift_faces k A Q σ hQ 0 α _ _ _ 0

/--
The one face of `firstPrism` is the first endpoint map `f`.
-/
@[simp]
theorem firstPrism_one_face (hQ : additiveResolutionCondition k A Q)
    (α : MvPolynomial σ k →ₐ[k] A)
    (f g : MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋0⦌))
    (hf : (Q.hom.app (op ⦋0⦌)).hom.comp f = α)
    (hg : (Q.hom.app (op ⦋0⦌)).hom.comp g = α) :
    (Q.left.δ (1 : Fin 2)).hom.comp (firstPrism k A Q σ hQ α f g hf hg) = f :=
  boundaryLift_faces k A Q σ hQ 0 α _ _ _ 1

end CommAlgCat.PolynomialBoundaryComparison

end
