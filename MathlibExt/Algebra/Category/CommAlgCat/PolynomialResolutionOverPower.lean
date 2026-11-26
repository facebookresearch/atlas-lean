/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Comonad.Over
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentProjective
public import MathlibExt.CategoryTheory.Comonad.CobarCosimplicial

/-!
# Polynomial-comonad powers over a coefficient algebra

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The polynomial
comonad lifts to `Over A`, sending `P→A` to `T(P)→P→A`. Its powers have underlying algebras
`T^n(P)` and the corresponding iterated counit maps to `A`.

The `(n+1)`st slice-comonad power is naturally isomorphic to the degree-`n` polynomial
resolution algebra over `A`. The comparison identifies their underlying algebra maps and their
augmentations; the augmentation successor formula is `ε_{n+1}(P)=ε_n(TP) ≫ ε_T(P)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- For a commutative ring `k` and `k`-algebra `A`, `polynomialOverComonad k A` is the polynomial
comonad lifted to `Over A`. On `P=(B→A)`, its underlying object is `T(B)` and its structure
map to `A` is the polynomial counit `T(B)→B` followed by `P.hom`. -/
abbrev polynomialOverComonad : Comonad (Over A) :=
  Comonad.overComonad (polynomialComonad.{u, v} k) A

/-- Let `k` be a commutative ring, `P` a `k`-algebra, and `n : ℕ`. Writing `T` for the polynomial
comonad and `ε_n(P)` for the degree-`n` resolution augmentation, `ε_{n+1}(P) = ε_n(TP) ≫
ε_T(P)`. Both sides are algebra morphisms `T^{n+2}P → P`. -/
@[reassoc]
theorem polynomialResolution_augmentation_shift (P : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k P).hom.app (op ⦋n + 1⦌) =
      (polynomialResolution.{u, v} k ((polynomialComonad.{u, v} k).obj P)).hom.app (op ⦋n⦌) ≫
        (polynomialComonad.{u, v} k).ε.app P := by
  have h := polynomialResolution_augmentation_naturality.{u, v} k P
    (SimplexCategory.δ (Fin.last (n + 1) : Fin (n + 2))).op
  rw [polynomialResolution_map_δ, Comonad.cobarEpsilonAtPos, Fin.rev_last,
    ] at h
  have hε : (polynomialComonad.{u, v} k).epsilonAtPos (n + 1) 0 P =
      (polynomialPower.{u, v} k (n + 1)).map ((polynomialComonad.{u, v} k).ε.app P) := by
    exact Comonad.epsilonAtPos_zero_eq _ _ _
  have h' := (congrArg (fun f => f ≫ (polynomialResolution.{u, v} k P).hom.app (op ⦋n⦌)) hε.symm).trans h
  exact h'.symm.trans
    (polynomialResolutionMap_augmentation.{u, v} k
      ((polynomialComonad.{u, v} k).ε.app P) n)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P,Q∈Over A`, and `f : P → Q`. For `n : ℕ`,
let `q_P,q_Q` be the canonical equality transports from the underlying slice-power objects to
`T^n(P.left),T^n(Q.left)`. Then `((T_{/A}^n).map f).left ≫ q_Q = q_P ≫ T^n(f.left)`, where
`T_{/A}=polynomialOverComonad k A`. -/
theorem polynomialOverPower_map_naturality (n : ℕ) {P Q : Over A} (f : P ⟶ Q) :
    ((Comonad.comonadPow (polynomialOverComonad k A) n).map f).left ≫
        eqToHom (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A n Q) =
      eqToHom (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A n P) ≫
        (polynomialPower.{u, v} k n).map f.left := by
  induction n generalizing P Q with
  | zero =>
    change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
    rw [Category.comp_id, Category.id_comp]
  | succ n ih => exact ih ((polynomialOverComonad k A).map f)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `n : ℕ`. Under the canonical
identification of `(T_{/A}^{n+1}P).left` with `T^{n+1}(P.left)`, its map to `A` is the
degree-`n` polynomial-resolution augmentation `ε_n(P.left)` followed by `P.hom`. Equivalently,
`(T_{/A}^{n+1}P).hom = q_P ≫ ε_n(P.left) ≫ P.hom`. -/
theorem polynomialOverPower_hom (n : ℕ) (P : Over A) :
    ((Comonad.comonadPow (polynomialOverComonad k A) (n + 1)).obj P).hom =
      eqToHom (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A (n + 1) P) ≫
        (polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌) ≫ P.hom := by
  induction n generalizing P with
  | zero =>
    change (polynomialComonad.{u, v} k).ε.app P.left ≫ P.hom =
      𝟙 _ ≫ (polynomialResolution.{u, v} k P.left).hom.app (op ⦋0⦌) ≫ P.hom
    rw [Category.id_comp, polynomialResolution_augmentation_zero]
    rfl
  | succ n ih =>
    change ((Comonad.comonadPow (polynomialOverComonad k A) (n + 1)).obj
      ((polynomialOverComonad k A).obj P)).hom = _
    rw [ih]
    change eqToHom (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A
        (n + 1) ((polynomialOverComonad k A).obj P)) ≫
        (polynomialResolution.{u, v} k ((polynomialComonad.{u, v} k).obj P.left)).hom.app
          (op ⦋n⦌) ≫ ((polynomialComonad.{u, v} k).ε.app P.left ≫ P.hom) = _
    have h := polynomialResolution_augmentation_shift.{u, v} k P.left n
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => eqToHom (Comonad.overPow_obj_left
        (polynomialComonad.{u, v} k) A (n + 1) ((polynomialOverComonad k A).obj P)) ≫
          f ≫ P.hom) h.symm)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `n : ℕ`. The functor
`polynomialResolutionDegreeOverFunctor k A n : Over A → Over A` sends `P` to its degree-`n`
polynomial resolution algebra with the composed augmentation to `A`. A morphism `f : P → Q`
acts by the degree-`n` component of `polynomialResolutionMap k f.left`. -/
def polynomialResolutionDegreeOverFunctor (n : ℕ) : Over A ⥤ Over A where
  obj P := polynomialResolutionDegreeOver k A P n
  map {P Q} f := Over.homMk
    ((polynomialResolutionMap.{u, v} k f.left).left.app (op ⦋n⦌)) (by
      change ((polynomialResolutionMap.{u, v} k f.left).left.app (op ⦋n⦌)) ≫
        ((polynomialResolution.{u, v} k Q.left).hom.app (op ⦋n⦌) ≫ Q.hom) =
        (polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌) ≫ P.hom
      have h := polynomialResolutionMap_augmentation.{u, v} k f.left n
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ Q.hom) h).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun g => (polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌) ≫ g) f.w))))
  map_id P := by
    apply Over.OverMorphism.ext
    exact congrArg (fun f => f.left.app (op ⦋n⦌))
      ((polynomialResolutionFunctor.{u, v} k).map_id P.left)
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact congrArg (fun f => f.left.app (op ⦋n⦌))
      ((polynomialResolutionFunctor.{u, v} k).map_comp f.left g.left)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `n : ℕ`. The isomorphism
`polynomialOverPowerIso k A n P : T_{/A}^{n+1}(P) ≅ polynomialResolutionDegreeOver k A P n`
uses the canonical equality of underlying algebras with `T^{n+1}(P.left)` and the equality of
their augmentation maps to `A`. -/
def polynomialOverPowerIso (n : ℕ) (P : Over A) :
    (Comonad.comonadPow (polynomialOverComonad k A) (n + 1)).obj P ≅
      polynomialResolutionDegreeOver k A P n :=
  Over.isoMk
    (eqToIso (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A (n + 1) P))
    (polynomialOverPower_hom k A n P).symm

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `n : ℕ`. There is a natural isomorphism
of endofunctors of `Over A`, `T_{/A}^{n+1} ≅ polynomialResolutionDegreeOverFunctor k A n`. Its
component at `P` is `polynomialOverPowerIso k A n P`, and naturality identifies the underlying
slice-power map with the polynomial-power map. -/
def polynomialOverPowerNatIso (n : ℕ) :
    Comonad.comonadPow (polynomialOverComonad k A) (n + 1) ≅
      polynomialResolutionDegreeOverFunctor k A n :=
  NatIso.ofComponents (fun P => by
    change (Comonad.comonadPow (polynomialOverComonad k A) (n + 1)).obj P ≅
      polynomialResolutionDegreeOver k A P n
    exact polynomialOverPowerIso k A n P) (by
    intro P Q f
    apply Over.OverMorphism.ext
    change ((Comonad.comonadPow (polynomialOverComonad k A) (n + 1)).map f).left ≫
        eqToHom (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A (n + 1) Q) =
      eqToHom (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A (n + 1) P) ≫
        (polynomialResolutionMap.{u, v} k f.left).left.app (op ⦋n⦌)
    exact polynomialOverPower_map_naturality k A (n + 1) f)

end CommAlgCat

end
