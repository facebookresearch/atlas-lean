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
# Actual polynomial resolution powers over the augmentation target

The slice-comonad powers retain the original polynomial power objects and maps.
The actual polynomial augmentation satisfies the successor identity obtained
from its last face and native augmented functoriality. This identifies the
slice power's point map with the actual degreewise polynomial augmentation.
It supplies the natural comparison needed by the horizontal replacement proof,
with every point map constructed from the native counit.

Candidate source; UNEXECUTED. This file extends the frozen V3 owners.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The actual polynomial comonad in the slice over A. -/
abbrev polynomialOverComonad : Comonad (Over A) :=
  Comonad.overComonad (polynomialComonad.{u, v} k) A

/-- The native augmentation successor is the same original counit word. -/
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

/-- Forgetting a slice power map retains its actual original power map,
with both object transports displayed. -/
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

/-- The actual slice power point map equals the actual native polynomial augmentation. -/
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

/-- Every actual polynomial degree over A is functorial in the source algebra over A. -/
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

/-- The actual slice power and original polynomial degree have the same augmentation map. -/
def polynomialOverPowerIso (n : ℕ) (P : Over A) :
    (Comonad.comonadPow (polynomialOverComonad k A) (n + 1)).obj P ≅
      polynomialResolutionDegreeOver k A P n :=
  Over.isoMk
    (eqToIso (Comonad.overPow_obj_left (polynomialComonad.{u, v} k) A (n + 1) P))
    (polynomialOverPower_hom k A n P).symm

/-- The full degreewise comparison is the actual natural power comparison in the slice. -/
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
