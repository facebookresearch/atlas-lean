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

public import MathlibExt.CategoryTheory.Functor.BifunctorFold
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor

/-!
# Finite tensor folds with independently sized coefficients

A prefix module and a finite ordered family of coefficient modules form
a left-associated tensor fold. Prefix morphisms act functorially, and
isomorphisms of every factor give a natural fold isomorphism. The
ring and the two carrier universes are independent.

The fold is the specialization of the general bifunctor action. Its
isomorphism constructor retains native `TensorProduct.congr` maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.TensorFold

variable (R : Type u) [CommRing R]

/-- The left-associated tensor fold of a prefix and an ordered list of modules. -/
abbrev objAt (P : ModuleCat.{max v w} R) (Ms : List (ModuleCat.{w} R)) :
    ModuleCat.{max v w} R :=
  Functor.BifunctorFold.obj
    (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R) P Ms

/-- Tensor a prefix map with identities on all remaining coefficient factors. -/
abbrev mapAt {P Q : ModuleCat.{max v w} R} (f : P ⟶ Q)
    (Ms : List (ModuleCat.{w} R)) : objAt R P Ms ⟶ objAt R Q Ms :=
  Functor.BifunctorFold.map
    (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R) f Ms

@[simp] theorem objAt_nil (P : ModuleCat.{max v w} R) : objAt R P [] = P := rfl

@[simp] theorem objAt_cons (P : ModuleCat.{max v w} R)
    (M : ModuleCat.{w} R) (Ms : List (ModuleCat.{w} R)) :
    objAt R P (M :: Ms) = objAt R (tensorObjAt R P M) Ms := rfl

@[simp] theorem mapAt_nil {P Q : ModuleCat.{max v w} R} (f : P ⟶ Q) :
    mapAt R f [] = f := rfl

@[simp] theorem mapAt_cons {P Q : ModuleCat.{max v w} R} (f : P ⟶ Q)
    (M : ModuleCat.{w} R) (Ms : List (ModuleCat.{w} R)) :
    mapAt R f (M :: Ms) = mapAt R (tensorHomAt R f (𝟙 M)) Ms := rfl

/-- Isomorphisms of the prefix and all coefficient factors act by native tensor congruence. -/
def isoAt (R : Type u) [CommRing R] :
    ∀ {n : ℕ} {P Q : ModuleCat.{max v w} R} (_e : P ≅ Q)
      (M N : Fin n → ModuleCat.{w} R) (_h : ∀ j, M j ≅ N j),
      objAt R P (List.ofFn M) ≅ objAt R Q (List.ofFn N)
  | 0, P, Q, e, M, N, h => by
      simpa only [List.ofFn_zero, objAt, Functor.BifunctorFold.obj] using e
  | n + 1, P, Q, e, M, N, h => by
      simpa only [List.ofFn_succ, objAt, Functor.BifunctorFold.obj] using
        (isoAt R (TensorProduct.congr e.toLinearEquiv (h 0).toLinearEquiv).toModuleIso
          (fun j : Fin n => M j.succ) (fun j : Fin n => N j.succ)
          (fun j : Fin n => h j.succ))

private theorem tensorIso_eq {P Q : ModuleCat.{max v w} R} {M N : ModuleCat.{w} R}
    (e : P ≅ Q) (h : M ≅ N) :
    (TensorProduct.congr e.toLinearEquiv h.toLinearEquiv).toModuleIso =
      (Functor.uncurry.obj
        (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
          ModuleCat.{max v w} R)).mapIso (Iso.prod e h) := by
  apply Iso.ext
  change tensorHomAt R e.hom h.hom =
    (Functor.uncurry.obj
      (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
        ModuleCat.{max v w} R)).map (Prod.mkHom e.hom h.hom)
  exact (tensorBifunctorAt_uncurry_map R (Prod.mkHom e.hom h.hom)).symm

/-- Native tensor congruences agree with the general functorial fold isomorphism. -/
theorem isoAt_eq_bifunctorFold {n : ℕ} {P Q : ModuleCat.{max v w} R}
    (e : P ≅ Q) (M N : Fin n → ModuleCat.{w} R) (h : ∀ j, M j ≅ N j) :
    isoAt R e M N h =
      Functor.BifunctorFold.iso
        (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
          ModuleCat.{max v w} R) e M N h := by
  induction n generalizing P Q with
  | zero =>
      simp only [isoAt, Functor.BifunctorFold.iso]
  | succ n ih =>
      simp only [isoAt, Functor.BifunctorFold.iso, tensorIso_eq, ih]

/-- A prefix square commutes after tensoring all coefficient isomorphisms. -/
theorem isoAt_naturality {n : ℕ} {P Q P' Q' : ModuleCat.{max v w} R}
    (f : P ⟶ P') (g : Q ⟶ Q') (e : P ≅ Q) (e' : P' ≅ Q')
    (M N : Fin n → ModuleCat.{w} R) (h : ∀ j, M j ≅ N j)
    (hprefix : f ≫ e'.hom = e.hom ≫ g) :
    mapAt R f (List.ofFn M) ≫ (isoAt R e' M N h).hom =
      (isoAt R e M N h).hom ≫ mapAt R g (List.ofFn N) := by
  rw [isoAt_eq_bifunctorFold, isoAt_eq_bifunctorFold]
  exact Functor.BifunctorFold.iso_naturality
    (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R) f g e e' M N h hprefix

end ModuleCat.TensorFold
