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

/-- Let `R` be a commutative ring in universe `u`, `P` an `R`-module with carrier
in `max(v,w)`, and `Ms` an ordered list of `R`-modules with carriers in `w`.
The left tensor fold starts at `P` and tensors each successive factor onto
the right, retaining carrier height `max(v,w)` and the given factor order. -/
abbrev objAt (P : ModuleCat.{max v w} R) (Ms : List (ModuleCat.{w} R)) :
    ModuleCat.{max v w} R :=
  Functor.BifunctorFold.obj
    (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R) P Ms

/-- For a commutative ring `R`, an `R`-linear map `f : P → Q` between modules
with carriers in `max(v,w)`, and an ordered list `Ms` of modules in `w`, tensor
`f` successively with the identity maps of the factors. This gives a morphism
between the left tensor folds with prefixes `P` and `Q`. -/
abbrev mapAt {P Q : ModuleCat.{max v w} R} (f : P ⟶ Q)
    (Ms : List (ModuleCat.{w} R)) : objAt R P Ms ⟶ objAt R Q Ms :=
  Functor.BifunctorFold.map
    (tensorBifunctorAt R : ModuleCat.{max v w} R ⥤ ModuleCat.{w} R ⥤
      ModuleCat.{max v w} R) f Ms

@[simp] theorem objAt_nil (P : ModuleCat.{max v w} R) : objAt.{u, v, w} R P [] = P := rfl

@[simp] theorem objAt_cons (P : ModuleCat.{max v w} R)
    (M : ModuleCat.{w} R) (Ms : List (ModuleCat.{w} R)) :
    objAt R P (M :: Ms) = objAt R (tensorObjAt R P M) Ms := rfl

@[simp] theorem mapAt_nil {P Q : ModuleCat.{max v w} R} (f : P ⟶ Q) :
    mapAt.{u, v, w} R f [] = f := rfl

@[simp] theorem mapAt_cons {P Q : ModuleCat.{max v w} R} (f : P ⟶ Q)
    (M : ModuleCat.{w} R) (Ms : List (ModuleCat.{w} R)) :
    mapAt R f (M :: Ms) = mapAt R (tensorHomAt R f (𝟙 M)) Ms := rfl

/-- For a commutative ring `R`, an isomorphism `e : P ≅ Q` of modules in
`max(v,w)`, ordered families `M`, `N : Fin n → ModuleCat_w(R)`, and
isomorphisms `h(j) : M(j) ≅ N(j)`, there is an isomorphism between the two
left tensor folds. It applies the tensor congruence at each factor and
retains their index order; for the empty family it is `e`. -/
def isoAt (R : Type u) [CommRing R] :
    ∀ {n : ℕ} {P Q : ModuleCat.{max v w} R} (_e : P ≅ Q)
      (M N : Fin n → ModuleCat.{w} R) (_h : ∀ j, M j ≅ N j),
      objAt R P (List.ofFn M) ≅ objAt R Q (List.ofFn N)
  | 0, P, Q, e, M, N, h => by
      simpa only [List.ofFn_zero, objAt, Functor.BifunctorFold.obj] using e
  | n + 1, P, Q, e, M, N, h => by
      simpa only [List.ofFn_succ, objAt, Functor.BifunctorFold.obj,
        tensorBifunctorAt, tensorObjAt] using
        (isoAt R
          (TensorProduct.congr e.toLinearEquiv (h 0).toLinearEquiv).toModuleIso
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

/-- For a commutative ring `R`, a prefix isomorphism `e : P ≅ Q` in carrier
height `max(v,w)`, and ordered coefficient families in `w` with pointwise
isomorphisms, the isomorphism built from tensor congruences equals the
isomorphism obtained by the general bifunctor-fold construction applied
to the independently sized tensor bifunctor. -/
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
      simp only [isoAt, Functor.BifunctorFold.iso, ih]
      rw [tensorIso_eq.{u, v, w} R e (h 0)]
      rfl

/-- For a commutative ring `R`, let `f : P → P′`, `g : Q → Q′`,
`e : P ≅ Q` and `e′ : P′ ≅ Q′` be module maps/isomorphisms at height
`max(v,w)` satisfying `f ≫ e′.hom = e.hom ≫ g`. Fix ordered coefficient
families `M`, `N` in `w` and pointwise isomorphisms between them. The
square obtained from the two prefix maps and the two tensor-fold
isomorphisms commutes, with the same factor order. -/
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
