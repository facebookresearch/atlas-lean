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

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Data.List.OfFn
public import MathlibExt.CategoryTheory.CommSq.HomCongr

/-!
# Finite folds of a bifunctor action

A bifunctor `F : C ⥤ D ⥤ C` acts successively on a prefix object of `C`
and a finite ordered list of objects of `D`. The result is functorial
in the prefix. Isomorphisms of the prefix and all factors give an
isomorphism of the folds, natural with respect to a prefix square.

For a monoidal category, use its curried tensor bifunctor.
The object and morphism universes of the two categories are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory.Functor.BifunctorFold

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- Apply the factors successively to the prefix, in their listed order. -/
def obj (F : C ⥤ D ⥤ C) : C → List D → C
  | P, [] => P
  | P, M :: Ms => obj F ((F.obj P).obj M) Ms

/-- A prefix morphism acts through every factor of the fold. -/
def map (F : C ⥤ D ⥤ C) {P Q : C} (f : P ⟶ Q) :
    ∀ Ms : List D, obj F P Ms ⟶ obj F Q Ms
  | [] => f
  | M :: Ms => map F ((F.map f).app M) Ms

variable (F : C ⥤ D ⥤ C)

@[simp] theorem obj_nil (P : C) : obj F P [] = P := rfl

@[simp] theorem obj_cons (P : C) (M : D) (Ms : List D) :
    obj F P (M :: Ms) = obj F ((F.obj P).obj M) Ms := rfl

@[simp] theorem map_nil {P Q : C} (f : P ⟶ Q) : map F f [] = f := rfl

@[simp] theorem map_cons {P Q : C} (f : P ⟶ Q) (M : D) (Ms : List D) :
    map F f (M :: Ms) = map F ((F.map f).app M) Ms := rfl

/-- Folding a prefix identity gives the identity. -/
@[simp] theorem map_id (P : C) (Ms : List D) :
    map F (𝟙 P) Ms = 𝟙 (obj F P Ms) := by
  induction Ms generalizing P with
  | nil => rfl
  | cons M Ms ih =>
      change map F ((F.map (𝟙 P)).app M) Ms = 𝟙 (obj F ((F.obj P).obj M) Ms)
      rw [F.map_id]
      exact ih ((F.obj P).obj M)

/-- Folding preserves composition of prefix morphisms. -/
theorem map_comp {P Q U : C} (f : P ⟶ Q) (g : Q ⟶ U) (Ms : List D) :
    map F (f ≫ g) Ms = map F f Ms ≫ map F g Ms := by
  induction Ms generalizing P Q U with
  | nil => rfl
  | cons M Ms ih =>
      change map F ((F.map (f ≫ g)).app M) Ms =
        map F ((F.map f).app M) Ms ≫ map F ((F.map g).app M) Ms
      have h : (F.map (f ≫ g)).app M = (F.map f).app M ≫ (F.map g).app M :=
        congrArg (fun a : F.obj P ⟶ F.obj U => a.app M) (F.map_comp f g)
      rw [h]
      exact ih _ _

/-- The prefix-variable functor for a fixed list of factors. -/
def functor (F : C ⥤ D ⥤ C) (Ms : List D) : C ⥤ C where
  obj P := obj F P Ms
  map f := map F f Ms
  map_id P := map_id F P Ms
  map_comp f g := map_comp F f g Ms

/-- Appending a list continues the fold from the preceding fold object. -/
theorem obj_append (P : C) (Ms Ns : List D) :
    obj F P (Ms ++ Ns) = obj F (obj F P Ms) Ns := by
  induction Ms generalizing P with
  | nil => rfl
  | cons M Ms ih => exact ih ((F.obj P).obj M)

/-- Prefix maps respect the same append decomposition. -/
theorem map_append {P Q : C} (f : P ⟶ Q) (Ms Ns : List D) :
    HEq (map F f (Ms ++ Ns)) (map F (map F f Ms) Ns) := by
  induction Ms generalizing P Q with
  | nil => exact HEq.rfl
  | cons M Ms ih => exact ih ((F.map f).app M)

/-- Isomorphisms of the prefix and each factor give an isomorphism of finite folds. -/
def iso (F : C ⥤ D ⥤ C) :
    ∀ {n : ℕ} {P Q : C} (_e : P ≅ Q) (M N : Fin n → D) (_h : ∀ j, M j ≅ N j),
      obj F P (List.ofFn M) ≅ obj F Q (List.ofFn N)
  | 0, P, Q, e, M, N, h => by
      simpa only [List.ofFn_zero, obj] using e
  | n + 1, P, Q, e, M, N, h => by
      simpa only [List.ofFn_succ, obj, Functor.uncurry] using
        (iso F ((Functor.uncurry.obj F).mapIso (Iso.prod e (h 0)))
          (fun j : Fin n => M j.succ) (fun j : Fin n => N j.succ)
          (fun j : Fin n => h j.succ))

private theorem factorIso_hom {P Q : C} {M N : D} (e : P ≅ Q) (h : M ≅ N) :
    ((Functor.uncurry.obj F).mapIso (Iso.prod e h)).hom =
      (F.map e.hom).app M ≫ (F.obj Q).map h.hom := rfl

private theorem factorIso_square {P Q P' Q' : C} {M N : D}
    (f : P ⟶ P') (g : Q ⟶ Q') (e : P ≅ Q) (e' : P' ≅ Q') (h : M ≅ N)
    (hprefix : f ≫ e'.hom = e.hom ≫ g) :
    (F.map f).app M ≫ ((Functor.uncurry.obj F).mapIso (Iso.prod e' h)).hom =
      ((Functor.uncurry.obj F).mapIso (Iso.prod e h)).hom ≫ (F.map g).app N := by
  rw [factorIso_hom, factorIso_hom]
  let G : C ⥤ C := F.flip.obj M
  have hs : (F.map f).app M ≫ (F.map e'.hom).app M =
      (F.map e.hom).app M ≫ (F.map g).app M := by
    change G.map f ≫ G.map e'.hom = G.map e.hom ≫ G.map g
    rw [← G.map_comp, hprefix, G.map_comp]
  have hn : (F.obj Q).map h.hom ≫ (F.map g).app N =
      (F.map g).app M ≫ (F.obj Q').map h.hom := (F.map g).naturality h.hom
  calc
    (F.map f).app M ≫ ((F.map e'.hom).app M ≫ (F.obj Q').map h.hom) =
        ((F.map f).app M ≫ (F.map e'.hom).app M) ≫ (F.obj Q').map h.hom :=
      (Category.assoc _ _ _).symm
    _ = ((F.map e.hom).app M ≫ (F.map g).app M) ≫ (F.obj Q').map h.hom :=
      congrArg (fun a => a ≫ (F.obj Q').map h.hom) hs
    _ = (F.map e.hom).app M ≫ ((F.map g).app M ≫ (F.obj Q').map h.hom) :=
      Category.assoc _ _ _
    _ = (F.map e.hom).app M ≫ ((F.obj Q).map h.hom ≫ (F.map g).app N) :=
      congrArg (fun a => (F.map e.hom).app M ≫ a) hn.symm
    _ = ((F.map e.hom).app M ≫ (F.obj Q).map h.hom) ≫ (F.map g).app N :=
      (Category.assoc _ _ _).symm

private theorem square_of_heq {P Q P' Q' R S R' S' : C}
    (hP : P = R) (hQ : Q = S) (hP' : P' = R') (hQ' : Q' = S')
    (f : P ⟶ P') (g : Q ⟶ Q') (e : P ≅ Q) (e' : P' ≅ Q')
    (a : R ⟶ R') (b : S ⟶ S') (u : R ≅ S) (u' : R' ≅ S')
    (hf : HEq f a) (hg : HEq g b) (he : HEq e u) (he' : HEq e' u')
    (hsquare : a ≫ u'.hom = u.hom ≫ b) : f ≫ e'.hom = e.hom ≫ g := by
  have hehom : HEq e.hom u.hom := by
    cases hP
    cases hQ
    exact heq_of_eq (congrArg Iso.hom (eq_of_heq he))
  have hehom' : HEq e'.hom u'.hom := by
    cases hP'
    cases hQ'
    exact heq_of_eq (congrArg Iso.hom (eq_of_heq he'))
  have hfConj : f = (eqToIso hP.symm).homCongr (eqToIso hP'.symm) a :=
    (conj_eqToHom_iff_heq f a hP hP').2 hf
  have hgConj : g = (eqToIso hQ.symm).homCongr (eqToIso hQ'.symm) b :=
    (conj_eqToHom_iff_heq g b hQ hQ').2 hg
  have heConj : e.hom = (eqToIso hP.symm).homCongr (eqToIso hQ.symm) u.hom :=
    (conj_eqToHom_iff_heq e.hom u.hom hP hQ).2 hehom
  have heConj' : e'.hom = (eqToIso hP'.symm).homCongr (eqToIso hQ'.symm) u'.hom :=
    (conj_eqToHom_iff_heq e'.hom u'.hom hP' hQ').2 hehom'
  have sq : CommSq a u.hom u'.hom b := ⟨hsquare⟩
  have transported := sq.homCongr (eqToIso hP.symm) (eqToIso hP'.symm)
    (eqToIso hQ.symm) (eqToIso hQ'.symm)
  simpa only [← hfConj, ← hgConj, ← heConj, ← heConj'] using transported.w

/-- A prefix square is preserved by folding simultaneous factor isomorphisms. -/
theorem iso_naturality {n : ℕ} {P Q P' Q' : C}
    (f : P ⟶ P') (g : Q ⟶ Q') (e : P ≅ Q) (e' : P' ≅ Q')
    (M N : Fin n → D) (h : ∀ j, M j ≅ N j)
    (hprefix : f ≫ e'.hom = e.hom ≫ g) :
    map F f (List.ofFn M) ≫ (iso F e' M N h).hom =
      (iso F e M N h).hom ≫ map F g (List.ofFn N) := by
  induction n generalizing P Q P' Q' with
  | zero =>
      have hP : obj F P (List.ofFn M) = P := by rw [List.ofFn_zero]; rfl
      have hP' : obj F P' (List.ofFn M) = P' := by rw [List.ofFn_zero]; rfl
      have hQ : obj F Q (List.ofFn N) = Q := by rw [List.ofFn_zero]; rfl
      have hQ' : obj F Q' (List.ofFn N) = Q' := by rw [List.ofFn_zero]; rfl
      have hf : HEq (map F f (List.ofFn M)) f :=
        Eq.ndrec (motive := fun xs => HEq (map F f (List.ofFn M)) (map F f xs))
          HEq.rfl (List.ofFn_zero (f := M))
      have hg : HEq (map F g (List.ofFn N)) g :=
        Eq.ndrec (motive := fun xs => HEq (map F g (List.ofFn N)) (map F g xs))
          HEq.rfl (List.ofFn_zero (f := N))
      have he : HEq (iso F e M N h) e := by
        simp only [iso, Eq.mpr, eqRec_heq_iff, _root_.id]
        exact HEq.rfl
      have he' : HEq (iso F e' M N h) e' := by
        simp only [iso, Eq.mpr, eqRec_heq_iff, _root_.id]
        exact HEq.rfl
      exact square_of_heq hP hQ hP' hQ'
        (map F f (List.ofFn M)) (map F g (List.ofFn N))
        (iso F e M N h) (iso F e' M N h) f g e e' hf hg he he' hprefix
  | succ n ih =>
      let Mt := fun j : Fin n => M j.succ
      let Nt := fun j : Fin n => N j.succ
      let ht := fun j : Fin n => h j.succ
      let a := (F.map f).app (M 0)
      let b := (F.map g).app (N 0)
      let u := (Functor.uncurry.obj F).mapIso (Iso.prod e (h 0))
      let u' := (Functor.uncurry.obj F).mapIso (Iso.prod e' (h 0))
      have hP : obj F P (List.ofFn M) =
          obj F ((F.obj P).obj (M 0)) (List.ofFn Mt) := by
        rw [List.ofFn_succ]; rfl
      have hP' : obj F P' (List.ofFn M) =
          obj F ((F.obj P').obj (M 0)) (List.ofFn Mt) := by
        rw [List.ofFn_succ]; rfl
      have hQ : obj F Q (List.ofFn N) =
          obj F ((F.obj Q).obj (N 0)) (List.ofFn Nt) := by
        rw [List.ofFn_succ]; rfl
      have hQ' : obj F Q' (List.ofFn N) =
          obj F ((F.obj Q').obj (N 0)) (List.ofFn Nt) := by
        rw [List.ofFn_succ]; rfl
      have hf : HEq (map F f (List.ofFn M)) (map F a (List.ofFn Mt)) :=
        Eq.ndrec (motive := fun xs => HEq (map F f (List.ofFn M)) (map F f xs))
          HEq.rfl (List.ofFn_succ (f := M))
      have hg : HEq (map F g (List.ofFn N)) (map F b (List.ofFn Nt)) :=
        Eq.ndrec (motive := fun xs => HEq (map F g (List.ofFn N)) (map F g xs))
          HEq.rfl (List.ofFn_succ (f := N))
      have he : HEq (iso F e M N h) (iso F u Mt Nt ht) := by
        simp only [iso, Eq.mpr, eqRec_heq_iff, _root_.id]
        exact HEq.rfl
      have he' : HEq (iso F e' M N h) (iso F u' Mt Nt ht) := by
        simp only [iso, Eq.mpr, eqRec_heq_iff, _root_.id]
        exact HEq.rfl
      have hrecursive := ih a b u u' Mt Nt ht (factorIso_square F f g e e' (h 0) hprefix)
      exact square_of_heq hP hQ hP' hQ'
        (map F f (List.ofFn M)) (map F g (List.ofFn N))
        (iso F e M N h) (iso F e' M N h)
        (map F a (List.ofFn Mt)) (map F b (List.ofFn Nt))
        (iso F u Mt Nt ht) (iso F u' Mt Nt ht) hf hg he he' hrecursive

end CategoryTheory.Functor.BifunctorFold
