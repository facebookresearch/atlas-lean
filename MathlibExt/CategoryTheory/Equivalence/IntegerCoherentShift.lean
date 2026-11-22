/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Equivalence.IntegerOrbit
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# A coherent shift from the original equivalence powers

Integer translation on the full original orbit has coherent addition and
unit maps. The source-built evaluation equivalence transports this shift
to the exact native powers of the given equivalence. The original functor,
inverse, units, counits and successor comparisons construct every map;
coherence and replacement powers are not input certificates.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory Functor

namespace CategoryTheory.Equivalence.IntegerOrbit

variable {C : Type u} [Category.{v} C] {e : C ≌ C}

/-- Every orbit component retains transport along an equality of integer indices. -/
@[reassoc]
theorem app_transport {X Y : IntegerOrbit e} (f : X ⟶ Y) {a b : ℤ} (h : a = b) :
    f.app a ≫ eqToHom (congrArg Y.obj h) = eqToHom (congrArg X.obj h) ≫ f.app b := by
  cases h
  simp

/-- The original full successor map retains both endpoint transports. -/
@[reassoc]
theorem step_transport (X : IntegerOrbit e) {a b : ℤ} (h : a = b) :
    e.functor.map (eqToHom (congrArg X.obj h)) ≫ (X.step b).hom =
      (X.step a).hom ≫ eqToHom (congrArg X.obj (congrArg (fun n : ℤ => n + 1) h)) := by
  cases h
  simp

/-- Translation retains every actual orbit object and its original successor map. -/
def reindex (e : C ≌ C) (n : ℤ) : IntegerOrbit e ⥤ IntegerOrbit e where
  obj X :=
    { obj := fun k => X.obj (n + k)
      step := fun k => X.step (n + k) ≪≫ eqToIso (congrArg X.obj (add_assoc n k 1)) }
  map f :=
    { app := fun k => f.app (n + k)
      comm := fun k => by
        simp only [Iso.trans_hom, eqToIso.hom]
        rw [← Category.assoc, f.comm, Category.assoc, app_transport f (add_assoc n k 1)]
        exact (Category.assoc _ _ _).symm }
  map_id X := by apply Hom.ext; intro k; rfl
  map_comp f h := by apply Hom.ext; intro k; rfl

@[simp]
theorem reindex_obj_obj (e : C ≌ C) (n : ℤ) (X : IntegerOrbit e) (k : ℤ) :
    ((reindex e n).obj X).obj k = X.obj (n + k) := rfl

@[simp]
theorem reindex_map_app (e : C ≌ C) (n : ℤ) {X Y : IntegerOrbit e} (f : X ⟶ Y) (k : ℤ) :
    ((reindex e n).map f).app k = f.app (n + k) := rfl

/-- Zero translation retains the actual identity comparisons on the whole original orbit. -/
def zeroObjectIso (e : C ≌ C) (X : IntegerOrbit e) : (reindex e 0).obj X ≅ X :=
  isoMk (fun k => eqToIso (congrArg X.obj (zero_add k))) (fun k => by
    change e.functor.map (eqToHom (congrArg X.obj (zero_add k))) ≫ (X.step k).hom =
      ((X.step (0 + k)).hom ≫ eqToHom (congrArg X.obj (add_assoc 0 k 1))) ≫
        eqToHom (congrArg X.obj (zero_add (k + 1)))
    rw [step_transport X (zero_add k)]
    simp only [Category.assoc, eqToHom_trans])

/-- All source orbit morphisms preserve the complete zero-translation comparison. -/
def zeroNatIso (e : C ≌ C) : reindex e 0 ≅ 𝟭 (IntegerOrbit e) :=
  NatIso.ofComponents (zeroObjectIso e) (fun {X Y} f => by
    apply Hom.ext
    intro k
    change f.app (0 + k) ≫ eqToHom (congrArg Y.obj (zero_add k)) =
      eqToHom (congrArg X.obj (zero_add k)) ≫ f.app k
    exact app_transport f (zero_add k))

/-- The whole addition comparison transports every integer coordinate by associativity. -/
def additionObjectIso (e : C ≌ C) (n m : ℤ) (X : IntegerOrbit e) :
    (reindex e (n + m)).obj X ≅ ((reindex e n) ⋙ reindex e m).obj X :=
  isoMk (fun k => eqToIso (congrArg X.obj (add_assoc n m k))) (fun k => by
    change e.functor.map (eqToHom (congrArg X.obj (add_assoc n m k))) ≫
      (((X.step (n + (m + k))).hom ≫ eqToHom (congrArg X.obj (add_assoc n (m + k) 1))) ≫
        eqToHom (congrArg X.obj (congrArg (fun a : ℤ => n + a) (add_assoc m k 1)))) =
      ((X.step ((n + m) + k)).hom ≫ eqToHom (congrArg X.obj (add_assoc (n + m) k 1))) ≫
        eqToHom (congrArg X.obj (add_assoc n m (k + 1)))
    simp only [Category.assoc]
    rw [step_transport_assoc X (add_assoc n m k)]
    simp only [eqToHom_trans])

/-- Every whole orbit arrow retains the actual addition comparison square. -/
def additionNatIso (e : C ≌ C) (n m : ℤ) : reindex e (n + m) ≅ reindex e n ⋙ reindex e m :=
  NatIso.ofComponents (additionObjectIso e n m) (fun {X Y} f => by
    apply Hom.ext
    intro k
    change f.app ((n + m) + k) ≫ eqToHom (congrArg Y.obj (add_assoc n m k)) =
      eqToHom (congrArg X.obj (add_assoc n m k)) ≫ f.app (n + (m + k))
    exact app_transport f (add_assoc n m k))

/-- The entire zero component is its original index equality transport. -/
theorem zeroNatIso_hom_app (e : C ≌ C) (X : IntegerOrbit e) (k : ℤ) :
    ((zeroNatIso e).hom.app X).app k = eqToHom (congrArg X.obj (zero_add k)) := rfl

/-- The inverse zero comparison retains the original inverse index equality transport. -/
theorem zeroNatIso_inv_app (e : C ≌ C) (X : IntegerOrbit e) (k : ℤ) :
    ((zeroNatIso e).inv.app X).app k = eqToHom (congrArg X.obj (zero_add k).symm) := rfl

/-- Both source integer indices remain in every whole addition component. -/
theorem additionNatIso_hom_app (e : C ≌ C) (n m : ℤ) (X : IntegerOrbit e) (k : ℤ) :
    ((additionNatIso e n m).hom.app X).app k =
      eqToHom (congrArg X.obj (add_assoc n m k)) := rfl

/-- Equality transport in the orbit reads back the entire equality at every original coordinate. -/
theorem eqToHom_app {X Y : IntegerOrbit e} (h : X = Y) (k : ℤ) :
    (eqToHom h : X ⟶ Y).app k = eqToHom (congrArg (fun Z : IntegerOrbit e => Z.obj k) h) := by
  cases h
  rfl

/-- Translation has the full associativity and both unit coherences on every original orbit. -/
def shiftCore (e : C ≌ C) : ShiftMkCore (IntegerOrbit e) ℤ where
  F := reindex e
  zero := zeroNatIso e
  add := additionNatIso e
  assoc_hom_app n m k X := by
    apply Hom.ext
    intro a
    simp only [comp_app, reindex_map_app, additionNatIso_hom_app, eqToHom_app,
      eqToHom_trans, reindex_obj_obj]
  zero_add_hom_app n X := by
    apply Hom.ext
    intro a
    simp only [comp_app, reindex_map_app, additionNatIso_hom_app, zeroNatIso_inv_app,
      eqToHom_app, eqToHom_trans, reindex_obj_obj]
  add_zero_hom_app n X := by
    apply Hom.ext
    intro a
    simp only [comp_app, additionNatIso_hom_app, zeroNatIso_inv_app,
      eqToHom_app, eqToHom_trans, reindex_obj_obj]

/-- The actual orbit shift is constructed from those proved whole source coherences. -/
@[instance_reducible]
def orbitHasShift (e : C ≌ C) : HasShift (IntegerOrbit e) ℤ :=
  hasShiftMk (IntegerOrbit e) ℤ (shiftCore e)

/-- The original fully faithful evaluation compares translated orbits to the exact native power. -/
def nativeIntertwining (e : C ≌ C) (n : ℤ) :
    (e ^ n).functor ⋙ realization e ≅ realization e ⋙ reindex e n :=
  (((equivalence e).symm.fullyFaithfulFunctor).whiskeringRight C).preimageIso
    ((show ((e ^ n).functor ⋙ realization e) ⋙ evaluation e 0 ≅ (e ^ n).functor from Iso.refl _) ≪≫
      eqToIso (congrArg (fun a : ℤ => (e ^ a).functor) (add_zero n).symm) ≪≫
        (show (realization e ⋙ reindex e n) ⋙ evaluation e 0 ≅ (e ^ (n + 0)).functor from
          Iso.refl _).symm)

/-- The exact original integer powers carry a genuine coherent shift, with no addition premise. -/
@[instance_reducible]
def nativeHasShift (e : C ≌ C) : HasShift C ℤ := by
  letI := orbitHasShift e
  exact (equivalence e).fullyFaithfulFunctor.hasShift
    (fun n : ℤ => (e ^ n).functor) (fun n => nativeIntertwining e n)

/-- Each induced shift functor is definitionally the specified original native power. -/
theorem native_shiftFunctor (e : C ≌ C) (n : ℤ) :
    letI := nativeHasShift e
    shiftFunctor C n = (e ^ n).functor := rfl

/-- The complete native addition map has both unit laws and associativity from the constructed shift. -/
def nativeAddition (e : C ≌ C) (n m : ℤ) :
    (e ^ (n + m)).functor ≅ (e ^ n).functor ⋙ (e ^ m).functor := by
  letI := nativeHasShift e
  exact shiftFunctorAdd C n m

/-- Its inverse composes the original integer powers coherently at every pair of degrees. -/
def nativeComparison (e : C ≌ C) (n m : ℤ) :
    (e ^ n).functor ⋙ (e ^ m).functor ≅ (e ^ (n + m)).functor :=
  (nativeAddition e n m).symm

end CategoryTheory.Equivalence.IntegerOrbit
