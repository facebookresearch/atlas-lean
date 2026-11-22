/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Equivalence.IntegerSuccessor
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.Int.Init
public import Lean.Elab.Tactic.Omega

/-!
# The original integer orbit of an equivalence

An orbit retains every integer object and the specified forward equivalence
between adjacent objects. Evaluation at zero is an equivalence. Its inverse
uses the actual native powers and their original successor comparison.
Negative components are obtained through the original fully faithful
forward functor, whose preimage retains the original unit and inverse.
No coherent addition maps or substitute inverse are assumptions.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
open CategoryTheory Functor

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C]

/-- The full integer family and every original forward successor isomorphism. -/
structure IntegerOrbit (e : C ≌ C) where
  /-- The original object at each specified index. -/
  obj : ℤ → C
  /-- The original successor comparison between adjacent objects. -/
  step : ∀ n : ℤ, e.functor.obj (obj n) ≅ obj (n + 1)

namespace IntegerOrbit

variable {e : C ≌ C}

/-- Every integer component and its complete successor square are retained. -/
structure Hom (X Y : IntegerOrbit e) where
  /-- The component map at each original index. -/
  app : ∀ n : ℤ, X.obj n ⟶ Y.obj n
  comm : ∀ n : ℤ, e.functor.map (app n) ≫ (Y.step n).hom =
    (X.step n).hom ≫ app (n + 1)

@[ext]
theorem Hom.ext {X Y : IntegerOrbit e} {f h : Hom X Y}
    (happ : ∀ n, f.app n = h.app n) : f = h := by
  cases f
  cases h
  cases funext happ
  rfl

instance : Category.{v} (IntegerOrbit e) where
  Hom X Y := Hom X Y
  id X := { app := fun n => 𝟙 (X.obj n), comm := fun n => by simp }
  comp f h :=
    { app := fun n => f.app n ≫ h.app n
      comm := fun n => by
        rw [e.functor.map_comp, Category.assoc, h.comm, ← Category.assoc, f.comm,
          Category.assoc] }
  id_comp f := by apply Hom.ext; intro n; exact Category.id_comp _
  comp_id f := by apply Hom.ext; intro n; exact Category.comp_id _
  assoc f h k := by apply Hom.ext; intro n; exact Category.assoc _ _ _

@[simp]
theorem id_app (X : IntegerOrbit e) (n : ℤ) : (𝟙 X : X ⟶ X).app n = 𝟙 (X.obj n) := rfl

@[simp]
theorem comp_app {X Y Z : IntegerOrbit e} (f : X ⟶ Y) (h : Y ⟶ Z) (n : ℤ) :
    (f ≫ h).app n = f.app n ≫ h.app n := rfl

/-- The whole successor square propagates an equality of components forwards. -/
theorem hom_eq_next {X Y : IntegerOrbit e} (f h : X ⟶ Y) (n : ℤ)
    (hn : f.app n = h.app n) : f.app (n + 1) = h.app (n + 1) := by
  apply (cancel_epi (X.step n).hom).mp
  rw [← f.comm, ← h.comm, hn]

/-- The same full square propagates backwards through the original faithful forward functor. -/
theorem hom_eq_previous {X Y : IntegerOrbit e} (f h : X ⟶ Y) (n : ℤ)
    (hn : f.app (n + 1) = h.app (n + 1)) : f.app n = h.app n := by
  apply e.functor.map_injective
  apply (cancel_mono (Y.step n).hom).mp
  rw [f.comm, h.comm, hn]

/-- The original component at zero determines every positive and negative component. -/
theorem hom_ext_zero {X Y : IntegerOrbit e} (f h : X ⟶ Y)
    (hzero : f.app 0 = h.app 0) : f = h := by
  apply Hom.ext
  intro n
  induction n using Int.induction_on with
  | zero => exact hzero
  | succ n hn => exact hom_eq_next f h n hn
  | pred n hn =>
      apply hom_eq_previous f h (-n - 1)
      exact Eq.mpr (congrArg (fun k : ℤ => f.app k = h.app k)
        (show -(n : ℤ) - 1 + 1 = -n by omega)) hn

/-- Evaluation retains the original object and entire component function at each integer. -/
def evaluation (e : C ≌ C) (n : ℤ) : IntegerOrbit e ⥤ C where
  obj X := X.obj n
  map f := f.app n

instance evaluation_zero_faithful : (evaluation e 0).Faithful where
  map_injective heq := hom_ext_zero _ _ heq

/-- The inverse orbit functor uses every actual native integer power of the original equivalence. -/
def realization (e : C ≌ C) : C ⥤ IntegerOrbit e where
  obj X :=
    { obj := fun n => (e ^ n).functor.obj X
      step := fun n => (IntegerSuccessor.comparison e n).app X }
  map f :=
    { app := fun n => (e ^ n).functor.map f
      comm := fun n => (IntegerSuccessor.comparison e n).hom.naturality f }
  map_id X := by apply Hom.ext; intro n; exact (e ^ n).functor.map_id X
  map_comp f h := by apply Hom.ext; intro n; exact (e ^ n).functor.map_comp f h

/-- Every nonnegative component is built from the original successor and its actual orbit step. -/
def nonnegativeComponent (X : IntegerOrbit e) : (n : ℕ) →
    (e ^ (n : ℤ)).functor.obj (X.obj 0) ≅ X.obj (n : ℤ)
  | 0 => Iso.refl _
  | n + 1 => (IntegerSuccessor.comparison e (n : ℤ)).symm.app (X.obj 0) ≪≫
      e.functor.mapIso (nonnegativeComponent X n) ≪≫ X.step (n : ℤ)

/-- A complete next-degree comparison determines the previous comparison through the original inverse. -/
def previousComponent (X : IntegerOrbit e) (n : ℤ)
    (a : (e ^ (n + 1)).functor.obj (X.obj 0) ≅ X.obj (n + 1)) :
    (e ^ n).functor.obj (X.obj 0) ≅ X.obj n :=
  e.fullyFaithfulFunctor.preimageIso
    ((IntegerSuccessor.comparison e n).app (X.obj 0) ≪≫ a ≪≫ (X.step n).symm)

/-- Its entire forward image is the same original successor followed by the given next comparison. -/
theorem previousComponent_comm (X : IntegerOrbit e) (n : ℤ)
    (a : (e ^ (n + 1)).functor.obj (X.obj 0) ≅ X.obj (n + 1)) :
    e.functor.map (previousComponent X n a).hom ≫ (X.step n).hom =
      (IntegerSuccessor.comparison e n).hom.app (X.obj 0) ≫ a.hom := by
  simp only [previousComponent, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Each negative component is earned through the original fully faithful forward functor. -/
def negativeComponent (X : IntegerOrbit e) : (n : ℕ) →
    (e ^ Int.negSucc n).functor.obj (X.obj 0) ≅ X.obj (Int.negSucc n)
  | 0 => previousComponent X (Int.negSucc 0) (by
      rw [show Int.negSucc 0 + 1 = (0 : ℤ) by omega]
      exact Iso.refl _)
  | n + 1 => previousComponent X (Int.negSucc (n + 1)) (by
      rw [show Int.negSucc (n + 1) + 1 = Int.negSucc n by omega]
      exact negativeComponent X n)

/-- The complete comparison family includes every original positive and negative object. -/
def component (X : IntegerOrbit e) : (n : ℤ) →
    (e ^ n).functor.obj (X.obj 0) ≅ X.obj n
  | .ofNat n => nonnegativeComponent X n
  | .negSucc n => negativeComponent X n

/-- Every comparison component retains the entire original successor square. -/
theorem component_comm (X : IntegerOrbit e) (n : ℤ) :
    e.functor.map ((component X n).hom) ≫ (X.step n).hom =
      (IntegerSuccessor.comparison e n).hom.app (X.obj 0) ≫ (component X (n + 1)).hom := by
  cases n with
  | ofNat n =>
      change e.functor.map (nonnegativeComponent X n).hom ≫ (X.step (n : ℤ)).hom =
        (IntegerSuccessor.comparison e (n : ℤ)).hom.app (X.obj 0) ≫
          ((IntegerSuccessor.comparison e (n : ℤ)).inv.app (X.obj 0) ≫
            e.functor.map (nonnegativeComponent X n).hom ≫ (X.step (n : ℤ)).hom)
      simp only [Iso.hom_inv_id_app_assoc]
  | negSucc n =>
      cases n with
      | zero =>
          dsimp only [component, negativeComponent]
          rw [previousComponent_comm]
          rfl
      | succ n =>
          dsimp only [component, negativeComponent]
          rw [previousComponent_comm]
          rfl

/-- Componentwise original isomorphisms with the full square give a whole orbit isomorphism. -/
def isoMk {X Y : IntegerOrbit e} (a : ∀ n : ℤ, X.obj n ≅ Y.obj n)
    (ha : ∀ n, e.functor.map (a n).hom ≫ (Y.step n).hom =
      (X.step n).hom ≫ (a (n + 1)).hom) : X ≅ Y where
  hom := { app := fun n => (a n).hom, comm := ha }
  inv :=
    { app := fun n => (a n).inv
      comm := fun n => by
        exact (CommSq.horiz_inv
          (show CommSq (e.functor.mapIso (a n)).hom (X.step n).hom
            (Y.step n).hom (a (n + 1)).hom from ⟨ha n⟩)).w }
  hom_inv_id := by apply Hom.ext; intro n; exact (a n).hom_inv_id
  inv_hom_id := by apply Hom.ext; intro n; exact (a n).inv_hom_id

/-- The actual power orbit of the zero object is compared to the whole given orbit. -/
def orbitIso (X : IntegerOrbit e) : (realization e).obj (X.obj 0) ≅ X :=
  isoMk (component X) (component_comm X)

/-- The complete zero component of the original orbit comparison is the actual identity. -/
theorem orbitIso_hom_zero (X : IntegerOrbit e) : (orbitIso X).hom.app 0 = 𝟙 (X.obj 0) := rfl

/-- Every entire orbit morphism retains naturality of the source-built comparison. -/
def counitIso (e : C ≌ C) : evaluation e 0 ⋙ realization e ≅ 𝟭 (IntegerOrbit e) :=
  NatIso.ofComponents (fun X => orbitIso (e := e) X) (fun {X Y} f => by
    apply hom_ext_zero
    change f.app 0 ≫ (orbitIso Y).hom.app 0 = (orbitIso X).hom.app 0 ≫ f.app 0
    rw [orbitIso_hom_zero, orbitIso_hom_zero]
    exact (Category.comp_id (f.app 0)).trans (Category.id_comp (f.app 0)).symm)

/-- The full evaluation equivalence uses the original powers and both actual comparison maps. -/
def equivalence (e : C ≌ C) : C ≌ IntegerOrbit e where
  functor := realization e
  inverse := evaluation e 0
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun f => by
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    simp)
  counitIso := counitIso e
  functor_unitIso_comp X := by
    apply hom_ext_zero
    change 𝟙 X ≫ (orbitIso ((realization e).obj X)).hom.app 0 = 𝟙 X
    rw [orbitIso_hom_zero]
    exact Category.id_comp _

end IntegerOrbit
end CategoryTheory.Equivalence
