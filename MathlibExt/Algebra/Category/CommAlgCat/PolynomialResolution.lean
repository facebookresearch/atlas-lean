/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.Free
public import MathlibExt.CategoryTheory.Comonad.BarResolution
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The canonical polynomial comonad and augmented simplicial resolution

The actual polynomial free/forget adjunction supplies the comonad. Its
counit evaluates polynomials in algebra elements, and its comultiplication
renames each element as a formal variable. The existing comonad resolution
supplies all simplicial operators and the augmentation.

Degree n is canonically identified with the literal polynomial algebra on
the underlying set of the nth comonad power. The base ring and carrier-size
parameter are independent, with stable carrier universe max u v.

Mathematical source: Weibel, An Introduction to Homological Algebra,
Example 8.6.16. The generic resolution and insertion calculus reuse
`CategoryTheory.Comonad.BarResolution` and `CategoryTheory.Comonad.Cobar`.
The native adjunction-to-comonad construction is due to Kim Morrison and
Bhavik Mehta.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- The actual polynomial comonad induced by the constructed free/forget adjunction. -/
def polynomialComonad : Comonad (CommAlgCat.{max u v} k) :=
  (freeForgetAdjunction.{u, v} k).toComonad

@[simp]
theorem polynomialComonad_toFunctor :
    (polynomialComonad.{u, v} k).toFunctor =
      forget (CommAlgCat.{max u v} k) ⋙ free.{u, v} k := rfl

/-- The underlying comonad object is the literal polynomial ring on the algebra's carrier. -/
@[simp]
theorem polynomialComonad_obj_carrier (A : CommAlgCat.{max u v} k) :
    ↥((polynomialComonad.{u, v} k).obj A) = MvPolynomial A k := rfl

/-- The adjunction unit includes each element as its actual formal variable. -/
theorem polynomialComonad_unit_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((freeForgetAdjunction.{u, v} k).unit.app A) a = MvPolynomial.X a := rfl

/-- Comonad maps are the native renaming maps of the underlying algebra functions. -/
@[simp]
theorem polynomialComonad_map_hom {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    ((polynomialComonad.{u, v} k).map f).hom = MvPolynomial.rename (R := k) f.hom := rfl

theorem polynomialComonad_map_X {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) (a : A) :
    ((polynomialComonad.{u, v} k).map f).hom (MvPolynomial.X a) =
      MvPolynomial.X (f.hom a) := MvPolynomial.rename_X f.hom a

/-- The counit is the actual native evaluation map. -/
@[simp]
theorem polynomialComonad_counit_hom (A : CommAlgCat.{max u v} k) :
    ((polynomialComonad.{u, v} k).ε.app A).hom =
      MvPolynomial.aeval (R := k) (fun a : A => a) := rfl

theorem polynomialComonad_counit_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((polynomialComonad.{u, v} k).ε.app A).hom (MvPolynomial.X a) = a :=
  MvPolynomial.aeval_X (fun a : A => a) a

theorem polynomialComonad_counit_C (A : CommAlgCat.{max u v} k) (c : k) :
    ((polynomialComonad.{u, v} k).ε.app A).hom (MvPolynomial.C c) = algebraMap k A c :=
  MvPolynomial.aeval_C (fun a : A => a) c

/-- Comultiplication renames each algebra element as its polynomial variable. -/
@[simp]
theorem polynomialComonad_comultiplication_hom (A : CommAlgCat.{max u v} k) :
    ((polynomialComonad.{u, v} k).δ.app A).hom =
      MvPolynomial.rename (R := k) (fun a : A => (MvPolynomial.X a : MvPolynomial A k)) := rfl

theorem polynomialComonad_comultiplication_X (A : CommAlgCat.{max u v} k) (a : A) :
    ((polynomialComonad.{u, v} k).δ.app A).hom (MvPolynomial.X a) =
      MvPolynomial.X (MvPolynomial.X a : MvPolynomial A k) :=
  MvPolynomial.rename_X (fun a : A => (MvPolynomial.X a : MvPolynomial A k)) a

@[reassoc]
theorem polynomialComonad_counit_naturality {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialComonad.{u, v} k).map f ≫ (polynomialComonad.{u, v} k).ε.app B =
      (polynomialComonad.{u, v} k).ε.app A ≫ f :=
  (polynomialComonad.{u, v} k).ε.naturality f

@[reassoc]
theorem polynomialComonad_comultiplication_naturality
    {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialComonad.{u, v} k).map f ≫ (polynomialComonad.{u, v} k).δ.app B =
      (polynomialComonad.{u, v} k).δ.app A ≫
        (polynomialComonad.{u, v} k).map ((polynomialComonad.{u, v} k).map f) :=
  (polynomialComonad.{u, v} k).δ.naturality f

/-- Existing native comonad powers for this actual polynomial comonad. -/
abbrev polynomialPower (n : ℕ) : CommAlgCat.{max u v} k ⥤ CommAlgCat.{max u v} k :=
  Comonad.comonadPow (polynomialComonad.{u, v} k) n

/-- The next native power is polynomial on the actual underlying set of the preceding power. -/
theorem polynomialPower_succ_obj (n : ℕ) (A : CommAlgCat.{max u v} k) :
    (polynomialPower.{u, v} k (n + 1)).obj A =
      CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) :=
  Comonad.comonadPow_succ_obj_eq (polynomialComonad.{u, v} k) n A

/-- Canonical identification of a successor power with its literal polynomial object. -/
def polynomialPowerObjIso (n : ℕ) (A : CommAlgCat.{max u v} k) :
    (polynomialPower.{u, v} k (n + 1)).obj A ≅
      CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) :=
  eqToIso (polynomialPower_succ_obj.{u, v} k n A)

/-- Equality transport of the actual power maps is natural; no additional power functor is built. -/
@[reassoc]
theorem polynomialPowerObjIso_naturality (n : ℕ)
    {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialPower.{u, v} k (n + 1)).map f ≫ (polynomialPowerObjIso.{u, v} k n B).hom =
      (polynomialPowerObjIso.{u, v} k n A).hom ≫
        (polynomialComonad.{u, v} k).map ((polynomialPower.{u, v} k n).map f) := by
  induction n generalizing A B with
  | zero =>
    change (polynomialComonad.{u, v} k).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (polynomialComonad.{u, v} k).map f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n ih =>
    exact ih ((polynomialComonad.{u, v} k).map f)

/-- The actual augmented polynomial resolution functor, specialized from the generic owner. -/
def polynomialResolutionFunctor :
    CommAlgCat.{max u v} k ⥤ SimplicialObject.Augmented (CommAlgCat.{max u v} k) :=
  Comonad.resolutionAugmentedFunctor (polynomialComonad.{u, v} k)

/-- The canonical augmented simplicial polynomial object of an algebra. -/
abbrev polynomialResolution (A : CommAlgCat.{max u v} k) :
    SimplicialObject.Augmented (CommAlgCat.{max u v} k) :=
  (polynomialResolutionFunctor.{u, v} k).obj A

/-- The actual augmented resolution map induced by an algebra map. -/
abbrev polynomialResolutionMap {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    polynomialResolution.{u, v} k A ⟶ polynomialResolution.{u, v} k B :=
  (polynomialResolutionFunctor.{u, v} k).map f

@[simp]
theorem polynomialResolution_point (A : CommAlgCat.{max u v} k) :
    (polynomialResolution.{u, v} k A).right = A :=
  Comonad.resolutionAugmented_point (polynomialComonad.{u, v} k) A

@[simp]
theorem polynomialResolution_left (A : CommAlgCat.{max u v} k) :
    (polynomialResolution.{u, v} k A).left =
      Comonad.resolutionBar (polynomialComonad.{u, v} k) A :=
  Comonad.resolutionAugmented_left (polynomialComonad.{u, v} k) A

@[simp]
theorem polynomialResolution_obj (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) =
      (polynomialPower.{u, v} k (n + 1)).obj A := rfl

/-- The degree object is the literal polynomial object on the preceding native power's carrier. -/
def polynomialResolutionObjIso (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ≅
      CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) :=
  Comonad.resolutionBarObjIso (polynomialComonad.{u, v} k) A n ≪≫
    polynomialPowerObjIso.{u, v} k n A

@[simp]
theorem polynomialResolutionObjIso_hom (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolutionObjIso.{u, v} k A n).hom =
      (polynomialPowerObjIso.{u, v} k n A).hom := by
  change 𝟙 _ ≫ (polynomialPowerObjIso.{u, v} k n A).hom = _
  exact Category.id_comp _

@[simp]
theorem polynomialResolutionObjIso_inv (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolutionObjIso.{u, v} k A n).inv =
      (polynomialPowerObjIso.{u, v} k n A).inv := by
  change (polynomialPowerObjIso.{u, v} k n A).inv ≫ 𝟙 _ = _
  exact Category.comp_id _

@[simp]
theorem polynomialResolutionMap_left_app {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) :
    (polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n)) =
      (polynomialPower.{u, v} k (n + 1)).map f :=
  Comonad.resolutionHom_left_app (polynomialComonad.{u, v} k) f n

@[simp]
theorem polynomialResolutionMap_right {A B : CommAlgCat.{max u v} k} (f : A ⟶ B) :
    (polynomialResolutionMap.{u, v} k f).right = f := rfl

@[reassoc]
theorem polynomialResolutionObjIso_naturality {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) :
    (polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n)) ≫
        (polynomialResolutionObjIso.{u, v} k B n).hom =
      (polynomialResolutionObjIso.{u, v} k A n).hom ≫
        (polynomialComonad.{u, v} k).map ((polynomialPower.{u, v} k n).map f) := by
  change (polynomialPower.{u, v} k (n + 1)).map f ≫
      (polynomialPowerObjIso.{u, v} k n B).hom =
    (polynomialPowerObjIso.{u, v} k n A).hom ≫
      (polynomialComonad.{u, v} k).map ((polynomialPower.{u, v} k n).map f)
  exact polynomialPowerObjIso_naturality.{u, v} k n f

/-- Every face is the existing source-ordered counit insertion. -/
@[simp]
theorem polynomialResolution_map_δ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 2)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i).op =
      Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) (n + 1) i A :=
  Comonad.resolutionBar_map_δ_op (polynomialComonad.{u, v} k) A i

/-- Every degeneracy is the existing source-ordered comultiplication insertion. -/
@[simp]
theorem polynomialResolution_map_σ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i).op =
      Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A :=
  Comonad.resolutionBar_map_σ_op (polynomialComonad.{u, v} k) A i

/-- The actual degree-zero augmentation is the polynomial evaluation counit. -/
@[simp]
theorem polynomialResolution_augmentation_zero (A : CommAlgCat.{max u v} k) :
    (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk 0)) =
      (polynomialComonad.{u, v} k).ε.app A :=
  Comonad.resolutionAugmented_hom_zero (polynomialComonad.{u, v} k) A

/-- All actual simplicial maps commute with the actual augmentation. -/
@[reassoc]
theorem polynomialResolution_augmentation_naturality (A : CommAlgCat.{max u v} k)
    {m n : ℕ} (f : op (SimplexCategory.mk m) ⟶ op (SimplexCategory.mk n)) :
    (polynomialResolution.{u, v} k A).left.map f ≫
        (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n)) =
      (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk m)) :=
  ((polynomialResolution.{u, v} k A).hom.naturality f).trans (Category.comp_id _)

/-- The actual degree-n generator indexed by an element of the preceding native power. -/
def polynomialResolutionGenerator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k n).obj A) :
    (polynomialPower.{u, v} k (n + 1)).obj A :=
  (polynomialPowerObjIso.{u, v} k n A).inv.hom (MvPolynomial.X x)

/-- The degree identification sends the constructed generator to its literal variable. -/
theorem polynomialResolutionObjIso_hom_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k n).obj A) :
    (polynomialResolutionObjIso.{u, v} k A n).hom.hom
        (polynomialResolutionGenerator.{u, v} k A n x) = MvPolynomial.X x :=
  CommAlgCat.hom_inv_apply (polynomialResolutionObjIso.{u, v} k A n) (MvPolynomial.X x)

@[simp]
theorem polynomialResolutionGenerator_zero (A : CommAlgCat.{max u v} k) (a : A) :
    polynomialResolutionGenerator.{u, v} k A 0 a = MvPolynomial.X a := rfl

@[simp]
theorem polynomialResolutionGenerator_one (A : CommAlgCat.{max u v} k)
    (p : MvPolynomial A k) :
    polynomialResolutionGenerator.{u, v} k A 1 p = MvPolynomial.X p := rfl

/-- Maps from an actual degree object are determined by the constructed polynomial generators. -/
theorem polynomialResolution_hom_ext (A B : CommAlgCat.{max u v} k) (n : ℕ)
    (f g : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ⟶ B)
    (h : ∀ x : (polynomialPower.{u, v} k n).obj A,
      f.hom (polynomialResolutionGenerator.{u, v} k A n x) =
        g.hom (polynomialResolutionGenerator.{u, v} k A n x)) : f = g := by
  let e := polynomialResolutionObjIso.{u, v} k A n
  apply (cancel_epi e.inv).1
  apply CommAlgCat.hom_ext
  ext x
  exact h x

/-- Coefficient functoriality is actual renaming of the preceding power's generator index. -/
theorem polynomialResolutionMap_generator {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) (x : (polynomialPower.{u, v} k n).obj A) :
    ((polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n))).hom
        (polynomialResolutionGenerator.{u, v} k A n x) =
      polynomialResolutionGenerator.{u, v} k B n
        (((polynomialPower.{u, v} k n).map f).hom x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A n
  let eB := polynomialResolutionObjIso.{u, v} k B n
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj B) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A n x))
    (polynomialResolutionObjIso_naturality.{u, v} k f n)
  change eB.hom.hom
      (((polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n))).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    MvPolynomial.rename (R := k) ((polynomialPower.{u, v} k n).map f).hom
      (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A n x)) at h
  rw [polynomialResolutionObjIso_hom_generator, MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n))).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k B n
      (((polynomialPower.{u, v} k n).map f).hom x))
  rw [polynomialResolutionObjIso_hom_generator]
  exact h

/-- Raw counit insertions commute with the canonical outer-polynomial identification. -/
@[reassoc]
theorem polynomialPower_epsilon_castSucc (n : ℕ) (i : Fin (n + 1))
    (A : CommAlgCat.{max u v} k) :
    Comonad.epsilonAtPos (polynomialComonad.{u, v} k) (n + 1) i.castSucc A ≫
        (polynomialPowerObjIso.{u, v} k n A).hom =
      (polynomialPowerObjIso.{u, v} k (n + 1) A).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.epsilonAtPos (polynomialComonad.{u, v} k) n i A) := by
  induction n generalizing A with
  | zero =>
    have hi : i = 0 := Fin.eq_zero (i : Fin 1)
    subst i
    exact polynomialPowerObjIso_naturality.{u, v} k 0
      ((polynomialComonad.{u, v} k).ε.app A)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      exact polynomialPowerObjIso_naturality.{u, v} k (n + 1)
        ((polynomialComonad.{u, v} k).ε.app A)
    | succ j =>
      exact ih (i := j) (A := (polynomialComonad.{u, v} k).obj A)

/-- The zeroth face is evaluation at the actual elements of the preceding degree. -/
@[reassoc]
theorem polynomialResolution_face_zero (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op =
      (polynomialPowerObjIso.{u, v} k (n + 1) A).hom ≫
        (polynomialComonad.{u, v} k).ε.app ((polynomialPower.{u, v} k (n + 1)).obj A) := by
  rw [polynomialResolution_map_δ]
  induction n generalizing A with
  | zero =>
    change (polynomialComonad.{u, v} k).ε.app ((polynomialComonad.{u, v} k).obj A) =
      𝟙 _ ≫ (polynomialComonad.{u, v} k).ε.app ((polynomialComonad.{u, v} k).obj A)
    exact (Category.id_comp _).symm
  | succ n ih =>
    exact ih ((polynomialComonad.{u, v} k).obj A)

/-- Every positive face renames by the preceding counit insertion. -/
@[reassoc]
theorem polynomialResolution_face_succ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op ≫
        (polynomialResolutionObjIso.{u, v} k A n).hom =
      (polynomialResolutionObjIso.{u, v} k A (n + 1)).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A) := by
  rw [polynomialResolution_map_δ, polynomialResolutionObjIso_hom,
    polynomialResolutionObjIso_hom]
  change Comonad.epsilonAtPos (polynomialComonad.{u, v} k) (n + 1) i.succ.rev A ≫ _ =
    _ ≫ (polynomialComonad.{u, v} k).map
      (Comonad.epsilonAtPos (polynomialComonad.{u, v} k) n i.rev A)
  rw [Fin.rev_succ]
  exact polynomialPower_epsilon_castSucc.{u, v} k n i.rev A

/-- On a pure degree generator, the zeroth face returns its actual index element. -/
theorem polynomialResolution_face_zero_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op).hom
      (polynomialResolutionGenerator.{u, v} k A (n + 1) x) = x := by
  let e := polynomialResolutionObjIso.{u, v} k A (n + 1)
  have hd : (polynomialResolution.{u, v} k A).left.map
      (SimplexCategory.δ (0 : Fin (n + 2))).op =
      e.hom ≫ (polynomialComonad.{u, v} k).ε.app
        ((polynomialPower.{u, v} k (n + 1)).obj A) := by
    rw [polynomialResolutionObjIso_hom]
    exact polynomialResolution_face_zero.{u, v} k A n
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶
        (polynomialPower.{u, v} k (n + 1)).obj A =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) hd
  change _ = ((polynomialComonad.{u, v} k).ε.app
      ((polynomialPower.{u, v} k (n + 1)).obj A)).hom
    (e.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) at h
  rw [polynomialResolutionObjIso_hom_generator, polynomialComonad_counit_X] at h
  exact h

/-- Every positive face sends a generator to the generator of its actual lower-face image. -/
theorem polynomialResolution_face_succ_generator (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x) =
      polynomialResolutionGenerator.{u, v} k A n
        ((Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A (n + 1)
  let eB := polynomialResolutionObjIso.{u, v} k A n
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k n).obj A) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x))
    (polynomialResolution_face_succ.{u, v} k A i)
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    MvPolynomial.rename (R := k)
      (Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom
      (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) at h
  rw [polynomialResolutionObjIso_hom_generator, MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.δ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k A n
      ((Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom x))
  rw [polynomialResolutionObjIso_hom_generator]
  exact h

/-- The zeroth degeneracy applies actual comultiplication under the degree identification. -/
@[reassoc]
theorem polynomialResolution_degeneracy_zero (A : CommAlgCat.{max u v} k) (n : ℕ) :
    (polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op ≫
        (polynomialResolutionObjIso.{u, v} k A (n + 1)).hom =
      (polynomialResolutionObjIso.{u, v} k A n).hom ≫
        (polynomialComonad.{u, v} k).δ.app ((polynomialPower.{u, v} k n).obj A) ≫
          (polynomialComonad.{u, v} k).map (polynomialResolutionObjIso.{u, v} k A n).inv := by
  rw [polynomialResolution_map_σ, polynomialResolutionObjIso_hom,
    polynomialResolutionObjIso_hom, polynomialResolutionObjIso_inv]
  induction n generalizing A with
  | zero =>
    change (polynomialComonad.{u, v} k).δ.app A ≫ 𝟙 _ =
      𝟙 _ ≫ (polynomialComonad.{u, v} k).δ.app A ≫
        (polynomialComonad.{u, v} k).map (𝟙 _)
    rw [(polynomialComonad.{u, v} k).toFunctor.map_id]
    simp only [Category.id_comp, Category.comp_id]
    exact (Category.comp_id ((polynomialComonad.{u, v} k).δ.app A)).symm
  | succ n ih =>
    exact ih ((polynomialComonad.{u, v} k).obj A)

/-- Raw comultiplication insertions commute with the actual outer-polynomial identification. -/
@[reassoc]
theorem polynomialPower_delta_castSucc (n : ℕ) (i : Fin (n + 1))
    (A : CommAlgCat.{max u v} k) :
    Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 2) i.castSucc A ≫
        (polynomialPowerObjIso.{u, v} k (n + 2) A).hom =
      (polynomialPowerObjIso.{u, v} k (n + 1) A).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A) := by
  induction n generalizing A with
  | zero =>
    have hi : i = 0 := Fin.eq_zero (i : Fin 1)
    subst i
    exact polynomialPowerObjIso_naturality.{u, v} k 0
      ((polynomialComonad.{u, v} k).δ.app A)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      exact polynomialPowerObjIso_naturality.{u, v} k (n + 1)
        ((polynomialComonad.{u, v} k).δ.app A)
    | succ j =>
      exact ih (i := j) (A := (polynomialComonad.{u, v} k).obj A)

/-- Every positive degeneracy renames by the preceding comultiplication insertion. -/
@[reassoc]
theorem polynomialResolution_degeneracy_succ (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) :
    (polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op ≫
        (polynomialResolutionObjIso.{u, v} k A (n + 2)).hom =
      (polynomialResolutionObjIso.{u, v} k A (n + 1)).hom ≫
        (polynomialComonad.{u, v} k).map
          (Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A) := by
  rw [polynomialResolution_map_σ, polynomialResolutionObjIso_hom,
    polynomialResolutionObjIso_hom]
  change Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 2) i.succ.rev A ≫ _ =
    _ ≫ (polynomialComonad.{u, v} k).map
      (Comonad.deltaAtPos (polynomialComonad.{u, v} k) (n + 1) i.rev A)
  rw [Fin.rev_succ]
  exact polynomialPower_delta_castSucc.{u, v} k n i.rev A

/-- The zeroth degeneracy includes the actual degree generator as a new variable. -/
theorem polynomialResolution_degeneracy_zero_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k n).obj A) :
    ((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op).hom
      (polynomialResolutionGenerator.{u, v} k A n x) =
        polynomialResolutionGenerator.{u, v} k A (n + 1)
          (polynomialResolutionGenerator.{u, v} k A n x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A n
  let eB := polynomialResolutionObjIso.{u, v} k A (n + 1)
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk n)) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k (n + 1)).obj A) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A n x))
    (polynomialResolution_degeneracy_zero.{u, v} k A n)
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    MvPolynomial.rename (R := k) eA.inv.hom
      (((polynomialComonad.{u, v} k).δ.app ((polynomialPower.{u, v} k n).obj A)).hom
        (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A n x))) at h
  rw [polynomialResolutionObjIso_hom_generator, polynomialComonad_comultiplication_X,
    MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.σ (0 : Fin (n + 1))).op).hom
        (polynomialResolutionGenerator.{u, v} k A n x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1)
      (polynomialResolutionGenerator.{u, v} k A n x))
  have hindex : eA.inv.hom (MvPolynomial.X x) =
      polynomialResolutionGenerator.{u, v} k A n x := by
    dsimp only [eA, polynomialResolutionGenerator]
    rw [polynomialResolutionObjIso_inv]
    rfl
  have hright := polynomialResolutionObjIso_hom_generator.{u, v} k A (n + 1)
    (polynomialResolutionGenerator.{u, v} k A n x)
  exact h.trans
    ((congrArg (fun z : (polynomialPower.{u, v} k (n + 1)).obj A =>
      (MvPolynomial.X z : MvPolynomial ((polynomialPower.{u, v} k (n + 1)).obj A) k))
        hindex).trans hright.symm)

/-- Every positive degeneracy sends a generator to its actual lower-degeneracy image. -/
theorem polynomialResolution_degeneracy_succ_generator (A : CommAlgCat.{max u v} k) {n : ℕ}
    (i : Fin (n + 1)) (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x) =
      polynomialResolutionGenerator.{u, v} k A (n + 2)
        ((Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom x) := by
  let eA := polynomialResolutionObjIso.{u, v} k A (n + 1)
  let eB := polynomialResolutionObjIso.{u, v} k A (n + 2)
  apply (CommAlgCat.algEquivOfIso eB).injective
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶
        CommAlgCat.of k (MvPolynomial ((polynomialPower.{u, v} k (n + 2)).obj A) k) =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x))
    (polynomialResolution_degeneracy_succ.{u, v} k A i)
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    MvPolynomial.rename (R := k)
      (Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom
      (eA.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) at h
  rw [polynomialResolutionObjIso_hom_generator, MvPolynomial.rename_X] at h
  change eB.hom.hom
      (((polynomialResolution.{u, v} k A).left.map (SimplexCategory.σ i.succ).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) =
    eB.hom.hom (polynomialResolutionGenerator.{u, v} k A (n + 2)
      ((Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom x))
  rw [polynomialResolutionObjIso_hom_generator]
  exact h

/-- The actual augmentation evaluates a degree-zero formal variable at its index element. -/
theorem polynomialResolution_augmentation_zero_generator (A : CommAlgCat.{max u v} k) (a : A) :
    ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk 0))).hom
      (polynomialResolutionGenerator.{u, v} k A 0 a) = a := by
  rw [polynomialResolutionGenerator_zero, polynomialResolution_augmentation_zero]
  exact polynomialComonad_counit_X.{u, v} k A a

/-- In every positive degree, augmentation of a generator evaluates its actual preceding element. -/
theorem polynomialResolution_augmentation_succ_generator (A : CommAlgCat.{max u v} k) (n : ℕ)
    (x : (polynomialPower.{u, v} k (n + 1)).obj A) :
    ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk (n + 1)))).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x) =
      ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n))).hom x := by
  have h := congrArg
    (fun t : (polynomialResolution.{u, v} k A).left.obj (op (SimplexCategory.mk (n + 1))) ⟶ A =>
      t.hom (polynomialResolutionGenerator.{u, v} k A (n + 1) x))
    (polynomialResolution_augmentation_naturality.{u, v} k A
      (SimplexCategory.δ (0 : Fin (n + 2))).op)
  change ((polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n))).hom
      (((polynomialResolution.{u, v} k A).left.map
        (SimplexCategory.δ (0 : Fin (n + 2))).op).hom
        (polynomialResolutionGenerator.{u, v} k A (n + 1) x)) = _ at h
  rw [polynomialResolution_face_zero_generator] at h
  exact h.symm

/-- Augmented functoriality retains the actual coefficient algebra map at every level. -/
@[reassoc]
theorem polynomialResolutionMap_augmentation {A B : CommAlgCat.{max u v} k}
    (f : A ⟶ B) (n : ℕ) :
    (polynomialResolutionMap.{u, v} k f).left.app (op (SimplexCategory.mk n)) ≫
        (polynomialResolution.{u, v} k B).hom.app (op (SimplexCategory.mk n)) =
      (polynomialResolution.{u, v} k A).hom.app (op (SimplexCategory.mk n)) ≫ f := by
  have h : (polynomialResolutionMap.{u, v} k f).left ≫
      (polynomialResolution.{u, v} k B).hom =
    (polynomialResolution.{u, v} k A).hom ≫
      (SimplicialObject.const (CommAlgCat.{max u v} k)).map f :=
    (polynomialResolutionMap.{u, v} k f).w
  exact congrArg
    (fun t : (polynomialResolution.{u, v} k A).left ⟶
      (SimplicialObject.const (CommAlgCat.{max u v} k)).obj B =>
        t.app (op (SimplexCategory.mk n))) h

end CommAlgCat

end
