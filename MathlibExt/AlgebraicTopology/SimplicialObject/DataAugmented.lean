/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.AlgebraicTopology.SimplicialObject.FromData
public import Mathlib.CategoryTheory.Comma.Arrow

@[expose] public section

open CategoryTheory

universe v u

/-! # Augmented simplicial data

`Augmented C` is the comma category over the constant-data functor,
mirroring `SimplicialObject.Augmented`. A degree-zero map `p : X.obj 0 ⟶ Q`
lifts to `X ⟶ constData Q` iff it equalizes the two degree-one faces
(`IsBalanced`); the lift iterates the zeroth face (`balancedExtension`).
-/

namespace CategoryTheory.SimplicialObject.Data

variable {C : Type u} [Category.{v} C]

/-- Constant simplicial data on `Q`. -/
def constData (Q : C) : Data C where
  obj _ := Q
  δ _ := 𝟙 Q
  σ _ := 𝟙 Q
  δ_comp_δ := by
    intro n i j _
    simp
  δ_comp_σ_of_le := by
    intro n i j _
    simp
  δ_comp_σ_self := by
    intro n i
    simp
  δ_comp_σ_succ := by
    intro n i
    simp
  δ_comp_σ_of_gt := by
    intro n i j _
    simp
  σ_comp_σ := by
    intro n i j _
    simp

@[simp]
theorem constData_obj (Q : C) (n : ℕ) : (constData (Q := Q)).obj n = Q :=
  rfl

@[simp]
theorem constData_δ (Q : C) {n : ℕ} (i : Fin (n + 2)) :
    (constData (Q := Q)).δ i = 𝟙 Q :=
  rfl

@[simp]
theorem constData_σ (Q : C) {n : ℕ} (i : Fin (n + 1)) :
    (constData (Q := Q)).σ i = 𝟙 Q :=
  rfl

/-- Morphism between constant data induced by a morphism in `C`. -/
def constDataHom {Q R : C} (f : Q ⟶ R) : constData Q ⟶ constData R where
  app _ := f
  w_δ := by
    intro n i
    simp
  w_σ := by
    intro n i
    simp

@[simp]
theorem constDataHom_app {Q R : C} (f : Q ⟶ R) (n : ℕ) :
    (constDataHom (f := f)).app n = f :=
  rfl

/-- Constant functor `C ⥤ Data C`. -/
def constFunctor : C ⥤ Data C where
  obj Q := constData Q
  map f := constDataHom f
  map_id Q := by
    apply Hom.ext
    intro n
    simp
  map_comp f g := by
    apply Hom.ext
    intro n
    simp

@[simp]
theorem constFunctor_obj_obj (Q : C) (n : ℕ) :
    ((constFunctor (C := C)).obj Q).obj n = Q :=
  rfl

@[simp]
theorem constFunctor_obj_δ (Q : C) {n : ℕ} (i : Fin (n + 2)) :
    ((constFunctor (C := C)).obj Q).δ i = 𝟙 Q :=
  rfl

@[simp]
theorem constFunctor_obj_σ (Q : C) {n : ℕ} (i : Fin (n + 1)) :
    ((constFunctor (C := C)).obj Q).σ i = 𝟙 Q :=
  rfl

@[simp]
theorem constFunctor_map_app (Q R : C) (f : Q ⟶ R) (n : ℕ) :
    ((constFunctor (C := C)).map f).app n = f :=
  rfl

variable {X : Data C}

/--
Predicate that `p : X.obj 0 ⟶ Q` equalizes the two face maps in degree one.
Uses unambiguous `Fin 2` indices.
-/
def IsBalanced {Q : C} (p : X.obj 0 ⟶ Q) : Prop :=
  X.δ (0 : Fin 2) ≫ p = X.δ (1 : Fin 2) ≫ p

theorem isBalanced_iff {Q : C} {p : X.obj 0 ⟶ Q} :
    IsBalanced (X := X) p ↔ X.δ (0 : Fin 2) ≫ p = X.δ (1 : Fin 2) ≫ p :=
  Iff.rfl

/-- Recursive extension of a degree-zero map by iterating the zeroth face. -/
def balancedExtension {Q : C} (p : X.obj 0 ⟶ Q) : ∀ n, X.obj n ⟶ Q
  | 0 => p
  | n + 1 => X.δ (0 : Fin (n + 2)) ≫ balancedExtension p n

@[simp]
theorem balancedExtension_zero {Q : C} (p : X.obj 0 ⟶ Q) :
    balancedExtension (X := X) p 0 = p :=
  rfl

@[simp]
theorem balancedExtension_succ {Q : C} (p : X.obj 0 ⟶ Q) (n : ℕ) :
    balancedExtension (X := X) p (n + 1) = X.δ (0 : Fin (n + 2)) ≫ balancedExtension (X := X) p n :=
  rfl

/-- Every face followed by the lower extension equals the higher extension. -/
theorem balancedExtension_δ {Q : C} {p : X.obj 0 ⟶ Q}
    (hp : IsBalanced (X := X) p) :
    ∀ (n : ℕ) (i : Fin (n + 2)),
      X.δ i ≫ balancedExtension (X := X) p n = balancedExtension (X := X) p (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro i
    fin_cases i
    · rfl
    · exact hp.symm
  | succ n ih =>
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rfl
    · have hcomp := X.δ_comp_δ (Fin.zero_le (n := n + 2) (a := j))
      calc
        X.δ j.succ ≫ balancedExtension (X := X) p (n + 1)
            = X.δ j.succ ≫ (X.δ (0 : Fin (n + 2)) ≫ balancedExtension (X := X) p n) := rfl
        _ = (X.δ j.succ ≫ X.δ (0 : Fin (n + 2))) ≫ balancedExtension (X := X) p n := by
            rw [← Category.assoc]
        _ = (X.δ (0 : Fin (n + 2)).castSucc ≫ X.δ j) ≫ balancedExtension (X := X) p n := by
            rw [hcomp]
        _ = X.δ (0 : Fin (n + 2)).castSucc ≫ (X.δ j ≫ balancedExtension (X := X) p n) := by
            rw [Category.assoc]
        _ = X.δ (0 : Fin (n + 2)).castSucc ≫ balancedExtension (X := X) p (n + 1) := by
            rw [ih j]
        _ = X.δ (0 : Fin (n + 3)) ≫ balancedExtension (X := X) p (n + 1) := rfl
        _ = balancedExtension (X := X) p (n + 2) := rfl

/-- Degeneracy compatibility derived from the face theorem and `δ_comp_σ_self`. -/
theorem balancedExtension_σ {Q : C} {p : X.obj 0 ⟶ Q}
    (hp : IsBalanced (X := X) p) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      X.σ i ≫ balancedExtension (X := X) p (n + 1) = balancedExtension (X := X) p n := by
  intro n i
  have hface : X.δ i.castSucc ≫ balancedExtension (X := X) p n =
      balancedExtension (X := X) p (n + 1) :=
    balancedExtension_δ hp n i.castSucc
  calc
    X.σ i ≫ balancedExtension (X := X) p (n + 1)
        = X.σ i ≫ (X.δ i.castSucc ≫ balancedExtension (X := X) p n) := by
            rw [← hface]
        _ = (X.σ i ≫ X.δ i.castSucc) ≫ balancedExtension (X := X) p n := by
            rw [← Category.assoc]
        _ = 𝟙 (X.obj n) ≫ balancedExtension (X := X) p n := by
            rw [X.δ_comp_σ_self]
        _ = balancedExtension (X := X) p n := by
            rw [Category.id_comp]

/-- The morphism `X ⟶ constant Q` associated to a balanced degree-zero map. -/
def balancedHom {Q : C} {p : X.obj 0 ⟶ Q} (hp : IsBalanced (X := X) p) :
    X ⟶ constData Q where
  app n := balancedExtension (X := X) p n
  w_δ := by
    intro n i
    have h : X.δ i ≫ balancedExtension (X := X) p n = balancedExtension (X := X) p (n + 1) :=
      balancedExtension_δ hp n i
    simp only [constData]
    rw [Category.comp_id]
    exact h.symm
  w_σ := by
    intro n i
    have h : X.σ i ≫ balancedExtension (X := X) p (n + 1) = balancedExtension (X := X) p n :=
      balancedExtension_σ hp n i
    simp only [constData]
    rw [Category.comp_id]
    exact h.symm

@[simp]
theorem balancedHom_app_zero {Q : C} {p : X.obj 0 ⟶ Q} (hp : IsBalanced (X := X) p) :
    (balancedHom (X := X) hp).app 0 = p :=
  rfl

@[simp]
theorem balancedHom_app_succ {Q : C} {p : X.obj 0 ⟶ Q} (hp : IsBalanced (X := X) p) (n : ℕ) :
    (balancedHom (X := X) hp).app (n + 1) =
      X.δ (0 : Fin (n + 2)) ≫ (balancedHom (X := X) hp).app n :=
  rfl

theorem balancedHom_app {Q : C} {p : X.obj 0 ⟶ Q} (hp : IsBalanced (X := X) p) (n : ℕ) :
    (balancedHom (X := X) hp).app n = balancedExtension (X := X) p n :=
  rfl

/-- Any map to constant data is balanced in degree zero. -/
theorem isBalanced_of_hom {Q : C} (f : X ⟶ constData Q) :
    IsBalanced (X := X) (f.app 0) := by
  dsimp only [IsBalanced]
  have w0 := f.w_δ (0 : Fin 2)
  have w1 := f.w_δ (1 : Fin 2)
  simp only [constData] at w0 w1
  rw [Category.comp_id] at w0 w1
  exact w0.symm.trans w1

/-- Morphisms to constant data are determined by iterated zeroth faces. -/
theorem hom_app_eq_balancedExtension {Q : C} (f : X ⟶ constData Q) :
    ∀ n, f.app n = balancedExtension (X := X) (f.app 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have w0 := f.w_δ (0 : Fin (n + 2))
    simp only [constData] at w0
    rw [Category.comp_id] at w0
    -- w0 : f.app (n+1) = δ0 ≫ f.app n
    have h1 : f.app (n + 1) = X.δ (0 : Fin (n + 2)) ≫ balancedExtension (X := X) (f.app 0) n :=
      w0.trans (congrArg (X.δ (0 : Fin (n + 2)) ≫ ·) ih)
    exact h1

theorem hom_eq_of_app_zero_eq {Q : C} {f g : X ⟶ constData Q}
    (h : f.app 0 = g.app 0) : f = g := by
  apply Hom.ext
  intro n
  have hf := hom_app_eq_balancedExtension (X := X) f n
  have hg := hom_app_eq_balancedExtension (X := X) g n
  have hmid : balancedExtension (X := X) (f.app 0) n = balancedExtension (X := X) (g.app 0) n := by
    rw [h]
  exact hf.trans (hmid.trans hg.symm)

/-- Balanced degree-zero maps as a subtype. -/
def Balanced (Q : C) := { p : X.obj 0 ⟶ Q // IsBalanced (X := X) p }

/--
Equivalence from balanced degree-zero maps to maps into constant data:
forward sends `⟨p, hp⟩` to `balancedHom hp`; backward sends `f` to
`⟨f.app 0, isBalanced_of_hom f⟩`. Requires the equalizer hypothesis
`IsBalanced p : δ 0 ≫ p = δ 1 ≫ p`.
-/
def balancedEquiv {Q : C} : Balanced (X := X) Q ≃ (X ⟶ constData Q) where
  toFun p := balancedHom p.2
  invFun f := ⟨f.app 0, isBalanced_of_hom (X := X) f⟩
  left_inv := by
    intro ⟨p, hp⟩
    apply Subtype.ext
    rfl
  right_inv := by
    intro f
    apply hom_eq_of_app_zero_eq
    rfl

end Data

namespace Data

variable (C : Type u) [Category.{v} C]

/-- Augmented simplicial data as a comma category, mirroring `SimplicialObject.Augmented`. -/
def Augmented :=
  Comma (𝟭 (Data C)) (constFunctor (C := C))

instance : Category (Augmented C) :=
  inferInstanceAs (Category (Comma _ _))

namespace Augmented

variable {C}

/-- Forgetful functor to the underlying simplicial data. -/
def drop : Augmented C ⥤ Data C :=
  Comma.fst _ _

/-- Functor projecting the augmentation point. -/
def point : Augmented C ⥤ C :=
  Comma.snd _ _

/-- Constructor for augmented simplicial data from underlying data and augmentation map. -/
def mk (X : Data C) (Q : C) (f : X ⟶ constData Q) : Augmented C where
  left := X
  right := Q
  hom := f

/--
Augmentation over `Q` from a degree-zero map satisfying the equalizer
hypothesis `IsBalanced p`; packages `balancedHom hp` via `mk`.
-/
def augment (X : Data C) (Q : C) (p : X.obj 0 ⟶ Q) (hp : IsBalanced (X := X) p) :
    Augmented C :=
  mk X Q (balancedHom hp)

@[simp]
theorem augment_hom_app_zero (X : Data C) (Q : C) (p : X.obj 0 ⟶ Q)
    (hp : IsBalanced (X := X) p) :
    (augment X Q p hp).hom.app 0 = p :=
  rfl

theorem augment_hom_eq_balancedHom (X : Data C) (Q : C) (p : X.obj 0 ⟶ Q)
    (hp : IsBalanced (X := X) p) :
    (augment X Q p hp).hom = balancedHom hp :=
  rfl

end Augmented

end Data

end CategoryTheory.SimplicialObject

end
