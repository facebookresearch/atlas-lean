/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import MathlibExt.CategoryTheory.Comonad.Cobar

/-!
# The actual comonad induced in a slice over a fixed target

An object `P → A` is sent to `G(P) → P → A`, using the original counit.
The original counit and comultiplication are actual slice morphisms by their
native laws. This constructs a genuine comonad in the slice. Its underlying
functor, counit, comultiplication and powers retain the original maps after
forgetting the point map.

This is the missing categorical provider for polynomial resolution comparison
over the fixed augmentation target. It supplies no resolution-independence or
desired cotangent comparison certificate. Candidate source; UNEXECUTED.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] (G : Comonad C) (A : C)

/-- The actual original comonad functor with augmentation composed to A. -/
def overFunctor : Over A ⥤ Over A where
  obj P := Over.mk (G.ε.app P.left ≫ P.hom)
  map {P Q} f := Over.homMk (G.map f.left) (by
    change G.map f.left ≫ (G.ε.app Q.left ≫ Q.hom) = G.ε.app P.left ≫ P.hom
    exact (Category.assoc (G.map f.left) (G.ε.app Q.left) Q.hom).symm.trans
      ((congrArg (fun m => m ≫ Q.hom) (G.ε.naturality f.left)).trans
        ((Category.assoc (G.ε.app P.left) f.left Q.hom).trans
          (congrArg (fun m => G.ε.app P.left ≫ m) f.w))))
  map_id P := by
    apply Over.OverMorphism.ext
    exact G.map_id P.left
  map_comp f g := by
    apply Over.OverMorphism.ext
    change G.map (f.left ≫ g.left) = G.map f.left ≫ G.map g.left
    exact G.map_comp f.left g.left

/-- The original counit as an actual natural transformation in the slice. -/
def overCounit : overFunctor G A ⟶ 𝟭 (Over A) where
  app P := Over.homMk (G.ε.app P.left) rfl
  naturality {P Q} f := by
    apply Over.OverMorphism.ext
    exact G.ε.naturality f.left

/-- The original comultiplication as an actual slice morphism. -/
def overComultiplication : overFunctor G A ⟶ overFunctor G A ⋙ overFunctor G A where
  app P := Over.homMk (G.δ.app P.left) (by
    change G.δ.app P.left ≫ (G.ε.app (G.obj P.left) ≫ (G.ε.app P.left ≫ P.hom)) =
      G.ε.app P.left ≫ P.hom
    rw [← Category.assoc, G.left_counit, Category.id_comp])
  naturality {P Q} f := by
    apply Over.OverMorphism.ext
    exact G.δ.naturality f.left

/-- The genuine native comonad in the slice over the prescribed target. -/
def overComonad : Comonad (Over A) where
  toFunctor := overFunctor G A
  ε := overCounit G A
  δ := overComultiplication G A
  coassoc P := by
    apply Over.OverMorphism.ext
    exact G.coassoc P.left
  left_counit P := by
    apply Over.OverMorphism.ext
    exact G.left_counit P.left
  right_counit P := by
    apply Over.OverMorphism.ext
    exact G.right_counit P.left

/-- Forgetting the point map retains the same original functor. -/
def overForgetFunctorIso :
    (overComonad G A).toFunctor ⋙ Over.forget A ≅ Over.forget A ⋙ G.toFunctor :=
  Iso.refl _

@[simp]
theorem overCounit_app_left (P : Over A) :
    ((overComonad G A).ε.app P).left = G.ε.app P.left := rfl

@[simp]
theorem overComultiplication_app_left (P : Over A) :
    ((overComonad G A).δ.app P).left = G.δ.app P.left := rfl

/-- The actual slice power has the same original underlying power object. -/
theorem overPow_obj_left (n : ℕ) (P : Over A) :
    ((comonadPow (overComonad G A) n).obj P).left = (comonadPow G n).obj P.left := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => exact ih ((overComonad G A).obj P)

/-- Underlying power maps retain their genuine original maps, with their
source and target object equalities recorded by heterogeneous equality. -/
theorem overPow_map_left (n : ℕ) {P Q : Over A} (f : P ⟶ Q) :
    HEq (((comonadPow (overComonad G A) n).map f).left)
      ((comonadPow G n).map f.left) := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih => exact ih ((overComonad G A).map f)

/-- A genuine original counit section is an actual section in the slice. -/
def overCounitSection (P : Over A) (s : P.left ⟶ G.obj P.left)
    (hs : s ≫ G.ε.app P.left = 𝟙 P.left) : P ⟶ (overComonad G A).obj P :=
  Over.homMk s (by
    change s ≫ (G.ε.app P.left ≫ P.hom) = P.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ P.hom) hs).trans (Category.id_comp _)))

@[reassoc]
theorem overCounitSection_counit (P : Over A) (s : P.left ⟶ G.obj P.left)
    (hs : s ≫ G.ε.app P.left = 𝟙 P.left) :
    overCounitSection G A P s hs ≫ (overComonad G A).ε.app P = 𝟙 P := by
  apply Over.OverMorphism.ext
  exact hs

end CategoryTheory.Comonad

end
