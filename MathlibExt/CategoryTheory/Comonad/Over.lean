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
# Comonads on slices over a fixed object

Let G be a comonad on C and A : C. On Over A, send p : P → A to G(P) →^{ε_P} P →^p A, and a
slice morphism to G of its underlying map. The original counit and comultiplication are slice
morphisms and define a comonad G_A.

Forgetting to C identifies G_A with G on the underlying objects and maps. Its n-th power has
underlying object G^n(P), and its power maps agree heterogeneously with G^n applied to the
original slice map. A section of ε_P lifts to a counit section in Over A. Object and morphism
universes are independent.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C] (G : Comonad C) (A : C)

/-- Endofunctor of a slice induced by a comonad counit.

For G on C and fixed A, send p : P → A to ε_P ≫ p : G(P) → A. A morphism in Over A is sent to
G of its underlying arrow; counit naturality supplies its slice equation. -/
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

/-- Counit natural transformation in the slice.

The counit G_A(p) → p in Over A has underlying map ε_P : G(P) → P. Its compatibility with the
structural arrows to A is the definition of G_A(p). -/
def overCounit : overFunctor G A ⟶ 𝟭 (Over A) where
  app P := Over.homMk (G.ε.app P.left) rfl
  naturality {P Q} f := by
    apply Over.OverMorphism.ext
    exact G.ε.naturality f.left

/-- Comultiplication natural transformation in the slice.

For p : P → A, the underlying map of G_A(p) → G_A²(p) is δ_P : G(P) → G²(P). The comonad
counit law makes this map commute with both structural arrows to A. -/
def overComultiplication : overFunctor G A ⟶ overFunctor G A ⋙ overFunctor G A where
  app P := Over.homMk (G.δ.app P.left) (by
    change G.δ.app P.left ≫ (G.ε.app (G.obj P.left) ≫ (G.ε.app P.left ≫ P.hom)) =
      G.ε.app P.left ≫ P.hom
    rw [← Category.assoc, G.left_counit, Category.id_comp])
  naturality {P Q} f := by
    apply Over.OverMorphism.ext
    exact G.δ.naturality f.left

/-- Comonad induced on a slice category.

For a comonad G on C and any A : C, its counit-composed endofunctor on Over A, together with
the underlying ε and δ, satisfies coassociativity and both counit laws. This defines G_A
without a coalgebra structure on A. -/
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

/-- Forgetful comparison for a slice comonad.

For G_A on Over A and the forgetful functor U : Over A → C, the functors G_A ⋙ U and U ⋙ G are
canonically isomorphic, with the same underlying object and morphism assignments. -/
def overForgetFunctorIso :
    (overComonad G A).toFunctor ⋙ Over.forget A ≅ Over.forget A ⋙ G.toFunctor :=
  Iso.refl _

/-- Underlying slice-comonad counit component.

For p : P → A, forgetting the component ε^{G_A}_p yields ε^G_P : G(P) → P. -/
@[simp]
theorem overCounit_app_left (P : Over A) :
    ((overComonad G A).ε.app P).left = G.ε.app P.left := rfl

/-- Underlying slice-comonad comultiplication component.

For p : P → A, forgetting δ^{G_A}_p yields δ^G_P : G(P) → G²(P). -/
@[simp]
theorem overComultiplication_app_left (P : Over A) :
    ((overComonad G A).δ.app P).left = G.δ.app P.left := rfl

/-- Underlying object of an iterated slice comonad.

For n : ℕ and p : P → A, the underlying object of G_A^n(p) equals G^n(P), including the
identity power at n = 0. -/
theorem overPow_obj_left (n : ℕ) (P : Over A) :
    ((comonadPow (overComonad G A) n).obj P).left = (comonadPow G n).obj P.left := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => exact ih ((overComonad G A).obj P)

/-- Underlying map of an iterated slice comonad.

For n : ℕ and a slice morphism f : p → q, the underlying map of G_A^n(f) is heterogeneously
equal to G^n(f.left). The object identifications retain the original source and target types. -/
theorem overPow_map_left (n : ℕ) {P Q : Over A} (f : P ⟶ Q) :
    HEq (((comonadPow (overComonad G A) n).map f).left)
      ((comonadPow G n).map f.left) := by
  induction n generalizing P Q with
  | zero => rfl
  | succ n ih => exact ih ((overComonad G A).map f)

/-- Counit section lifted to a slice category.

For p : P → A and s : P → G(P) with s ≫ ε_P = id_P, the same s defines p → G_A(p) in Over A,
because s ≫ ε_P ≫ p = p. -/
def overCounitSection (P : Over A) (s : P.left ⟶ G.obj P.left)
    (hs : s ≫ G.ε.app P.left = 𝟙 P.left) : P ⟶ (overComonad G A).obj P :=
  Over.homMk s (by
    change s ≫ (G.ε.app P.left ≫ P.hom) = P.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ P.hom) hs).trans (Category.id_comp _)))

/-- Counit-section identity in the slice.

For a counit section s : P → G(P), its lifted slice map p → G_A(p) followed by the slice
counit equals id_p as a morphism in Over A. -/
@[reassoc]
theorem overCounitSection_counit (P : Over A) (s : P.left ⟶ G.obj P.left)
    (hs : s ≫ G.ε.app P.left = 𝟙 P.left) :
    overCounitSection G A P s hs ≫ (overComonad G A).ε.app P = 𝟙 P := by
  apply Over.OverMorphism.ext
  exact hs

end CategoryTheory.Comonad

end
