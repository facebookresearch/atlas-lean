/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monad.PowerOpposite
public import MathlibExt.CategoryTheory.Comonad.BarResolution

/-!
# The coaugmented cosimplicial coresolution of a monad

Let T be a monad on a category C and X an object of C. Dualizing the augmented resolution of
the opposite comonad gives a coaugmented cosimplicial object with coaugmentation point X and
degree-n term canonically identified with T^{n+1}(X).

In these power coordinates, cofaces insert the unit using barEtaAtPos and codegeneracies
multiply adjacent factors using barMuAtPos. The degree-zero coaugmentation is η_X, and a
morphism f : X → Y acts in degree n by T^{n+1}(f). Only the monad and category structure are
required.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Monad

variable {C : Type u} [Category.{v} C]

/-- For a monad T on C, dualizing the augmented comonad resolution of T.op gives a functor C →
CosimplicialObject.Augmented C. It assigns to X a coaugmented cosimplicial object whose point
is X and whose degree-n term is identified with T^{n+1}(X). Double-opposite whiskering returns
the construction to C. -/
def coresolutionAugmentedFunctor (T : Monad C) :
    C ⥤ CosimplicialObject.Augmented C :=
  (Comonad.resolutionAugmentedFunctor (Monad.op T)).rightOp ⋙
    (simplicialCosimplicialAugmentedEquiv Cᵒᵖ).functor ⋙
      CosimplicialObject.Augmented.whiskeringObj (Cᵒᵖ)ᵒᵖ C (unopUnop C)

/-- Let T be a monad on C and X ∈ C. Define coresolutionAugmented(T,X) to be the value at X of the
coaugmented coresolution functor. Its point is X, its zero-degree map is η_X, and its degree-n
cosimplicial term has T^{n+1}(X) coordinates. -/
def coresolutionAugmented (T : Monad C) (X : C) : CosimplicialObject.Augmented C :=
  (coresolutionAugmentedFunctor T).obj X

/-- For a monad T on C, forgetting the coaugmentation point from coresolutionAugmentedFunctor
gives a functor C → CosimplicialObject C. In degree n it is identified with T^{n+1} on objects
and morphisms. -/
def coresolutionFunctor (T : Monad C) : C ⥤ CosimplicialObject C :=
  coresolutionAugmentedFunctor T ⋙ CosimplicialObject.Augmented.drop

/-- Let T be a monad on C and X an object. The cosimplicial object coresolution(T,X) is the right
component of its coaugmented object. It has degree-n term canonically identified with
T^{n+1}(X), with unit cofaces and multiplication codegeneracies. -/
def coresolution (T : Monad C) (X : C) : CosimplicialObject C :=
  (coresolutionAugmented T X).right

/-- For a monad T on C and X ∈ C, the coaugmentation-point object of coresolutionAugmented(T,X) is
exactly X. -/
theorem coresolutionAugmented_point (T : Monad C) (X : C) :
    (coresolutionAugmented T X).left = X := by
  change (Comonad.resolutionAugmented (Monad.op T) (Opposite.op X)).right.unop = X
  rw [Comonad.resolutionAugmented_point]

/-- Let T be a monad on C, X ∈ C, and n ∈ ℕ. The degree-n term of coresolution(T,X) equals
((T.op)^{n+1}(op X)).unop, using the comonad-power construction. The opposite-power comparison
identifies it with T^{n+1}(X). -/
theorem coresolution_obj (T : Monad C) (X : C) (n : ℕ) :
    (coresolution T X).obj (SimplexCategory.mk n) =
      ((Comonad.comonadPow (Monad.op T) (n + 1)).obj (Opposite.op X)).unop := by
  change ((Comonad.resolutionAugmented (Monad.op T) (Opposite.op X)).left.obj
    (Opposite.op (SimplexCategory.mk n))).unop = _
  rw [Comonad.resolutionAugmented_left, Comonad.resolutionBar_obj]

/-- For a monad T on C, X ∈ C, n ∈ ℕ, and i ∈ Fin(n+2), the cosimplicial coface from degree n to
n+1 is the unop of cobarEpsilonAtPos(T.op,n+1,i,op X). Under monad-power coordinates it is the
source-ordered unit insertion. -/
theorem coresolution_map_δ (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 2)) :
    (coresolution T X).map (SimplexCategory.δ i) =
      (Comonad.cobarEpsilonAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop := by
  change ((Comonad.resolutionBar (Monad.op T) (Opposite.op X)).map
    (SimplexCategory.δ i).op).unop = _
  exact congrArg Quiver.Hom.unop
    (Comonad.resolutionBar_map_δ_op (Monad.op T) (Opposite.op X) i)

/-- Let T be a monad on C, X ∈ C, n ∈ ℕ, and i ∈ Fin(n+1). The codegeneracy from degree n+1 to n
is the unop of cobarDeltaAtPos(T.op,n+1,i,op X). Its monad-power coordinates multiply the
corresponding adjacent factors. -/
theorem coresolution_map_σ (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 1)) :
    (coresolution T X).map (SimplexCategory.σ i) =
      (Comonad.cobarDeltaAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop := by
  change ((Comonad.resolutionBar (Monad.op T) (Opposite.op X)).map
    (SimplexCategory.σ i).op).unop = _
  exact congrArg Quiver.Hom.unop
    (Comonad.resolutionBar_map_σ_op (Monad.op T) (Opposite.op X) i)

/-- For a monad T on C and X ∈ C, the degree-zero coaugmentation of coresolutionAugmented(T,X)
equals η_X : X → T(X). -/
theorem coresolutionAugmented_hom_zero (T : Monad C) (X : C) :
    (coresolutionAugmented T X).hom.app (SimplexCategory.mk 0) = T.η.app X := by
  change 𝟙 _ ≫ ((Comonad.resolutionAugmented (Monad.op T) (Opposite.op X)).hom.app
    (Opposite.op (SimplexCategory.mk 0))).unop = T.η.app X
  simp only [Category.id_comp, Comonad.resolutionAugmented_hom_zero,
    Monad.op_ε_app]
  rfl

/-- Let T be a monad on C, f : X → Y, and n ∈ ℕ. The degree-n component of
coresolutionFunctor(T)(f) is the unop of (T.op)^{n+1}(f.op). In the monad-power coordinates
this is T^{n+1}(f). -/
theorem coresolutionFunctor_map_app (T : Monad C) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((coresolutionFunctor T).map f).app (SimplexCategory.mk n) =
      ((Comonad.comonadPow (Monad.op T) (n + 1)).map f.op).unop := by
  change ((Comonad.resolutionHom (Monad.op T) f.op).left.app
    (Opposite.op (SimplexCategory.mk n))).unop = _
  exact congrArg Quiver.Hom.unop
    (Comonad.resolutionHom_left_app (Monad.op T) f.op n)

/-- For a monad T on C and f : X → Y, the point component of coresolutionAugmentedFunctor(T)(f)
equals f. Thus the functorial coaugmentation retains the starting morphism. -/
theorem coresolutionAugmentedFunctor_map_left (T : Monad C) {X Y : C} (f : X ⟶ Y) :
    ((coresolutionAugmentedFunctor T).map f).left = f := by
  change (Comonad.resolutionHom (Monad.op T) f.op).right.unop = f
  rw [Comonad.resolutionHom_right]
  rfl

/-- Let T be a monad on C, X ∈ C, and n ∈ ℕ. The opposite-power comparison gives
coresolution(T,X)_n ≅ T^{n+1}(X). It first uses the degree-object equality with the
opposite-comonad power and then the natural unop power isomorphism. -/
def coresolutionObjIso (T : Monad C) (X : C) (n : ℕ) :
    (coresolution T X).obj (SimplexCategory.mk n) ≅ (monadPow T (n + 1)).obj X :=
  eqToIso (coresolution_obj T X n) ≪≫ (monadPowOpIso T (n + 1)).app X

/-- For a monad T on C, X ∈ C, and n ∈ ℕ, the forward morphism of coresolutionObjIso(T,X,n) equals
the component at X of monadPowOpIso(T,n+1). This fixes its map from the cosimplicial degree
object to T^{n+1}(X). -/
@[simp]
theorem coresolutionObjIso_hom (T : Monad C) (X : C) (n : ℕ) :
    (coresolutionObjIso T X n).hom = (monadPowOpIso T (n + 1)).hom.app X := by
  induction n generalizing X with
  | zero =>
      change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      exact Category.id_comp _
  | succ n ih =>
      exact ih (T.obj X)

/-- Let T be a monad on C, f : X → Y, and n ∈ ℕ. If e_X,e_Y are the degree-n power charts, then
coresolutionFunctor(T)(f)_n ≫ e_Y.hom = e_X.hom ≫ T^{n+1}(f). -/
theorem coresolutionObjIso_naturality (T : Monad C) {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((coresolutionFunctor T).map f).app (SimplexCategory.mk n) ≫
        (coresolutionObjIso T Y n).hom =
      (coresolutionObjIso T X n).hom ≫ (monadPow T (n + 1)).map f := by
  rw [coresolutionFunctor_map_app, coresolutionObjIso_hom, coresolutionObjIso_hom]
  change ((Comonad.comonadPow (Monad.op T) (n + 1)).map f.op).unop ≫
      (monadPowOpIso T (n + 1)).hom.app Y =
    (monadPowOpIso T (n + 1)).hom.app X ≫ (monadPow T (n + 1)).map f
  exact (monadPowOpIso T (n + 1)).hom.naturality f

/-- For a monad T on C, X ∈ C, n ∈ ℕ, and i ∈ Fin(n+2), let e_n,e_{n+1} be the degree charts. Then
d^i ≫ e_{n+1}.hom = e_n.hom ≫ barEtaAtPos(T,n+1,i,X). The map inserts the unit in the reversed
finite-position convention. -/
theorem coresolutionObjIso_coface (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 2)) :
    (coresolution T X).map (SimplexCategory.δ i) ≫
        (coresolutionObjIso T X (n + 1)).hom =
      (coresolutionObjIso T X n).hom ≫ barEtaAtPos T (n + 1) i X := by
  rw [coresolution_map_δ, coresolutionObjIso_hom, coresolutionObjIso_hom]
  change (Comonad.cobarEpsilonAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop ≫
      (monadPowOpIso T (n + 2)).hom.app X =
    (monadPowOpIso T (n + 1)).hom.app X ≫ barEtaAtPos T (n + 1) i X
  exact cobarEpsilonAtPos_op T (n + 1) i X

/-- Let T be a monad on C, X ∈ C, n ∈ ℕ, and i ∈ Fin(n+1). For the power charts e, the
codegeneracy satisfies s^i ≫ e_n.hom = e_{n+1}.hom ≫ barMuAtPos(T,n+1,i,X). The target has n+1
monad factors. -/
theorem coresolutionObjIso_codegeneracy (T : Monad C) (X : C) {n : ℕ} (i : Fin (n + 1)) :
    (coresolution T X).map (SimplexCategory.σ i) ≫ (coresolutionObjIso T X n).hom =
      (coresolutionObjIso T X (n + 1)).hom ≫ barMuAtPos T (n + 1) i X := by
  rw [coresolution_map_σ, coresolutionObjIso_hom, coresolutionObjIso_hom]
  change (Comonad.cobarDeltaAtPos (Monad.op T) (n + 1) i (Opposite.op X)).unop ≫
      (monadPowOpIso T (n + 1)).hom.app X =
    (monadPowOpIso T (n + 2)).hom.app X ≫ barMuAtPos T (n + 1) i X
  exact cobarDeltaAtPos_op T (n + 1) i X

end CategoryTheory.Monad

end
