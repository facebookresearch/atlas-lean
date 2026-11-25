/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteRootTowers
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# Infinite-root stacks with actual tower projections and family maps

Finite roots are the already specified actual denominator extensions for
the power-n map of the actual monoid sheaf. Global transition morphisms
are normalized to the literal m/n root restrictions in every fibre; their
unit/composition 2-cells are native invertible modifications of strong
transformations. Infinite fibres are the actual compatible-root groupoid.

All projections, parameter restrictions and component comparisons are
retained. The Kummer-flat site is not defined through this stack, and
reconstruction only concerns the later universal-root-preserving maps.

Source: Mattia Talpo and Angelo Vistoli, https://arxiv.org/abs/1410.1164v2,
§§3--4, Theorems 5.24/6.16. The native modification category is completed
Mathlib mathematics (copyright 2024 Calle Sönne; author Calle Sönne;
Apache License 2.0),
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Bicategory/Modification/Pseudo.lean
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.InfiniteDenominatorRoots
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.FiniteRootTowers
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage

universe u

variable {X : Scheme.{u}}
  [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]

/-- Use the native modification category on the fixed relative pseudofunctors. -/
local instance nativeModificationCategory
    (F G : Pseudofunctor (LocallyDiscrete (Over X)ᵒᵖ) Cat.{u, u+1}) :
    Category (Pseudofunctor.StrongTrans F G) :=
  Pseudofunctor.StrongTrans.homCategory (F := F) (G := G)

abbrev Hom (P Q : GeneralStackGeometry.RelativeStack X) :=
  Pseudofunctor.StrongTrans P.toPseudofunctor Q.toPseudofunctor

abbrev component {P Q : GeneralStackGeometry.RelativeStack X} (f : Hom P Q) (T : Over X) :=
  (f.app (.mk (op T))).toFunctor

/-- Evaluate a native invertible modification on an actual parameter scheme. -/
def componentIso {P Q : GeneralStackGeometry.RelativeStack X} {f g : Hom P Q}
    (e : f ≅ g) (T : Over X) : component f T ≅ component g T where
  hom := (e.hom.as.app (.mk (op T))).toNatTrans
  inv := (e.inv.as.app (.mk (op T))).toNatTrans
  hom_inv_id := by
    ext E
    exact congrArg (fun k : f ⟶ f => (k.as.app (.mk (op T))).toNatTrans.app E) e.hom_inv_id
  inv_hom_id := by
    ext E
    exact congrArg (fun k : g ⟶ g => (k.as.app (.mk (op T))).toNatTrans.app E) e.inv_hom_id

variable (I : NativeDFImages.{u})
  {A : MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A)

abbrev FiniteModels := ∀ n : Exponent, Model I D (powerMap A n.val) (𝟙 X)

abbrev fibreBase (T : Over X) := (Over.map (𝟙 X)).obj T

/-- Literal evaluation from the compatible-root core to the n-th root groupoid. -/
def evaluation {T : Over X} (K : Tower I D T) (n : Exponent) :
    InfiniteRoots I D K ⥤ FiniteRoots I D T n :=
  Core.inclusion (CompatibleRoot I D K) ⋙ CompatibleRoot.evaluation n

/-- The actual global finite-root tower, with native stack 2-cell coherence. -/
structure GlobalTower (R : FiniteModels I D) where
  tower : ∀ T : Over X, Tower I D (fibreBase T)
  transition : ∀ (n m : Exponent) (_h : n.val ∣ m.val), Hom (R m).stack (R n).stack
  normalization : ∀ (n m : Exponent) (h : n.val ∣ m.val) (T : Over X),
    component (transition n m h) T ⋙ ((R n).fibre T).functor ≅
      ((R m).fibre T).functor ⋙ ((tower T).transition n m h).functor
  identity : ∀ n : Exponent,
    transition n n (dvd_refl _) ≅ Pseudofunctor.StrongTrans.id (R n).stack.toPseudofunctor
  composition : ∀ (n m k : Exponent) (h : n.val ∣ m.val) (h' : m.val ∣ k.val),
    Pseudofunctor.StrongTrans.vcomp (transition m k h') (transition n m h) ≅
      transition n k (dvd_trans h h')
  identity_normalization : ∀ (n : Exponent) (T : Over X) (E : (R n).stack.Fibre T),
    (normalization n n (dvd_refl _) T).hom.app E ≫
      ((tower T).identity n).hom.app (((R n).fibre T).functor.obj E) =
    ((R n).fibre T).functor.map ((componentIso (identity n) T).hom.app E)
  composition_normalization : ∀ (n m k : Exponent) (h : n.val ∣ m.val)
      (h' : m.val ∣ k.val) (T : Over X) (E : (R k).stack.Fibre T),
    (normalization n k (dvd_trans h h') T).hom.app E =
      ((R n).fibre T).functor.map ((componentIso (composition n m k h h') T).inv.app E) ≫
      (normalization n m h T).hom.app ((component (transition m k h') T).obj E) ≫
      ((tower T).transition n m h).functor.map ((normalization m k h' T).hom.app E) ≫
      ((tower T).composition n m k h h').hom.app (((R k).fibre T).functor.obj E)

/-- An actual infinite-root fppf stack with its compatible-root fibres and projections. -/
structure InfiniteModel {R : FiniteModels I D} (K : GlobalTower I D R) where
  stack : GeneralStackGeometry.RelativeStack X
  fibre : ∀ T : Over X, stack.Fibre T ≌ InfiniteRoots I D (K.tower T)
  reindex : ∀ {T V : Over X} (_f : V ⟶ T),
    InfiniteRoots I D (K.tower T) ⥤ InfiniteRoots I D (K.tower V)
  reindex_components : ∀ {T V : Over X} (f : V ⟶ T) (n : Exponent),
    reindex f ⋙ evaluation I D (K.tower V) n ≅
      evaluation I D (K.tower T) n ⋙ ((R n).reindexing f).functor
  mapComparison : ∀ {T V : Over X} (f : V ⟶ T),
    (stack.toPseudofunctor.map f.op.toLoc).toFunctor ⋙ (fibre V).functor ≅
      (fibre T).functor ⋙ reindex f
  projection : ∀ n : Exponent, Hom stack (R n).stack
  projection_normalization : ∀ (n : Exponent) (T : Over X),
    component (projection n) T ⋙ ((R n).fibre T).functor ≅
      (fibre T).functor ⋙ evaluation I D (K.tower T) n
  projectionCompatibility : ∀ (n m : Exponent) (h : n.val ∣ m.val),
    projection n ≅ Pseudofunctor.StrongTrans.vcomp (projection m) (K.transition n m h)
  projection_compatibility_normalization : ∀ (n m : Exponent) (h : n.val ∣ m.val)
      (T : Over X) (E : stack.Fibre T),
    ((R n).fibre T).functor.map
      ((componentIso (projectionCompatibility n m h) T).hom.app E) ≫
      (K.normalization n m h T).hom.app ((component (projection m) T).obj E) ≫
      ((K.tower T).transition n m h).functor.map ((projection_normalization m T).hom.app E) =
    (projection_normalization n T).hom.app E ≫
      (((fibre T).functor.obj E).of.comparison n m h).hom

end MathlibExt.AlgebraicGeometry.InfiniteDenominatorRoots
