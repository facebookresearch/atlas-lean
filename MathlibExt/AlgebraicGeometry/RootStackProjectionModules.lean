/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DenominatorRootStacks
public import MathlibExt.AlgebraicGeometry.SchemeStackModuleModels
public import MathlibExt.AlgebraicGeometry.CartesianStackTensorProducts
public import Mathlib.CategoryTheory.Whiskering

/-!
# The structural root projection and its native weighted direct image

The projection is a strong transformation to the represented scheme stack.
Its entire Grothendieck functor is compared with the actual base-forgetful
functor, and its test map is the given parameter-scheme structural map.
The weighted functor is literally `pi_*(F tensor L_v)` with native tensor
and module maps; it does not assign an independent parabolic value or arrow.

The represented-stack, QCoh dictionary, tensor and right-adjoint producers
are completed-source integration from AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache License 2.0):
`StacksFrontier/AlgebraicGeometry/Stacks/AlgebraicSpaceStack.lean`,
`Stacks/Sheaves/QuasiCoherentCartesianEquivalence.lean`, and
`Stacks/Quasicoherent/{FppfModulesDirectImage,TensorQuasicoherent}.lean`.
Those files have no individual author or copyright notice. Adaptation:
use the native relative stack, full cartesian module category and native
tensor; keep the full represented-category/base normalization and the
adjunction to the fixed native pullback. No duplicate Wanted provider is
introduced for those completed generic source results.

The root-specific parabolic construction is Borne--Vistoli,
https://arxiv.org/abs/1001.0466v2, Theorem 6.1, pp33--35.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootStackProjectionModules

open _root_.CategoryTheory _root_.Opposite _root_.AlgebraicGeometry
open _root_.CategoryTheory.Functor
open _root_.AlgebraicGeometry.GeneralStackGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackFibreModels
open _root_.AlgebraicGeometry.StackAffineModules
open _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.SchemeStackModuleModels
open _root_.AlgebraicGeometry.CartesianStackTensorProducts
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage

variable {X : Scheme.{0}}
  [∀ (T Z : Scheme.{0}) (f : T ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (U : X.Etale) (R : DenominatorRootStacks.Model I D j U.hom)

/-- The actual structural map to the represented base scheme, including
the entire category of parameter families and its affine test maps. -/
structure Projection (S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))) where
  morphism : StackHom R.stack S.stack
  total_normalization : totalMap morphism ⋙ S.comparison.functor ≅
    Pseudofunctor.CoGrothendieck.forget R.stack.toPseudofunctor
  test_normalization : ∀ a : AffinePoint R.stack,
    S.testMap ((affineMap morphism).obj a) = a.obj.base.hom

/-- The actual right adjoint followed by the completed native scheme-QCoh dictionary. -/
def directImageToModules {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
    (P : Projection I D j U R S) (Q : DirectImage P.morphism)
    (K : ModuleDictionary S) : QCoh R.stack ⥤ U.left.Modules :=
  Q.functor ⋙ K.toModules

/-- The native weighted direct-image bifunctor. When `L` is the universal
root-weight functor, this is precisely the Borne--Vistoli prescription. -/
def weightedDirectImage {W : Type 1} [Category.{0} W]
    {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
    (P : Projection I D j U R S) (Q : DirectImage P.morphism)
    (K : ModuleDictionary S) (T : TensorLanding R.stack) (L : W ⥤ QCoh R.stack) :
    QCoh R.stack ⥤ W ⥤ U.left.Modules :=
  tensor R.stack T ⋙ (whiskeringLeft W (QCoh R.stack) (QCoh R.stack)).obj L ⋙
    (whiskeringRight W (QCoh R.stack) U.left.Modules).obj
      (directImageToModules I D j U R P Q K)

/-- Values are the actual native tensor followed by the fixed direct image. -/
theorem weightedDirectImage_obj {W : Type 1} [Category.{0} W]
    {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
    (P : Projection I D j U R S) (Q : DirectImage P.morphism)
    (K : ModuleDictionary S) (T : TensorLanding R.stack) (L : W ⥤ QCoh R.stack)
    (F : QCoh R.stack) (w : W) :
    ((weightedDirectImage I D j U R P Q K T L).obj F).obj w =
      K.toModules.obj (Q.functor.obj (((tensor R.stack T).obj F).obj (L.obj w))) := rfl

/-- Weight arrows use the actual section-induced root-line map under native tensor. -/
theorem weightedDirectImage_weightMap {W : Type 1} [Category.{0} W]
    {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
    (P : Projection I D j U R S) (Q : DirectImage P.morphism)
    (K : ModuleDictionary S) (T : TensorLanding R.stack) (L : W ⥤ QCoh R.stack)
    (F : QCoh R.stack) {v w : W} (a : v ⟶ w) :
    ((weightedDirectImage I D j U R P Q K T L).obj F).map a =
      K.toModules.map (Q.functor.map (((tensor R.stack T).obj F).map (L.map a))) := rfl

/-- Coefficient maps use the actual module map tensor the identity on the root line. -/
theorem weightedDirectImage_moduleMap {W : Type 1} [Category.{0} W]
    {S : SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))}
    (P : Projection I D j U R S) (Q : DirectImage P.morphism)
    (K : ModuleDictionary S) (T : TensorLanding R.stack) (L : W ⥤ QCoh R.stack)
    {F G : QCoh R.stack} (a : F ⟶ G) (w : W) :
    ((weightedDirectImage I D j U R P Q K T L).map a).app w =
      K.toModules.map (Q.functor.map (((tensor R.stack T).map a).app (L.obj w))) := rfl

end MathlibExt.AlgebraicGeometry.RootStackProjectionModules
