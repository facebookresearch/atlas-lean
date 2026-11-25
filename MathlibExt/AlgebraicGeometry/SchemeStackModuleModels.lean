/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CartesianStackModules
public import MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections

/-!
# Source-integration models of scheme stacks and their actual modules

A represented stack model is an equivalence of the entire native
CoGrothendieck category with schemes over Y, compatible with the actual
projection to the base. Its scheme-valued test map is computed from that
comparison. The QCoh dictionary is pinned on every affine point and every
actual base arrow, ruling out independently chosen locally isomorphic values.

The represented-stack and affine-cartesian/QCoh producers are complete
public mathematics: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Stacks/AlgebraicSpaceStack.lean and
Stacks/Sheaves/QuasiCoherentCartesianEquivalence.lean (Apache2.0).
This module supplies their native conditional carrier integration; it
contains no new Wanted request for the already proved scheme dictionary.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace AlgebraicGeometry.SchemeStackModuleModels
open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules
open CartesianStackModules
open MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections

variable {S : Scheme.{0}}

/-- The actual full category of quasicoherent scheme modules. General
sheaf modules do not satisfy the affine scalar-extension dictionary. -/
abbrev SchemeQCoh (Y : Scheme.{0}) :=
  (show ObjectProperty Y.Modules from fun F =>
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) F).FullSubcategory

/-- The literal inclusion into all sheaf modules on the scheme. -/
def schemeQCohForget (Y : Scheme.{0}) : SchemeQCoh Y ⥤ Y.Modules :=
  (show ObjectProperty Y.Modules from fun F =>
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) F).ι

/-- Full represented-category normalization, including nonreduced schemes
and all arrows, rather than a set of field-point isomorphism classes. -/
structure Model (Y : Over S) where
  stack : Stack S
  comparison : Total stack ≌ Over Y.left
  overBase : comparison.functor ⋙ Over.map Y.hom ≅
    Pseudofunctor.CoGrothendieck.forget stack.toPseudofunctor

/-- The literal scheme map of an affine stack point into Y. -/
def Model.testMap {Y : Over S} (R : Model Y) (a : AffinePoint R.stack) :
    (pointScheme R.stack).obj a ⟶ Y.left :=
  (R.overBase.inv.app a.obj).left ≫ (R.comparison.functor.obj a.obj).hom

lemma Model.testMap_comp {Y : Over S} (R : Model Y)
    {a b : AffinePoint R.stack} (h : a ⟶ b) :
    h.hom.base.left ≫ R.testMap b = R.testMap a := by
  have hn := congrArg Over.Hom.left (R.overBase.inv.naturality h.hom)
  change h.hom.base.left ≫ (R.overBase.inv.app b.obj).left =
    (R.overBase.inv.app a.obj).left ≫ (R.comparison.functor.map h.hom).left at hn
  dsimp only [Model.testMap]
  rw [← Category.assoc, hn, Category.assoc, Over.w]

/-- The actual scalar-semilinear map of pulled global sections along a test arrow. -/
def testRestriction {Y : Over S} (R : Model Y) (F : Y.left.Modules)
    {a b : AffinePoint R.stack} (h : a ⟶ b)
    (s : Γ((Scheme.Modules.pullback (R.testMap b)).obj F,⊤)) :
    Γ((Scheme.Modules.pullback (R.testMap a)).obj F,⊤) :=
  let t := localPullback h.hom.base.left ((Scheme.Modules.pullback (R.testMap b)).obj F) ⊤ s
  let v := ((Scheme.Modules.pullbackComp h.hom.base.left (R.testMap b)).hom.app F).val.app
    (op (⊤ : ((pointScheme R.stack).obj a).Opens))
  let e := eqToHom (congrArg (fun f => (Scheme.Modules.pullback f).obj F) (R.testMap_comp h))
  (e.val.app (op (⊤ : ((pointScheme R.stack).obj a).Opens))).hom (v.hom t)

/-- A dictionary between quasicoherent modules on the stack $\mathcal X$ of a model `R` of $Y$ (a
stack over $S$ whose fibred category is identified with schemes over $Y$, compatibly with the
projections to $S$) and quasicoherent modules on $Y$: an equivalence
`QCoh R.stack ≌ SchemeQCoh Y.left`, with, for every module $M$ and every affine point $a$ of
$\mathcal X$, a linear isomorphism between $M(a)$ and the global sections of the pullback of the
corresponding module on $Y$ along the test map of $a$, natural in $M$ and compatible with
restriction along morphisms of affine points. -/
structure ModuleDictionary {Y : Over S} (R : Model Y) where
  equivalence : QCoh R.stack ≌ SchemeQCoh Y.left
  sections : ∀ (M : QCoh R.stack) (a : AffinePoint R.stack),
    M.obj.obj (op a) ≃ₗ[Γ((pointScheme R.stack).obj a,⊤)]
      Γ((Scheme.Modules.pullback (R.testMap a)).obj
        ((equivalence.functor ⋙ schemeQCohForget Y.left).obj M),⊤)
  module_naturality : ∀ {M N : QCoh R.stack} (f : M ⟶ N)
    (a : AffinePoint R.stack) (s : M.obj.obj (op a)),
    sections N a (f.hom.app (op a) s) =
      (((Scheme.Modules.pullback (R.testMap a)).map
        ((equivalence.functor ⋙ schemeQCohForget Y.left).map f)).val.app
        (op (⊤ : ((pointScheme R.stack).obj a).Opens))).hom (sections M a s)
  base_naturality : ∀ (M : QCoh R.stack) {a b : AffinePoint R.stack} (h : a ⟶ b)
    (s : M.obj.obj (op b)),
    sections M a (M.obj.map h.op s) =
      testRestriction R ((equivalence.functor ⋙ schemeQCohForget Y.left).obj M) h (sections M b s)

/-- The dictionary's underlying native scheme-module functor. -/
def ModuleDictionary.toModules {Y : Over S} {R : Model Y} (D : ModuleDictionary R) :
    QCoh R.stack ⥤ Y.left.Modules :=
  D.equivalence.functor ⋙ schemeQCohForget Y.left

end AlgebraicGeometry.SchemeStackModuleModels
