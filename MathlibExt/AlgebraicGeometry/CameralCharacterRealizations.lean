/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRamificationCocycles

/-!
# Native character lines of cameral torus bundles

The associated line is represented by its actual scheme of frames. The
frame scheme is the character pushout of the original torus torsor, with
the comparison fixed on every quotient point. Module arrows and all
pullback comparisons are fixed by these frames on every coefficient
scheme, including nonreduced schemes.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5--6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralCharacterRealizations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles ContractedTorsorModels ExpansionParameterModels
open TorusLineFrameModels CoherentCurveLinearSeries

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)

attribute [local instance] CameralRamificationTensorModels.torusGroup

def characterBundle (Y : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
    (P : Bundle (Torus F) Y) : letI := (tori 1).group; Bundle Multiplicative Y := by
  letI := (tori 1).group
  letI := K.characterHom i
  exact ((D.character i).map Y).obj P

structure CharacterRealization (Y : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
    (P : Bundle (Torus F) Y) (M : Y.left.Modules) where
  frames : LineFrames (tori 1) Y M
  comparison : letI := (tori 1).group
    characterBundle F K D Y i P ≅ frames.bundle
  pushout : letI := (tori 1).group; letI := K.characterHom i
    Pushout Multiplicative (F.roots.character i) P frames.bundle
  quotient : letI := (tori 1).group; letI := K.characterHom i
    ((D.character i).diagram Y P).quotient ≫ comparison.hom.iso.hom = pushout.quotient

def characterFrame {Y : Over (Spec (.of ℂ))} {i : Fin F.roots.count}
    {P : Bundle (Torus F) Y} {M : Y.left.Modules}
    (R : CharacterRealization F K D Y i P M) {U : Over (Spec (.of ℂ))}
    (p : U ⟶ P.torsor.total) : letI := (tori 1).group; U ⟶ R.frames.bundle.torsor.total := by
  letI := (tori 1).group
  letI := K.characterHom i
  exact CartesianMonoidalCategory.lift p (toUnit U ≫ η[torusScheme ℂ 1]) ≫ R.pushout.quotient

theorem characterFrame_over {Y : Over (Spec (.of ℂ))} {i : Fin F.roots.count}
    {P : Bundle (Torus F) Y} {M : Y.left.Modules}
    (R : CharacterRealization F K D Y i P M) {U : Over (Spec (.of ℂ))}
    (p : U ⟶ P.torsor.total) : letI := (tori 1).group
    characterFrame F K D R p ≫ R.frames.bundle.torsor.projection = p ≫ P.torsor.projection := by
  let := (tori 1).group
  let := K.characterHom i
  rw [characterFrame, Category.assoc, R.pushout.projection, ← Category.assoc,
    CartesianMonoidalCategory.lift_fst]

structure CharacterCalculus where
  line : ∀ (Y : Over (Spec (.of ℂ))) (_i : Fin F.roots.count),
    Bundle (Torus F) Y ⥤ Y.left.Modules
  realization : ∀ (Y : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (P : Bundle (Torus F) Y),
    CharacterRealization F K D Y i P ((line Y i).obj P)
  arrows : letI := (tori 1).group
    ∀ (Y : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
      (P Q : Bundle (Torus F) Y) (a : P ⟶ Q) (U : Over (Spec (.of ℂ)))
      (y : U ⟶ Y) (p : U ⟶ P.torsor.total)
      (hp : characterFrame F K D (realization Y i P) p ≫
        (realization Y i P).frames.bundle.torsor.projection = y)
      (hq : characterFrame F K D (realization Y i Q) (p ≫ a.iso.hom) ≫
        (realization Y i Q).frames.bundle.torsor.projection = y),
    (frameBasis (tori 1) Y ((line Y i).obj P) (realization Y i P).frames U y
      (characterFrame F K D (realization Y i P) p) hp).hom ≫
        (Scheme.Modules.pullback y.left).map ((line Y i).map a) =
    (frameBasis (tori 1) Y ((line Y i).obj Q) (realization Y i Q).frames U y
      (characterFrame F K D (realization Y i Q) (p ≫ a.iso.hom)) hq).hom
  pullback : ∀ {Y Y' : Over (Spec (.of ℂ))} (f : Y' ⟶ Y) (i : Fin F.roots.count),
    line Y i ⋙ Scheme.Modules.pullback f.left ≅
      D.torus.baseChange.change f ⋙ line Y' i
  pullback_frames : letI := (tori 1).group
    ∀ {Y Y' : Over (Spec (.of ℂ))} (f : Y' ⟶ Y) (i : Fin F.roots.count)
      (P : Bundle (Torus F) Y) (U : Over (Spec (.of ℂ))) (y : U ⟶ Y')
      (p : U ⟶ ((D.torus.baseChange.change f).obj P).torsor.total)
      (hp : characterFrame F K D (realization Y' i ((D.torus.baseChange.change f).obj P)) p ≫
        (realization Y' i ((D.torus.baseChange.change f).obj P)).frames.bundle.torsor.projection =
          y)
      (hq : characterFrame F K D (realization Y i P)
        (p ≫ original (D.torus.baseChange.pullback f P)) ≫
        (realization Y i P).frames.bundle.torsor.projection = y ≫ f),
    (frameBasis (tori 1) Y' ((line Y' i).obj ((D.torus.baseChange.change f).obj P))
      (realization Y' i ((D.torus.baseChange.change f).obj P)).frames U y
      (characterFrame F K D (realization Y' i ((D.torus.baseChange.change f).obj P)) p) hp).hom =
    (frameBasis (tori 1) Y ((line Y i).obj P) (realization Y i P).frames U (y ≫ f)
      (characterFrame F K D (realization Y i P)
        (p ≫ original (D.torus.baseChange.pullback f P))) hq).hom ≫
      (Scheme.Modules.pullbackComp y.left f.left).inv.app ((line Y i).obj P) ≫
      (Scheme.Modules.pullback y.left).map ((pullback f i).hom.app P)
  pullback_unit : ∀ (Y : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (P : Bundle (Torus F) Y),
    (pullback (𝟙 Y) i).hom.app P ≫
      (line Y i).map ((D.torus.baseChange.unit Y).hom.app P) =
        (Scheme.Modules.pullbackId Y.left).hom.app ((line Y i).obj P)
  pullback_composition : ∀ {Y Y' Y'' : Over (Spec (.of ℂ))}
      (f : Y' ⟶ Y) (g : Y'' ⟶ Y') (i : Fin F.roots.count) (P : Bundle (Torus F) Y),
    (Scheme.Modules.pullbackComp g.left f.left).hom.app ((line Y i).obj P) ≫
      (pullback (g ≫ f) i).hom.app P =
    (Scheme.Modules.pullback g.left).map ((pullback f i).hom.app P) ≫
      (pullback g i).hom.app ((D.torus.baseChange.change f).obj P) ≫
      (line Y'' i).map ((D.torus.baseChange.composition f g).hom.app P)

end MathlibExt.AlgebraicGeometry.CameralCharacterRealizations
