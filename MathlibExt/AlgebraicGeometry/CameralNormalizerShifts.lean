/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralSimpleRootTrivializations

/-!
# Full scheme-valued normalizer shifts

Normalizer maps have locally constant Weyl labels. Their actual clopen
label schemes cover every test scheme. Shift data on all constant-label
families assemble on this cover into a genuine global torsor isomorphism.
The parameter covers are Cartesian pulls to X times U; their arrows are
fixed by both original-cover and parameter projections. Composition uses
v*gamma(u), gamma(v) and varpi in the order R_(u*v) to v*R_u tensor R_v.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.8 and 6.1--6.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralNormalizerShifts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open ContractedTorsorModels ExpansionParameterModels TorusLineFrameModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

def Label {U : Over (Spec (.of ℂ))} (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) : Prop :=
  ∀ x : U.left, F.weyl.points U (n ≫ F.normalizer.quotient) x = w

def labelOpen (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) :
    U.left.Opens :=
  ⟨{x | F.weyl.points U (n ≫ F.normalizer.quotient) x = w},
    (F.weyl.points U (n ≫ F.normalizer.quotient)).isLocallyConstant.isOpen_fiber w⟩

theorem labelOpen_clopen (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) :
    IsClopen ((labelOpen F U n w) : Set U.left) :=
  (F.weyl.points U (n ≫ F.normalizer.quotient)).isLocallyConstant.isClopen_fiber w

theorem labelOpen_cover (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (x : U.left) :
    ∃ w, x ∈ labelOpen F U n w :=
  ⟨F.weyl.points U (n ≫ F.normalizer.quotient) x, rfl⟩

theorem labelOpen_disjoint (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
    {u v : F.Weyl} (h : u ≠ v) :
    Disjoint ((labelOpen F U n u) : Set U.left) ((labelOpen F U n v) : Set U.left) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact h (hx.symm.trans hy)

def labelScheme (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) :
    Over (Spec (.of ℂ)) := Over.mk ((labelOpen F U n w).ι ≫ U.hom)

def labelInclusion (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) :
    labelScheme F U n w ⟶ U := Over.homMk (labelOpen F U n w).ι rfl

theorem labelConstant (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) :
    Label F (labelInclusion F U n w ≫ n) w := by
  intro x
  rw [Category.assoc, F.weyl.naturality]
  exact x.property

def normalizerProduct {U : Over (Spec (.of ℂ))} (n m : U ⟶ F.normalizer.scheme) :
    U ⟶ F.normalizer.scheme := by
  letI := F.normalizer.group
  exact CartesianMonoidalCategory.lift n m ≫ μ[F.normalizer.scheme]

theorem productLabel {U : Over (Spec (.of ℂ))} (n m : U ⟶ F.normalizer.scheme)
    (u v : F.Weyl) (hn : Label F n u) (hm : Label F m v) :
    Label F (normalizerProduct F n m) (u * v) := by
  let := F.normalizer.group
  let := F.normalizer.quotient_hom
  intro x
  dsimp only [normalizerProduct]
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
    CartesianMonoidalCategory.lift_map, F.weyl.multiply, hn x, hm x]

variable [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D)

attribute [local instance] CameralRamificationTensorModels.torusGroup

@[implicit_reducible] def shiftFunctor {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl) :
    Bundle (Torus F) (total F C) ⥤ Bundle (Torus F) (total F C) :=
  combinedFunctor F K D C w ⋙
    _root_.CategoryTheory.Prod.sectL (Bundle (Torus F) (total F C))
      (ramificationTorsor F K D C w) ⋙ D.torus.tensor.tensor (total F C)

abbrev shifted {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl)
    (P : Bundle (Torus F) (total F C)) : Bundle (Torus F) (total F C) :=
  (shiftFunctor F K D C w).obj P

def shiftUnit {X : Over (Spec (.of ℂ))} (C : Cover F X)
    (P : Bundle (Torus F) (total F C)) : shifted F K D C 1 P ≅ P :=
  NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor
    ((R.weyl C).unit.app P) (eqToIso (ramificationTorsor_one F K D C)) ≪≫
      D.torus.rightUnit (total F C) P

def shiftComposition {X : Over (Spec (.of ℂ))} (C : Cover F X) (u v : F.Weyl)
    (P : Bundle (Torus F) (total F C)) :
    shifted F K D C (u * v) P ≅ shifted F K D C v (shifted F K D C u P) :=
  NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor (Iso.refl _)
    (R.varpi C u v) ≪≫
  (D.torus.associator (total F C) (combined F K D C (u * v) P)
    (combined F K D C v (ramificationTorsor F K D C u)) (ramificationTorsor F K D C v)).symm ≪≫
  NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor
    (NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor
      (((R.weyl C).composition u v).symm.app P) (Iso.refl _)) (Iso.refl _) ≪≫
  NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor
    ((R.weyl C).tensor v (combined F K D C u P) (ramificationTorsor F K D C u)).symm (Iso.refl _)

structure ParameterCovers {X : Over (Spec (.of ℂ))} (C : Cover F X) where
  pulled : ∀ U : Over (Spec (.of ℂ)), CameralBaseChange F C (fst X U)
  arrow : ∀ {U V : Over (Spec (.of ℂ))} (_f : V ⟶ U),
    CameralArrow F (pulled V).cover (pulled U).cover
  base : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U),
    (arrow f).base = tensorHom (𝟙 X) f
  original : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U),
    (arrow f).total ≫ (pulled U).arrow.total = (pulled V).arrow.total
  equivariant : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (w : F.Weyl),
    (coverIso F (pulled V).cover w).hom ≫ (arrow f).total =
      (arrow f).total ≫ (coverIso F (pulled U).cover w).hom
  reflections : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (i : Fin F.roots.count),
    ReflectionCompatible F (arrow f) i i
  unit : ∀ U : Over (Spec (.of ℂ)), (arrow (𝟙 U)).total = 𝟙 _
  composition : ∀ {U V Z : Over (Spec (.of ℂ))} (f : V ⟶ U) (g : Z ⟶ V),
    (arrow (g ≫ f)).total = (arrow g).total ≫ (arrow f).total

variable {X : Over (Spec (.of ℂ))} {C : Cover F X} (B : ParameterCovers F C)
  (L : Bundle (Torus F) (total F C))

abbrev parameterBundle (U : Over (Spec (.of ℂ))) :
    Bundle (Torus F) (total F (B.pulled U).cover) :=
  (D.torus.baseChange.change (B.pulled U).arrow.total).obj L

def parameterBundleIso {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) :
    (D.torus.baseChange.change (B.arrow f).total).obj (parameterBundle F K D B L U) ≅
      parameterBundle F K D B L V :=
  (D.torus.baseChange.composition (B.pulled U).arrow.total (B.arrow f).total).app L ≪≫
    eqToIso (congrArg (fun h => (D.torus.baseChange.change h).obj L) (B.original f))

def shiftBaseIso {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (w : F.Weyl)
    (P : Bundle (Torus F) (total F (B.pulled U).cover)) :
    (D.torus.baseChange.change (B.arrow f).total).obj (shifted F K D (B.pulled U).cover w P) ≅
      shifted F K D (B.pulled V).cover w ((D.torus.baseChange.change (B.arrow f).total).obj P) :=
  D.torus.baseTensor (B.arrow f).total
    (combined F K D (B.pulled U).cover w P) (ramificationTorsor F K D (B.pulled U).cover w) ≪≫
  NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor
    ((R.baseWeyl (B.arrow f) (B.equivariant f) w P).iso)
    (ramificationPullbackIso F K D R.symbols R.torsors (B.arrow f) (B.reflections f) w)

def parameterProjection (U : Over (Spec (.of ℂ))) : total F (B.pulled U).cover ⟶ U :=
  projection F (B.pulled U).cover ≫ snd X U

structure TorusTranslation (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F) where
  iso : parameterBundle F K D B L U ≅ parameterBundle F K D B L U
  normalized : iso.hom.iso.hom =
    CartesianMonoidalCategory.lift
      ((parameterBundle F K D B L U).torsor.projection ≫ parameterProjection F B U ≫ t)
      (𝟙 (parameterBundle F K D B L U).torsor.total) ≫
        γ[Torus F,(parameterBundle F K D B L U).torsor.total]

structure ConstantNormalizerShift where
  gamma : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (_hw : Label F n w),
    shifted F K D (B.pulled U).cover w (parameterBundle F K D B L U) ≅ parameterBundle F K D B L U
  torus : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F), TorusTranslation F K D B L U t
  torus_label : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F),
    Label F (t ≫ F.normalizer.torus) 1
  torus_restriction : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F),
    (gamma U (t ≫ F.normalizer.torus) 1 (torus_label U t)).hom =
      (shiftUnit F K D R (B.pulled U).cover (parameterBundle F K D B L U)).hom ≫ (torus U t).iso.hom
  composition : ∀ (U : Over (Spec (.of ℂ))) (n m : U ⟶ F.normalizer.scheme)
      (u v : F.Weyl) (hn : Label F n u) (hm : Label F m v),
    (gamma U (normalizerProduct F n m) (u * v) (productLabel F n m u v hn hm)).hom =
      (shiftComposition F K D R (B.pulled U).cover u v (parameterBundle F K D B L U)).hom ≫
      (shiftFunctor F K D (B.pulled U).cover v).map (gamma U n u hn).hom ≫ (gamma U m v hm).hom
  naturality : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w) (hf : Label F (f ≫ n) w),
    (D.torus.baseChange.change (B.arrow f).total).map (gamma U n w hn).hom ≫
      (parameterBundleIso F K D B L f).hom =
    (shiftBaseIso F K D R B f w (parameterBundle F K D B L U)).hom ≫
      (shiftFunctor F K D (B.pulled V).cover w).map (parameterBundleIso F K D B L f).hom ≫
        (gamma V (f ≫ n) w hf).hom

variable (S : ConstantNormalizerShift F K D R B L)

def gammaPiece (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) :=
  S.gamma (labelScheme F U n w) (labelInclusion F U n w ≫ n) w (labelConstant F U n w)

structure AssembledShift (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) where
  bundle : Bundle (Torus F) (total F (B.pulled U).cover)
  gamma : bundle ≅ parameterBundle F K D B L U
  piece : ∀ w : F.Weyl,
    (D.torus.baseChange.change (B.arrow (labelInclusion F U n w)).total).obj bundle ≅
      shifted F K D (B.pulled (labelScheme F U n w)).cover w
        (parameterBundle F K D B L (labelScheme F U n w))
  normalized : ∀ w : F.Weyl,
    (D.torus.baseChange.change (B.arrow (labelInclusion F U n w)).total).map gamma.hom ≫
      (parameterBundleIso F K D B L (labelInclusion F U n w)).hom =
    (piece w).hom ≫ (gammaPiece F K D R B L S U n w).hom

structure FullNormalizerShift where
  assemble : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme),
    AssembledShift F K D R B L S U n
  base_change : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (n : U ⟶ F.normalizer.scheme),
    (D.torus.baseChange.change (B.arrow f).total).obj (assemble U n).bundle ≅
      (assemble V (f ≫ n)).bundle
  naturality : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (n : U ⟶ F.normalizer.scheme),
    (D.torus.baseChange.change (B.arrow f).total).map (assemble U n).gamma.hom ≫
      (parameterBundleIso F K D B L f).hom =
      (base_change f n).hom ≫ (assemble V (f ≫ n)).gamma.hom

end MathlibExt.AlgebraicGeometry.CameralNormalizerShifts
