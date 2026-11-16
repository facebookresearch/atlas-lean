/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralCharacterRealizations

/-!
# Proposition 5.5 on the actual reflection divisor

The divisor is the native scheme equalizer of the reflection and the
identity. The dense normalization locus is used only on the universal
polynomial Chevalley cover: the simple-root divisor with all other root
divisors removed. Frames there come from the actual canonical sections
of the computed ramification duals. Every Cartesian cameral pullback
uses the full symbol, coefficient, dual and frame comparisons.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Proposition 5.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralSimpleRootTrivializations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations
open ContractedTorsorModels ExpansionParameterModels TorusLineFrameModels
open CoherentCurveLinearSeries LineBundleTaskContracts
open FiniteCoverLocalComparison
open scoped BigOperators

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

def fixedScheme {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    Over (Spec (.of ℂ)) :=
  Over.mk (equalizer.ι (reflection F C i).hom (𝟙 (total F C).left) ≫ (total F C).hom)

def fixedInclusion {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    fixedScheme F C i ⟶ total F C :=
  Over.homMk (equalizer.ι (reflection F C i).hom (𝟙 (total F C).left)) rfl

def fixedMap {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i : Fin F.roots.count) (h : ReflectionCompatible F m i i) :
    fixedScheme F C i ⟶ fixedScheme F C' i := by
  let f := equalizer.ι (reflection F C i).hom (𝟙 (total F C).left) ≫ m.total.left
  have hf : f ≫ (reflection F C' i).hom = f ≫ 𝟙 (total F C').left := by
    dsimp only [f]
    rw [Category.assoc, ← h, ← Category.assoc, equalizer.condition]
    simp
  refine Over.homMk (equalizer.lift f hf) ?_
  change equalizer.lift f hf ≫
      (equalizer.ι (reflection F C' i).hom (𝟙 (total F C').left) ≫ (total F C').hom) = _
  rw [← Category.assoc, equalizer.lift_ι]
  dsimp only [f, fixedScheme, Over.mk_hom]
  rw [Category.assoc, m.total.w]

theorem fixedMap_inclusion {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i : Fin F.roots.count) (h : ReflectionCompatible F m i i) :
    fixedMap F m i h ≫ fixedInclusion F C' i = fixedInclusion F C i ≫ m.total := by
  apply Over.OverMorphism.ext
  dsimp only [fixedMap, fixedInclusion, Over.homMk_left, Over.comp_left]
  exact equalizer.lift_ι _ _

def otherDiscriminant (i : Fin F.roots.count) :
    CameralChevalleyModels.Coordinate (k := ℂ) (r := F.rank) := by
  classical
  exact ∏ j ∈ Finset.univ.filter (fun j => F.roots.reflection j ≠ F.roots.reflection i),
    CameralChevalleyModels.rootEquation (tori F.rank) (tori 1) F.Weyl F.roots j

def simpleRegularCoordinate (U : ChevalleyCameral F) (i : Fin F.roots.count) :
    Γ((fixedScheme F U.cover i).left, ⊤) :=
  (fixedInclusion F U.cover i).left.appTop.hom
    ((polynomialIso F U).hom.appTop.hom
      ((Scheme.ΓSpecIso (.of (CameralChevalleyModels.Coordinate (k := ℂ) (r := F.rank)))).inv.hom
        (otherDiscriminant F i)))

def simpleRegularScheme (U : ChevalleyCameral F) (i : Fin F.roots.count) :
    Over (Spec (.of ℂ)) :=
  Over.mk (((fixedScheme F U.cover i).left.basicOpen (simpleRegularCoordinate F U i)).ι ≫
    (fixedScheme F U.cover i).hom)

def simpleRegularInclusion (U : ChevalleyCameral F) (i : Fin F.roots.count) :
    simpleRegularScheme F U i ⟶ fixedScheme F U.cover i :=
  Over.homMk ((fixedScheme F U.cover i).left.basicOpen (simpleRegularCoordinate F U i)).ι rfl

variable [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)

attribute [local instance] CameralRamificationTensorModels.torusGroup

structure SimpleRegularFrames (U : ChevalleyCameral F) (i : Fin F.roots.count)
    (w : F.Weyl) (_hi : SimpleRoot G tori F i)
    (_hw : SimpleRoot G tori F (K.permutations.index w i)) where
  dense : Dense (((fixedScheme F U.cover i).left.basicOpen
    (simpleRegularCoordinate F U i)) : Set (fixedScheme F U.cover i).left)
  points : letI := (tori 1).group
    ∀ j : Fin F.roots.count, j ∈ inversionRoots F K w →
      (simpleRegularScheme F U i ⟶ (frames F U.cover j).bundle.torsor.total)
  over : letI := (tori 1).group
    ∀ (j : Fin F.roots.count) (hj : j ∈ inversionRoots F K w),
      points j hj ≫ (frames F U.cover j).bundle.torsor.projection =
        simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i
  sections : letI := (tori 1).group
    ∀ (j : Fin F.roots.count) (hj : j ∈ inversionRoots F K w),
      (frameBasis (tori 1) (total F U.cover) (line F U.cover j) (frames F U.cover j)
        (simpleRegularScheme F U i) (simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i)
        (points j hj) (over j hj)).hom =
      pullbackSection (simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i).left
        (sectionData F U.cover j).sectionMap

def simpleRootPoint (U : ChevalleyCameral F) (i : Fin F.roots.count) (w : F.Weyl)
    {hi : SimpleRoot G tori F i} {hw : SimpleRoot G tori F (K.permutations.index w i)}
    (A : SimpleRegularFrames F K U i w hi hw) (j : Fin F.roots.count)
    (hj : j ∈ inversionRoots F K w) :
    TorsorPoint F (rootTorsor F K D U.cover j)
      (simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i) := by
  letI := (tori 1).group
  letI := K.corootHom j
  refine ⟨CartesianMonoidalCategory.lift (A.points j hj)
    (toUnit (simpleRegularScheme F U i) ≫ η[Torus F]) ≫ (rootPushout F K D U.cover j).quotient, ?_⟩
  rw [Category.assoc, (rootPushout F K D U.cover j).projection, ← Category.assoc,
    CartesianMonoidalCategory.lift_fst, A.over j hj]

def simpleProductPoint (U : ChevalleyCameral F) (i : Fin F.roots.count) (w : F.Weyl)
    {hi : SimpleRoot G tori F i} {hw : SimpleRoot G tori F (K.permutations.index w i)}
    (A : SimpleRegularFrames F K U i w hi hw) :
    ∀ (is : List (Fin F.roots.count)), (∀ j ∈ is, j ∈ inversionRoots F K w) →
      TorsorPoint F (ramificationProduct F K D U.cover is)
        (simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i)
  | [], _ => ⟨NormalizedTorsorOperations.unitPoint (Torus F) (D.torus.unit (total F U.cover))
      (simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i),
      NormalizedTorsorOperations.unitPoint_over _ _ _⟩
  | j :: js, h => by
    let p := simpleRootPoint F K D U i w A j (h j (List.mem_cons_self))
    let q := simpleProductPoint U i w A js (fun k hk => h k (List.mem_cons_of_mem j hk))
    refine ⟨tensorPoint (D.torus.tensor.model (total F U.cover)
      (rootTorsor F K D U.cover j) (ramificationProduct F K D U.cover js))
      p.val q.val (p.property.trans q.property.symm), ?_⟩
    exact (tensorPoint_over _ _ _ _).trans p.property

def simpleRamificationPoint (U : ChevalleyCameral F) (i : Fin F.roots.count) (w : F.Weyl)
    {hi : SimpleRoot G tori F i} {hw : SimpleRoot G tori F (K.permutations.index w i)}
    (A : SimpleRegularFrames F K U i w hi hw) :
    TorsorPoint F (ramificationTorsor F K D U.cover w)
      (simpleRegularInclusion F U i ≫ fixedInclusion F U.cover i) :=
  simpleProductPoint F K D U i w A (inversionRoots F K w) (fun _ h => h)

variable (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)

def twistLine {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) (w : F.Weyl) :
    (fixedScheme F C i).left.Modules :=
  (Scheme.Modules.pullback (fixedInclusion F C i).left).obj
    ((A.line (total F C) i).obj (ramificationTorsor F K D C w))

def twistLinePullback {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i : Fin F.roots.count) (w : F.Weyl)
    (h : ∀ j, ReflectionCompatible F m j j) :
    (Scheme.Modules.pullback (fixedMap F m i (h i)).left).obj (twistLine F K D A C' i w) ≅
      twistLine F K D A C i w :=
  (Scheme.Modules.pullbackComp (fixedMap F m i (h i)).left (fixedInclusion F C' i).left).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg (fun f : fixedScheme F C i ⟶ total F C' => f.left)
        (fixedMap_inclusion F m i (h i)))).app _ ≪≫
    (Scheme.Modules.pullbackComp (fixedInclusion F C i).left m.total.left).symm.app _ ≪≫
    (Scheme.Modules.pullback (fixedInclusion F C i).left).mapIso
      ((A.pullback m.total i).app (ramificationTorsor F K D C' w) ≪≫
        (A.line (total F C) i).mapIso
          (ramificationPullbackIso F K D R.symbols R.torsors m h w))

structure CanonicalSimpleRootTrivializations where
  universalFrames : ∀ (i : Fin F.roots.count) (w : F.Weyl)
      (hi : SimpleRoot G tori F i) (hw : SimpleRoot G tori F (K.permutations.index w i)),
    SimpleRegularFrames F K R.universal i w hi hw
  trivialization : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X)
      (i : Fin F.roots.count) (w : F.Weyl)
      (_hi : SimpleRoot G tori F i) (_hw : SimpleRoot G tori F (K.permutations.index w i)),
    twistLine F K D A C i w ≅ structureModule (fixedScheme F C i).left
  universal_normalized : letI := (tori 1).group
    ∀ (i : Fin F.roots.count) (w : F.Weyl)
      (hi : SimpleRoot G tori F i) (hw : SimpleRoot G tori F (K.permutations.index w i))
      (hp : characterFrame F K D
        (A.realization (total F R.universal.cover) i
          (ramificationTorsor F K D R.universal.cover w))
        (simpleRamificationPoint F K D R.universal i w (universalFrames i w hi hw)).val ≫
        (A.realization (total F R.universal.cover) i
          (ramificationTorsor F K D R.universal.cover w)).frames.bundle.torsor.projection =
        simpleRegularInclusion F R.universal i ≫ fixedInclusion F R.universal.cover i),
    (frameBasis (tori 1) (total F R.universal.cover)
      ((A.line (total F R.universal.cover) i).obj (ramificationTorsor F K D R.universal.cover w))
      (A.realization (total F R.universal.cover) i
        (ramificationTorsor F K D R.universal.cover w)).frames
      (simpleRegularScheme F R.universal i)
      (simpleRegularInclusion F R.universal i ≫ fixedInclusion F R.universal.cover i)
      (characterFrame F K D
        (A.realization (total F R.universal.cover) i
          (ramificationTorsor F K D R.universal.cover w))
        (simpleRamificationPoint F K D R.universal i w (universalFrames i w hi hw)).val) hp).hom ≫
      (Scheme.Modules.pullbackComp (simpleRegularInclusion F R.universal i).left
        (fixedInclusion F R.universal.cover i).left).inv.app _ ≫
      (Scheme.Modules.pullback (simpleRegularInclusion F R.universal i).left).map
        (trivialization R.universal.cover i w hi hw).hom ≫
      (pullbackStructureIso (simpleRegularInclusion F R.universal i).left).hom = 𝟙 _
  base_change : ∀ {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
      (m : CameralArrow F C C') (h : ∀ j, ReflectionCompatible F m j j)
      (i : Fin F.roots.count) (w : F.Weyl)
      (hi : SimpleRoot G tori F i) (hw : SimpleRoot G tori F (K.permutations.index w i)),
    (Scheme.Modules.pullback (fixedMap F m i (h i)).left).map (trivialization C' i w hi hw).hom ≫
      (pullbackStructureIso (fixedMap F m i (h i)).left).hom =
    (twistLinePullback F K D R A m i w h).hom ≫ (trivialization C i w hi hw).hom

end MathlibExt.AlgebraicGeometry.CameralSimpleRootTrivializations
