/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRamificationTorsorReindexing

/-!
# Canonical ramification cocycles from the universal Chevalley source

Varpi has the source order R_(u*v) to v*R_u tensor R_v. Its cocycle
diagram uses the actual combined pullbacks and native tensor coherence.
The universal normalization uses the actual polynomial Chevalley scheme
and canonical ramification sections. Only that universal open is required
to be dense. All Cartesian cameral pullbacks preserve full symbol, dual,
frame and quotient maps, so fibres with empty unramified locus retain the
same normalization.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Lemma 5.4 and Proposition 5.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRamificationCocycles

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open ContractedTorsorModels ExpansionParameterModels CoherentCurveLinearSeries
open LineBundleTaskContracts
open scoped BigOperators

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)

attribute [local instance] CameralRamificationTensorModels.torusGroup

structure ChevalleyCameral where
  cover : Cover F F.chevalley.chevalley.base
  source : cover.cover = F.chevalley.chevalley.cover

def polynomialIso (U : ChevalleyCameral F) : (total F U.cover).left ≅
    (CameralChevalleyModels.space (k := ℂ) (r := F.rank)).left :=
  eqToIso (congrArg (fun c => c.scheme.left) U.source) ≪≫ F.chevalley.total

def discriminant : CameralChevalleyModels.Coordinate (k := ℂ) (r := F.rank) :=
  ∏ i : Fin F.roots.count,
    CameralChevalleyModels.rootEquation (tori F.rank) (tori 1) F.Weyl F.roots i

def regularCoordinate (U : ChevalleyCameral F) : Γ((total F U.cover).left, ⊤) :=
  (polynomialIso F U).hom.appTop.hom
    ((Scheme.ΓSpecIso (.of (CameralChevalleyModels.Coordinate (k := ℂ) (r := F.rank)))).inv.hom
      (discriminant F))

def regularScheme (U : ChevalleyCameral F) : Over (Spec (.of ℂ)) :=
  Over.mk (((total F U.cover).left.basicOpen (regularCoordinate F U)).ι ≫ (total F U.cover).hom)

def regularInclusion (U : ChevalleyCameral F) : regularScheme F U ⟶ total F U.cover :=
  Over.homMk ((total F U.cover).left.basicOpen (regularCoordinate F U)).ι rfl

abbrev TorsorPoint {Y V : Over (Spec (.of ℂ))} (P : Bundle (Torus F) Y) (y : V ⟶ Y) :=
  {p : V ⟶ P.torsor.total // p ≫ P.torsor.projection = y}

structure UniversalRootFrames (U : ChevalleyCameral F) where
  dense : Dense (((total F U.cover).left.basicOpen (regularCoordinate F U)) :
    Set (total F U.cover).left)
  action : ∀ _w : F.Weyl, regularScheme F U ≅ regularScheme F U
  action_normalized : ∀ w,
    (action w).hom ≫ regularInclusion F U = regularInclusion F U ≫ (coverIso F U.cover w).hom
  point : letI := (tori 1).group
    ∀ i, regularScheme F U ⟶ (frames F U.cover i).bundle.torsor.total
  over : letI := (tori 1).group
    ∀ i, point i ≫ (frames F U.cover i).bundle.torsor.projection = regularInclusion F U
  section_normalized : letI := (tori 1).group
    ∀ i, (frameBasis (tori 1) (total F U.cover) (line F U.cover i) (frames F U.cover i)
      (regularScheme F U) (regularInclusion F U) (point i) (over i)).hom =
        LineBundleTaskContracts.pullbackSection (regularInclusion F U).left
          (sectionData F U.cover i).sectionMap

set_option maxHeartbeats 1000000 in
-- Transporting the root torsor point through the regular inclusion needs extra budget.
def universalRootPoint (U : ChevalleyCameral F) (A : UniversalRootFrames F U)
    (i : Fin F.roots.count) :
    TorsorPoint F (rootTorsor F K D U.cover i) (regularInclusion F U) := by
  letI := (tori 1).group
  letI := K.corootHom i
  refine ⟨CartesianMonoidalCategory.lift (A.point i)
      (toUnit (regularScheme F U) ≫ η[Torus F]) ≫ (rootPushout F K D U.cover i).quotient, ?_⟩
  rw [Category.assoc, (rootPushout F K D U.cover i).projection]
  rw [← Category.assoc, CartesianMonoidalCategory.lift_fst, A.over i]

def universalProductPoint (U : ChevalleyCameral F) (A : UniversalRootFrames F U) :
    ∀ is : List (Fin F.roots.count),
      TorsorPoint F (ramificationProduct F K D U.cover is) (regularInclusion F U)
  | [] => ⟨NormalizedTorsorOperations.unitPoint (Torus F) (D.torus.unit (total F U.cover))
      (regularInclusion F U), NormalizedTorsorOperations.unitPoint_over _ _ _⟩
  | i :: is => by
    let p := universalRootPoint F K D U A i
    let q := universalProductPoint U A is
    refine ⟨tensorPoint (D.torus.tensor.model (total F U.cover)
      (rootTorsor F K D U.cover i) (ramificationProduct F K D U.cover is)) p.val q.val
        (p.property.trans q.property.symm), ?_⟩
    change tensorPoint (D.torus.tensor.model (total F U.cover)
      (rootTorsor F K D U.cover i) (ramificationProduct F K D U.cover is)) p.val q.val
        (p.property.trans q.property.symm) ≫
      ((D.torus.tensor.tensor (total F U.cover)).obj
        (rootTorsor F K D U.cover i, ramificationProduct F K D U.cover is)).torsor.projection = _
    exact (tensorPoint_over _ _ _ _).trans p.property

def universalRamificationPoint (U : ChevalleyCameral F) (A : UniversalRootFrames F U) (w : F.Weyl) :
    TorsorPoint F (ramificationTorsor F K D U.cover w) (regularInclusion F U) :=
  universalProductPoint F K D U A (inversionRoots F K w)

def universalTwistedPoint (U : ChevalleyCameral F) (A : UniversalRootFrames F U)
    (W : WeylCalculus F K D U.cover) (v w : F.Weyl) :
    TorsorPoint F (combined F K D U.cover w (ramificationTorsor F K D U.cover v))
      (regularInclusion F U) := by
  let p := universalRamificationPoint F K D U A v
  let M := W.model w (ramificationTorsor F K D U.cover v)
  have h : (A.action w).hom ≫ p.val ≫ (ramificationTorsor F K D U.cover v).torsor.projection =
      regularInclusion F U ≫ (coverIso F U.cover w).hom := by
    rw [p.property, A.action_normalized]
  refine ⟨pullback.lift ((A.action w).hom ≫ p.val) (regularInclusion F U) h ≫ M.comparison.inv, ?_⟩
  rw [← M.projection]
  simp

structure WeylBaseComparison {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C')
    (W : WeylCalculus F K D C) (W' : WeylCalculus F K D C') (w : F.Weyl)
    (P : Bundle (Torus F) (total F C')) where
  iso : (D.torus.baseChange.change m.total).obj (combined F K D C' w P) ≅
    combined F K D C w ((D.torus.baseChange.change m.total).obj P)
  original : iso.hom.iso.hom ≫
      combinedOriginal F K D C (W.model w ((D.torus.baseChange.change m.total).obj P)) ≫
        ContractedTorsorModels.original (D.torus.baseChange.pullback m.total P) =
    ContractedTorsorModels.original (D.torus.baseChange.pullback m.total (combined F K D C' w P)) ≫
      combinedOriginal F K D C' (W'.model w P)

structure LocalUniversalArrow (U : ChevalleyCameral F) {X : Over (Spec (.of ℂ))}
    (C : Cover F X) (x : X.left) where
  pulled : CameralBaseChange F C
    (TorusLineFrameModels.testMap X (C.charts x).neighborhood)
  arrow : CameralArrow F pulled.cover U.cover
  base : arrow.base = (C.charts x).value
  total : arrow.total.left ≫ (eqToIso (congrArg (fun c => c.scheme.left) U.source)).hom =
    pulled.comparison.hom.left ≫ (C.charts x).comparison.hom.left ≫
      pullback.fst F.chevalley.chevalley.cover.scheme.hom (C.charts x).value.left
  equivariant : ∀ w,
    (coverIso F pulled.cover w).hom ≫ arrow.total = arrow.total ≫ (coverIso F U.cover w).hom

structure CanonicalRamificationFamily where
  universal : ChevalleyCameral F
  rootFrames : UniversalRootFrames F universal
  symbols : RamificationReindexing F
  torsors : TorsorReindexing F K D symbols
  localArrows : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (x : X.left),
    LocalUniversalArrow F universal C x
  weyl : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X), WeylCalculus F K D C
  baseWeyl : ∀ {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
      (m : CameralArrow F C C')
      (_h : ∀ w, (coverIso F C w).hom ≫ m.total = m.total ≫ (coverIso F C' w).hom)
      (w : F.Weyl) (P : Bundle (Torus F) (total F C')),
    WeylBaseComparison F K D m (weyl C) (weyl C') w P
  varpi : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (u v : F.Weyl),
    ramificationTorsor F K D C (u * v) ≅
      NormalizedTorsorOperations.tensorObj (G := Torus F) D.torus.tensor
        (combined F K D C v (ramificationTorsor F K D C u)) (ramificationTorsor F K D C v)
  universal_normalized : ∀ u v,
    (universalRamificationPoint F K D universal rootFrames (u * v)).val ≫
      (varpi universal.cover u v).hom.iso.hom =
    tensorPoint (D.torus.tensor.model (total F universal.cover)
      (combined F K D universal.cover v (ramificationTorsor F K D universal.cover u))
      (ramificationTorsor F K D universal.cover v))
      (universalTwistedPoint F K D universal rootFrames (weyl universal.cover) u v).val
      (universalRamificationPoint F K D universal rootFrames v).val
      ((universalTwistedPoint F K D universal rootFrames (weyl universal.cover) u v).property.trans
        (universalRamificationPoint F K D universal rootFrames v).property.symm)
  pullback : ∀ {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
      (m : CameralArrow F C C')
      (hW : ∀ w, (coverIso F C w).hom ≫ m.total = m.total ≫ (coverIso F C' w).hom)
      (h : ∀ i, ReflectionCompatible F m i i) (u v : F.Weyl),
    (D.torus.baseChange.change m.total).map (varpi C' u v).hom ≫
      (D.torus.baseTensor m.total
        (combined F K D C' v (ramificationTorsor F K D C' u))
        (ramificationTorsor F K D C' v)).hom ≫
      NormalizedTorsorOperations.tensorMap (G := Torus F) D.torus.tensor
        ((baseWeyl m hW v (ramificationTorsor F K D C' u)).iso.hom ≫
          (combinedFunctor F K D C v).map
            (ramificationPullbackIso F K D symbols torsors m h u).hom)
        (ramificationPullbackIso F K D symbols torsors m h v).hom =
    (ramificationPullbackIso F K D symbols torsors m h (u * v)).hom ≫ (varpi C u v).hom
  cocycle : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (u v w : F.Weyl),
    (varpi C (u * v) w).hom ≫
      NormalizedTorsorOperations.tensorMap (G := Torus F) D.torus.tensor
        ((combinedFunctor F K D C w).map (varpi C u v).hom) (𝟙 _) ≫
      NormalizedTorsorOperations.tensorMap (G := Torus F) D.torus.tensor
        ((weyl C).tensor w (combined F K D C v (ramificationTorsor F K D C u))
          (ramificationTorsor F K D C v)).hom (𝟙 _) ≫
      NormalizedTorsorOperations.tensorMap (G := Torus F) D.torus.tensor
        (NormalizedTorsorOperations.tensorMap (G := Torus F) D.torus.tensor
          (((weyl C).composition v w).hom.app (ramificationTorsor F K D C u)) (𝟙 _)) (𝟙 _) ≫
      (D.torus.associator (total F C)
        (combined F K D C (v * w) (ramificationTorsor F K D C u))
        (combined F K D C w (ramificationTorsor F K D C v)) (ramificationTorsor F K D C w)).hom =
    (eqToIso (congrArg (ramificationTorsor F K D C) (mul_assoc u v w))).hom ≫
      (varpi C u (v * w)).hom ≫
      NormalizedTorsorOperations.tensorMap (G := Torus F) D.torus.tensor (𝟙 _) (varpi C v w).hom

end MathlibExt.AlgebraicGeometry.CameralRamificationCocycles
