/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSimplicialModel
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellSphericalGenerators
public import MathlibExt.AlgebraicTopology.SimplicialSet.PullbackPushout
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
public import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.Topology.Category.TopCat.EpiMono

/-!
# Pulling the original two-cell model through its native cover

The actual singular attachment model is pulled back through the original
native covering projection. Van Kampen stability of monic simplicial
pushouts retains its entire old space and disk family. The original model
comparison and existing right properness give a weak comparison to the
same native cover. The actual relative chain map and both quotient laws
follow from the existing short-exact cokernel sequence.

This module does not yet identify these relative chains with a free
quotient-group-ring module or compute the spherical three-cell boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace OriginalPulledCellPushoutConstruction

private def legPullbackMap {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    pullback f p ⟶ pullback g p :=
  SSet.pullbackLegMap f g p s hs

private theorem legPullbackMap_fst {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    legPullbackMap f g p s hs ≫ pullback.fst g p = pullback.fst f p ≫ s := by
  exact SSet.pullbackLegMap_fst f g p s hs

private theorem legPullbackMap_snd {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    legPullbackMap f g p s hs ≫ pullback.snd g p = pullback.snd f p := by
  exact SSet.pullbackLegMap_snd f g p s hs

private theorem legPullbackMap_isPullback {A B Y Z : SSet.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) (p : Z ⟶ Y) (s : A ⟶ B) (hs : f = s ≫ g) :
    IsPullback (legPullbackMap f g p s hs) (pullback.fst f p) (pullback.fst g p) s := by
  exact SSet.pullbackLegMap_isPullback f g p s hs

private theorem legPullbackPushout {A B C D Y Z : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {i : C ⟶ D}
    [Mono f] (sq : IsPushout f g h i) (c : D ⟶ Y) (p : Z ⟶ Y)
    (bY : B ⟶ Y) (cY : C ⟶ Y) (hbY : bY = h ≫ c) (hcY : cY = i ≫ c) :
    let aY := g ≫ cY
    let haY : aY = f ≫ bY :=
      (congrArg (fun t => g ≫ t) hcY).trans
        ((Category.assoc g i c).symm.trans
          ((congrArg (fun t => t ≫ c) sq.w.symm).trans
            ((Category.assoc f h c).trans (congrArg (fun t => f ≫ t) hbY.symm))))
    IsPushout
      (legPullbackMap aY bY p f haY)
      (legPullbackMap aY cY p g rfl)
      (legPullbackMap bY c p h hbY)
      (legPullbackMap cY c p i hcY) := by
  exact SSet.pullbackLegPushout sq c p bY cY hbY hcY

private theorem relativeChainMap_quasiIso {P Q : SSetPair.{u}} (f : P ⟶ Q)
    (hLeft : SSet.realizationWeakEquivalences f.left)
    (hRight : SSet.realizationWeakEquivalences f.right) (R : AddCommGrpCat.{u}) :
    QuasiIso (SSetPair.chainComplexMap f R) := by
  let F : SSet.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
    (SSet.chainComplexFunctor AddCommGrpCat.{u}).obj R
  let φ : Arrow.mk P.hom ⟶ Arrow.mk Q.hom := SSetPair.forget.map f
  have hSquare : F.map φ.left ≫ F.map Q.hom = F.map P.hom ≫ F.map φ.right :=
    (F.map_comp φ.left Q.hom).symm.trans
      ((congrArg F.map φ.w).trans (F.map_comp P.hom φ.right))
  have hProjection : F.map φ.right ≫ Q.chainComplexπ R =
      P.chainComplexπ R ≫ SSetPair.chainComplexMap f R := by
    exact ((SSetPair.chainComplexFunctorπ AddCommGrpCat.{u}).app R).naturality f
  let ψ : P.chainComplexShortComplex R ⟶ Q.chainComplexShortComplex R :=
    ShortComplex.homMk (F.map φ.left) (F.map φ.right)
      (SSetPair.chainComplexMap f R) hSquare hProjection
  have hL : QuasiIso ψ.τ₁ :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp hLeft R
  have hR : QuasiIso ψ.τ₂ :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp hRight R
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ
    (P.shortExact_chainComplexShortComplex R) (Q.shortExact_chainComplexShortComplex R) hL hR

end OriginalPulledCellPushoutConstruction

public section

namespace AlgebraicTopology.LoopCellPulledSimplicialModel

/-- The actual native target-cover projection for the original attachment. -/
abbrev projection (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    LoopCellSphericalGenerators.nativeCover X x P ⟶
      TopCat.toSSet.obj (LoopCellAttachment.space X x P) :=
  SSet.KanComplex.nativeCoverProjection
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (LoopCellSphericalGenerators.nativeTargetPoint X x P)

/-- The literal pullback of the ACTUAL model comparison through the original native cover. -/
abbrev space (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  pullback (LoopCellSimplicialModel.toSingular X x P) (projection X x P)

/-- The literal old singular-space pullback along the original inclusion. -/
abbrev oldSpace (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  LoopCellSphericalGenerators.nativePullback X x P

/-- The literal pulled family of the actual original characteristic-disk adjoints. -/
abbrev disks (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  pullback (LoopCellSimplicialModel.diskMates X x P) (projection X x P)

/-- The literal pulled family of the original boundary adjoints through the original inclusion. -/
abbrev boundaries (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  pullback (LoopCellSimplicialModel.attaching X x P ≫
    LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P)

/-- The actual old-cover inclusion into the pulled model. -/
def oldInclusion (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    oldSpace X x P ⟶ space X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap
    (LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.oldInclusion X x P)
    (LoopCellSimplicialModel.toSingular_old X x P).symm

/-- The actual pulled characteristic-disk family inclusion. -/
def diskInclusion (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    disks X x P ⟶ space X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap
    (LoopCellSimplicialModel.diskMates X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.newDisks X x P)
    (LoopCellSimplicialModel.toSingular_disks X x P).symm

/-- The actual map from the pulled boundary family to the pulled disk family. -/
def boundaryToDisks (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    boundaries X x P ⟶ disks X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.diskMates X x P) (projection X x P)
    (LoopCellSimplicialModel.boundarySum X x P)
    (LoopCellSimplicialModel.adjunctSquare X x P).symm

/-- The actual pulled boundary attaching map into the SAME old cover. -/
def attaching (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    boundaries X x P ⟶ oldSpace X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P)
    (LoopCellSimplicialModel.attaching X x P) rfl

/-- The original monic P-cell pushout is a pushout after this ACTUAL native-cover pullback. -/
theorem isPushout (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    IsPushout (boundaryToDisks X x P) (attaching X x P)
      (diskInclusion X x P) (oldInclusion X x P) := by
  let f := LoopCellSimplicialModel.boundarySum X x P
  have hf : Mono f := by
    have h : Mono (CategoryTheory.Limits.Sigma.map
      (fun _ : P => (SSet.boundary.{u} 2).ι)) := inferInstance
    exact Eq.mp (congrArg (fun t : LoopCellSimplicialModel.boundaries X x P ⟶
      LoopCellSimplicialModel.disks X x P => Mono t)
        (LoopCellSimplicialModel.boundarySum_eq X x P).symm) h
  let _ : Mono f := hf
  exact OriginalPulledCellPushoutConstruction.legPullbackPushout
    (LoopCellSimplicialModel.isPushout X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.diskMates X x P)
    (LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.toSingular_disks X x P).symm
    (LoopCellSimplicialModel.toSingular_old X x P).symm

/-- The pulled model's second projection is the actual comparison to the original native cover. -/
abbrev toCover (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    space X x P ⟶ LoopCellSphericalGenerators.nativeCover X x P :=
  pullback.snd (LoopCellSimplicialModel.toSingular X x P) (projection X x P)

/-- The actual old cover map is retained, without changing its first-path connector. -/
theorem oldInclusion_toCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    oldInclusion X x P ≫ toCover X x P =
        LoopCellSphericalGenerators.nativePullbackToCover X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_snd
    (LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.oldInclusion X x P)
    (LoopCellSimplicialModel.toSingular_old X x P).symm

/-- Every actual pulled disk retains its full projection to the SAME original native cover. -/
theorem diskInclusion_toCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    diskInclusion X x P ≫ toCover X x P =
      pullback.snd (LoopCellSimplicialModel.diskMates X x P) (projection X x P) := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_snd
    (LoopCellSimplicialModel.diskMates X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.newDisks X x P)
    (LoopCellSimplicialModel.toSingular_disks X x P).symm

/-- The actual old-cover inclusion is monic by its genuine pullback square. -/
theorem oldInclusion_mono (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : Mono (oldInclusion X x P) := by
  have h : IsPullback (oldInclusion X x P)
      (LoopCellSphericalGenerators.nativePullbackProjection X x P)
      (pullback.fst (LoopCellSimplicialModel.toSingular X x P) (projection X x P))
      (LoopCellSimplicialModel.oldInclusion X x P) :=
    OriginalPulledCellPushoutConstruction.legPullbackMap_isPullback
      (LoopCellSphericalGenerators.nativeInclusion X x P)
      (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
      (LoopCellSimplicialModel.oldInclusion X x P)
      (LoopCellSimplicialModel.toSingular_old X x P).symm
  exact h.mono_fst_of_mono (LoopCellSimplicialModel.oldInclusion_mono X x P)

/-- The pulled old-space map retains the actual original model old inclusion. -/
theorem oldInclusion_toModel (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    oldInclusion X x P ≫ pullback.fst (LoopCellSimplicialModel.toSingular X x P)
        (projection X x P) =
      LoopCellSphericalGenerators.nativePullbackProjection X x P ≫
        LoopCellSimplicialModel.oldInclusion X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_fst
    (LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.oldInclusion X x P)
    (LoopCellSimplicialModel.toSingular_old X x P).symm

/-- Every pulled disk retains its original whole model disk inclusion. -/
theorem diskInclusion_toModel (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    diskInclusion X x P ≫ pullback.fst (LoopCellSimplicialModel.toSingular X x P)
        (projection X x P) =
      pullback.fst (LoopCellSimplicialModel.diskMates X x P) (projection X x P) ≫
        LoopCellSimplicialModel.newDisks X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_fst
    (LoopCellSimplicialModel.diskMates X x P)
    (LoopCellSimplicialModel.toSingular X x P) (projection X x P)
    (LoopCellSimplicialModel.newDisks X x P)
    (LoopCellSimplicialModel.toSingular_disks X x P).symm

/-- The native projection is a fibration by the actual under-groupoid nerve and pullback. -/
theorem projection_fibration (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    HomotopicalAlgebra.Fibration (projection X x P) := by
  let Y : SSet.{u} := TopCat.toSSet.obj (LoopCellAttachment.space X x P)
  let y : Y _⦋0⦌ := LoopCellSphericalGenerators.nativeTargetPoint X x P
  let : Groupoid (CategoryTheory.Under (SSet.FundamentalGroupoid.mk y)) :=
    Groupoid.ofIsGroupoid
  let : HomotopicalAlgebra.Fibration (SSet.KanComplex.nativeCoverNerveProjection Y y) := by
    dsimp only [SSet.KanComplex.nativeCoverNerveProjection]
    exact CategoryTheory.nerve.fibration_nerveMap_of_isIsofibration
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk y))
  change HomotopicalAlgebra.Fibration
    (pullback.fst (SSet.KanComplex.nativeCoverUnit Y)
      (SSet.KanComplex.nativeCoverNerveProjection Y y))
  infer_instance

/-- The actual pulled model comparison is weak by the existing right-proper base-change rule. -/
theorem toCover_weak (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    SSet.realizationWeakEquivalences (toCover X x P) := by
  let c := LoopCellSimplicialModel.toSingular X x P
  let p := projection X x P
  let : HomotopicalAlgebra.Fibration p := projection_fibration X x P
  let : HomotopicalAlgebra.WeakEquivalence c :=
    (HomotopicalAlgebra.weakEquivalence_iff c).mpr
      (LoopCellSimplicialModel.toSingular_weak X x P)
  have h : HomotopicalAlgebra.WeakEquivalence (pullback.snd c p) :=
    HomotopicalAlgebra.IsRightProper.weakEquivalence_of_isPullback
      (IsPullback.of_hasPullback c p)
  exact (HomotopicalAlgebra.weakEquivalence_iff (toCover X x P)).mp h

/-- The old-cover inclusion in the literal pulled model, bundled as an actual simplicial pair. -/
abbrev pair (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : SSetPair.{u} := by
  letI : Mono (oldInclusion X x P) := oldInclusion_mono X x P
  exact SSetPair.of (oldInclusion X x P)

/-- The SAME original old-cover inclusion in the native target cover is monic. -/
theorem nativePair_mono (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    Mono (LoopCellSphericalGenerators.nativePullbackToCover X x P) := by
  let : Mono (LoopCellAttachment.inclusion X x P) :=
    (TopCat.mono_iff_injective _).mpr
      (LoopCellAttachment.inclusion_isClosedEmbedding X x P).injective
  let : Mono (LoopCellSphericalGenerators.nativeInclusion X x P) :=
    inferInstanceAs (Mono (TopCat.toSSet.map (LoopCellAttachment.inclusion X x P)))
  change Mono (pullback.snd (LoopCellSphericalGenerators.nativeInclusion X x P)
    (projection X x P))
  infer_instance

/-- The original native covering pair, with its original old-cover map. -/
abbrev nativePair (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : SSetPair.{u} := by
  letI : Mono (LoopCellSphericalGenerators.nativePullbackToCover X x P) := nativePair_mono X x P
  exact SSetPair.of (LoopCellSphericalGenerators.nativePullbackToCover X x P)

/-- The actual comparison of pairs is identity on the old cover and the second projection on top. -/
def pairToNativeCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : pair X x P ⟶ nativePair X x P := by
  exact SSetPair.homMk (𝟙 (oldSpace X x P)) (toCover X x P)
    ((Category.id_comp (LoopCellSphericalGenerators.nativePullbackToCover X x P)).trans
      (oldInclusion_toCover X x P).symm)

/-- Its old-cover component is the actual identity, not an independently selected model map. -/
theorem pairToNativeCover_left (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (pairToNativeCover X x P).left = 𝟙 (oldSpace X x P) := by
  rfl

/-- Its ambient component is the SAME pulled comparison map. -/
theorem pairToNativeCover_right (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (pairToNativeCover X x P).right = toCover X x P := by
  rfl

/-- The actual induced map of relative chains. -/
abbrev relativeChainMap (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    (pair X x P).chainComplex R ⟶ (nativePair X x P).chainComplex R :=
  SSetPair.chainComplexMap (pairToNativeCover X x P) R

/-- The whole relative-chain comparison retains both original quotient maps. -/
theorem relativeChainMap_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    (pair X x P).chainComplexπ R ≫ relativeChainMap X x P R =
      SSet.chainComplexMap (toCover X x P) R ≫ (nativePair X x P).chainComplexπ R := by
  exact (((SSetPair.chainComplexFunctorπ AddCommGrpCat.{u}).app R).naturality
    (pairToNativeCover X x P)).symm

/-- The actual relative comparison is a quasi-isomorphism, derived from the two original legs. -/
theorem relativeChainMap_quasiIso (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) :
    QuasiIso (relativeChainMap X x P R) := by
  have hId : SSet.realizationWeakEquivalences (𝟙 (oldSpace X x P)) :=
    SSet.realizationWeakEquivalences.id_mem _
  exact OriginalPulledCellPushoutConstruction.relativeChainMap_quasiIso
    (pairToNativeCover X x P) hId (toCover_weak X x P) R

/-- Relative homology of the literal pulled cell model is the original native covering relative
homology. -/
noncomputable def relativeHomologyIso (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (pair X x P).homology R n ≅ (nativePair X x P).homology R n := by
  letI : QuasiIso (relativeChainMap X x P R) := relativeChainMap_quasiIso X x P R
  exact asIso (SSetPair.homologyMap (pairToNativeCover X x P) R n)

/-- The whole absolute-to-relative quotient law uses the same actual comparison. -/
theorem relativeHomologyIso_projection (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    (pair X x P).homologyπ R n ≫ (relativeHomologyIso X x P R n).hom =
      SSet.homologyMap (toCover X x P) R n ≫ (nativePair X x P).homologyπ R n := by
  let H : ChainComplex AddCommGrpCat.{u} ℕ ⥤ AddCommGrpCat.{u} :=
    HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n
  exact (H.map_comp ((pair X x P).chainComplexπ R) (relativeChainMap X x P R)).symm.trans
    ((congrArg H.map (relativeChainMap_projection X x P R)).trans
      (H.map_comp (SSet.chainComplexMap (toCover X x P) R)
        ((nativePair X x P).chainComplexπ R)))

/-- The inverse homology comparison retains that SAME quotient law. -/
theorem relativeHomologyIso_inverse_projection (X : TopCat.{u}) [T2Space X]
    [Topology.CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (R : AddCommGrpCat.{u}) (n : ℕ) :
    SSet.homologyMap (toCover X x P) R n ≫ (nativePair X x P).homologyπ R n ≫
        (relativeHomologyIso X x P R n).inv = (pair X x P).homologyπ R n := by
  let q := (pair X x P).homologyπ R n
  let q' := (nativePair X x P).homologyπ R n
  let f := SSet.homologyMap (toCover X x P) R n
  let e := relativeHomologyIso X x P R n
  have h : q ≫ e.hom = f ≫ q' := relativeHomologyIso_projection X x P R n
  exact (Category.assoc f q' e.inv).symm.trans
    ((congrArg (fun t => t ≫ e.inv) h.symm).trans
      ((Category.assoc q e.hom e.inv).trans
        ((congrArg (fun t => q ≫ t) e.hom_inv_id).trans (Category.comp_id q))))

/-- The pulled boundary map retains the actual original boundary-family inclusion on first
projections. -/
theorem boundaryToDisks_fst (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    boundaryToDisks X x P ≫ pullback.fst (LoopCellSimplicialModel.diskMates X x P)
        (projection X x P) =
      pullback.fst (LoopCellSimplicialModel.attaching X x P ≫
        LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P) ≫
          LoopCellSimplicialModel.boundarySum X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_fst
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.diskMates X x P) (projection X x P)
    (LoopCellSimplicialModel.boundarySum X x P)
    (LoopCellSimplicialModel.adjunctSquare X x P).symm

/-- The pulled boundary-family inclusion retains the SAME native-cover coordinate. -/
theorem boundaryToDisks_snd (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    boundaryToDisks X x P ≫ pullback.snd (LoopCellSimplicialModel.diskMates X x P)
        (projection X x P) =
      pullback.snd (LoopCellSimplicialModel.attaching X x P ≫
        LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P) := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_snd
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSimplicialModel.diskMates X x P) (projection X x P)
    (LoopCellSimplicialModel.boundarySum X x P)
    (LoopCellSimplicialModel.adjunctSquare X x P).symm

/-- The actual attaching map retains its original boundary adjoint on first projections. -/
theorem attaching_fst (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    attaching X x P ≫ LoopCellSphericalGenerators.nativePullbackProjection X x P =
      pullback.fst (LoopCellSimplicialModel.attaching X x P ≫
        LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P) ≫
          LoopCellSimplicialModel.attaching X x P := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_fst
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P)
    (LoopCellSimplicialModel.attaching X x P) rfl

/-- The actual attaching map retains its SAME native-cover coordinate. -/
theorem attaching_snd (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    attaching X x P ≫ LoopCellSphericalGenerators.nativePullbackToCover X x P =
      pullback.snd (LoopCellSimplicialModel.attaching X x P ≫
        LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P) := by
  exact OriginalPulledCellPushoutConstruction.legPullbackMap_snd
    (LoopCellSimplicialModel.attaching X x P ≫ LoopCellSphericalGenerators.nativeInclusion X x P)
    (LoopCellSphericalGenerators.nativeInclusion X x P) (projection X x P)
    (LoopCellSimplicialModel.attaching X x P) rfl

end AlgebraicTopology.LoopCellPulledSimplicialModel

end
