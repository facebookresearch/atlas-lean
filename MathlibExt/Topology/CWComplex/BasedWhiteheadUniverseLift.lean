/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.UniverseLift
public import MathlibExt.Topology.CWComplex.BasedWhitehead
public import MathlibExt.Topology.Homotopy.PointRelativeComposition
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
public import MathlibExt.Topology.Category.TopCat.UniverseLift
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelCompatibilityFromSSet
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual independently sized based CW model transport

The given original weak map is lifted using actual boundary RLP transport and
Ken Brown's existing fibrant factorization. Classical CW fields and points,
all model maps and both given model homotopies are lifted to a common maximum.
The resulting inverse and both relative families return to the original map
and points. Original carriers have no separation or CW hypothesis.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology Set
open scoped Simplicial TopCat.modelCategory unitInterval

universe u v w z u₁ v₁ w₁

namespace CWIndependentUniverseSource101

private def flattenHomeomorph (X : Type w) [TopologicalSpace X] :
    ULift.{v} (ULift.{u} X) ≃ₜ ULift.{max u v} X where
  toFun x := ULift.up x.down.down
  invFun x := ULift.up (ULift.up x.down)
  left_inv x := by cases x with | up x => cases x; rfl
  right_inv x := by cases x; rfl
  continuous_toFun := continuous_uliftUp.comp
    (continuous_uliftDown.comp continuous_uliftDown)
  continuous_invFun := continuous_uliftUp.comp
    (continuous_uliftUp.comp continuous_uliftDown)

private def flattenDiskIso (n : ℕ) :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.disk.{u} n) ≅ TopCat.disk.{max u v} n :=
  TopCat.isoOfHomeo (flattenHomeomorph (Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin n)) 1))

private def flattenBoundaryIso (n : ℕ) :
    TopCat.uliftFunctor.{v, u}.obj (TopCat.diskBoundary.{u} n) ≅
      TopCat.diskBoundary.{max u v} n :=
  TopCat.isoOfHomeo (flattenHomeomorph (Metric.sphere
    (0 : EuclideanSpace ℝ (Fin n)) 1))

private theorem flattenDisk_boundary (n : ℕ) :
    TopCat.uliftFunctor.{v, u}.map (TopCat.diskBoundaryInclusion.{u} n) ≫
        (flattenDiskIso n :
          TopCat.uliftFunctor.{v, u}.obj (TopCat.disk.{u} n) ≅ TopCat.disk.{max u v} n).hom =
      (flattenBoundaryIso n :
        TopCat.uliftFunctor.{v, u}.obj (TopCat.diskBoundary.{u} n) ≅
          TopCat.diskBoundary.{max u v} n).hom ≫
        TopCat.diskBoundaryInclusion.{max u v} n := by
  apply TopCat.ext
  intro x
  rfl

private def flattenDiskArrowIso (n : ℕ) :
    Arrow.mk (TopCat.uliftFunctor.{v, u}.map (TopCat.diskBoundaryInclusion.{u} n)) ≅
      Arrow.mk (TopCat.diskBoundaryInclusion.{max u v} n) :=
  Arrow.isoMk (flattenBoundaryIso n) (flattenDiskIso n) (flattenDisk_boundary n).symm

/-- The whole generator arrow, including the empty zero-dimensional boundary. -/
private def liftedBoundaryArrowIso (n : ℕ) :
    Arrow.mk (TopCat.uliftFunctor.{v, u}.map
      (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι)) ≅
        Arrow.mk (SSet.toTop.{max u v}.map (SSet.boundary.{max u v} n).ι) :=
  ((TopCat.uliftFunctor.{v, u}).mapArrow.mapIso
      (SSet.boundary.toTopDiskArrowIso.{u} n)).trans
    ((flattenDiskArrowIso n).trans (SSet.boundary.toTopDiskArrowIso.{max u v} n).symm)

/-- The actual fully faithful lift carries every original lifting square. -/
private theorem lifted_hasLiftingProperty {A B E D : TopCat.{u}}
    (i : A ⟶ B) (p : E ⟶ D) [HasLiftingProperty i p] :
    HasLiftingProperty (TopCat.uliftFunctor.{v, u}.map i)
      (TopCat.uliftFunctor.{v, u}.map p) := by
  let F := TopCat.uliftFunctor.{v, u}
  constructor
  intro a b sq
  let a₀ : A ⟶ E := F.preimage a
  let b₀ : B ⟶ D := F.preimage b
  let cs : CommSq a₀ i p b₀ := by
    constructor
    apply F.map_injective
    simpa only [Functor.map_comp, a₀, b₀, Functor.map_preimage] using sq.w
  exact CommSq.HasLift.mk'
    { l := F.map cs.lift
      fac_left := by
        simpa only [Functor.map_comp, a₀, Functor.map_preimage] using
          congrArg F.map cs.fac_left
      fac_right := by
        simpa only [Functor.map_comp, b₀, Functor.map_preimage] using
          congrArg F.map cs.fac_right }

private theorem liftedBoundaryRLP {E B : TopCat.{u}} (p : E ⟶ B)
    (hp : TopCat.realizedBoundaryInclusions.{u}.rlp p) :
    TopCat.realizedBoundaryInclusions.{max u v}.rlp
      (TopCat.uliftFunctor.{v, u}.map p) := by
  intro A D i hi
  change MorphismProperty.ofHoms
    (fun n : ℕ => SSet.toTop.{max u v}.map (SSet.boundary.{max u v} n).ι) i at hi
  obtain ⟨n⟩ := hi
  let : HasLiftingProperty (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι) p :=
    hp _ (TopCat.boundary_mem_realizedBoundaryInclusions n)
  let : HasLiftingProperty
      (TopCat.uliftFunctor.{v, u}.map (SSet.toTop.{u}.map (SSet.boundary.{u} n).ι))
      (TopCat.uliftFunctor.{v, u}.map p) := lifted_hasLiftingProperty _ _
  exact HasLiftingProperty.of_arrow_iso_left (liftedBoundaryArrowIso n)
    (TopCat.uliftFunctor.{v, u}.map p)

private theorem selected_boundary_dictionary :
    TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences =
      TopCat.realizedBoundaryInclusions.{u}.rlp :=
  TopCat.hornRLP_inf_W_eq_boundaryRLP_of_sSet
    TopCat.horn_llp_le_weakHomotopyEquivalences
    SSet.KanComplex.I_rlp_to_W_kanRestricted
    SSet.modelCategoryQuillen.J_rlp_inf_W_le_I_rlp

private theorem boundaryRLP_of_trivialFibration {E B : TopCat.{u}}
    (p : E ⟶ B) [Fibration p] [WeakEquivalence p] :
    TopCat.realizedBoundaryInclusions.{u}.rlp p := by
  have h : (TopCat.realizedHornInclusions.{u}.rlp ⊓
      TopCat.weakHomotopyEquivalences) p :=
    ⟨(fibration_iff p).mp inferInstance, (weakEquivalence_iff p).mp inferInstance⟩
  rw [selected_boundary_dictionary] at h
  exact h

private theorem weak_of_boundaryRLP {E B : TopCat.{u}} (p : E ⟶ B)
    (hp : TopCat.realizedBoundaryInclusions.{u}.rlp p) :
    TopCat.weakHomotopyEquivalences p := by
  rw [← selected_boundary_dictionary] at hp
  exact hp.2

/-- Both actual Brown projections lift to weak maps; original weakness is the input. -/
private theorem original_weak_map_ulift {X Y : TopCat.{u}} (f : X ⟶ Y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    TopCat.weakHomotopyEquivalences (TopCat.uliftFunctor.{v, u}.map f) := by
  let : IsFibrant X := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant X
  let : IsFibrant Y := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant Y
  let : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  let h : FibrantBrownFactorization f := Classical.arbitrary _
  let F := TopCat.uliftFunctor.{v, u}
  have hp : TopCat.weakHomotopyEquivalences (F.map h.p) :=
    weak_of_boundaryRLP _ (liftedBoundaryRLP _ (boundaryRLP_of_trivialFibration h.p))
  have hr : TopCat.weakHomotopyEquivalences (F.map h.r) :=
    weak_of_boundaryRLP _ (liftedBoundaryRLP _ (boundaryRLP_of_trivialFibration h.r))
  have hi_r : TopCat.weakHomotopyEquivalences (F.map h.i ≫ F.map h.r) := by
    rw [← CategoryTheory.Functor.map_comp, h.i_r, CategoryTheory.Functor.map_id]
    exact TopCat.weakHomotopyEquivalences.of_isIso _
  have hi : TopCat.weakHomotopyEquivalences (F.map h.i) :=
    TopCat.weakHomotopyEquivalences.of_postcomp _ _ hr hi_r
  have hcomp : TopCat.weakHomotopyEquivalences (F.map h.i ≫ F.map h.p) :=
    TopCat.weakHomotopyEquivalences.comp_mem _ _ hi hp
  simpa only [← Functor.map_comp, h.fac] using hcomp



private def conjugateMap
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (f : C(X, Y)) : C(X', Y') :=
  ⟨fun z => ey (f (ex.symm z)), ey.continuous_toFun.comp
    (f.continuous.comp ex.symm.continuous_toFun)⟩

private theorem conjugateMap_point
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (f : C(X, Y)) (x : X) :
    conjugateMap ex ey f (ex x) = ey (f x) := by
  change ey (f (ex.symm (ex x))) = _
  rw [ex.symm_apply_apply]

private theorem conjugateMap_comp
    {X : Type u} {Y : Type v} {Z : Type w}
    {X' : Type u₁} {Y' : Type v₁} {Z' : Type w₁}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z']
    (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (ez : Z ≃ₜ Z')
    (f : C(X, Y)) (g : C(Y, Z)) :
    conjugateMap ex ez (g.comp f) =
      (conjugateMap ey ez g).comp (conjugateMap ex ey f) := by
  ext x
  change ez (g (f (ex.symm x))) = ez (g (ey.symm (ey (f (ex.symm x)))))
  rw [ey.symm_apply_apply]

private theorem conjugateMap_id
    {X : Type u} {X' : Type u₁} [TopologicalSpace X] [TopologicalSpace X']
    (ex : X ≃ₜ X') :
    conjugateMap ex ex (ContinuousMap.id X) = ContinuousMap.id X' := by
  ext x
  exact ex.apply_symm_apply x

private def conjugateHomotopyRel
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    {f g : C(X, Y)} (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (x : X)
    (H : ContinuousMap.HomotopyRel f g {x}) :
    ContinuousMap.HomotopyRel (conjugateMap ex ey f) (conjugateMap ex ey g) {ex x} where
  toFun z := ey (H (z.1, ex.symm z.2))
  continuous_toFun := ey.continuous_toFun.comp
    (H.continuous.comp (continuous_fst.prodMk
      (ex.symm.continuous_toFun.comp continuous_snd)))
  map_zero_left z := congrArg ey (H.map_zero_left (ex.symm z))
  map_one_left z := congrArg ey (H.map_one_left (ex.symm z))
  prop' t z hz := by
    have hz' : z = ex x := Set.mem_singleton_iff.mp hz
    subst z
    change ey (H (t, ex.symm (ex x))) = ey (f (ex.symm (ex x)))
    rw [ex.symm_apply_apply]
    exact congrArg ey (H.eq_fst t (Set.mem_singleton x))

private theorem conjugate_inverse
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (f : C(X, Y)) :
    conjugateMap ex.symm ey.symm (conjugateMap ex ey f) = f := by
  ext x
  change ey.symm (ey (f (ex.symm (ex x)))) = f x
  rw [ex.symm_apply_apply, ey.symm_apply_apply]

private theorem return_left_original_comp
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (f : C(X, Y)) (g' : C(Y', X')) :
    conjugateMap ex.symm ex.symm (g'.comp (conjugateMap ex ey f)) =
      (conjugateMap ey.symm ex.symm g').comp f := by
  ext x
  change ex.symm (g' (ey (f (ex.symm (ex x))))) = ex.symm (g' (ey (f x)))
  rw [ex.symm_apply_apply]

private theorem return_right_original_comp
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (f : C(X, Y)) (g' : C(Y', X')) :
    conjugateMap ey.symm ey.symm ((conjugateMap ex ey f).comp g') =
      f.comp (conjugateMap ey.symm ex.symm g') := by
  ext y
  change ey.symm (ey (f (ex.symm (g' (ey y))))) = f (ex.symm (g' (ey y)))
  rw [ey.symm_apply_apply]

/-- Return the actual whole relative family to the original point and carrier. -/
private def returnHomotopyRel
    {X : Type u} {Y : Type v} {X' : Type u₁} {Y' : Type v₁}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    {f' g' : C(X', Y')} (ex : X ≃ₜ X') (ey : Y ≃ₜ Y') (x : X)
    (H : ContinuousMap.HomotopyRel f' g' {ex x}) :
    ContinuousMap.HomotopyRel (conjugateMap ex.symm ey.symm f')
      (conjugateMap ex.symm ey.symm g') {x} where
  toFun z := ey.symm (H (z.1, ex z.2))
  continuous_toFun := ey.symm.continuous_toFun.comp
    (H.continuous.comp (continuous_fst.prodMk
      (ex.continuous_toFun.comp continuous_snd)))
  map_zero_left z := congrArg ey.symm (H.map_zero_left (ex z))
  map_one_left z := congrArg ey.symm (H.map_one_left (ex z))
  prop' t z hz := by
    have hz' : z = x := Set.mem_singleton_iff.mp hz
    subst z
    exact congrArg ey.symm (H.eq_fst t (Set.mem_singleton (ex x)))



private theorem independent_native_CW_models
    (X Y : TopCat.{u}) (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0)
    (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
    (hjx : Topology.CWComplex.map 0 jx ![] = cx)
    (hjy : Topology.CWComplex.map 0 jy ![] = cy)
    (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
    (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
    (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
    (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom
        (TopCat.Hom.hom (𝟙 X)) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom
        (TopCat.Hom.hom (𝟙 Y)) {y}) := by
  let F := TopCat.uliftFunctor.{max v w, u}
  let XU : TopCat.{max u v w} := F.obj X
  let YU : TopCat.{max u v w} := F.obj Y
  let CXU : TopCat.{max u v w} := TopCat.uliftFunctor.{max u w, v}.obj CX
  let CYU : TopCat.{max u v w} := TopCat.uliftFunctor.{max u v, w}.obj CY
  let ex : X ≃ₜ XU := X.uliftFunctorObjHomeo
  let ey : Y ≃ₜ YU := Y.uliftFunctorObjHomeo
  let ecx : CX ≃ₜ CXU := CX.uliftFunctorObjHomeo
  let ecy : CY ≃ₜ CYU := CY.uliftFunctorObjHomeo
  let : T2Space CXU := by change T2Space (ULift.{max u w} CX); infer_instance
  let : T2Space CYU := by change T2Space (ULift.{max u v} CY); infer_instance
  let : Topology.CWComplex (Set.univ : Set CXU) := Topology.CWComplex.uliftCWComplex CX
  let : Topology.CWComplex (Set.univ : Set CYU) := Topology.CWComplex.uliftCWComplex CY
  let jxU : Topology.CWComplex.cell (Set.univ : Set CXU) 0 := ULift.up jx
  let jyU : Topology.CWComplex.cell (Set.univ : Set CYU) 0 := ULift.up jy
  have hjxU : Topology.CWComplex.map 0 jxU ![] = ecx cx := by
    change ULift.up (Topology.CWComplex.map 0 jx ![]) = ULift.up cx
    exact congrArg ULift.up hjx
  have hjyU : Topology.CWComplex.map 0 jyU ![] = ecy cy := by
    change ULift.up (Topology.CWComplex.map 0 jy ![]) = ULift.up cy
    exact congrArg ULift.up hjy
  let rxU : XU ⟶ CXU := TopCat.ofHom (conjugateMap ex ecx rx)
  let sxU : CXU ⟶ XU := TopCat.ofHom (conjugateMap ecx ex sx)
  let ryU : YU ⟶ CYU := TopCat.ofHom (conjugateMap ey ecy ry)
  let syU : CYU ⟶ YU := TopCat.ofHom (conjugateMap ecy ey sy)
  have hrxU : rxU (ex x) = ecx cx := by
    change conjugateMap ex ecx rx (ex x) = ecx cx
    rw [conjugateMap_point, hrx]
  have hsxU : sxU (ecx cx) = ex x := by
    change conjugateMap ecx ex sx (ecx cx) = ex x
    rw [conjugateMap_point, hsx]
  have hryU : ryU (ey y) = ecy cy := by
    change conjugateMap ey ecy ry (ey y) = ecy cy
    rw [conjugateMap_point, hry]
  have hsyU : syU (ecy cy) = ey y := by
    change conjugateMap ecy ey sy (ecy cy) = ey y
    rw [conjugateMap_point, hsy]
  let LXU₀ := (conjugateHomotopyRel ex ex x LX).cast
    (conjugateMap_comp ex ecx ex rx sx) (conjugateMap_id ex)
  let RXU₀ := (conjugateHomotopyRel ecx ecx cx RX).cast
    (conjugateMap_comp ecx ex ecx sx rx) (conjugateMap_id ecx)
  let LYU₀ := (conjugateHomotopyRel ey ey y LY).cast
    (conjugateMap_comp ey ecy ey ry sy) (conjugateMap_id ey)
  let RYU₀ := (conjugateHomotopyRel ecy ecy cy RY).cast
    (conjugateMap_comp ecy ey ecy sy ry) (conjugateMap_id ecy)
  let LXU : ContinuousMap.HomotopyRel (rxU ≫ sxU).hom
      (TopCat.Hom.hom (𝟙 XU)) {ex x} :=
    LXU₀.cast (TopCat.hom_comp rxU sxU).symm (TopCat.hom_id (X := XU)).symm
  let RXU : ContinuousMap.HomotopyRel (sxU ≫ rxU).hom
      (TopCat.Hom.hom (𝟙 CXU)) {ecx cx} :=
    RXU₀.cast (TopCat.hom_comp sxU rxU).symm (TopCat.hom_id (X := CXU)).symm
  let LYU : ContinuousMap.HomotopyRel (ryU ≫ syU).hom
      (TopCat.Hom.hom (𝟙 YU)) {ey y} :=
    LYU₀.cast (TopCat.hom_comp ryU syU).symm (TopCat.hom_id (X := YU)).symm
  let RYU : ContinuousMap.HomotopyRel (syU ≫ ryU).hom
      (TopCat.Hom.hom (𝟙 CYU)) {ecy cy} :=
    RYU₀.cast (TopCat.hom_comp syU ryU).symm (TopCat.hom_id (X := CYU)).symm
  let fU : XU ⟶ YU := F.map f
  have hfU : TopCat.weakHomotopyEquivalences fU := original_weak_map_ulift f hf
  have hxyU : fU (ex x) = ey y := by
    change TopCat.uliftFunctor.map f (X.uliftFunctorObjHomeo x) = Y.uliftFunctorObjHomeo y
    rw [TopCat.uliftFunctorObjHomeo_naturality_apply, hxy]
  obtain ⟨gU, hgU, ⟨HLU⟩, ⟨HRU⟩⟩ :=
    Topology.CWComplex.basedCWTypeWhitehead XU YU CXU CYU (ex x) (ey y) (ecx cx) (ecy cy)
      jxU jyU hjxU hjyU rxU sxU ryU syU hrxU hsxU hryU hsyU LXU RXU LYU RYU fU hxyU hfU
  let g₀ : C(Y, X) := conjugateMap ey.symm ex.symm gU.hom
  let g : Y ⟶ X := TopCat.ofHom g₀
  have hg : g y = x := by
    change ex.symm (gU (ey y)) = x
    rw [hgU, ex.symm_apply_apply]
  have hfU_map : fU.hom = conjugateMap ex ey f.hom := by
    ext z
    rfl
  let HLU₀ : ContinuousMap.HomotopyRel
      (gU.hom.comp (conjugateMap ex ey f.hom)) (ContinuousMap.id XU) {ex x} :=
    HLU.cast ((TopCat.hom_comp fU gU).trans (by rw [hfU_map])) (TopCat.hom_id (X := XU))
  let HRU₀ : ContinuousMap.HomotopyRel
      ((conjugateMap ex ey f.hom).comp gU.hom) (ContinuousMap.id YU) {ey y} :=
    HRU.cast ((TopCat.hom_comp gU fU).trans (by rw [hfU_map])) (TopCat.hom_id (X := YU))
  let HL₀ : ContinuousMap.HomotopyRel (g₀.comp f.hom) (ContinuousMap.id X) {x} :=
    (returnHomotopyRel ex ex x HLU₀).cast
      (return_left_original_comp ex ey f.hom gU.hom) (conjugateMap_id ex.symm)
  let HR₀ : ContinuousMap.HomotopyRel (f.hom.comp g₀) (ContinuousMap.id Y) {y} :=
    (returnHomotopyRel ey ey y HRU₀).cast
      (return_right_original_comp ex ey f.hom gU.hom) (conjugateMap_id ey.symm)
  exact ⟨g, hg,
    ⟨HL₀.cast (TopCat.hom_comp f g).symm (TopCat.hom_id (X := X)).symm⟩,
    ⟨HR₀.cast (TopCat.hom_comp g f).symm (TopCat.hom_id (X := Y)).symm⟩⟩



/-- For separately sized originals, the native original arrow is represented in
ONLY their minimum common universe. Model universes do not enter this input. -/
private theorem four_independent_carriers
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (CX : TopCat.{w}) (CY : TopCat.{z}) [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0)
    (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
    (hjx : Topology.CWComplex.map 0 jx ![] = cx)
    (hjy : Topology.CWComplex.map 0 jy ![] = cy)
    (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
    (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
    (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
    (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
    (f : C(X, Y)) (hxy : f x = y)
    (hf : TopCat.weakHomotopyEquivalences
      (TopCat.minimumCommonCarrierMap f)) :
    ∃ g : C(Y, X), g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y}) := by
  let X₀ : TopCat.{max u v} := TopCat.of (ULift.{v} X)
  let Y₀ : TopCat.{max u v} := TopCat.of (ULift.{u} Y)
  let ex : X ≃ₜ X₀ := Homeomorph.ulift.symm
  let ey : Y ≃ₜ Y₀ := Homeomorph.ulift.symm
  let icx : CX ≃ₜ CX := Homeomorph.refl CX
  let icy : CY ≃ₜ CY := Homeomorph.refl CY
  let rx₀ : C(X₀, CX) := conjugateMap ex icx rx
  let sx₀ : C(CX, X₀) := conjugateMap icx ex sx
  let ry₀ : C(Y₀, CY) := conjugateMap ey icy ry
  let sy₀ : C(CY, Y₀) := conjugateMap icy ey sy
  have hrx₀ : rx₀ (ex x) = cx := by rw [conjugateMap_point, hrx]; rfl
  have hsx₀ : sx₀ cx = ex x := by
    change conjugateMap icx ex sx (icx cx) = ex x
    rw [conjugateMap_point, hsx]
  have hry₀ : ry₀ (ey y) = cy := by rw [conjugateMap_point, hry]; rfl
  have hsy₀ : sy₀ cy = ey y := by
    change conjugateMap icy ey sy (icy cy) = ey y
    rw [conjugateMap_point, hsy]
  let LX₀ : ContinuousMap.HomotopyRel (sx₀.comp rx₀) (ContinuousMap.id X₀) {ex x} :=
    (conjugateHomotopyRel ex ex x LX).cast
      (conjugateMap_comp ex icx ex rx sx) (conjugateMap_id ex)
  let RX₀ : ContinuousMap.HomotopyRel (rx₀.comp sx₀) (ContinuousMap.id CX) {cx} :=
    (conjugateHomotopyRel icx icx cx RX).cast
      (conjugateMap_comp icx ex icx sx rx) (conjugateMap_id icx)
  let LY₀ : ContinuousMap.HomotopyRel (sy₀.comp ry₀) (ContinuousMap.id Y₀) {ey y} :=
    (conjugateHomotopyRel ey ey y LY).cast
      (conjugateMap_comp ey icy ey ry sy) (conjugateMap_id ey)
  let RY₀ : ContinuousMap.HomotopyRel (ry₀.comp sy₀) (ContinuousMap.id CY) {cy} :=
    (conjugateHomotopyRel icy icy cy RY).cast
      (conjugateMap_comp icy ey icy sy ry) (conjugateMap_id icy)
  let f₀ : X₀ ⟶ Y₀ := TopCat.minimumCommonCarrierMap f
  have hf₀_hom : f₀.hom = conjugateMap ex ey f := by
    apply ContinuousMap.ext
    intro q
    change TopCat.minimumCommonCarrierMap f q = (ULift.up (f q.down) : ULift.{u} Y)
    exact TopCat.minimumCommonCarrierMap_apply f q
  have hf₀ : TopCat.weakHomotopyEquivalences f₀ := hf
  have hxy₀ : f₀ (ex x) = ey y := by
    change TopCat.minimumCommonCarrierMap f (ULift.up x) = (ULift.up y : ULift.{u} Y)
    rw [TopCat.minimumCommonCarrierMap_apply, hxy]
  obtain ⟨g₀, hg₀, ⟨HL₀⟩, ⟨HR₀⟩⟩ :=
    independent_native_CW_models X₀ Y₀ CX CY (ex x) (ey y) cx cy jx jy hjx hjy
      rx₀ sx₀ ry₀ sy₀ hrx₀ hsx₀ hry₀ hsy₀ LX₀ RX₀ LY₀ RY₀ f₀ hxy₀ hf₀
  let g : C(Y, X) := conjugateMap ey.symm ex.symm g₀.hom
  have hg : g y = x := by
    change ex.symm (g₀ (ey y)) = x
    rw [hg₀, ex.symm_apply_apply]
  let HL₁ : ContinuousMap.HomotopyRel
      (g₀.hom.comp (conjugateMap ex ey f)) (ContinuousMap.id X₀) {ex x} :=
    HL₀.cast
      ((TopCat.hom_comp f₀ g₀).trans (congrArg (fun k => g₀.hom.comp k) hf₀_hom))
      (TopCat.hom_id (X := X₀))
  let HR₁ : ContinuousMap.HomotopyRel
      ((conjugateMap ex ey f).comp g₀.hom) (ContinuousMap.id Y₀) {ey y} :=
    HR₀.cast
      ((TopCat.hom_comp g₀ f₀).trans (congrArg (fun k => k.comp g₀.hom) hf₀_hom))
      (TopCat.hom_id (X := Y₀))
  let HL : ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x} :=
    (returnHomotopyRel ex ex x HL₁).cast
      (return_left_original_comp ex ey f g₀.hom) (conjugateMap_id ex.symm)
  let HR : ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y} :=
    (returnHomotopyRel ey ey y HR₁).cast
      (return_right_original_comp ex ey f g₀.hom) (conjugateMap_id ey.symm)
  exact ⟨g, hg, ⟨HL⟩, ⟨HR⟩⟩


end CWIndependentUniverseSource101

public section

namespace Topology.CWComplex

/-- Transport the actual given based CW models from independent universes,
retaining the ORIGINAL weak morphism and both original point-relative families. -/
theorem basedCWTypeWhiteheadIndependentModels
    (X Y : TopCat.{u}) (CX : TopCat.{v}) (CY : TopCat.{w})
    [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0)
    (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
    (hjx : Topology.CWComplex.map 0 jx ![] = cx)
    (hjy : Topology.CWComplex.map 0 jy ![] = cy)
    (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
    (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
    (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
    (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
    (f : X ⟶ Y) (hxy : f x = y) (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : Y ⟶ X, g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom
        (TopCat.Hom.hom (𝟙 X)) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom
        (TopCat.Hom.hom (𝟙 Y)) {y})  := by
  exact CWIndependentUniverseSource101.independent_native_CW_models
    X Y CX CY x y cx cy jx jy hjx hjy rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf

/-- Independently sized original carriers and genuine based CW models
have a based Whitehead inverse for the literal original continuous map.
Weakness is required only for that original map in its minimum common
universe; the model universes do not enter the weak-map premise. Both
singleton-relative inverse families return to the original carriers. This
specializes the existing general transport proof without a new framework. -/
theorem basedCWTypeWhiteheadIndependentCarriers
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (CX : TopCat.{w}) (CY : TopCat.{z}) [T2Space CX] [T2Space CY]
    [Topology.CWComplex (Set.univ : Set CX)] [Topology.CWComplex (Set.univ : Set CY)]
    (x : X) (y : Y) (cx : CX) (cy : CY)
    (jx : Topology.CWComplex.cell (Set.univ : Set CX) 0)
    (jy : Topology.CWComplex.cell (Set.univ : Set CY) 0)
    (hjx : Topology.CWComplex.map 0 jx ![] = cx)
    (hjy : Topology.CWComplex.map 0 jy ![] = cy)
    (rx : C(X, CX)) (sx : C(CX, X)) (ry : C(Y, CY)) (sy : C(CY, Y))
    (hrx : rx x = cx) (hsx : sx cx = x) (hry : ry y = cy) (hsy : sy cy = y)
    (LX : ContinuousMap.HomotopyRel (sx.comp rx) (ContinuousMap.id X) {x})
    (RX : ContinuousMap.HomotopyRel (rx.comp sx) (ContinuousMap.id CX) {cx})
    (LY : ContinuousMap.HomotopyRel (sy.comp ry) (ContinuousMap.id Y) {y})
    (RY : ContinuousMap.HomotopyRel (ry.comp sy) (ContinuousMap.id CY) {cy})
    (f : C(X, Y)) (hxy : f x = y)
    (hf : TopCat.weakHomotopyEquivalences
      (TopCat.minimumCommonCarrierMap f)) :
    ∃ g : C(Y, X), g y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (g.comp f) (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (f.comp g) (ContinuousMap.id Y) {y}) := by
  exact CWIndependentUniverseSource101.four_independent_carriers
    CX CY x y cx cy jx jy hjx hjy rx sx ry sy hrx hsx hry hsy LX RX LY RY f hxy hf

end Topology.CWComplex

namespace TopCat

/-- The actual universe-lift functor preserves original weak homotopy
equivalences. This reuses the existing Brown/whole-boundary transport proof. -/
theorem uliftFunctor_map_mem_weakHomotopyEquivalences
    {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : TopCat.weakHomotopyEquivalences f) :
    TopCat.weakHomotopyEquivalences (TopCat.uliftFunctor.{v, u}.map f) := by
  exact CWIndependentUniverseSource101.original_weak_map_ulift f hf

end TopCat

universe a b

namespace TopCat

/-- A source homeomorphism transports the actual point-path retuning of an
original equivalence through a common-universe model. Both original endpoint
points, both whole relative inverse families and the complete prescribed
point trace return to the independently sized original source carrier. -/
public theorem exists_pointRelativeEquivalence_of_sourceHomeomorph
    (X : TopCat.{a}) (M Y : TopCat.{b}) (x : X) (m : M) (y : Y)
    (h : M ≃ₜ X) (hm : h m = x)
    (e₀ : ContinuousMap.HomotopyEquiv X Y) (p₀ : Path (e₀.toFun x) y)
    (hHEP : TopCat.IsHurewiczCofibration
      (TopCat.const m : TopCat.of PUnit.{b + 1} ⟶ M))
    [Cofibration (TopCat.const m : TopCat.of PUnit.{b + 1} ⟶ M)]
    [Cofibration (TopCat.const y : TopCat.of PUnit.{b + 1} ⟶ Y)] :
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun x = y ∧ e.invFun y = x ∧
      Nonempty (ContinuousMap.HomotopyRel (e.invFun.comp e.toFun)
        (ContinuousMap.id X) {x}) ∧
      Nonempty (ContinuousMap.HomotopyRel (e.toFun.comp e.invFun)
        (ContinuousMap.id Y) {y}) ∧
      ∃ K : ContinuousMap.Homotopy e₀.toFun e.toFun,
        ∀ t : unitInterval, K (t, x) = p₀ t := by
  let eH : ContinuousMap.HomotopyEquiv M X := h.toHomotopyEquiv
  have hForward (q : M) : eH.toFun q = h q := rfl
  have hInverse (q : X) : eH.invFun q = h.symm q := rfl
  have hForwardInverse (q : X) : eH.toFun (eH.invFun q) = q :=
    (hForward (eH.invFun q)).trans
      ((congrArg h (hInverse q)).trans (h.apply_symm_apply q))
  have hInverseForward (q : M) : eH.invFun (eH.toFun q) = q :=
    (hInverse (eH.toFun q)).trans
      ((congrArg h.symm (hForward q)).trans (h.symm_apply_apply q))
  have hmx : eH.toFun m = x := (hForward m).trans hm
  let eM : ContinuousMap.HomotopyEquiv M Y := eH.trans e₀
  have hmi : eH.invFun x = m :=
    (hInverse x).trans ((congrArg h.symm hm).symm.trans (h.symm_apply_apply m))
  let p : Path (eM.toFun m) y :=
    p₀.cast
      (congrArg e₀.toFun hmx) rfl
  let i : TopCat.of PUnit.{b + 1} ⟶ M := TopCat.const m
  let H : C(unitInterval × PUnit.{b + 1}, Y) :=
    p.toContinuousMap.comp ContinuousMap.fst
  have h0 : ∀ q : PUnit.{b + 1}, H (0, q) = eM.toFun (i q) :=
    fun q => p.source
  let d : HomotopyExtensionData i.hom eM.toFun H h0 :=
    Classical.choice (hHEP eM.toFun H h0)
  let K : ContinuousMap.Homotopy eM.toFun d.endpoint := d.toHomotopy
  let f : M ⟶ Y := TopCat.ofHom d.endpoint
  have hfy : f m = y := (d.extension_subspace 1 (PUnit.unit : PUnit.{b + 1})).trans p.target
  let eRetuned : ContinuousMap.HomotopyEquiv M Y :=
    { toFun := d.endpoint
      invFun := eM.invFun
      left_inv := ⟨((ContinuousMap.Homotopy.refl eM.invFun).comp K.symm).trans
        eM.left_inv.some⟩
      right_inv := ⟨(K.symm.comp (ContinuousMap.Homotopy.refl eM.invFun)).trans
        eM.right_inv.some⟩ }
  have hf : TopCat.weakHomotopyEquivalences f := TopCat.mem_of_eq_toFun eRetuned rfl
  obtain ⟨g, hg, ⟨LG⟩, ⟨RG⟩⟩ :=
    TopCat.exists_based_inverse_of_weak_of_cofibrant_points M Y m y f hfy hf
  let f₀ : C(X, Y) := f.hom.comp eH.invFun
  let g₀ : C(Y, X) := eH.toFun.comp g.hom
  have hf₀ : f₀ x = y := (congrArg f hmi).trans hfy
  have hg₀ : g₀ y = x := (congrArg eH.toFun hg).trans hmx
  let L₀ := (LG.compContinuousMap eH.toFun).precomposePointRelative eH.invFun x hmi
  have hLstart :
      (eH.toFun.comp (f ≫ g).hom).comp eH.invFun = g₀.comp f₀ := rfl
  have hLend :
      (eH.toFun.comp (𝟙 M : M ⟶ M).hom).comp eH.invFun =
        ContinuousMap.id X := by
    apply ContinuousMap.ext
    intro q
    exact hForwardInverse q
  let LX : ContinuousMap.HomotopyRel (g₀.comp f₀) (ContinuousMap.id X) {x} :=
    L₀.cast hLstart hLend
  have hRstart : (g ≫ f).hom = f₀.comp g₀ := by
    apply ContinuousMap.ext
    intro q
    exact (congrArg f (hInverseForward (g q))).symm
  let RY : ContinuousMap.HomotopyRel (f₀.comp g₀) (ContinuousMap.id Y) {y} :=
    RG.cast hRstart (TopCat.hom_id (X := Y))
  let e : ContinuousMap.HomotopyEquiv X Y :=
    { toFun := f₀
      invFun := g₀
      left_inv := ⟨LX.toHomotopy⟩
      right_inv := ⟨RY.toHomotopy⟩ }
  have hOld : eM.toFun.comp eH.invFun = e₀.toFun := by
    apply ContinuousMap.ext
    intro q
    exact congrArg e₀.toFun (hForwardInverse q)
  let KO : ContinuousMap.Homotopy e₀.toFun f₀ :=
    (K.compContinuousMap eH.invFun).cast hOld rfl
  refine ⟨e, hf₀, hg₀, ⟨LX⟩, ⟨RY⟩, KO, ?_⟩
  intro t
  change d.toHomotopy (t, eH.invFun x) = p₀ t
  exact (congrArg (fun q : M => d.toHomotopy (t, q)) hmi).trans
    (d.extension_subspace t (PUnit.unit : PUnit.{b + 1}))


end TopCat
