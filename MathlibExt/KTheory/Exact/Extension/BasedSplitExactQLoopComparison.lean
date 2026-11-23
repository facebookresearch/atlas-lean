/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.SplitExactOriginalComparisons
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberBasedComparison
public import MathlibExt.KTheory.Exact.Extension.OriginalZeroHomotopyFiberLoopPointPairEquivalence
public import MathlibExt.Topology.CWComplex.BasedWhiteheadUniverseLift
public import MathlibExt.Topology.Homotopy.RawLoopCWPointModel
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff

/-!
# The full based split-exact original Q-loop comparison

The canonical completed-Core realization has its actual classical CW structure
and literal unit zero cell. The actual Q realization similarly supplies the
point NDR and CW inputs for the constructed raw-loop CW model. Transport that
model through the already constructed original zero-fiber/loop equivalence,
then apply the existing based CW Whitehead theorem to the original weak fiber
comparison. Its inverse and both actual point-relative homotopies compose
with the original full-path return into the entire raw Q-loop space.

The only additional mathematical input is splitness of the original admissible
rows. No CW model, inverse, point match,
relative witness, countability or original-space Hausdorffness is supplied.
The canonical K0 component comparison and independent plus construction are
separate obligations.
-/

public section

universe u v w

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial Topology ZeroObject

namespace AlgebraicKTheory.BasedSplitExactQLoop

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction
attribute [local instance] ExtensionCategory.localizedTarget_isFibered

/-- The original completed-Core nerve realization, on every component. -/
abbrev completedCoreSpace : TopCat.{max u v} :=
  SSet.toTop.obj (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})

/-- The literal realized positive image of the original Core unit. -/
abbrev completedCorePoint : completedCoreSpace (C := C) :=
  SSet.realizedVertex (ComposableArrows.mk₀
    ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C))))

/-- The whole original zero homotopy fiber, with its raw compact-open path coordinate. -/
abbrev originalZeroFiber : TopCat.{max u v} :=
  TopCat.homotopyFiber
    (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
      (ExtensionCategory.localizedTarget (C := C))))
    (OriginalQZeroComparison.zeroQVertex (C := C))

/-- The independently constructed total-and-constant-path point in the original fiber. -/
abbrev selectedZeroFiberPoint : originalZeroFiber (C := C) :=
  TopCat.homotopyFiberSelectedPointMap
    (SSet.toTop.map (nerveMapCommonHom.{u, max u v, 0}
      (ExtensionCategory.localizedTarget (C := C))))
    (OriginalQZeroComparison.zeroTotalVertex (C := C))
    (OriginalQZeroComparison.zeroQVertex (C := C))
    (OriginalQZeroComparison.zeroTotalVertex_map (C := C)) PUnit.unit

/-- The entire original raw Q-loop space at the literal Q-zero vertex. -/
abbrev originalQLoops : TopCat.{max u v} :=
  TopCat.of (LoopSpace (SSet.toTop.obj (nerve (QuillenQ C) : SSet.{max u v}))
    (OriginalQZeroComparison.zeroQVertex (C := C)))

/-- The literal constant loop in that entire original loop space. -/
abbrev constantQLoop : originalQLoops (C := C) :=
  Path.refl (OriginalQZeroComparison.zeroQVertex (C := C))

/-- The existing original completed-Core comparison followed by the existing full-path return. -/
abbrev comparisonMap : completedCoreSpace (C := C) ⟶ originalQLoops (C := C) :=
  OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C) ≫
    OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)

private def whiskerAtPoint {A B Z T : Type w}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z] [TopologicalSpace T]
    {f g : C(A, B)} (a : A) (H : ContinuousMap.HomotopyRel f g {a})
    (p : C(Z, A)) (q : C(B, T)) (z₀ : Z) (hp : p z₀ = a) :
    ContinuousMap.HomotopyRel (q.comp (f.comp p)) (q.comp (g.comp p)) {z₀} where
  toHomotopy := (ContinuousMap.Homotopy.refl q).comp
    (H.toHomotopy.compContinuousMap p)
  prop' t z hz := by
    have hzpoint : z = z₀ := Set.mem_singleton_iff.mp hz
    subst z
    change q (H (t, p z₀)) = q (f (p z₀))
    rw [hp]
    exact congrArg q (H.eq_fst t (Set.mem_singleton_iff.mpr rfl))

/-- The actual full fiber and raw-loop inverses, tied to the original forward maps and points. -/
structure ComparisonData where
  /-- The return from the original full zero fiber to the entire completed-Core realization. -/
  fiberInverse : C(originalZeroFiber (C := C), completedCoreSpace (C := C))
  /-- The fiber return preserves the independently selected point. -/
  fiberInverse_point : fiberInverse (selectedZeroFiberPoint (C := C)) = completedCorePoint (C := C)
  /-- The original completed-Core inverse family, fixed at its literal unit. -/
  fiberSourceHomotopy : ContinuousMap.HomotopyRel
    (fiberInverse.comp (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)).hom)
    (ContinuousMap.id (completedCoreSpace (C := C))) {completedCorePoint (C := C)}
  /-- The original fiber inverse family, fixed at its independent full selected point. -/
  fiberTargetHomotopy : ContinuousMap.HomotopyRel
    ((OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)).hom.comp fiberInverse)
    (ContinuousMap.id (originalZeroFiber (C := C))) {selectedZeroFiberPoint (C := C)}
  /-- The return from all original raw Q loops to the original completed-Core realization. -/
  loopInverse : C(originalQLoops (C := C), completedCoreSpace (C := C))
  /-- This same loop return is the original selected-loop inclusion followed by the fiber
  inverse. -/
  loopInverse_eq : loopInverse =
    fiberInverse.comp (OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber (C := C)).hom
  /-- The loop return preserves the literal constant loop and completed unit. -/
  loopInverse_point : loopInverse (constantQLoop (C := C)) = completedCorePoint (C := C)
  /-- Both original completed-Core maps compose to the identity relative to the unit. -/
  loopSourceHomotopy : ContinuousMap.HomotopyRel
    (loopInverse.comp (comparisonMap (C := C)).hom)
    (ContinuousMap.id (completedCoreSpace (C := C))) {completedCorePoint (C := C)}
  /-- Both original loop maps compose to the identity relative to the constant loop. -/
  loopTargetHomotopy : ContinuousMap.HomotopyRel
    ((comparisonMap (C := C)).hom.comp loopInverse)
    (ContinuousMap.id (originalQLoops (C := C))) {constantQLoop (C := C)}

/-- The actual original completed unit is sent to the literal constant Q loop. -/
theorem comparisonMap_point :
    comparisonMap (C := C) (completedCorePoint (C := C)) = constantQLoop (C := C) := by
  have hκ := ConcreteCategory.congr_hom
    (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_selectedPoint (C := C))
    PUnit.unit
  have hr := ConcreteCategory.congr_hom
    (OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_selectedPoint (C := C)) PUnit.unit
  change OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)
    (completedCorePoint (C := C)) = selectedZeroFiberPoint (C := C) at hκ
  change OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)
    (selectedZeroFiberPoint (C := C)) = constantQLoop (C := C) at hr
  exact (TopCat.comp_app _ _ _).trans ((congrArg
    (OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)) hκ).trans hr)

/-- Construct the full original based split-exact comparison with actual return maps
and both point-relative families on both the original fiber and raw-loop spaces. -/
def comparison
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ComparisonData (C := C) := by
  classical
  let NK : SSet.{max u v} := nerve (SInverse (Core C) (Core C))
  let NQ : SSet.{max u v} := nerve (QuillenQ C)
  let A : TopCat.{max u v} := completedCoreSpace (C := C)
  let H : TopCat.{max u v} := originalZeroFiber (C := C)
  let Q : TopCat.{max u v} := SSet.toTop.obj NQ
  let L : TopCat.{max u v} := originalQLoops (C := C)
  let x : A := completedCorePoint (C := C)
  let z : H := selectedZeroFiberPoint (C := C)
  let b : Q := OriginalQZeroComparison.zeroQVertex (C := C)
  let y : L := constantQLoop (C := C)
  let κ : A ⟶ H := OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber (C := C)
  let r₀ : H ⟶ L := OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops (C := C)
  let j₀ : L ⟶ H := OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber (C := C)
  have hκ : κ x = z := ConcreteCategory.congr_hom
    (OriginalQZeroComparison.completedCoreToOriginalHomotopyFiber_unit_selectedPoint (C := C))
    PUnit.unit
  have hr₀ : r₀ z = y := ConcreteCategory.congr_hom
    (OriginalQZeroComparison.zeroOriginalHomotopyFiberToLoops_selectedPoint (C := C)) PUnit.unit
  have hj₀ : j₀ y = z := ConcreteCategory.congr_hom
    (OriginalQZeroComparison.zeroLoopToOriginalHomotopyFiber_constant_point (C := C)) PUnit.unit
  let HF : ContinuousMap.HomotopyRel (j₀.hom.comp r₀.hom)
      (ContinuousMap.id H) {z} :=
    (OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_leftHomotopyRel (C := C)).cast
      (by rw [OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_invFun,
        OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_toFun]) rfl
  let HL : ContinuousMap.HomotopyRel (r₀.hom.comp j₀.hom)
      (ContinuousMap.id L) {y} :=
    (OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_rightHomotopyRel (C := C)).cast
      (by rw [OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_invFun,
        OriginalQZeroComparison.zeroOriginalHomotopyFiberLoopEquiv_toFun]) rfl
  letI : T2Space A := SSet.realization_t2Space NK
  letI : Topology.CWComplex (Set.univ : Set A) := SSet.instCWComplexToTop NK
  let vK : NK _⦋0⦌ := ComposableArrows.mk₀
    ((SInverse.inclusion (Core C) (Core C)).obj (𝟙_ (Core C)))
  let vQ : NQ _⦋0⦌ := ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)
  letI : T2Space Q := SSet.realization_t2Space NQ
  letI : Topology.CWComplex (Set.univ : Set Q) := SSet.instCWComplexToTop NQ
  let hKcell := SSet.realizedVertex_is_classical_zeroCell vK
  let hQcell := SSet.realizedVertex_is_classical_zeroCell vQ
  let kcell := Classical.choose hKcell
  let qcell := Classical.choose hQcell
  have hkcell : Topology.CWComplex.map 0 kcell ![] = x := Classical.choose_spec hKcell ![]
  have hqcell : Topology.CWComplex.map 0 qcell ![] = b := Classical.choose_spec hQcell ![]
  let PQ : PointedTopCat.{max u v} :=
    { left := Discrete.mk PUnit.unit, right := Q, hom := TopCat.const b }
  let dQ : TopPair.StandardNDRData (PointedTopCat.pointedPair.obj PQ) := by
    change TopPair.StandardNDRData (SSet.realizedVertexPair vQ)
    exact SSet.realizedVertexStandardNDRData vQ
  let IQ : ContinuousMap.HomotopyRel
      ((ContinuousMap.id Q).comp (ContinuousMap.id Q)) (ContinuousMap.id Q) {b} :=
    ContinuousMap.HomotopyRel.refl (ContinuousMap.id Q) {b}
  let M := PointedTopCat.rawLoopCWPointModel PQ dQ Q b qcell hqcell
    (ContinuousMap.id Q) (ContinuousMap.id Q) rfl rfl IQ IQ
  letI : T2Space M.model := M.hausdorff
  letI : Topology.CWComplex (Set.univ : Set M.model) := M.cw
  let RH : C(H, M.model) := M.toModel.comp r₀.hom
  let SH : C(M.model, H) := j₀.hom.comp M.fromModel
  have hRH : RH z = M.point := (congrArg M.toModel hr₀).trans M.toModel_point
  have hSH : SH M.point = z := (congrArg j₀.hom M.fromModel_point).trans hj₀
  let FH := whiskerAtPoint y M.originalHomotopy r₀.hom j₀.hom z hr₀
  let FY := whiskerAtPoint y HL M.fromModel M.toModel M.point M.fromModel_point
  let LH : ContinuousMap.HomotopyRel (SH.comp RH) (ContinuousMap.id H) {z} :=
    (FH.cast rfl rfl).trans HF
  let RM : ContinuousMap.HomotopyRel (RH.comp SH) (ContinuousMap.id M.model) {M.point} :=
    (FY.cast rfl rfl).trans M.modelHomotopy
  let IA : ContinuousMap.HomotopyRel
      ((ContinuousMap.id A).comp (ContinuousMap.id A)) (ContinuousMap.id A) {x} :=
    ContinuousMap.HomotopyRel.refl (ContinuousMap.id A) {x}
  have hWeak : TopCat.weakHomotopyEquivalences κ :=
    SplitExactOriginalComparisons.splitExactCompletedCoreToOriginalHomotopyFiber_weak hSplit
  have hInverse := Topology.CWComplex.basedCWTypeWhiteheadIndependentModels
    A H A M.model x z x M.point kcell M.zeroCell hkcell (M.zeroCell_value ![])
    (ContinuousMap.id A) (ContinuousMap.id A) RH SH rfl rfl hRH hSH IA IA LH RM κ hκ hWeak
  let g : H ⟶ A := Classical.choose hInverse
  have hg := Classical.choose_spec hInverse
  let G : C(H, A) := g.hom
  let GK : ContinuousMap.HomotopyRel (G.comp κ.hom) (ContinuousMap.id A) {x} :=
    (Classical.choice hg.2.1).cast (TopCat.hom_comp κ g) rfl
  let GH : ContinuousMap.HomotopyRel (κ.hom.comp G) (ContinuousMap.id H) {z} :=
    (Classical.choice hg.2.2).cast (TopCat.hom_comp g κ) rfl
  let inverseLoopMap : C(L, A) := G.comp j₀.hom
  have hGL : inverseLoopMap y = x := (congrArg G hj₀).trans hg.1
  let FK := whiskerAtPoint z HF κ.hom G x hκ
  let FL := whiskerAtPoint z GH j₀.hom r₀.hom y hj₀
  let KL : ContinuousMap.HomotopyRel (inverseLoopMap.comp (comparisonMap (C := C)).hom)
      (ContinuousMap.id A) {x} := (FK.cast rfl rfl).trans GK
  let LL : ContinuousMap.HomotopyRel ((comparisonMap (C := C)).hom.comp inverseLoopMap)
      (ContinuousMap.id L) {y} := (FL.cast rfl rfl).trans HL
  exact
    { fiberInverse := G
      fiberInverse_point := hg.1
      fiberSourceHomotopy := GK
      fiberTargetHomotopy := GH
      loopInverse := inverseLoopMap
      loopInverse_eq := rfl
      loopInverse_point := hGL
      loopSourceHomotopy := KL
      loopTargetHomotopy := LL }

/-- The full homotopy equivalence has exactly the original comparison as forward map. -/
def homotopyEquiv
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    ContinuousMap.HomotopyEquiv (completedCoreSpace (C := C)) (originalQLoops (C := C)) := by
  let D := comparison hSplit
  exact
    { toFun := (comparisonMap (C := C)).hom
      invFun := D.loopInverse
      left_inv := ⟨D.loopSourceHomotopy.toHomotopy⟩
      right_inv := ⟨D.loopTargetHomotopy.toHomotopy⟩ }

/-- The returned equivalence uses the same literal original forward comparison. -/
theorem homotopyEquiv_toFun
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    (homotopyEquiv hSplit).toFun = (comparisonMap (C := C)).hom := by
  rfl

/-- The actual inverse of the full original loop equivalence is the
inverse stored in the same constructed comparison data. -/
theorem homotopyEquiv_invFun
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting) :
    (homotopyEquiv hSplit).invFun = (comparison hSplit).loopInverse := by
  unfold homotopyEquiv
  rfl

end AlgebraicKTheory.BasedSplitExactQLoop

end
