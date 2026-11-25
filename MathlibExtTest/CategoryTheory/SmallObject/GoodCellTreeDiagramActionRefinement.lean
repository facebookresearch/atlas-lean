/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionRefinement
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramActionCapture

/-!
# Whole original Nat actions and genuine delayed equality semantics

The real public constructor chooses its own original chain. Its original
source colimit, every original stage leg, whole object/action functions,
root and endpoint natural transformations and strict factorization are
inspected on the complete infinite nonthin index. Distinct raw maps from
a source compact under its noncompact root become equal only through the
same actual larger lower support. Empty and identity-only indices use the
same real constructors.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  DiagramActionCapture DiagramActionRefinement BoundedLowerSupport

namespace OriginalDiagramActionRefinementExamples

open DiagramActionConstraintBoundExamples GoodCellTreeDataExamples
  OriginalDiagramActionCaptureExamples

/-- The actual original chain is internally constructed from the same primitive data and seeds. -/
def originalChain (B : Supports (P := originalLabels) chi) :
    RefinementChain originalTrees.{t} originalLower.{t} chi B :=
  refinementChain originalTrees.{t} originalLower.{t} chi originalArrowBound originalTrees_good.{t} B

/-- A real first unit-enforced capture, selected without a desired unit premise. -/
def originalUnitalStage (B : Supports (P := originalLabels) chi) :
    UnitalStage originalTrees.{t} originalLower.{t} chi B :=
  Classical.choice (nonemptyUnitalStage originalTrees.{t} originalLower.{t} chi
    originalArrowBound originalTrees_good.{t} B)

/-- The actual next refinement takes the SAME internally selected first factors. -/
def originalRefinedStage (B : Supports (P := originalLabels) chi) :
    RefinedStage originalTrees.{t} originalLower.{t} chi B (originalUnitalStage.{t} B).target
      (originalUnitalStage.{t} B).le (originalUnitalStage.{t} B).factors :=
  Classical.choice (nonemptyRefinedStage originalTrees.{t} originalLower.{t} chi
    originalArrowBound originalTrees_good.{t} B (originalUnitalStage.{t} B).target
      (originalUnitalStage.{t} B).le (originalUnitalStage.{t} B).factors)

/-- Actual unit enforcement yields precisely the original L comparison at each original object. -/
theorem originalUnitalStage_units (B : Supports (P := originalLabels) chi) (d : OriginalIndex) :
    (originalUnitalStage.{t} B).factors.map (𝟙 d) =
      ((originalLower.{t} d).map ((originalUnitalStage.{t} B).le d)).right :=
  (originalUnitalStage.{t} B).unit d

/-- Every original arrow has the exact old/new ladder equality on the real refinement output. -/
theorem originalRefinedStage_ladder (B : Supports (P := originalLabels) chi)
    {d e : OriginalIndex} (g : d ⟶ e) :
    (originalUnitalStage.{t} B).factors.map g ≫
        ((originalLower.{t} e).map ((originalRefinedStage.{t} B).le e)).right =
      ((originalLower.{t} d).map ((originalUnitalStage.{t} B).le d)).right ≫
        (originalRefinedStage.{t} B).factors.map g :=
  (originalRefinedStage.{t} B).ladder g

/-- Delayed composition retains both original g/h values and the original intermediate object. -/
theorem originalRefinedStage_composition (B : Supports (P := originalLabels) chi)
    {d m e : OriginalIndex} (g : d ⟶ m) (h : m ⟶ e) :
    (originalUnitalStage.{t} B).factors.map g ≫ (originalRefinedStage.{t} B).factors.map h =
      (originalUnitalStage.{t} B).factors.map (g ≫ h) ≫
        ((originalLower.{t} e).map ((originalRefinedStage.{t} B).le e)).right :=
  (originalRefinedStage.{t} B).composition g h

/-- The two distinct actual pair labels each receive the real delayed composition certificate. -/
theorem originalRefinedStage_parallel_pairs (B : Supports (P := originalLabels) chi) :
    firstPair ≠ secondPair ∧
      ((originalUnitalStage.{t} B).factors.map firstArrow ≫
          (originalRefinedStage.{t} B).factors.map lastArrow =
        (originalUnitalStage.{t} B).factors.map (firstArrow ≫ lastArrow) ≫
          ((originalLower.{t} targetSeven).map ((originalRefinedStage.{t} B).le targetSeven)).right) ∧
      ((originalUnitalStage.{t} B).factors.map secondArrow ≫
          (originalRefinedStage.{t} B).factors.map lastArrow =
        (originalUnitalStage.{t} B).factors.map (secondArrow ≫ lastArrow) ≫
          ((originalLower.{t} targetSeven).map ((originalRefinedStage.{t} B).le targetSeven)).right) :=
  ⟨originalPairLabelsDifferent, originalRefinedStage_composition.{t} B firstArrow lastArrow,
    originalRefinedStage_composition.{t} B secondArrow lastArrow⟩

/-- Every stage unit in the internally selected Nat chain is its actual original inclusion. -/
theorem originalChain_units (B : Supports (P := originalLabels) chi) (n : ℕ) (d : OriginalIndex) :
    ((originalChain.{t} B).factors n).map (𝟙 d) =
      ((originalLower.{t} d).map ((originalChain.{t} B).le n d)).right :=
  (originalChain.{t} B).unit n d

/-- Every actual old/new chain ladder retains its literal original support domains. -/
theorem originalChain_ladders (B : Supports (P := originalLabels) chi) (n : ℕ)
    {d e : OriginalIndex} (g : d ⟶ e) :
    ((originalChain.{t} B).factors n).map g ≫
        ((originalLower.{t} e).map ((originalChain.{t} B).le (n + 1) e)).right =
      ((originalLower.{t} d).map ((originalChain.{t} B).le n d)).right ≫
        ((originalChain.{t} B).factors (n + 1)).map g :=
  (originalChain.{t} B).ladder n g

/-- Every original pair has its exact delayed-composition equality at every actual Nat stage. -/
theorem originalChain_compositions (B : Supports (P := originalLabels) chi) (n : ℕ)
    {d m e : OriginalIndex} (g : d ⟶ m) (h : m ⟶ e) :
    ((originalChain.{t} B).factors n).map g ≫ ((originalChain.{t} B).factors (n + 1)).map h =
      ((originalChain.{t} B).factors n).map (g ≫ h) ≫
        ((originalLower.{t} e).map ((originalChain.{t} B).le (n + 1) e)).right :=
  (originalChain.{t} B).composition n g h

/-- The actual support union is precisely the original supremum, on every original component. -/
theorem originalChain_union_function (B : Supports (P := originalLabels) chi) :
    (fun d => (unionSupport originalTrees.{t} originalLower.{t} chi chi_uncountable
      (originalChain.{t} B) d).1) =
    (fun d => ⨆ n, ((originalChain.{t} B).supports n d).1) := rfl

/-- Its entire actual selected label family is bounded by the genuine original Arrow D premise. -/
theorem originalChain_selected_labels (B : Supports (P := originalLabels) chi) :
    HasCardinalLT (Sigma (fun d : OriginalIndex =>
      ((unionSupport originalTrees.{t} originalLower.{t} chi chi_uncountable (originalChain.{t} B) d).1 :
        Set (originalLabels d)))) chi :=
  total_selected_labels originalTrees.{t} originalLower.{t} chi chi_uncountable (originalChain.{t} B)
    originalArrowBound

/-- The real public slice constructor internally chooses its own original refinement chain. -/
def originalSlice (B : Supports (P := originalLabels) chi) :
    CompatibleSlice originalTrees.{t} originalLower.{t} chi B :=
  actionCompatibleSlice originalTrees.{t} originalLower.{t} chi chi_uncountable
    originalArrowBound originalTrees_good.{t} B

/-- Its whole original support function is the SAME internally chosen countable union. -/
theorem originalSlice_support_function (B : Supports (P := originalLabels) chi) :
    (originalSlice.{t} B).supports =
      unionSupport originalTrees.{t} originalLower.{t} chi chi_uncountable (originalChain.{t} B) := rfl

/-- The whole output functor uses the literal original selected lower-piece objects. -/
theorem originalSlice_object_function (B : Supports (P := originalLabels) chi) :
    (fun d => ((originalSlice.{t} B).toFunctor originalTrees.{t} originalLower.{t} chi).obj d) =
      (fun d => ((originalLower.{t} d).obj ((originalSlice.{t} B).supports d).1).right) := rfl

/-- Every output Hom map is the exact right function of the ORIGINAL source colimit descender. -/
theorem originalSlice_native_descender_function (B : Supports (P := originalLabels) chi) :
    (fun (d e : OriginalIndex) (g : d ⟶ e) => (originalSlice.{t} B).map g) =
      (fun (d e : OriginalIndex) (g : d ⟶ e) =>
        (((originalLower.{t} d).isColimitFilteredCocone
          (B := supportFunctor originalTrees.{t} originalLower.{t} chi (originalChain.{t} B) d)).desc
            (actionCocone originalTrees.{t} originalLower.{t} chi chi_uncountable
              (originalChain.{t} B) g)).right) := rfl

/-- Native fac retains every original source-stage leg and the exact original partial action. -/
theorem originalSlice_all_stage_legs (B : Supports (P := originalLabels) chi) (n : ℕ)
    {d e : OriginalIndex} (g : d ⟶ e) :
    ((originalLower.{t} d).map
      (stage_le_union originalTrees.{t} originalLower.{t} chi chi_uncountable (originalChain.{t} B) d n)).right ≫
        (originalSlice.{t} B).map g =
      ((originalChain.{t} B).factors n).map g ≫ ((originalLower.{t} e).map
        (stage_le_union originalTrees.{t} originalLower.{t} chi chi_uncountable
          (originalChain.{t} B) e (n + 1))).right :=
  action_fac originalTrees.{t} originalLower.{t} chi chi_uncountable (originalChain.{t} B) g n

/-- The actual whole output unit is proved, with the SAME selected coefficient object. -/
theorem originalSlice_unit (B : Supports (P := originalLabels) chi) (d : OriginalIndex) :
    (originalSlice.{t} B).map (𝟙 d) =
      𝟙 ((originalLower.{t} d).obj ((originalSlice.{t} B).supports d).1).right :=
  (originalSlice.{t} B).map_id d

/-- All original composition functions are actual native output laws. -/
theorem originalSlice_composition (B : Supports (P := originalLabels) chi)
    {d m e : OriginalIndex} (g : d ⟶ m) (h : m ⟶ e) :
    (originalSlice.{t} B).map (g ≫ h) = (originalSlice.{t} B).map g ≫ (originalSlice.{t} B).map h :=
  (originalSlice.{t} B).map_comp g h

/-- The original coincident composites have equal output actions, while pair labels remain distinct. -/
theorem originalSlice_parallel_composites (B : Supports (P := originalLabels) chi) :
    firstPair ≠ secondPair ∧
      (originalSlice.{t} B).map firstArrow ≫ (originalSlice.{t} B).map lastArrow =
        (originalSlice.{t} B).map secondArrow ≫ (originalSlice.{t} B).map lastArrow := by
  refine ⟨originalPairLabelsDifferent, ?_⟩
  rw [← originalSlice_composition, ← originalSlice_composition, originalCompositesEqual]

/-- The entire whole root function is the literal original selected lower-piece root. -/
theorem originalSlice_root_function (B : Supports (P := originalLabels) chi) :
    (fun d => ((originalSlice.{t} B).root originalTrees.{t} originalLower.{t} chi).app d) =
      (fun d => ((originalLower.{t} d).obj ((originalSlice.{t} B).supports d).1).hom) := rfl

/-- The entire endpoint function retains the SAME original L, gamma and given tau. -/
theorem originalSlice_endpoint_function (B : Supports (P := originalLabels) chi) :
    (fun d => ((originalSlice.{t} B).target originalTrees.{t} originalLower.{t} chi).app d) =
      (fun d => ((originalLower.{t} d).map
        (le_top : ((originalSlice.{t} B).supports d).1 ≤ ⊤) ≫
          ((originalTrees.{t}.component d).tree.endpointIso (originalLower.{t} d)).hom ≫
            (originalTrees.{t}.component d).endpointIso.hom).right) := by
  funext d
  simp only [CompatibleSlice.target, leg, legUnder, EndpointDiagramTransport.lowerLeg,
    Under.comp_right, Category.assoc]
  rfl

/-- Both original whole natural transformations retain the strict original factorization. -/
theorem originalSlice_strict_factor (B : Supports (P := originalLabels) chi) :
    (originalSlice.{t} B).root originalTrees.{t} originalLower.{t} chi ≫
      (originalSlice.{t} B).target originalTrees.{t} originalLower.{t} chi = originalMap :=
  (originalSlice.{t} B).factor originalTrees.{t} originalLower.{t} chi

/-- The actual nonempty original seed remains in the literal selected original lower support. -/
theorem originalSlice_nonempty_seed_retained (d : OriginalIndex) :
    (⟨originalRootPoint d⟩ : originalLabels d) ∈ ((originalSlice.{t} nonemptySeeds.{t}).supports d).1 :=
  LowerSetColimits.memOfLE ((originalSlice.{t} nonemptySeeds.{t}).le d) (nonemptySeeds_contains.{t} d)

section RawEventualEquality

/-- This is literally the same actual original source coefficient at label seven. -/
abbrev OriginalSourceRoot : Type := originalSource.obj sourceSeven

/-- Its actual original selected point, with the literal original coefficient TYPE. -/
abbrev originalSourcePoint : OriginalSourceRoot := originalRootPoint sourceSeven

/-- The actual original source still has exactly the internally selected rank cardinal. -/
theorem originalSourceRoot_cardinal : Cardinal.mk OriginalSourceRoot = chi := by
  change Cardinal.mk LargeRoot = chi
  exact largeRoot_cardinal

/-- The same actual original source is not bounded strictly below its original chi. -/
theorem originalSourceRoot_not_cardinalLT : ¬ HasCardinalLT OriginalSourceRoot chi := by
  intro h
  have hl := (hasCardinalLT_iff_cardinal_mk_lt OriginalSourceRoot chi).1 h
  rw [originalSourceRoot_cardinal] at hl
  exact lt_irrefl chi hl


/-- An actual second point exists in the SAME original noncompact root. -/
theorem exists_other_original_point : ∃ x : OriginalSourceRoot, x ≠ originalSourcePoint := by
  classical
  by_contra hn
  have hall (x : OriginalSourceRoot) : x = originalSourcePoint := by
    by_contra hx
    exact hn ⟨x, hx⟩
  let : Subsingleton OriginalSourceRoot := ⟨fun x y => (hall x).trans (hall y).symm⟩
  exact originalSourceRoot_not_cardinalLT (hasCardinalLT_of_finite OriginalSourceRoot chi chi_regular.aleph0_le)

/-- Select that original second root point before the equality-family call. -/
def secondRootPoint : OriginalSourceRoot := Classical.choose exists_other_original_point

/-- The original two selected root points are different. -/
theorem secondRootPoint_ne : secondRootPoint ≠ originalSourcePoint :=
  Classical.choose_spec exists_other_original_point

/-- The original source tree's actual empty-lower Iso, on the SAME chosen L object. -/
def originalEmptyIso : (originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1 ≅
    Under.mk (𝟙 OriginalSourceRoot) :=
  (originalTrees.{t}.component sourceSeven).tree.emptyLowerIso (originalLower.{t} sourceSeven)

/-- The actual original point map into the SAME selected empty piece. -/
def originalPoint (x : OriginalSourceRoot) : PUnit.{1} ⟶
    ((originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1).right :=
  (↾fun _ => x) ≫ originalEmptyIso.{t}.inv.right

/-- Its original inverse/hom comparison recovers the SAME selected original point. -/
theorem originalPoint_mapback (x : OriginalSourceRoot) :
    originalPoint.{t} x ≫ originalEmptyIso.{t}.hom.right = (↾fun _ => x) := by
  simp only [originalPoint, Category.assoc, Under.inv_right_hom_right, Under.mk_right, Category.comp_id]

/-- Native costar supplies a genuinely relatively presentable source under this noncompact root. -/
abbrev equalitySource : Under OriginalSourceRoot := (Under.costar OriginalSourceRoot).obj PUnit.{1}

instance equalitySourcePresentable : IsCardinalPresentable equalitySource chi := by
  let : IsCardinalPresentable PUnit.{1} chi :=
    (hasCardinalLT_of_finite PUnit.{1} chi chi_regular.aleph0_le).isCardinalPresentable
  exact UnderColimits.costarPresentable chi PUnit.{1}

/-- Actual raw point maps transpose through the SAME original costar/forget adjunction. -/
def equalityMap (x : OriginalSourceRoot) : equalitySource ⟶
    (originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1 :=
  UnderColimits.transpose (originalPoint.{t} x)

/-- The original right functions remain genuinely different BEFORE any larger-support map. -/
theorem equalityMapsDifferent : (equalityMap.{t} originalSourcePoint).right ≠ (equalityMap.{t} secondRootPoint).right := by
  intro h
  have hUnder := Under.UnderMorphism.ext h
  have hPoint := congrArg ((Under.costarAdjForget OriginalSourceRoot).homEquiv PUnit.{1}
    ((originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1)) hUnder
  have hRaw : originalPoint.{t} originalSourcePoint = originalPoint.{t} secondRootPoint := by
    simpa only [equalityMap, UnderColimits.transpose, Equiv.apply_symm_apply] using hPoint
  have hBack := congrArg (fun k : PUnit.{1} ⟶
    ((originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1).right =>
      k ≫ originalEmptyIso.{t}.hom.right) hRaw
  rw [originalPoint_mapback, originalPoint_mapback] at hBack
  exact secondRootPoint_ne (ConcreteCategory.congr_hom hBack PUnit.unit).symm

/-- The endpoint composites agree on the SAME original tree endpoint and original gamma. -/
theorem equalityMaps_endpoint :
    (equalityMap.{t} originalSourcePoint).right ≫
        ((originalLower.{t} sourceSeven).map (le_top : (emptySeeds sourceSeven).1 ≤ ⊤) ≫
          ((originalTrees.{t}.component sourceSeven).tree.endpointIso (originalLower.{t} sourceSeven)).hom).right =
      (equalityMap.{t} secondRootPoint).right ≫
        ((originalLower.{t} sourceSeven).map (le_top : (emptySeeds sourceSeven).1 ≤ ⊤) ≫
          ((originalTrees.{t}.component sourceSeven).tree.endpointIso (originalLower.{t} sourceSeven)).hom).right := by
  let e := (originalTrees.{t}.component sourceSeven).endpointIso
  let : Mono e.hom.right := by
    change Mono ((Under.forget OriginalSourceRoot).map e.hom)
    infer_instance
  apply (cancel_mono e.hom.right).1
  ext x
  change (_ : PUnit.{1}) = _
  exact Subsingleton.elim _ _

/-- A fixed original nonempty seed is retained in the SAME native equality comparison. -/
def equalitySeed : Carrier chi (P := originalLabels sourceSeven) :=
  principal chi (originalTrees_good.{t} sourceSeven).predecessor_lt ⟨secondRootPoint⟩

/-- Actual compact-source eventual equality gives the larger original support and both root laws. -/
theorem actual_original_raw_equality :
    ∃ Q : Carrier chi (P := originalLabels sourceSeven), equalitySeed.{t} ≤ Q ∧
      ∃ hBQ : (emptySeeds sourceSeven).1 ≤ Q.1,
        equalitySource.hom ≫ ((equalityMap.{t} originalSourcePoint).right ≫
            ((originalLower.{t} sourceSeven).map hBQ).right) =
          (𝟙 OriginalSourceRoot) ≫ ((originalLower.{t} sourceSeven).obj Q.1).hom ∧
        equalitySource.hom ≫ ((equalityMap.{t} secondRootPoint).right ≫
            ((originalLower.{t} sourceSeven).map hBQ).right) =
          (𝟙 OriginalSourceRoot) ≫ ((originalLower.{t} sourceSeven).obj Q.1).hom ∧
        (equalityMap.{t} originalSourcePoint).right ≫ ((originalLower.{t} sourceSeven).map hBQ).right =
          (equalityMap.{t} secondRootPoint).right ≫ ((originalLower.{t} sourceSeven).map hBQ).right :=
  RootChangeCapture.existsTreeEqualityContaining chi (𝟙 OriginalSourceRoot)
    (originalTrees.{t}.component sourceSeven).tree (originalTrees_good.{t} sourceSeven)
      (originalLower.{t} sourceSeven) (emptySeeds sourceSeven) equalitySeed.{t}
      (equalityMap.{t} originalSourcePoint).right (equalityMap.{t} secondRootPoint).right
      (by simpa only [Category.id_comp] using Under.w (equalityMap.{t} originalSourcePoint))
      (by simpa only [Category.id_comp] using Under.w (equalityMap.{t} secondRootPoint))
      equalityMaps_endpoint.{t}

end RawEventualEquality

section EmptyIndex

/-- The actual empty source functor keeps its original noncompact coefficient choice. -/
abbrev emptySource : EmptyIndex ⥤ Type := (Functor.const EmptyIndex).obj LargeRoot

/-- The actual original empty target functor. -/
abbrev emptyTarget : EmptyIndex ⥤ Type := (Functor.const EmptyIndex).obj PUnit.{1}

/-- The actual original transformation on the empty original category. -/
def emptyMap : emptySource ⟶ emptyTarget where
  app d := isEmptyElim d
  naturality d _ _ := by exact False.elim (IsEmpty.false d)

/-- Every requested original empty component is eliminated on its SAME original index. -/
def emptyTrees : PointwiseCellTreePresentation (s := foldFamily.{t}) emptyMap
    (fun _ => NoVertices) where
  component d := isEmptyElim d

/-- The real public constructor handles the actual empty index with the unchanged native types. -/
def actualEmptySlice : CompatibleSlice emptyTrees.{t} (fun d => isEmptyElim d) chi
    (fun d => isEmptyElim d) :=
  actionCompatibleSlice emptyTrees.{t} (fun d => isEmptyElim d) chi chi_uncountable
    (hasCardinalLT_of_finite (Arrow EmptyIndex) chi chi_regular.aleph0_le)
    (fun d => isEmptyElim d) (fun d => isEmptyElim d)

/-- The original empty strict factor equation is produced by the real construction. -/
theorem actualEmptySlice_factor :
    actualEmptySlice.{t}.root emptyTrees.{t} (fun d => isEmptyElim d) chi ≫
      actualEmptySlice.{t}.target emptyTrees.{t} (fun d => isEmptyElim d) chi = emptyMap :=
  actualEmptySlice.{t}.factor emptyTrees.{t} (fun d => isEmptyElim d) chi

end EmptyIndex

section IdentityIndex

/-- The actual identity-only source has the SAME noncompact original root. -/
abbrev identitySource : IdentityIndex ⥤ Type := (Functor.const IdentityIndex).obj LargeRoot

/-- The actual identity-only target remains the original unit coefficient. -/
abbrev identityTarget : IdentityIndex ⥤ Type := (Functor.const IdentityIndex).obj PUnit.{1}

/-- The original identity-only root transformation. -/
def identityMap : identitySource ⟶ identityTarget where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := by ext x; rfl

/-- Its actual equality-order fold tree is selected before any action construction. -/
def identityTrees : PointwiseCellTreePresentation (s := foldFamily.{t}) identityMap
    (fun _ => Occurrence LargeRoot) where
  component _ := foldPresentation LargeRoot rootPoint

/-- Keep every original identity-only selected lower colimit. -/
def identityLower : ∀ d, LowerSetColimitData (identityTrees.{t}.component d).tree.diagram :=
  fun d => (identityTrees.{t}.component d).tree.lowerData

/-- Invoke the real public constructor on the actual identity-only category and empty seeds. -/
def actualIdentitySlice : CompatibleSlice identityTrees.{t} identityLower.{t} chi
    (fun _ => BoundedLowerSupport.empty chi) :=
  actionCompatibleSlice identityTrees.{t} identityLower.{t} chi chi_uncountable
    (hasCardinalLT_of_finite (Arrow IdentityIndex) chi chi_regular.aleph0_le)
    (fun _ => foldTree_good LargeRoot rootPoint chi) (fun _ => BoundedLowerSupport.empty chi)

/-- The output identity is the native identity on the SAME actual selected coefficient. -/
theorem actualIdentitySlice_unit : actualIdentitySlice.{t}.map (𝟙 identityObject) =
    𝟙 ((identityLower.{t} identityObject).obj (actualIdentitySlice.{t}.supports identityObject).1).right :=
  actualIdentitySlice.{t}.map_id identityObject

/-- Both original coherence tags remain distinct in the identity-only real constructor case. -/
theorem actualIdentityConstraint_tags :
    (.inl PUnit.unit : DiagramActionConstraintBounds.Constraint identityObject) ≠
      .inr (.inl (Over.mk (𝟙 identityObject))) := identityOnlyUnitDistinct

end IdentityIndex

section IndependentOriginalUniverses

universe w uD vD uC vC

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [LocallySmall.{w} C] [HasBinaryCoproducts C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (k : Cardinal.{w}) [Fact k.IsRegular]
  (hUncountable : Cardinal.aleph0 < k) (hArrow : HasCardinalLT (Arrow D) k)
  (good : ∀ d, (theta.component d).tree.IsGood k) (seed : Supports (P := P) k)

/-- The primitive public construction keeps every independent working and coefficient universe. -/
def independentOriginalCompatibleSlice : CompatibleSlice theta L k seed :=
  actionCompatibleSlice theta L k hUncountable hArrow good seed

/-- Its entire original Hom function uses the SAME native source colimit at every universe. -/
theorem independentOriginalDescenderFunction :
    (fun (d e : D) (g : d ⟶ e) =>
      (independentOriginalCompatibleSlice theta L k hUncountable hArrow good seed).map g) =
      (fun (d e : D) (g : d ⟶ e) =>
        (((L d).isColimitFilteredCocone
          (B := supportFunctor theta L k (refinementChain theta L k hArrow good seed) d)).desc
            (actionCocone theta L k hUncountable
              (refinementChain theta L k hArrow good seed) g)).right) := rfl

/-- Every original root function is the chosen original lower-object root in its actual universe. -/
theorem independentOriginalRootFunction :
    (fun d => ((independentOriginalCompatibleSlice theta L k hUncountable hArrow good seed).root
      theta L k).app d) =
      (fun d => ((L d).obj
        ((independentOriginalCompatibleSlice theta L k hUncountable hArrow good seed).supports d).1).hom) := rfl

/-- Both whole native natural transformations retain the literal original factor at every universe. -/
theorem independentOriginalWholeFactor :
    (independentOriginalCompatibleSlice theta L k hUncountable hArrow good seed).root theta L k ≫
      (independentOriginalCompatibleSlice theta L k hUncountable hArrow good seed).target theta L k = f :=
  (independentOriginalCompatibleSlice theta L k hUncountable hArrow good seed).factor theta L k

end IndependentOriginalUniverses

end OriginalDiagramActionRefinementExamples
