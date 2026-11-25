/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionCapture
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeDiagramActionConstraintBounds
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeRootChangeCapture

/-!
# Original action capture from an actual noncompact root at the chosen direct rank

The original index is the whole infinite nonthin parallel-terminal category.
The direct rank is selected internally. Its actual source root has exactly
that cardinal. All fold cells have finite endpoints and equality-order
occurrences. Original lower colimits and actual endpoint Isos are selected
once, before invoking the first capture or any refinement constructor.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  DiagramActionCapture BoundedLowerSupport

namespace OriginalDiagramActionCaptureExamples

open DiagramActionConstraintBoundExamples GoodCellTreeDataExamples

/-- The actual direct rank is selected once from the original infinite arrow carrier. -/
def chi : Cardinal.{0} := Classical.choose chosenOriginalConstraintRank

/-- The selected original direct rank is genuinely regular. -/
theorem chi_regular : chi.IsRegular := (Classical.choose_spec chosenOriginalConstraintRank).1

instance chiRegular : Fact chi.IsRegular := ⟨chi_regular⟩

/-- Genuine uncountability belongs to that SAME internally selected rank. -/
theorem chi_uncountable : Cardinal.aleph0 < chi :=
  (Classical.choose_spec chosenOriginalConstraintRank).2.1

/-- The native bound is on every original arrow of the unchanged original index. -/
theorem originalArrowBound : HasCardinalLT (Arrow OriginalIndex) chi :=
  (Classical.choose_spec chosenOriginalConstraintRank).2.2.1

/-- The actual original source root has exactly the selected direct cardinal. -/
abbrev LargeRoot := chi.out

instance largeRootNonempty : Nonempty LargeRoot :=
  Cardinal.nonempty_out (ne_of_gt (Cardinal.aleph0_pos.trans chi_uncountable))

/-- Select one actual point of the original root for the fold attaching maps. -/
def rootPoint : LargeRoot := Classical.arbitrary LargeRoot

/-- The same root cardinal is exactly chi, rather than a smaller proxy cardinal. -/
theorem largeRoot_cardinal : Cardinal.mk LargeRoot = chi := Cardinal.mk_out chi

/-- This original root is not bounded strictly below the actual direct rank. -/
theorem largeRoot_not_cardinalLT : ¬ HasCardinalLT LargeRoot chi := by
  intro h
  have hl := (hasCardinalLT_iff_cardinal_mk_lt LargeRoot chi).1 h
  rw [largeRoot_cardinal] at hl
  exact lt_irrefl chi hl

/-- The original source coefficient is not chi-presentable in the coefficient category. -/
theorem largeRoot_not_presentable : ¬ IsCardinalPresentable LargeRoot chi := by
  intro h
  exact largeRoot_not_cardinalLT ((Types.isCardinalPresentable_iff chi).1 h)

section FoldTree

variable (X : Type) (x0 : X)

/-- At occurrence x the two actual attaching values are x and the selected original x0. -/
def attaching (x : X) : Fin 2 ⟶ X := ↾fun i => if i = 0 then x else x0

/-- The actual native chosen quotient arrow at this original occurrence. -/
def quotientArrow (x : X) : X ⟶ pushout (attaching X x0 x) fold :=
  pushout.inl (attaching X x0 x) fold

/-- The actual cell-target inclusion into the same original chosen pushout. -/
def quotientCell (x : X) : PUnit.{1} ⟶ pushout (attaching X x0 x) fold :=
  pushout.inr (attaching X x0 x) fold

/-- The original two root values have the same image in precisely that original quotient. -/
theorem quotient_identifies (x : X) : quotientArrow X x0 x x = quotientArrow X x0 x x0 := by
  have h0 := ConcreteCategory.congr_hom
    (pushout.condition (f := attaching X x0 x) (g := fold)) (0 : Fin 2)
  have h1 := ConcreteCategory.congr_hom
    (pushout.condition (f := attaching X x0 x) (g := fold)) (1 : Fin 2)
  change quotientArrow X x0 x (attaching X x0 x (0 : Fin 2)) =
    quotientCell X x0 x (fold (0 : Fin 2)) at h0
  change quotientArrow X x0 x (attaching X x0 x (1 : Fin 2)) =
    quotientCell X x0 x (fold (1 : Fin 2)) at h1
  have he0 : quotientArrow X x0 x x = quotientCell X x0 x PUnit.unit := by
    change quotientArrow X x0 x x = quotientCell X x0 x PUnit.unit at h0
    exact h0
  have he1 : quotientArrow X x0 x x0 = quotientCell X x0 x PUnit.unit := by
    change quotientArrow X x0 x x0 = quotientCell X x0 x PUnit.unit at h1
    exact h1
  exact he0.trans he1.symm

/-- The whole vertex function retains the original equality-order occurrences and quotient values. -/
def diagram : Occurrence X ⥤ Under X where
  obj a := Under.mk (quotientArrow X x0 a.val)
  map {a b} f := eqToHom (congrArg (fun z : Occurrence X =>
    Under.mk (quotientArrow X x0 z.val)) (leOfHom f))
  map_id _ := rfl
  map_comp f g := by
    cases leOfHom f
    cases leOfHom g
    rfl

/-- Every occurrence has no strict predecessor in its ORIGINAL equality order. -/
instance predecessorEmpty (a : Occurrence X) : IsEmpty (LowerSet.Iio a) :=
  ⟨fun b => False.elim b.2⟩

/-- The actual selected predecessor cocone retains the original identity under X. -/
def predecessor (a : Occurrence X) :
    ColimitCocone (LowerSetColimits.restriction (diagram X x0) (LowerSet.Iio a)) where
  cocone :=
    { pt := Under.mk (𝟙 X)
      ι := { app b := isEmptyElim b
             naturality b _ _ := by exact False.elim (IsEmpty.false b) } }
  isColimit :=
    { desc c := Under.mkIdInitial.to c.pt
      fac c b := isEmptyElim b
      uniq c m _ := Under.mkIdInitial.hom_ext m (Under.mkIdInitial.to c.pt) }

/-- Its raw predecessor map is exactly the original native pushout injection. -/
theorem predecessorMap_right (a : Occurrence X) :
    (cellTreePredecessorMap (diagram X x0) a (predecessor X x0 a)).right =
      quotientArrow X x0 a.val := by
  have h : cellTreePredecessorMap (diagram X x0) a (predecessor X x0 a) =
      Under.mkIdInitial.to ((diagram X x0).obj a) := Under.mkIdInitial.hom_ext _ _
  simpa only [Under.mkIdInitial_to_right, diagram, Under.mk_hom] using congrArg Under.Hom.right h

/-- The whole endpoint is the actual unit coefficient under the original constant root map. -/
def endpointCocone : Cocone (diagram X x0) where
  pt := Under.mk (↾fun _ : X => PUnit.unit)
  ι :=
    { app a := Under.homMk (↾fun _ => PUnit.unit) (by ext x; rfl)
      naturality a b g := by
        apply Under.UnderMorphism.ext
        ext q
        rfl }

/-- Every genuine under-cocone root identifies all original x with x0, by its original quotient leg. -/
theorem cocone_root_constant (c : Cocone (diagram X x0)) (x : X) : c.pt.hom x = c.pt.hom x0 := by
  have h0 := ConcreteCategory.congr_hom (Under.w (c.ι.app ⟨x⟩)) x
  have h1 := ConcreteCategory.congr_hom (Under.w (c.ι.app ⟨x⟩)) x0
  exact h0.symm.trans ((congrArg (c.ι.app ⟨x⟩).right (quotient_identifies X x0 x)).trans h1)

/-- The actual universal endpoint map sends the unit to the original cocone root value at x0. -/
def endpointDesc (c : Cocone (diagram X x0)) : (endpointCocone X x0).pt ⟶ c.pt :=
  Under.homMk (↾fun _ => c.pt.hom x0) (by
    ext x
    exact (cocone_root_constant X x0 c x).symm)

/-- Every original quotient leg factors through the SAME actual whole endpoint descender. -/
theorem endpointDesc_fac (c : Cocone (diagram X x0)) (a : Occurrence X) :
    (endpointCocone X x0).ι.app a ≫ endpointDesc X x0 c = c.ι.app a := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · ext x
    have h := ConcreteCategory.congr_hom (Under.w (c.ι.app a)) x
    exact (cocone_root_constant X x0 c x).symm.trans h.symm
  · ext u
    have h := ConcreteCategory.congr_hom
      (pushout.condition (f := attaching X x0 a.val) (g := fold)) (1 : Fin 2)
    have hx := ConcreteCategory.congr_hom (Under.w (c.ι.app a)) x0
    change quotientArrow X x0 a.val (attaching X x0 a.val (1 : Fin 2)) =
      quotientCell X x0 a.val (fold (1 : Fin 2)) at h
    have he : quotientArrow X x0 a.val x0 = quotientCell X x0 a.val PUnit.unit := by
      change quotientArrow X x0 a.val x0 = quotientCell X x0 a.val PUnit.unit at h
      exact h
    cases u
    exact hx.symm.trans (congrArg (c.ι.app a).right he)

/-- Original under-root compatibility makes the endpoint descender unique. -/
theorem endpointDesc_unique (c : Cocone (diagram X x0))
    (m : (endpointCocone X x0).pt ⟶ c.pt) : m = endpointDesc X x0 c := by
  apply Under.UnderMorphism.ext
  ext u
  cases u
  exact ConcreteCategory.congr_hom (Under.w m) x0

/-- The whole original PUnit endpoint is colimiting in the SAME Under X category. -/
def endpointIsColimit : IsColimit (endpointCocone X x0) where
  desc c := endpointDesc X x0 c
  fac c a := endpointDesc_fac X x0 c a
  uniq c m _ := endpointDesc_unique X x0 c m

/-- The actual equality-order fold tree keeps every original occurrence, root and pushout. -/
def foldTree : CellTree foldFamily.{t} X (P := Occurrence X) where
  wellFounded := ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩
  diagram := diagram X x0
  label _ := originalLabel
  predecessor a := predecessor X x0 a
  attaching a := attaching X x0 a.val
  cell a := quotientCell X x0 a.val
  isPushout a := by
    rw [predecessorMap_right]
    exact IsPushout.of_hasPushout (attaching X x0 a.val) fold
  endpoint := ⟨endpointCocone X x0, endpointIsColimit X x0⟩

/-- Finite original cell endpoints make this actual tree good at every regular rank. -/
theorem foldTree_good (k : Cardinal.{0}) [Fact k.IsRegular] : (foldTree.{t} X x0).IsGood k where
  presentable_source _ :=
    (hasCardinalLT_of_finite (Fin 2) k (Fact.out : k.IsRegular).aleph0_le).isCardinalPresentable
  presentable_target _ :=
    (hasCardinalLT_of_finite PUnit.{1} k (Fact.out : k.IsRegular).aleph0_le).isCardinalPresentable
  predecessor_lt a := by
    let : IsEmpty (Set.Iio a) := ⟨fun b => False.elim b.2⟩
    exact hasCardinalLT_of_finite _ k (Fact.out : k.IsRegular).aleph0_le

/-- The actual full tree presents the original constant map from X to the unit coefficient. -/
def foldPresentation : CellTree.Presentation (s := foldFamily.{t}) (P := Occurrence X)
    (↾fun _ : X => PUnit.unit) where
  tree := foldTree X x0
  endpointIso := Iso.refl _

end FoldTree

/-- Original parallel source actions are actual different constant functions into Fin 2. -/
@[implicit_reducible]
def parallelSource : WalkingParallelPair ⥤ Type :=
  parallelPair (↾fun _ : LargeRoot => (0 : Fin 2)) (↾fun _ : LargeRoot => (1 : Fin 2))

/-- Native terminal extension retains those two actual original source actions and the finite fold. -/
@[implicit_reducible]
def terminalSource : WithTerminal WalkingParallelPair ⥤ Type :=
  WithTerminal.lift (Z := PUnit.{1}) parallelSource (fun _ => ↾fun _ => PUnit.unit)
    (by
      intro a b g
      apply ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _)

/-- Pull the whole native source functor to every original Nat label without changing its Hom values. -/
@[implicit_reducible]
def originalSource : OriginalIndex ⥤ Type where
  obj d := terminalSource.obj d.2
  map g := terminalSource.map g.2
  map_id d := terminalSource.map_id d.2
  map_comp g h := terminalSource.map_comp g.2 h.2

/-- The original target is the same actual constant unit functor on the entire infinite index. -/
abbrev originalTarget : OriginalIndex ⥤ Type := constantTarget

/-- The actual original root-to-target natural transformation. -/
def originalMap : originalSource ⟶ originalTarget where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := by ext x; rfl

/-- Original coefficient points are fixed before any capture or refinement selection. -/
def originalRootPoint : (d : OriginalIndex) → originalSource.obj d
  | ⟨_, .star⟩ => PUnit.unit
  | ⟨_, .of .zero⟩ => rootPoint
  | ⟨_, .of .one⟩ => (0 : Fin 2)

/-- Every original component keeps its own equality-order occurrence family. -/
abbrev originalLabels (d : OriginalIndex) : Type := Occurrence (originalSource.obj d)

/-- Select the entire original component tree presentation once from the actual original maps. -/
def originalTrees : PointwiseCellTreePresentation (s := foldFamily.{t}) originalMap originalLabels where
  component d := foldPresentation (originalSource.obj d) (originalRootPoint d)

/-- The original all-lower colimit family is selected once on those SAME original trees. -/
def originalLower : ∀ d, LowerSetColimitData (originalTrees.{t}.component d).tree.diagram :=
  fun d => (originalTrees.{t}.component d).tree.lowerData

/-- Every actual original tree is good at the SAME internally selected direct rank. -/
theorem originalTrees_good (d : OriginalIndex) : (originalTrees.{t}.component d).tree.IsGood chi :=
  foldTree_good (originalSource.obj d) (originalRootPoint d) chi

/-- Actual empty seeds, preserving the same original label family at every original object. -/
def emptySeeds : Supports (P := originalLabels) chi := fun _ => BoundedLowerSupport.empty chi

/-- Actual nonempty seeds, fixed from the original selected coefficient points. -/
def nonemptySeeds : Supports (P := originalLabels) chi := fun d =>
  principal chi (originalTrees_good.{t} d).predecessor_lt ⟨originalRootPoint d⟩

/-- Every actual nonempty seed retains its original specified occurrence. -/
theorem nonemptySeeds_contains (d : OriginalIndex) :
    (⟨originalRootPoint d⟩ : originalLabels d) ∈ (nonemptySeeds.{t} d).1 := by
  change (⟨originalRootPoint d⟩ : originalLabels d) ≤ ⟨originalRootPoint d⟩
  exact le_rfl

/-- The original source actions at the original label seven are different actual functions. -/
theorem original_parallel_actions_different :
    originalSource.map firstArrow ≠ originalSource.map secondArrow := by
  intro h
  have hx := ConcreteCategory.congr_hom h rootPoint
  change (0 : Fin 2) = 1 at hx
  exact (by decide : (0 : Fin 2) ≠ 1) hx

/-- The original nonmonomorphic root change is valid even at the larger direct rank. -/
theorem original_first_root_change_not_mono : ¬ Mono (originalSource.map firstArrow) := by
  intro h
  have hi := (mono_iff_injective (originalSource.map firstArrow)).1 h
  have hFin : HasCardinalLT (Fin 2) chi :=
    hasCardinalLT_of_finite (Fin 2) chi chi_regular.aleph0_le
  exact largeRoot_not_cardinalLT (hFin.of_injective (originalSource.map firstArrow) hi)

/-- Select actual first capture supports with only primitive original data and actual seeds. -/
def firstSupports (B : Supports (P := originalLabels) chi) : Supports (P := originalLabels) chi :=
  Classical.choose (existsFirstFactors originalTrees.{t} originalLower.{t} chi
    originalArrowBound originalTrees_good.{t} B)

/-- Every specified original seed is included in that SAME selected actual output. -/
theorem firstSupports_le (B : Supports (P := originalLabels) chi) (d : OriginalIndex) :
    B d ≤ firstSupports.{t} B d :=
  (Classical.choose_spec (existsFirstFactors originalTrees.{t} originalLower.{t} chi
    originalArrowBound originalTrees_good.{t} B)).1 d

/-- Select the actual raw factors returned by that SAME first support capture. -/
def firstFactors (B : Supports (P := originalLabels) chi) :
    Factors originalTrees.{t} originalLower.{t} chi B (firstSupports.{t} B) :=
  Classical.choice (Classical.choose_spec
    (existsFirstFactors originalTrees.{t} originalLower.{t} chi originalArrowBound originalTrees_good.{t} B)).2

/-- Every original Hom has both literal native root and original G-endpoint equations. -/
theorem firstSquares (B : Supports (P := originalLabels) chi)
    {d e : OriginalIndex} (g : d ⟶ e) :
    ((originalLower.{t} d).obj (B d).1).hom ≫ (firstFactors.{t} B).map g =
        originalSource.map g ≫ ((originalLower.{t} e).obj (firstSupports.{t} B e).1).hom ∧
      (firstFactors.{t} B).map g ≫ leg originalTrees.{t} originalLower.{t} e (firstSupports.{t} B e).1 =
        leg originalTrees.{t} originalLower.{t} d (B d).1 ≫ originalTarget.map g :=
  ⟨(firstFactors.{t} B).root g, (firstFactors.{t} B).endpoint g⟩

/-- The actual empty source piece is relatively chi-presentable under its SAME noncompact root. -/
theorem original_empty_source_relative :
    IsCardinalPresentable ((originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1) chi :=
  RelativeCellPresentability.selectedLower chi (originalTrees.{t}.component sourceSeven).tree
    (originalTrees_good.{t} sourceSeven) (originalLower.{t} sourceSeven)
      (emptySeeds sourceSeven).1 (emptySeeds sourceSeven).2

/-- That SAME chosen source piece is not absolutely chi-presentable in the coefficient category. -/
theorem original_empty_source_not_absolute :
    ¬ IsCardinalPresentable ((originalLower.{t} sourceSeven).obj (emptySeeds sourceSeven).1).right chi := by
  intro h
  let : IsCardinalPresentable
      ((Under.forget (originalSource.obj sourceSeven)).obj
        ((originalLower.{t} sourceSeven).obj ⊥)) chi := by
    rw [Under.forget_obj]
    exact h
  let e := (Under.forget (originalSource.obj sourceSeven)).mapIso
    ((originalTrees.{t}.component sourceSeven).tree.emptyLowerIso (originalLower.{t} sourceSeven))
  have hRoot := isCardinalPresentable_of_iso e chi
  change IsCardinalPresentable LargeRoot chi at hRoot
  exact largeRoot_not_presentable hRoot

/-- Both original incoming pair labels remain distinct even when original composites coincide. -/
theorem original_pair_boundary :
    firstPair ≠ secondPair ∧ firstArrow ≫ lastArrow = secondArrow ≫ lastArrow ∧
      originalTarget.map firstArrow = originalTarget.map secondArrow :=
  ⟨originalPairLabelsDifferent, originalCompositesEqual, constantFirstActionsEqual⟩

/-- The actual target support contains every originally supplied nonempty occurrence. -/
theorem first_nonempty_seed_retained (d : OriginalIndex) :
    (⟨originalRootPoint d⟩ : originalLabels d) ∈ (firstSupports.{t} nonemptySeeds.{t} d).1 :=
  LowerSetColimits.memOfLE (firstSupports_le.{t} nonemptySeeds.{t} d) (nonemptySeeds_contains.{t} d)

/-- Both real first arrows and their common actual following arrow have their own complete squares. -/
theorem first_original_three_squares :
    (∀ d, emptySeeds d ≤ firstSupports.{t} emptySeeds d) ∧
      (∀ (d e : OriginalIndex) (g : d ⟶ e),
        ((originalLower.{t} d).obj (emptySeeds d).1).hom ≫ (firstFactors.{t} emptySeeds).map g =
          originalSource.map g ≫ ((originalLower.{t} e).obj (firstSupports.{t} emptySeeds e).1).hom) :=
  ⟨firstSupports_le.{t} emptySeeds, fun _ _ g => (firstSquares.{t} emptySeeds g).1⟩

section IndependentUniverses

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [LocallySmall.{w} C] [HasBinaryCoproducts C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (k : Cardinal.{w}) [Fact k.IsRegular]
  (hArrow : HasCardinalLT (Arrow D) k)
  (good : ∀ d, (theta.component d).tree.IsGood k)

include hArrow good in
/-- The expected factor family TYPE fixes all original chosen domains, roots and endpoint legs. -/
theorem independent_first_factor_TYPE (B : Supports (P := P) k) :
    ∃ E : Supports (P := P) k, (∀ d, B d ≤ E d) ∧
      ∃ p : ∀ (d e : D) (_ : d ⟶ e), ((L d).obj (B d).1).right ⟶ ((L e).obj (E e).1).right,
        ∀ (d e : D) (g : d ⟶ e),
          ((L d).obj (B d).1).hom ≫ p d e g = F.map g ≫ ((L e).obj (E e).1).hom ∧
            p d e g ≫ leg theta L e (E e).1 = leg theta L d (B d).1 ≫ G.map g := by
  obtain ⟨E, hBE, ⟨a⟩⟩ := existsFirstFactors theta L k hArrow good B
  exact ⟨E, hBE, (fun _ _ g => a.map g), fun _ _ g => ⟨a.root g, a.endpoint g⟩⟩

end IndependentUniverses

end OriginalDiagramActionCaptureExamples


namespace OriginalDiagramActionCoherenceExamples

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

section IndependentOriginalUniverses

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [LocallySmall.{w} C] [HasBinaryCoproducts C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (k : Cardinal.{w}) [Fact k.IsRegular]
  (hArrow : HasCardinalLT (Arrow D) k)
  (good : ∀ d, (theta.component d).tree.IsGood k)
  (seed : Supports (P := P) k)

include hArrow good in
/-- The real public constructor retains every independent working/index/coefficient universe. -/
def independentOriginalRefinementChain : RefinementChain theta L k seed :=
  refinementChain theta L k hArrow good seed

end IndependentOriginalUniverses

end OriginalDiagramActionCoherenceExamples
