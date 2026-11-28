/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionRefinement

/-!
# Enlarging bounded slices while preserving the given diagram actions

The ordering records naturality of the actual selected lower-colimit maps.
An inclusion of label sets alone is not an arrow of this ordering. A bounded
family of existing slices is preserved by simultaneous eventual equality in
the original root-changing presentations. The main results assume that the
regular rank `chi` is uncountable (`Cardinal.aleph0 < chi`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t uD vD uC vC uI

namespace CategoryTheory.SmallObject.DiagramSliceExtensions

open Limits BoundedLowerSupport DiagramActionCapture DiagramActionRefinement

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  {alpha : Type t} {s : alpha → Arrow C} {F G : D ⥤ C} {f : F ⟶ G}
  {P : D → Type w} [∀ d, PartialOrder (P d)]
  (theta : PointwiseCellTreePresentation (s := s) f P)
  (L : ∀ d, LowerSetColimitData (theta.component d).tree.diagram)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- The empty seed has the same original component carriers and roots. -/
abbrev emptySupports : Supports (P := P) chi := fun _ => empty chi

/-- A bounded slice with actual actions on its original selected pieces. -/
abbrev Slice := CompatibleSlice theta L chi (emptySupports (P := P) chi)

namespace Slice

variable {theta L chi}

/-- An actual inclusion of the same lower pieces, with its action squares. -/
-- This Type-valued carrier supplies the Hom type of the slice category below.
@[nolint structureInType]
structure Inclusion (A B : Slice theta L chi) : Type where
  /-- The original component label inclusions. -/
  support_le (d : D) : A.supports d ≤ B.supports d
  /-- The selected comparison functions commute with every original action. -/
  naturality {d e : D} (g : d ⟶ e) :
    ((L d).map (support_le d)).right ≫ B.map g =
      A.map g ≫ ((L e).map (support_le e)).right

instance inclusionSubsingleton (A B : Slice theta L chi) :
    Subsingleton (Inclusion A B) := by
  refine ⟨fun p q => ?_⟩
  cases p
  cases q
  rfl

/-- The identity comparison uses the original selected identity maps. -/
def Inclusion.id (A : Slice theta L chi) : Inclusion A A where
  support_le d := le_rfl
  naturality g := by
    rw [(L _).map_id, (L _).map_id]
    simp only [Under.id_right, Category.id_comp, Category.comp_id]

/-- Composition retains the same original lower-colimit comparisons. -/
def Inclusion.comp {A B E : Slice theta L chi}
    (p : Inclusion A B) (q : Inclusion B E) : Inclusion A E where
  support_le d := (p.support_le d).trans (q.support_le d)
  naturality {d e} g := by
    rw [← (L d).map_comp (p.support_le d) (q.support_le d),
      ← (L e).map_comp (p.support_le e) (q.support_le e), Under.comp_right, Under.comp_right]
    calc
      _ = ((L _).map (p.support_le _)).right ≫
          (((L _).map (q.support_le _)).right ≫ E.map g) := Category.assoc _ _ _
      _ = ((L _).map (p.support_le _)).right ≫
          (B.map g ≫ ((L _).map (q.support_le _)).right) := by rw [q.naturality]
      _ = (A.map g ≫ ((L _).map (p.support_le _)).right) ≫
          ((L _).map (q.support_le _)).right := by rw [← Category.assoc, p.naturality]
      _ = _ := Category.assoc _ _ _

/-- This category remembers the action squares, not only an upper support. -/
@[reducible]
instance category : Category.{0} (Slice theta L chi) where
  Hom := Inclusion
  id := Inclusion.id
  comp := Inclusion.comp
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance isThin : Quiver.IsThin (Slice theta L chi) :=
  fun A B => inclusionSubsingleton A B

/-- The actual natural transformation belonging to an inclusion arrow. -/
def Inclusion.toNatTrans {A B : Slice theta L chi} (p : A ⟶ B) :
    A.toFunctor theta L chi ⟶ B.toFunctor theta L chi where
  app d := ((L d).map (p.support_le d)).right
  naturality _ _ g := (p.naturality g).symm

@[reassoc]
theorem Inclusion.root {A B : Slice theta L chi} (p : A ⟶ B) :
    A.root theta L chi ≫ p.toNatTrans = B.root theta L chi := by
  apply NatTrans.ext
  funext d
  exact Under.w ((L d).map (p.support_le d))

@[reassoc]
theorem Inclusion.target {A B : Slice theta L chi} (p : A ⟶ B) :
    p.toNatTrans ≫ B.target theta L chi = A.target theta L chi := by
  apply NatTrans.ext
  funext d
  exact inclusion_leg theta L d (p.support_le d)

/-- The slice diagram has the original objects and all original Hom actions. -/
def diagram : Slice theta L chi ⥤ (D ⥤ C) where
  obj A := A.toFunctor theta L chi
  map p := p.toNatTrans
  map_id A := by
    apply NatTrans.ext
    funext d
    change ((L d).map (le_refl (A.supports d).1)).right = 𝟙 _
    exact congrArg Under.Hom.right ((L d).map_id (A.supports d).1)
  map_comp p q := by
    apply NatTrans.ext
    funext d
    exact (congrArg Under.Hom.right ((L d).map_comp (p.support_le d) (q.support_le d))).symm

/-- Every slice and comparison remains under the same entire original functor. -/
def underDiagram : Slice theta L chi ⥤ Under F where
  obj A := Under.mk (A.root theta L chi)
  map p := Under.homMk p.toNatTrans p.root
  map_id A := by
    apply Under.UnderMorphism.ext
    change (𝟙 A : A ⟶ A).toNatTrans = 𝟙 (A.toFunctor theta L chi)
    exact (diagram (theta := theta) (L := L) (chi := chi)).map_id A
  map_comp p q := by
    apply Under.UnderMorphism.ext
    change (p ≫ q).toNatTrans = p.toNatTrans ≫ q.toNatTrans
    exact (diagram (theta := theta) (L := L) (chi := chi)).map_comp p q

/-- The comparison to the original endpoint keeps its complete natural transformation. -/
def endpointCocone : Cocone (underDiagram (theta := theta) (L := L) (chi := chi)) where
  pt := Under.mk f
  ι :=
    { app A := Under.homMk (A.target theta L chi) (A.factor theta L chi)
      naturality A B p := by
        apply Under.UnderMorphism.ext
        change p.toNatTrans ≫ B.target theta L chi = A.target theta L chi ≫ 𝟙 _
        rw [Category.comp_id]
        exact p.target }

end Slice

section PreservingFactors

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)
  {I : Type uI} (hI : HasCardinalLT I chi) (A : I → Slice theta L chi)

/-- Containment of every prescribed slice in the source of a captured stage. -/
abbrev Contains (B : Supports (P := P) chi) : Prop :=
  ∀ i d, (A i).supports d ≤ B d

/-- One captured stage retains all prescribed naturality squares. -/
def Preserves {B E : Supports (P := P) chi}
    (hBE : ∀ d, B d ≤ E d) (hA : Contains theta L chi A B)
    (a : Factors theta L chi B E) : Prop :=
  ∀ (i : I) (d e : D) (g : d ⟶ e),
    ((L d).map (hA i d)).right ≫ a.map g =
      (A i).map g ≫ ((L e).map ((hA i e).trans (hBE e))).right

/-- The same component union includes the original seed and the given slice family. -/
def familySeed (seed : Supports (P := P) chi) : Supports (P := P) chi :=
  fun d => union chi (seed d) (indexedUnion chi (fun i => (A i).supports d) hI)

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem seed_le_familySeed (seed : Supports (P := P) chi) (d : D) :
    seed d ≤ familySeed theta L chi hI A seed d :=
  le_union_left chi _ _

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
theorem family_le_familySeed (seed : Supports (P := P) chi) :
    Contains theta L chi A (familySeed theta L chi hI A seed) := by
  intro i d
  exact (le_indexedUnion chi (fun j => (A j).supports d) hI i).trans
    (le_union_right chi _ _)

include hArrow good hI in
/-- Capture all action squares in a single original target support per component.

The index is the actual product of the given slice family and the incoming
arrow category. Each equality is tested in the original root-changing
presentation. No endpoint map is cancelled.
-/
theorem existsPreservingExtension {B E : Supports (P := P) chi}
    (hBE : ∀ d, B d ≤ E d) (hA : Contains theta L chi A B)
    (a : Factors theta L chi B E) :
    ∃ (Q : Supports (P := P) chi) (hEQ : ∀ d, E d ≤ Q d),
      Preserves theta L chi A (fun d => (hBE d).trans (hEQ d)) hA
        (a.extend theta L hEQ) := by
  have h (e : D) :
      ∃ (Q : Carrier chi (P := P e)) (hEQ : E e ≤ Q),
        ∀ (i : I) (b : Over e),
          (((L b.left).map (hA i b.left)).right ≫ a.map b.hom) ≫
              ((L e).map hEQ).right =
            ((A i).map b.hom ≫ ((L e).map ((hA i e).trans (hBE e))).right) ≫
              ((L e).map hEQ).right := by
    let J := I × Over e
    have hJ : HasCardinalLT J chi :=
      hasCardinalLT_prod (Fact.out : chi.IsRegular).aleph0_le hI
        (DiagramActionConstraintBounds.incomingLt chi hArrow e)
    let roots : J → C := fun j => F.obj j.2.left
    let sources : ∀ j : J, Under (roots j) :=
      fun j => piece theta L j.2.left ((A j.1).supports j.2.left).1
    let : ∀ j : J, IsCardinalPresentable (sources j) chi := fun j =>
      RelativeCellPresentability.selectedLower chi (theta.component j.2.left).tree
        (good j.2.left) (L j.2.left) ((A j.1).supports j.2.left).1
        ((A j.1).supports j.2.left).2
    let p : ∀ j : J, (sources j).right ⟶ ((L e).obj (E e).1).right :=
      fun j => ((L j.2.left).map (hA j.1 j.2.left)).right ≫ a.map j.2.hom
    let q : ∀ j : J, (sources j).right ⟶ ((L e).obj (E e).1).right :=
      fun j => (A j.1).map j.2.hom ≫ ((L e).map ((hA j.1 e).trans (hBE e))).right
    have hp (j : J) :
        (sources j).hom ≫ p j = F.map j.2.hom ≫ ((L e).obj (E e).1).hom := by
      dsimp only [sources, p, piece]
      rw [← Category.assoc, Under.w]
      exact a.root j.2.hom
    have hq (j : J) :
        (sources j).hom ≫ q j = F.map j.2.hom ≫ ((L e).obj (E e).1).hom := by
      dsimp only [sources, q, piece]
      rw [← Category.assoc, (A j.1).map_root, Category.assoc, Under.w]
    have he (j : J) :
        p j ≫ (EndpointDiagramTransport.lowerLeg theta L e (E e).1).right =
          q j ≫ (EndpointDiagramTransport.lowerLeg theta L e (E e).1).right := by
      apply originalEndpoint_eq_to_tree theta L e (E e).1 (p j) (q j)
      dsimp only [p, q]
      rw [Category.assoc, a.endpoint, ← Category.assoc, inclusion_leg,
        Category.assoc, inclusion_leg]
      exact ((A j.1).map_endpoint j.2.hom).symm
    obtain ⟨Q, _, _, hEQ, hEq⟩ := RootChangeCapture.existsTreeEqualityFamily chi
      (theta.component e).tree (good e) (L e) hJ roots
      (fun j => F.map j.2.hom) sources (E e) (E e) (fun _ => E e) p q hp hq he
    refine ⟨Q, hEQ, ?_⟩
    intro i b
    exact (hEq (i, b)).2.2
  choose Q hEQ hEq using h
  refine ⟨Q, hEQ, ?_⟩
  intro i d e g
  change ((L d).map (hA i d)).right ≫
      (a.map g ≫ ((L e).map (hEQ e)).right) = _
  have hh := hEq e i (Over.mk g)
  simp only [Over.mk_left, Over.mk_hom] at hh
  rw [← Category.assoc, hh]
  rw [Category.assoc, ← Under.comp_right, (L e).map_comp]

omit [LocallySmall.{w} C] [HasBinaryCoproducts C] in
/-- Extending a target preserves every previously forced whole action square. -/
theorem preserves_extend {B E Q : Supports (P := P) chi}
    (hBE : ∀ d, B d ≤ E d) (hEQ : ∀ d, E d ≤ Q d)
    (hA : Contains theta L chi A B) (a : Factors theta L chi B E)
    (ha : Preserves theta L chi A hBE hA a) :
    Preserves theta L chi A (fun d => (hBE d).trans (hEQ d)) hA
      (a.extend theta L hEQ) := by
  intro i d e g
  change ((L d).map (hA i d)).right ≫
      (a.map g ≫ ((L e).map (hEQ e)).right) = _
  rw [← Category.assoc, ha i d e g, Category.assoc, ← Under.comp_right, (L e).map_comp]

/-- An actual unital captured stage, now preserving the given family. -/
structure PreservingUnitalStage (B : Supports (P := P) chi)
    (hA : Contains theta L chi A B) extends UnitalStage theta L chi B where
  preserves : Preserves theta L chi A le hA factors

include hArrow good hI in
theorem nonemptyPreservingUnitalStage (B : Supports (P := P) chi)
    (hA : Contains theta L chi A B) :
    Nonempty (PreservingUnitalStage theta L chi A B hA) := by
  let S := Classical.choice (nonemptyUnitalStage theta L chi hArrow good B)
  obtain ⟨Q, hEQ, hQ⟩ :=
    existsPreservingExtension theta L chi hArrow good hI A S.le hA S.factors
  refine ⟨{
    target := Q
    le := fun d => (S.le d).trans (hEQ d)
    factors := S.factors.extend theta L hEQ
    unit := ?_
    preserves := hQ }⟩
  intro d
  change S.factors.map (𝟙 d) ≫ ((L d).map (hEQ d)).right = _
  rw [S.unit]
  exact congrArg Under.Hom.right ((L d).map_comp (S.le d) (hEQ d))

/-- The original refined stage with an additional simultaneous family constraint. -/
structure PreservingRefinedStage (Bprev Bnow : Supports (P := P) chi)
    (hPrev : ∀ d, Bprev d ≤ Bnow d) (old : Factors theta L chi Bprev Bnow)
    (hA : Contains theta L chi A Bnow)
    extends RefinedStage theta L chi Bprev Bnow hPrev old where
  preserves : Preserves theta L chi A le hA factors

include hArrow good hI in
theorem nonemptyPreservingRefinedStage
    (Bprev Bnow : Supports (P := P) chi) (hPrev : ∀ d, Bprev d ≤ Bnow d)
    (old : Factors theta L chi Bprev Bnow) (hA : Contains theta L chi A Bnow) :
    Nonempty (PreservingRefinedStage theta L chi A Bprev Bnow hPrev old hA) := by
  let S := Classical.choice
    (nonemptyRefinedStage theta L chi hArrow good Bprev Bnow hPrev old)
  obtain ⟨Q, hEQ, hQ⟩ :=
    existsPreservingExtension theta L chi hArrow good hI A S.le hA S.factors
  refine ⟨{
    target := Q
    le := fun d => (S.le d).trans (hEQ d)
    factors := S.factors.extend theta L hEQ
    unit := ?_
    ladder := ?_
    composition := ?_
    preserves := hQ }⟩
  · intro d
    change S.factors.map (𝟙 d) ≫ ((L d).map (hEQ d)).right = _
    rw [S.unit]
    exact congrArg Under.Hom.right ((L d).map_comp (S.le d) (hEQ d))
  · intro d e g
    change old.map g ≫ ((L e).map ((S.le e).trans (hEQ e))).right =
      ((L d).map (hPrev d)).right ≫
        (S.factors.map g ≫ ((L e).map (hEQ e)).right)
    rw [← (L e).map_comp (S.le e) (hEQ e), Under.comp_right,
      ← Category.assoc, S.ladder g]
    exact Category.assoc _ _ _
  · intro d m e g h
    change old.map g ≫ (S.factors.map h ≫ ((L e).map (hEQ e)).right) = _
    rw [← Category.assoc, S.composition g h, Category.assoc, ← Under.comp_right,
      (L e).map_comp (S.le e) (hEQ e)]

end PreservingFactors

section Chain

variable [LocallySmall.{w} C] [HasBinaryCoproducts C]
  (hArrow : HasCardinalLT (Arrow D) chi)
  (good : ∀ d, (theta.component d).tree.IsGood chi)
  {I : Type uI} (hI : HasCardinalLT I chi) (A : I → Slice theta L chi)

/-- Internal data of one stage, retaining every given slice inclusion. -/
structure FamilyState where
  /-- The current original component supports. -/
  source : Supports (P := P) chi
  /-- The original component supports after this refinement. -/
  target : Supports (P := P) chi
  le (d : D) : source d ≤ target d
  /-- The complete original action factorization between these support families. -/
  factors : Factors theta L chi source target
  unit (d : D) : factors.map (𝟙 d) = inclusion theta L le d
  contains : Contains theta L chi A source
  preserves : Preserves theta L chi A le contains factors

/-- The first internally chosen state includes the literal given seed. -/
def firstState (seed : Supports (P := P) chi) : FamilyState theta L chi A :=
  let B := familySeed theta L chi hI A seed
  let hA := family_le_familySeed theta L chi hI A seed
  let S := Classical.choice
    (nonemptyPreservingUnitalStage theta L chi hArrow good hI A B hA)
  { source := B
    target := S.target
    le := S.le
    factors := S.factors
    unit := S.unit
    contains := hA
    preserves := S.preserves }

/-- The same refinement value supplies the successor and all of its certificates. -/
def refineState (S : FamilyState theta L chi A) :
    PreservingRefinedStage theta L chi A S.source S.target S.le S.factors
      (fun i d => (S.contains i d).trans (S.le d)) :=
  Classical.choice (nonemptyPreservingRefinedStage theta L chi hArrow good hI A
    S.source S.target S.le S.factors (fun i d => (S.contains i d).trans (S.le d)))

/-- Its successor source is the exact preceding chosen target. -/
def nextState (S : FamilyState theta L chi A) : FamilyState theta L chi A :=
  let Q := refineState theta L chi hArrow good hI A S
  { source := S.target
    target := Q.target
    le := Q.le
    factors := Q.factors
    unit := Q.unit
    contains := fun i d => (S.contains i d).trans (S.le d)
    preserves := Q.preserves }

/-- Nat recursion constructs the actual simultaneous action refinement. -/
def states (seed : Supports (P := P) chi) : ℕ → FamilyState theta L chi A :=
  Nat.rec (firstState theta L chi hArrow good hI A seed)
    (fun _ S => nextState theta L chi hArrow good hI A S)

/-- Forgetting the extra certificates keeps the same whole original chain. -/
def chain (seed : Supports (P := P) chi) :
    RefinementChain theta L chi (familySeed theta L chi hI A seed) where
  supports n := (states theta L chi hArrow good hI A seed n).source
  start := rfl
  le n := (states theta L chi hArrow good hI A seed n).le
  factors n := (states theta L chi hArrow good hI A seed n).factors
  unit n := (states theta L chi hArrow good hI A seed n).unit
  ladder n :=
    (refineState theta L chi hArrow good hI A
      (states theta L chi hArrow good hI A seed n)).ladder
  composition n :=
    (refineState theta L chi hArrow good hI A
      (states theta L chi hArrow good hI A seed n)).composition

variable (hUncountable : Cardinal.aleph0 < chi)

/-- The returned slice uses precisely the preceding original chain union. -/
def extension (seed : Supports (P := P) chi) : Slice theta L chi := by
  let K := chain theta L chi hArrow good hI A seed
  exact
    { supports := unionSupport theta L chi hUncountable K
      le := fun d => by
        change (⊥ : LowerSet (P d)) ≤ _
        exact bot_le
      map := action theta L chi hUncountable K
      map_id := action_id theta L chi hUncountable K
      map_comp := fun g h => (action_comp theta L chi hUncountable K g h).symm
      map_root := action_root theta L chi hUncountable K
      map_endpoint := action_endpoint theta L chi hUncountable K
      labels_lt := total_selected_labels theta L chi hUncountable K hArrow }

theorem seed_le_extension (seed : Supports (P := P) chi) (d : D) :
    seed d ≤ (extension theta L chi hArrow good hI A hUncountable seed).supports d :=
  (seed_le_familySeed theta L chi hI A seed d).trans
    (seed_le_union theta L chi hUncountable
      (chain theta L chi hArrow good hI A seed) d)

/-- The prescribed inclusion is the same original lower comparison at stage zero. -/
def extensionInclusion (seed : Supports (P := P) chi) (i : I) :
    A i ⟶ extension theta L chi hArrow good hI A hUncountable seed where
  support_le d := (family_le_familySeed theta L chi hI A seed i d).trans
    (seed_le_union theta L chi hUncountable
      (chain theta L chi hArrow good hI A seed) d)
  naturality {d e} g := by
    let K := chain theta L chi hArrow good hI A seed
    let h0 : Contains theta L chi A (K.supports 0) :=
      family_le_familySeed theta L chi hI A seed
    have hP : Preserves theta L chi A (K.le 0) h0 (K.factors 0) :=
      (states theta L chi hArrow good hI A seed 0).preserves
    change ((L d).map ((h0 i d).trans
        (stage_le_union theta L chi hUncountable K d 0))).right ≫
      action theta L chi hUncountable K g = _
    rw [← (L d).map_comp (h0 i d)
      (stage_le_union theta L chi hUncountable K d 0), Under.comp_right, Category.assoc]
    change ((L d).map (h0 i d)).right ≫
      ((stageLeg theta L chi hUncountable K d 0).right ≫
        action theta L chi hUncountable K g) = _
    rw [action_fac theta L chi hUncountable K g 0, ← Category.assoc,
      hP i d e g, Category.assoc, ← Under.comp_right, (L e).map_comp]
    rfl

include hArrow good hI hUncountable in
/-- A genuinely bounded family has one larger slice and actual inclusion arrows. -/
theorem existsExtension (seed : Supports (P := P) chi) :
    ∃ (B : Slice theta L chi), (∀ d, seed d ≤ B.supports d) ∧
      Nonempty (∀ i : I, A i ⟶ B) :=
  ⟨extension theta L chi hArrow good hI A hUncountable seed,
    seed_le_extension theta L chi hArrow good hI A hUncountable seed,
    ⟨extensionInclusion theta L chi hArrow good hI A hUncountable seed⟩⟩

include hArrow good hUncountable in
/-- Actual bounded slices, with their full action-preserving arrows, are chi-filtered. -/
theorem cardinalFiltered : IsCardinalFiltered (Slice theta L chi) chi where
  nonempty_cocone {J} _ K hJ := by
    let hObj := hasCardinalLT_of_hasCardinalLT_arrow hJ
    let B := extension theta L chi hArrow good hObj K.obj hUncountable
      (emptySupports (P := P) chi)
    refine ⟨{ pt := B, ι := { app := ?_, naturality := ?_ } }⟩
    · intro j
      exact extensionInclusion theta L chi hArrow good hObj K.obj hUncountable
        (emptySupports (P := P) chi) j
    · intro i j g
      exact Subsingleton.elim _ _

end Chain

end CategoryTheory.SmallObject.DiagramSliceExtensions
