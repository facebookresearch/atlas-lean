/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerPresentation
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Infinite original nonmonomorphic fold cells and bounded presentations

All original adjacent natural-number relations have their chosen native
pushouts. Their endpoint is the constant under-object on PUnit. Every
bounded chosen piece is relatively presentable, while the full endpoint
is not. A finite original set of relations has its actual nonconstant
root comparison, so no full-endpoint under-map into that piece exists.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  LowerSetColimits BoundedLowerSupport

namespace BoundedLowerPresentationExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original countably infinite equality-order occurrence carrier. -/
abbrev Index := GoodCellTreeDataExamples.Occurrence ℕ

/-- This occurrence attaches the actual two original root values n and n+1. -/
def attach (n : ℕ) : Fin 2 ⟶ ℕ := ↾fun i => n + i.val

/-- Retain the actual chosen native pushout source leg for each original occurrence. -/
def quotient (n : ℕ) : ℕ ⟶ pushout (attach n) GoodCellTreeDataExamples.fold :=
  pushout.inl (attach n) GoodCellTreeDataExamples.fold

/-- Retain its actual original fold-cell target leg. -/
def cell (n : ℕ) : PUnit.{1} ⟶ pushout (attach n) GoodCellTreeDataExamples.fold :=
  pushout.inr (attach n) GoodCellTreeDataExamples.fold

/-- Every original adjacent relation has its entire genuine native pushout square. -/
theorem square (n : ℕ) :
    IsPushout (attach n) GoodCellTreeDataExamples.fold (quotient n) (cell n) :=
  IsPushout.of_hasPushout (attach n) GoodCellTreeDataExamples.fold

/-- The original pushout identifies these displayed adjacent root values. -/
theorem identifies (n : ℕ) : quotient n n = quotient n (n + 1) := by
  have h0 := ConcreteCategory.congr_hom
    (pushout.condition (f := attach n) (g := GoodCellTreeDataExamples.fold)) (0 : Fin 2)
  have h1 := ConcreteCategory.congr_hom
    (pushout.condition (f := attach n) (g := GoodCellTreeDataExamples.fold)) (1 : Fin 2)
  have e0 : quotient n n = cell n PUnit.unit := by
    change quotient n (n + 0) = cell n PUnit.unit at h0
    simpa only [Nat.add_zero] using h0
  have e1 : quotient n (n + 1) = cell n PUnit.unit := by
    exact h1
  exact e0.trans e1.symm

/-- Each original chosen quotient is genuinely nonmonomorphic. -/
theorem quotient_not_mono (n : ℕ) : ¬ Mono (quotient n) := by
  intro h
  have e : n = n + 1 := (mono_iff_injective (quotient n)).1 h (identifies n)
  omega

/-- The same actual occurrence diagram uses only its original equality-order maps. -/
def originalDiagram : Index ⥤ Under ℕ where
  obj a := Under.mk (quotient a.val)
  map {a b} f := eqToHom (by
    have h : a = b := leOfHom f
    exact congrArg (fun k : Index => Under.mk (quotient k.val)) h)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- Every original strict-predecessor carrier of this equality order is empty. -/
theorem predecessors_empty (a : Index) : IsEmpty (LowerSet.Iio a) :=
  ⟨fun b => False.elim b.2⟩

/-- The actual given empty predecessor colimit retains identity under the original root. -/
def predecessor (a : Index) :
    ColimitCocone (restriction originalDiagram (LowerSet.Iio a)) := by
  let : IsEmpty (LowerSet.Iio a) := predecessors_empty a
  exact
    { cocone :=
        { pt := Under.mk (𝟙 ℕ)
          ι := { app b := isEmptyElim b
                 naturality b _ _ := by exact False.elim (IsEmpty.false b) } }
      isColimit :=
        { desc c := Under.mkIdInitial.to c.pt
          fac c b := isEmptyElim b
          uniq c m _ := Under.mkIdInitial.hom_ext m (Under.mkIdInitial.to c.pt) } }

/-- The original whole endpoint root function is actually constant. -/
def root : ℕ ⟶ PUnit.{1} := ↾fun _ => PUnit.unit

/-- The original whole endpoint remains under the same nonpresentable Nat root. -/
abbrev endpointObj : Under ℕ := Under.mk root

/-- Each original vertex has its literal constant endpoint leg under Nat. -/
def endpointLeg (a : Index) : originalDiagram.obj a ⟶ endpointObj :=
  Under.homMk (↾fun _ => PUnit.unit) (by ext n; rfl)

/-- The entire original full-index endpoint cocone. -/
def endpointCocone : Cocone originalDiagram where
  pt := endpointObj
  ι :=
    { app a := endpointLeg a
      naturality a b f := by
        have h : a = b := leOfHom f
        subst b
        have hf : f = 𝟙 a := Subsingleton.elim _ _
        subst f
        simp }

/-- The original raw square forces every given cocone's adjacent root values equal. -/
theorem cocone_adjacent (c : Cocone originalDiagram) (n : ℕ) :
    c.pt.hom n = c.pt.hom (n + 1) := by
  let a : Index := ⟨n⟩
  have h0 := ConcreteCategory.congr_hom (Under.w (c.ι.app a)) n
  have h1 := ConcreteCategory.congr_hom (Under.w (c.ι.app a)) (n + 1)
  change (c.ι.app a).right (quotient n n) = c.pt.hom n at h0
  change (c.ι.app a).right (quotient n (n + 1)) = c.pt.hom (n + 1) at h1
  exact h0.symm.trans ((congrArg (c.ι.app a).right (identifies n)).trans h1)

/-- The whole given cocone root function has its actual value at zero everywhere. -/
theorem cocone_root_value (c : Cocone originalDiagram) (n : ℕ) :
    c.pt.hom n = c.pt.hom 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (cocone_adjacent c n).symm.trans ih

/-- The actual endpoint descender sends the original unit to the cocone's original root at zero. -/
def endpointDesc (c : Cocone originalDiagram) : endpointObj ⟶ c.pt :=
  Under.homMk (↾fun _ => c.pt.hom 0) (by
    ext n
    exact (cocone_root_value c n).symm)

/-- Every original vertex leg factors through that SAME full descender. -/
theorem endpointDesc_fac (c : Cocone originalDiagram) (a : Index) :
    endpointLeg a ≫ endpointDesc c = c.ι.app a := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · exact (Under.w (endpointLeg a ≫ endpointDesc c)).trans (Under.w (c.ι.app a)).symm
  · ext u
    cases u
    change c.pt.hom 0 = (c.ι.app a).right (cell a.val PUnit.unit)
    have h0 := ConcreteCategory.congr_hom
      (pushout.condition (f := attach a.val) (g := GoodCellTreeDataExamples.fold)) (0 : Fin 2)
    have he : quotient a.val a.val = cell a.val PUnit.unit := by
      change quotient a.val (a.val + 0) = cell a.val PUnit.unit at h0
      simpa only [Nat.add_zero] using h0
    have hw := ConcreteCategory.congr_hom (Under.w (c.ι.app a)) a.val
    change (c.ι.app a).right (quotient a.val a.val) = c.pt.hom a.val at hw
    rw [← he, hw]
    exact (cocone_root_value c a.val).symm

/-- The original root equation alone detects the whole endpoint descender function. -/
theorem endpointDesc_uniq (c : Cocone originalDiagram) (m : endpointObj ⟶ c.pt) :
    m = endpointDesc c := by
  apply Under.UnderMorphism.ext
  ext u
  cases u
  exact ConcreteCategory.congr_hom (Under.w m) 0

/-- The entire displayed original endpoint cocone has its genuine universal property. -/
def endpointIsColimit : IsColimit endpointCocone where
  desc c := endpointDesc c
  fac c a := endpointDesc_fac c a
  uniq c m _ := endpointDesc_uniq c m

/-- Retain the same endpoint cocone and its fully proved colimit dictionary. -/
def endpoint : ColimitCocone originalDiagram := ⟨endpointCocone, endpointIsColimit⟩

/-- Infinitely many actual nonmonomorphic fold cells over the arbitrary original Nat source. -/
def tree : CellTree GoodCellTreeDataExamples.foldFamily ℕ (P := Index) where
  wellFounded := ⟨fun a => Acc.intro a (fun _ h => False.elim h)⟩
  diagram := originalDiagram
  label _ := GoodCellTreeDataExamples.originalLabel
  predecessor a := predecessor a
  attaching a := attach a.val
  cell a := cell a.val
  isPushout a := by
    have hp : cellTreePredecessorMap originalDiagram a (predecessor a) =
        Under.mkIdInitial.to (originalDiagram.obj a) :=
      Under.mkIdInitial.hom_ext _ _
    have hr : (cellTreePredecessorMap originalDiagram a (predecessor a)).right =
        quotient a.val := by
      simpa only [Under.mkIdInitial_to_right, Under.mk_hom, originalDiagram] using
        congrArg (fun k => k.right) hp
    rw [hr]
    exact square a.val
  endpoint := endpoint

theorem original_label (a : Index) :
    tree.{t}.label a = (GoodCellTreeDataExamples.originalLabel : ULift.{t} PUnit.{1}) := rfl

theorem original_root_function : tree.{t}.hom = root := rfl

/-- All original cells have compact endpoints and genuinely empty strict predecessors. -/
theorem good : tree.{t}.IsGood Cardinal.aleph0.{0} where
  presentable_source _ := GoodCellTreeDataExamples.finTwoPresentable
  presentable_target _ := GoodCellTreeDataExamples.punitPresentable
  predecessor_lt a := by
    let : IsEmpty (Set.Iio a) := ⟨fun b => False.elim b.2⟩
    exact hasCardinalLT_of_finite _ Cardinal.aleph0.{0} le_rfl

/-- All actual bounded chosen pieces are presentable relative to the SAME nonpresentable root. -/
theorem all_bounded_pieces_presentable (B : Carrier (P := Index) Cardinal.aleph0.{0}) :
    IsCardinalPresentable (tree.{t}.lowerData.obj B.1) Cardinal.aleph0.{0} :=
  BoundedLowerPresentation.piecePresentable Cardinal.aleph0.{0} tree.{t} good.{t} tree.{t}.lowerData B

/-- The exact bounded-support native presentation of the full original endpoint. -/
def originalPresentation :
    ColimitPresentation (Carrier (P := Index) Cardinal.aleph0.{0}) tree.{t}.endpointObj :=
  BoundedLowerPresentation.treePresentation Cardinal.aleph0.{0}
    tree.{t} good.{t} tree.{t}.lowerData

/-- A finite original relation support has this actual nonconstant root comparison. -/
def finiteRoot (N : ℕ) : ℕ ⟶ ℕ := ↾fun k => k - (N + 1)

/-- The actual root values on any bounded occurrence relation agree at zero. -/
theorem finiteCondition (N n : ℕ) (hn : n ≤ N) :
    attach n ≫ finiteRoot N = GoodCellTreeDataExamples.fold ≫ (↾fun _ => (0 : ℕ)) := by
  ext i
  change n + i.val - (N + 1) = 0
  have hi : i.val ≤ 1 := by omega
  omega

/-- The given original finite lower support has a complete actual under-root cocone. -/
def finiteCocone (B : LowerSet Index) (N : ℕ) (hN : ∀ a : B, a.1.val ≤ N) :
    Cocone (restriction originalDiagram B) where
  pt := Under.mk (finiteRoot N)
  ι :=
    { app a := Under.homMk
        (pushout.desc (finiteRoot N) (↾fun _ => (0 : ℕ)) (finiteCondition N a.1.val (hN a)))
        (pushout.inl_desc _ _ _)
      naturality a b f := by
        have h : a = b := Subtype.ext (leOfHom f)
        subst b
        have hf : f = 𝟙 a := Subsingleton.elim _ _
        subst f
        simp }

/-- No original whole-endpoint under-map can land in any bounded chosen piece. -/
theorem no_under_factor (B : Carrier (P := Index) Cardinal.aleph0.{0}) :
    ¬ Nonempty (tree.{t}.endpointObj ⟶ tree.{t}.lowerData.obj B.1) := by
  let : Finite (B.1 : Set Index) := (hasCardinalLT_aleph0_iff (B.1 : Set Index)).1 B.2
  let : Fintype (B.1 : Set Index) := Fintype.ofFinite _
  let N : ℕ := Finset.univ.sup (fun a : B.1 => a.1.val)
  have hN (a : B.1) : a.1.val ≤ N :=
    Finset.le_sup (f := fun a : B.1 => a.1.val) (Finset.mem_univ a)
  let c := finiteCocone B.1 N hN
  let comparison : tree.{t}.lowerData.obj B.1 ⟶ Under.mk (finiteRoot N) :=
    (tree.{t}.lowerData.isColimit B.1).desc c
  rintro ⟨p⟩
  let m : endpointObj ⟶ Under.mk (finiteRoot N) := p ≫ comparison
  have h0 := ConcreteCategory.congr_hom (Under.w m) 0
  have h1 := ConcreteCategory.congr_hom (Under.w m) (N + 2)
  change (m.right PUnit.unit : ℕ) = (0 : ℕ) - (N + 1) at h0
  change (m.right PUnit.unit : ℕ) = N + 2 - (N + 1) at h1
  have e0 : m.right PUnit.unit = (0 : ℕ) := by
    simpa only [Nat.zero_sub] using h0
  have e1 : m.right PUnit.unit = (1 : ℕ) := by
    simpa only [Nat.add_sub_add_left] using h1
  exact Nat.zero_ne_one (e0.symm.trans e1)

/-- Its complete original κ-filtered presentation proves genuine relative nonpresentability. -/
theorem endpoint_not_presentable :
    ¬ IsCardinalPresentable tree.{t}.endpointObj Cardinal.aleph0.{0} := by
  intro h
  let : IsCardinalPresentable tree.{t}.endpointObj Cardinal.aleph0.{0} := h
  obtain ⟨B, p, _⟩ := BoundedLowerPresentation.existsTreeFactor Cardinal.aleph0.{0}
    tree.{t} good.{t} tree.{t}.lowerData (𝟙 tree.{t}.endpointObj)
  exact no_under_factor.{t} B ⟨p⟩

/-- The actual base endpoint remains absolutely finite and presentable. -/
theorem base_endpoint_presentable :
    IsCardinalPresentable tree.{t}.endpointObj.right Cardinal.aleph0.{0} :=
  GoodCellTreeDataExamples.punitPresentable

/-- A raw finite source DOES have its actual factor, retaining the original independent labels. -/
theorem original_unit_raw_factor :
    ∃ (B : Carrier (P := Index) Cardinal.aleph0.{0}),
      BoundedLowerSupport.empty Cardinal.aleph0.{0} ≤ B ∧
        ∃ (p : PUnit.{1} ⟶ (tree.{t}.lowerData.obj B.1).right),
          p ≫ (tree.{t}.lowerData.map (le_top : B.1 ≤ ⊤) ≫
            (tree.{t}.endpointIso tree.{t}.lowerData).hom).right = 𝟙 PUnit.{1} :=
  BoundedLowerPresentation.existsRawFactorContaining Cardinal.aleph0.{0}
    tree.{t} good.{t} tree.{t}.lowerData (𝟙 PUnit.{1})
    (BoundedLowerSupport.empty Cardinal.aleph0.{0})

end BoundedLowerPresentationExamples
