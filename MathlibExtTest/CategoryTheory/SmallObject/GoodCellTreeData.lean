/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Complete semantic clients of the rooted cell-tree data

The examples retain a nonpresentable root, a non-monomorphic actual
pushout, attaching labels in an independent universe, an empty tree,
and both distinct arrows of a nonthin ordinary index.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open CategoryTheory.ConcreteCategory

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

@[expose] public section

namespace GoodCellTreeDataExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Occurrence carriers have the equality order, with no other category dictionary. -/
structure Occurrence (β : Type) where
  /-- The original occurrence value. -/
  val : β

instance (β : Type) : PartialOrder (Occurrence β) where
  le a b := a = b
  lt _ _ := False
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h
  lt_iff_le_not_ge a b := by
    constructor
    · intro h
      exact h.elim
    · intro h
      exact h.2 h.1.symm

instance (β : Type) [Unique β] : Unique (Occurrence β) where
  default := ⟨default⟩
  uniq a := by
    cases a with
    | mk v => congr; exact Subsingleton.elim v _

instance (β : Type) [IsEmpty β] : IsEmpty (Occurrence β) where
  false a := isEmptyElim a.val

/-- A genuine one-occurrence vertex carrier. -/
abbrev OneVertex := Occurrence PUnit.{1}
/-- A genuine empty vertex carrier. -/
abbrev NoVertices := Occurrence Empty

/-- The original non-monomorphic cell. -/
def fold : Fin 2 ⟶ PUnit.{1} := ↾fun _ => PUnit.unit

/-- Attaching-family labels retain a universe independent of the vertex carrier. -/
abbrev foldFamily (_ : ULift.{t} PUnit.{1}) : Arrow (Type) := Arrow.mk fold

/-- The actual attaching label in its independent universe. -/
def originalLabel : ULift.{t} PUnit.{1} := ⟨PUnit.unit⟩

/-- This actual attaching map uses two different original natural numbers. -/
def attachNat : Fin 2 ⟶ ℕ := ↾fun i => i.val

/-- The actual chosen pushout arrow under the nonpresentable root ℕ. -/
def quotientArrow : ℕ ⟶ pushout attachNat fold := pushout.inl attachNat fold

/-- Its actual cell-target map. -/
def quotientCell : PUnit.{1} ⟶ pushout attachNat fold := pushout.inr attachNat fold

/-- The original square, with its actual chosen pushout object. -/
theorem quotientSquare : IsPushout attachNat fold quotientArrow quotientCell :=
  IsPushout.of_hasPushout attachNat fold

/-- A genuine nonempty tree over the original large root. -/
def quotientTree : CellTree foldFamily ℕ (P := OneVertex) :=
  CellTree.ofPushout foldFamily ℕ originalLabel attachNat quotientArrow quotientCell
    quotientSquare

theorem quotientTree_original_label (p : OneVertex) :
    quotientTree.label p = (originalLabel : ULift.{t} PUnit.{1}) := rfl

theorem quotientTree_original_root :
    quotientTree.hom = quotientArrow := rfl

/-- The root is actually not ℵ₀-presentable in Set. -/
theorem root_not_presentable : ¬ IsCardinalPresentable ℕ Cardinal.aleph0.{0} := by
  intro h
  have hh := (Types.isCardinalPresentable_iff Cardinal.aleph0.{0}).1 h
  have hn := (hasCardinalLT_iff_cardinal_mk_lt ℕ Cardinal.aleph0.{0}).1 hh
  simp only [Cardinal.mk_nat, lt_self_iff_false] at hn

instance finTwoPresentable : IsCardinalPresentable (Fin 2) Cardinal.aleph0.{0} :=
  (hasCardinalLT_of_finite (Fin 2) Cardinal.aleph0.{0} le_rfl).isCardinalPresentable

instance punitPresentable : IsCardinalPresentable PUnit.{1} Cardinal.aleph0.{0} :=
  (hasCardinalLT_of_finite PUnit.{1} Cardinal.aleph0.{0} le_rfl).isCardinalPresentable

/-- Goodness of a nonempty tree does not force absolute compactness of its root. -/
theorem quotientTreeGood : quotientTree.{t}.IsGood Cardinal.aleph0.{0} where
  presentable_source p := by
    change IsCardinalPresentable (Fin 2) Cardinal.aleph0.{0}
    exact finTwoPresentable
  presentable_target p := by
    change IsCardinalPresentable PUnit.{1} Cardinal.aleph0.{0}
    exact punitPresentable
  predecessor_lt p := by
    have : IsEmpty (Set.Iio p) := ⟨fun a => False.elim a.2⟩
    exact hasCardinalLT_of_finite _ Cardinal.aleph0.{0} le_rfl

/-- Both original numbers are identified by the actual chosen pushout arrow. -/
theorem quotientArrow_identifies : quotientArrow 0 = quotientArrow 1 := by
  have h0 := ConcreteCategory.congr_hom (pushout.condition (f := attachNat) (g := fold)) (0 : Fin 2)
  have h1 := ConcreteCategory.congr_hom (pushout.condition (f := attachNat) (g := fold)) (1 : Fin 2)
  have e0 : quotientArrow 0 = quotientCell PUnit.unit := by
    change quotientArrow (attachNat (0 : Fin 2)) = quotientCell (fold (0 : Fin 2)) at h0
    exact h0
  have e1 : quotientArrow 1 = quotientCell PUnit.unit := by
    change quotientArrow (attachNat (1 : Fin 2)) = quotientCell (fold (1 : Fin 2)) at h1
    exact h1
  exact e0.trans e1.symm

/-- The tree's original root-to-target arrow is genuinely non-monomorphic. -/
theorem quotientArrow_not_mono : ¬ Mono quotientArrow := by
  intro h
  have hi := (mono_iff_injective quotientArrow).1 h
  exact Nat.zero_ne_one (hi quotientArrow_identifies)

/-- The attaching cell itself is genuinely non-monomorphic. -/
theorem fold_not_mono : ¬ Mono fold := by
  intro h
  have hi := (mono_iff_injective fold).1 h
  have he : (0 : Fin 2) = 1 := hi (by rfl)
  norm_num at he

/-- The actual empty tree keeps ℕ as its original root. -/
def emptyTree : CellTree foldFamily ℕ (P := NoVertices) :=
  CellTree.empty foldFamily ℕ

theorem emptyTree_original_arrow : emptyTree.hom = 𝟙 ℕ := rfl

theorem emptyTreeGood : emptyTree.IsGood Cardinal.aleph0.{0} :=
  CellTree.emptyIsGood Cardinal.aleph0.{0}

/-- The original-root empty lower comparison is a genuine Under isomorphism. -/
def quotientEmptyLowerIso :
    quotientTree.{t}.lowerData.obj ⊥ ≅ Under.mk (𝟙 ℕ) :=
  quotientTree.{t}.emptyLowerIso quotientTree.{t}.lowerData

theorem quotientEmptyLower_root :
    (quotientTree.lowerData.obj ⊥).hom ≫ quotientEmptyLowerIso.hom.right = 𝟙 ℕ :=
  Under.w quotientEmptyLowerIso.hom

/-- Both maps of the full original endpoint comparison are actual inverse functions. -/
def quotientWholeEndpointIso :
    quotientTree.{t}.lowerData.obj ⊤ ≅ quotientTree.{t}.endpointObj :=
  quotientTree.{t}.endpointIso quotientTree.{t}.lowerData

theorem quotientWholeEndpoint_inverse :
    quotientWholeEndpointIso.{t}.hom ≫ quotientWholeEndpointIso.{t}.inv =
      𝟙 (quotientTree.{t}.lowerData.obj ⊤) :=
  quotientWholeEndpointIso.{t}.hom_inv_id

/-- All original lower comparison functions give an actual underlying pushout,
even though this tree contains a non-monomorphic cell. -/
theorem quotientLowerUnion
    (B D : LowerSet OneVertex) :
    IsPushout
      ((quotientTree.lowerData.map (inf_le_left : B ⊓ D ≤ B)).right)
      ((quotientTree.lowerData.map (inf_le_right : B ⊓ D ≤ D)).right)
      ((quotientTree.lowerData.map (le_sup_left : B ≤ B ⊔ D)).right)
      ((quotientTree.lowerData.map (le_sup_right : D ≤ B ⊔ D)).right) :=
  (quotientTree.lowerData.union_isPushout B D).map (Under.forget ℕ)

/-- The two source actions of this ordinary index are distinct actual functions. -/
def swap : Fin 2 ⟶ Fin 2 := ↾Fin.rev

/-- Both distinct original parallel source actions. -/
def parallelSource : WalkingParallelPair ⥤ Type :=
  parallelPair (𝟙 (Fin 2)) swap

/-- The original constant target diagram. -/
def parallelTarget : WalkingParallelPair ⥤ Type :=
  (Functor.const WalkingParallelPair).obj PUnit.{1}

/-- The original fold transformation is natural for both distinct parallel actions. -/
def parallelFold : parallelSource ⟶ parallelTarget where
  app d := by cases d <;> exact fold
  naturality _ _ g := by
    cases g <;> ext x <;> rfl

theorem parallel_actions_different :
    parallelSource.map WalkingParallelPairHom.left ≠
      parallelSource.map WalkingParallelPairHom.right := by
  intro h
  have hh := ConcreteCategory.congr_hom h (0 : Fin 2)
  change (0 : Fin 2) = 1 at hh
  norm_num at hh

/-- Both original arrow naturalities are retained without a thin-index assumption. -/
theorem parallel_left_naturality :
    parallelSource.map WalkingParallelPairHom.left ≫ parallelFold.app .one =
      parallelFold.app .zero ≫ parallelTarget.map WalkingParallelPairHom.left :=
  parallelFold.naturality WalkingParallelPairHom.left

theorem parallel_right_naturality :
    parallelSource.map WalkingParallelPairHom.right ≫ parallelFold.app .one =
      parallelFold.app .zero ≫ parallelTarget.map WalkingParallelPairHom.right :=
  parallelFold.naturality WalkingParallelPairHom.right

/-- Actual component tree data on an ordinary NONTHIN source category. -/
def parallelTrees :
    PointwiseCellTreePresentation foldFamily parallelFold
      (fun (_ : WalkingParallelPair) => OneVertex) where
  component d := by
    cases d
    · exact CellTree.presentationOfPushout (s := foldFamily) (X := Fin 2)
        originalLabel (𝟙 (Fin 2)) fold (𝟙 PUnit.{1}) (IsPushout.of_id_fst (f := fold))
    · exact CellTree.presentationOfPushout (s := foldFamily) (X := Fin 2)
        originalLabel (𝟙 (Fin 2)) fold (𝟙 PUnit.{1}) (IsPushout.of_id_fst (f := fold))

theorem parallel_component_original_endpoint (d : WalkingParallelPair) :
    (parallelTrees.component d).tree.hom ≫
      (parallelTrees.component d).endpointIso.hom.right = parallelFold.app d :=
  (parallelTrees.component d).hom_endpointIso_hom

/-- The genuine source-preserving Arrow isomorphism of every original component. -/
def parallelComponentArrowIso (d : WalkingParallelPair) :
    Arrow.mk (parallelTrees.component d).tree.hom ≅ Arrow.mk (parallelFold.app d) :=
  (parallelTrees.component d).arrowIso

/-- Literal Set difference retains an uncovered upper occurrence. -/
theorem literal_increment_one :
    (1 : ℕ) ∈ ((LowerSet.Iic 1 : LowerSet ℕ) : Set ℕ) \
      ((LowerSet.Iic 0 : LowerSet ℕ) : Set ℕ) := by
  norm_num

/-- The bundled lower-set difference is a different operation. -/
theorem bundled_difference_loses_one :
    (1 : ℕ) ∉ (LowerSet.Iic 1).sdiff ((LowerSet.Iic 0 : LowerSet ℕ) : Set ℕ) := by
  change ¬ (1 ≤ 1 ∧ (1 : ℕ) ∉ upperClosure {n : ℕ | n ≤ 0})
  simp

end GoodCellTreeDataExamples
