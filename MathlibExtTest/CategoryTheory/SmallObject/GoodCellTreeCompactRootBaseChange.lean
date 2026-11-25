/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRootBaseChange
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeRootChangeCapture
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# Full original compact-root semantic clients

The actual constructor is applied to the original noncompact Nat root and
nonmonomorphic fold tree, and to its empty-tree counterpart. Generic clients
keep all coefficient, Hom, cell-label and working universes independent and
exercise every root, predecessor, endpoint and lower comparison function.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
  CompactRootBaseChange LowerSetColimits

namespace CompactRootBaseChangeExamples

section NoncompactOriginalRoot

attribute [local instance] Cardinal.fact_isRegular_aleph0

open GoodCellTreeDataExamples

/-- The complete actual constructor on the original nonempty fold tree under Nat. -/
def quotientCompact : CompactRootPresentation Cardinal.aleph0.{0} quotientTree.{t} :=
  compactRootPresentation Cardinal.aleph0.{0} quotientTree.{t}
    (hasCardinalLT_of_finite OneVertex Cardinal.aleph0.{0} le_rfl)
    quotientTreeGood.{t}.presentable_source quotientTreeGood.{t}.presentable_target

/-- The complete actual constructor on the original empty tree under the same Nat root. -/
def emptyCompact : CompactRootPresentation Cardinal.aleph0.{0} emptyTree.{t} :=
  compactRootPresentation Cardinal.aleph0.{0} emptyTree.{t}
    (hasCardinalLT_of_finite NoVertices Cardinal.aleph0.{0} le_rfl)
    emptyTreeGood.{t}.presentable_source emptyTreeGood.{t}.presentable_target

/-- The same original root is not compact at the construction's actual cardinal. -/
theorem originalRoot_noncompact : ¬ IsCardinalPresentable ℕ Cardinal.aleph0.{0} :=
  root_not_presentable

/-- The original coefficient endpoint is also noncompact; only the new pieces are compact. -/
theorem originalEndpoint_noncompact :
    ¬ IsCardinalPresentable quotientTree.{t}.endpointObj.right Cardinal.aleph0.{0} :=
  RootChangeCaptureExamples.originalCoefficientNotPresentable.{t}

/-- The original cell is genuinely nonmonomorphic, with its two original source values. -/
theorem originalCell_nonmono : ¬ Mono fold := fold_not_mono

/-- The original root-to-endpoint function is genuinely nonmonomorphic. -/
theorem originalEndpoint_nonmono : ¬ Mono quotientTree.{t}.hom := quotientArrow_not_mono

/-- Every new attaching-family label retains its same independently raised original value. -/
theorem quotientLabels : quotientCompact.{t}.tree.label = quotientTree.{t}.label :=
  quotientCompact.{t}.label_eq

/-- The actual new root is compact even though the original Nat root is not. -/
theorem quotientRoot_compact : IsCardinalPresentable quotientCompact.{t}.root Cardinal.aleph0.{0} :=
  quotientCompact.{t}.root_presentable

/-- The actual new whole endpoint is compact while its original coefficient endpoint is not. -/
theorem quotientEndpoint_compact :
    IsCardinalPresentable quotientCompact.{t}.tree.endpointObj.right Cardinal.aleph0.{0} :=
  quotientCompact.{t}.endpoint_presentable

/-- Every actual selected new lower piece is compact at the same original cardinal. -/
theorem quotientLower_compact (B : LowerSet OneVertex) :
    IsCardinalPresentable (quotientCompact.{t}.lower.obj B).right Cardinal.aleph0.{0} :=
  quotientCompact.{t}.lower_presentable B

/-- The actual new predecessor is compact, with no compactness premise on old Nat. -/
theorem quotientPredecessor_compact (p : OneVertex) :
    IsCardinalPresentable (quotientCompact.{t}.tree.predecessorObj p).right Cardinal.aleph0.{0} :=
  quotientCompact.{t}.predecessor_presentable p

/-- The actual original singleton predecessor point is the original identity under Nat. -/
def quotientOriginalPredecessorIso (p : OneVertex) :
    quotientTree.{t}.predecessorObj p ≅ Under.mk (𝟙 ℕ) := eqToIso rfl

/-- The original attaching map interpreted through that actual native predecessor point. -/
def quotientOriginalAttachingNat (p : OneVertex) : Fin 2 ⟶ ℕ :=
  quotientTree.{t}.attaching p ≫ (quotientOriginalPredecessorIso.{t} p).hom.right

/-- The complete actual original attaching function has its native Nat value. -/
theorem quotientOriginalAttachingNat_eq (p : OneVertex) :
    quotientOriginalAttachingNat.{t} p = attachNat := rfl

/-- The new predecessor coefficient map, through both actual original native comparisons. -/
def quotientPredecessorCoefficient (p : OneVertex) :
    (quotientCompact.{t}.tree.predecessorObj p).right ⟶ ℕ :=
  pushout.inl (quotientCompact.{t}.tree.predecessorObj p).hom quotientCompact.{t}.rootMap ≫
    (quotientCompact.{t}.predecessorComparison p).hom.right ≫
    (quotientOriginalPredecessorIso.{t} p).hom.right

/-- The actual whole new attaching function interpreted at the original native Nat point. -/
def quotientAttachingNat (p : OneVertex) : Fin 2 ⟶ ℕ :=
  quotientCompact.{t}.tree.attaching p ≫ quotientPredecessorCoefficient.{t} p

/-- The returned whole-function field retains the complete original attaching map. -/
theorem quotientAttachingNat_eq (p : OneVertex) : quotientAttachingNat.{t} p = attachNat := by
  let g := quotientCompact.{t}.tree.attaching p
  let u := pushout.inl (quotientCompact.{t}.tree.predecessorObj p).hom quotientCompact.{t}.rootMap
  let e := (quotientCompact.{t}.predecessorComparison p).hom.right
  let z := (quotientOriginalPredecessorIso.{t} p).hom.right
  have hField := congrFun quotientCompact.{t}.attaching_function p
  change g ≫ u ≫ e = 𝟙 (Fin 2) ≫ quotientTree.{t}.attaching p at hField
  have h := hField.trans (Category.id_comp _)
  have hPost := congrArg (fun m : Fin 2 ⟶ (quotientTree.{t}.predecessorObj p).right => m ≫ z) h
  have hAssoc : (g ≫ u ≫ e) ≫ z = g ≫ u ≫ e ≫ z :=
    (Category.assoc g (u ≫ e) z).trans
      (congrArg (fun m => g ≫ m) (Category.assoc u e z))
  change g ≫ u ≫ e ≫ z = attachNat
  exact hAssoc.symm.trans (hPost.trans (quotientOriginalAttachingNat_eq.{t} p))

/-- The whole original attaching function is retained at both distinct finite source values. -/
theorem quotientAttachingValue (p : OneVertex) (b : Fin 2) :
    quotientAttachingNat.{t} p b = b.val :=
  congrArg (fun f : Fin 2 ⟶ ℕ => f b) (quotientAttachingNat_eq.{t} p)

/-- The two new attaching values remain distinct because their original images are 0 and 1. -/
theorem quotientAttachingValues_distinct (p : OneVertex) :
    quotientCompact.{t}.tree.attaching p (0 : Fin 2) ≠
      quotientCompact.{t}.tree.attaching p (1 : Fin 2) := by
  intro h
  let m := quotientPredecessorCoefficient.{t} p
  have he := congrArg m h
  have h₀ := quotientAttachingValue.{t} p (0 : Fin 2)
  have h₁ := quotientAttachingValue.{t} p (1 : Fin 2)
  change m (quotientCompact.{t}.tree.attaching p (0 : Fin 2)) = 0 at h₀
  change m (quotientCompact.{t}.tree.attaching p (1 : Fin 2)) = 1 at h₁
  exact Nat.zero_ne_one (h₀.symm.trans (he.trans h₁))

/-- The actual original vertex point is the same original native quotient under Nat. -/
def quotientOriginalVertexIso (p : OneVertex) :
    quotientTree.{t}.vertex p ≅ Under.mk quotientArrow := eqToIso rfl

/-- The new vertex coefficient map retains both actual original native comparisons. -/
def quotientVertexCoefficient (p : OneVertex) :
    (quotientCompact.{t}.tree.vertex p).right ⟶ pushout attachNat fold :=
  pushout.inl (quotientCompact.{t}.tree.vertex p).hom quotientCompact.{t}.rootMap ≫
    (quotientCompact.{t}.comparison.hom.app p).right ≫
    (quotientOriginalVertexIso.{t} p).hom.right

/-- The complete new target-cell function interpreted at the same actual original quotient point. -/
def quotientCellNative (p : OneVertex) : PUnit.{1} ⟶ pushout attachNat fold :=
  quotientCompact.{t}.tree.cell p ≫ quotientVertexCoefficient.{t} p

/-- The returned whole target-cell field preserves the actual original native inclusion. -/
theorem quotientCellNative_eq (p : OneVertex) : quotientCellNative.{t} p = quotientCell := by
  let k := quotientCompact.{t}.tree.cell p
  let u := pushout.inl (quotientCompact.{t}.tree.vertex p).hom quotientCompact.{t}.rootMap
  let e := (quotientCompact.{t}.comparison.hom.app p).right
  let z := (quotientOriginalVertexIso.{t} p).hom.right
  have hField := congrFun quotientCompact.{t}.cell_function p
  change k ≫ u ≫ e = 𝟙 PUnit.{1} ≫ quotientTree.{t}.cell p at hField
  have h := hField.trans (Category.id_comp _)
  have hPost := congrArg
    (fun m : PUnit.{1} ⟶ (quotientTree.{t}.vertex p).right => m ≫ z) h
  have hAssoc : (k ≫ u ≫ e) ≫ z = k ≫ u ≫ e ≫ z :=
    (Category.assoc k (u ≫ e) z).trans
      (congrArg (fun m => k ≫ m) (Category.assoc u e z))
  have hNative : quotientTree.{t}.cell p ≫ z = quotientCell := rfl
  change k ≫ u ≫ e ≫ z = quotientCell
  exact hAssoc.symm.trans (hPost.trans hNative)

/-- Every original generator-target value retains the actual original native cell inclusion. -/
theorem quotientCellValue (p : OneVertex) (b : PUnit.{1}) :
    quotientCellNative.{t} p b = quotientCell b :=
  congrArg (fun f : PUnit.{1} ⟶ pushout attachNat fold => f b) (quotientCellNative_eq.{t} p)

/-- The full original Nat root function is retained at every natural number. -/
theorem quotientEndpointRootValue (n : ℕ) :
    (pushout.inr quotientCompact.{t}.tree.hom quotientCompact.{t}.rootMap ≫
      quotientCompact.{t}.endpointComparison.hom.right) n = quotientArrow n :=
  ConcreteCategory.congr_hom (Under.w quotientCompact.{t}.endpointComparison.hom) n

/-- The inverse endpoint comparison retains every actual original root value as well. -/
theorem quotientEndpointRootValue_inv (n : ℕ) :
    (quotientArrow ≫ quotientCompact.{t}.endpointComparison.inv.right) n =
      pushout.inr quotientCompact.{t}.tree.hom quotientCompact.{t}.rootMap n := by
  have h := ConcreteCategory.congr_hom (Under.w quotientCompact.{t}.endpointComparison.inv) n
  exact h

/-- Both root maps and the entire original quotient endpoint form the actual native pushout. -/
theorem quotientEndpointPushout :
    IsPushout quotientCompact.{t}.tree.hom quotientCompact.{t}.rootMap
      (pushout.inl quotientCompact.{t}.tree.hom quotientCompact.{t}.rootMap ≫
        quotientCompact.{t}.endpointComparison.hom.right) quotientArrow :=
  quotientCompact.{t}.endpoint_isPushout

/-- All original lower pairs retain their actual whole map function after root change. -/
theorem quotientAllLowerMap (B D : LowerSet OneVertex) (h : B ≤ D) :
    (Under.pushout quotientCompact.{t}.rootMap).map (quotientCompact.{t}.lower.map h) ≫
      (quotientCompact.{t}.lowerComparison quotientTree.{t}.lowerData).hom.app D =
    (quotientCompact.{t}.lowerComparison quotientTree.{t}.lowerData).hom.app B ≫
      quotientTree.{t}.lowerData.map h :=
  (quotientCompact.{t}.lowerComparison quotientTree.{t}.lowerData).hom.naturality (homOfLE h)

/-- Both directions preserve the complete actual lower-to-endpoint Iso, with its same choices. -/
theorem quotientAllLowerEndpoint :
    (Under.pushout quotientCompact.{t}.rootMap).mapIso
      (quotientCompact.{t}.tree.endpointIso quotientCompact.{t}.lower) ≪≫
      quotientCompact.{t}.endpointComparison =
    (quotientCompact.{t}.lowerComparison quotientTree.{t}.lowerData).app ⊤ ≪≫
      quotientTree.{t}.endpointIso quotientTree.{t}.lowerData :=
  quotientCompact.{t}.lower_endpoint_iso quotientTree.{t}.lowerData

/-- Empty old labels still produce an actual compact root through the genuine full cone. -/
theorem emptyRoot_compact : IsCardinalPresentable emptyCompact.{t}.root Cardinal.aleph0.{0} :=
  emptyCompact.{t}.root_presentable

/-- The actual empty-tree new endpoint is compact by its root-adjoined singleton C diagram. -/
theorem emptyEndpoint_compact :
    IsCardinalPresentable emptyCompact.{t}.tree.endpointObj.right Cardinal.aleph0.{0} :=
  emptyCompact.{t}.endpoint_presentable

/-- The empty lower choice retains its actual new root through the native initial Under Iso. -/
def emptyNewRootIso : emptyCompact.{t}.lower.obj ⊥ ≅ Under.mk (𝟙 emptyCompact.{t}.root) :=
  emptyCompact.{t}.tree.emptyLowerIso emptyCompact.{t}.lower

/-- The original empty Nat-root tree has its full actual compact-root endpoint pushout. -/
theorem emptyEndpointPushout :
    IsPushout emptyCompact.{t}.tree.hom emptyCompact.{t}.rootMap
      (pushout.inl emptyCompact.{t}.tree.hom emptyCompact.{t}.rootMap ≫
        emptyCompact.{t}.endpointComparison.hom.right) (𝟙 ℕ) :=
  emptyCompact.{t}.endpoint_isPushout

/-- The original empty-tree identity root is retained at every original natural number. -/
theorem emptyEndpointRootValue (n : ℕ) :
    (pushout.inr emptyCompact.{t}.tree.hom emptyCompact.{t}.rootMap ≫
      emptyCompact.{t}.endpointComparison.hom.right) n = n :=
  ConcreteCategory.congr_hom (Under.w emptyCompact.{t}.endpointComparison.hom) n

/-- The actual empty new tree still retains its true entire root-adjoined colimit UP. -/
abbrev emptyNewAdjoined : ColimitCocone
    (UnderColimits.adjoinedDiagram (Y := emptyCompact.{t}.tree.diagram)) :=
  UnderColimits.adjoinedColimit emptyCompact.{t}.tree.endpoint

/-- The root-adjoined star retains the actual selected new root-to-endpoint function. -/
theorem emptyNewAdjoinedStar :
    emptyNewAdjoined.{t}.cocone.ι.app WithInitial.star = emptyCompact.{t}.tree.hom :=
  UnderColimits.adjoined_star emptyCompact.{t}.tree.endpoint.cocone

end NoncompactOriginalRoot

section IndependentFullUniverses

variable {C : Type u} [Category.{v} C] [HasPushouts C] [HasColimitsOfSize.{w, w} C]
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalAccessibleCategory C chi]
  {X : C} {P : Type w} [PartialOrder P] {alpha : Type t} {s : alpha → Arrow C}
  (T : CellTree s X (P := P)) (hP : HasCardinalLT P chi)
  (hSource : ∀ a : P, IsCardinalPresentable (s (T.label a)).left chi)
  (hTarget : ∀ a : P, IsCardinalPresentable (s (T.label a)).right chi)

/-- The full actual output keeps all original working, coefficient, Hom and label universes. -/
def independentData : CompactRootPresentation chi T :=
  compactRootPresentation chi T hP hSource hTarget

/-- The entire actual original label function is retained, with no universe identification. -/
theorem independentLabels : (independentData chi T hP hSource hTarget).tree.label = T.label :=
  (independentData chi T hP hSource hTarget).label_eq

/-- The entire actual new root and original-root map are the internally chosen values. -/
theorem independentRootValue :
    (independentData chi T hP hSource hTarget).root = finalRoot chi T hP hSource := rfl

/-- The entire actual tree is the internally built literal-P tree, with its full choices. -/
theorem independentTreeValue :
    (independentData chi T hP hSource hTarget).tree = finalTree chi T hP hSource := rfl

/-- The entire vertex Iso, including all inverses and naturality, is the actual original value. -/
theorem independentComparisonValue :
    (independentData chi T hP hSource hTarget).comparison = finalOriginalIso chi T hP hSource := rfl

/-- The full native flat predecessor Iso is retained as data on every original label. -/
theorem independentPredecessorValue (a : P) :
    (independentData chi T hP hSource hTarget).predecessorComparison a =
      finalPredecessorComparison chi T hP hSource a := rfl

/-- The entire actual endpoint Iso, including both original coefficient maps, is retained. -/
theorem independentEndpointValue :
    (independentData chi T hP hSource hTarget).endpointComparison =
      finalEndpointComparison chi T hP hSource := rfl

/-- The actual all-lower selected cocones and every full UP remain the internally chosen values. -/
theorem independentLowerValue :
    (independentData chi T hP hSource hTarget).lower = (finalTree chi T hP hSource).lowerData := rfl

/-- Every all-lower comparison retains its entire original natural Iso value. -/
theorem independentAllLowerValue (L : LowerSetColimitData T.diagram) :
    (independentData chi T hP hSource hTarget).lowerComparison L =
      finalAllLowerComparison chi T hP hSource L := rfl

/-- The whole original attaching function is retained, including explicit label transport. -/
theorem independentAttachingFunction :
    (fun a : P => (independentData chi T hP hSource hTarget).tree.attaching a ≫
      pushout.inl ((independentData chi T hP hSource hTarget).tree.predecessorObj a).hom
        (independentData chi T hP hSource hTarget).rootMap ≫
      ((independentData chi T hP hSource hTarget).predecessorComparison a).hom.right) =
    (fun a : P => eqToHom (congrArg (fun l : alpha => (s l).left)
      (congrFun (independentData chi T hP hSource hTarget).label_eq a)) ≫ T.attaching a) :=
  (independentData chi T hP hSource hTarget).attaching_function

/-- The whole original target-cell function is retained, including explicit label transport. -/
theorem independentCellFunction :
    (fun a : P => (independentData chi T hP hSource hTarget).tree.cell a ≫
      pushout.inl ((independentData chi T hP hSource hTarget).tree.vertex a).hom
        (independentData chi T hP hSource hTarget).rootMap ≫
      ((independentData chi T hP hSource hTarget).comparison.hom.app a).right) =
    (fun a : P => eqToHom (congrArg (fun l : alpha => (s l).right)
      (congrFun (independentData chi T hP hSource hTarget).label_eq a)) ≫ T.cell a) :=
  (independentData chi T hP hSource hTarget).cell_function

/-- Every predecessor retains the whole actual structural map in the original Under category. -/
theorem independentPredecessorMap (a : P) :
    (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
      ((independentData chi T hP hSource hTarget).tree.predecessorMap a) ≫
      (independentData chi T hP hSource hTarget).comparison.hom.app a =
    ((independentData chi T hP hSource hTarget).predecessorComparison a).hom ≫
      T.predecessorMap a :=
  (independentData chi T hP hSource hTarget).predecessor_map a

/-- Every predecessor retains the whole inverse structural-map comparison as well. -/
theorem independentPredecessorMap_inv (a : P) :
    T.predecessorMap a ≫ (independentData chi T hP hSource hTarget).comparison.inv.app a =
    ((independentData chi T hP hSource hTarget).predecessorComparison a).inv ≫
      (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
        ((independentData chi T hP hSource hTarget).tree.predecessorMap a) :=
  (independentData chi T hP hSource hTarget).predecessor_map_inv a

/-- Every actual predecessor leg retains its full original map, with its literal old label. -/
theorem independentPredecessorLeg (a : P) (b : LowerSet.Iio a) :
    (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
      (((independentData chi T hP hSource hTarget).tree.predecessor a).cocone.ι.app b) ≫
      ((independentData chi T hP hSource hTarget).predecessorComparison a).hom =
    (independentData chi T hP hSource hTarget).comparison.hom.app b.1 ≫
      (T.predecessor a).cocone.ι.app b :=
  (independentData chi T hP hSource hTarget).predecessor_leg a b

/-- Every actual predecessor leg retains the complete inverse original comparison. -/
theorem independentPredecessorLeg_inv (a : P) (b : LowerSet.Iio a) :
    (T.predecessor a).cocone.ι.app b ≫
      ((independentData chi T hP hSource hTarget).predecessorComparison a).inv =
    (independentData chi T hP hSource hTarget).comparison.inv.app b.1 ≫
      (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
        (((independentData chi T hP hSource hTarget).tree.predecessor a).cocone.ι.app b) :=
  (independentData chi T hP hSource hTarget).predecessor_leg_inv a b

/-- All original lower pairs retain the actual whole B-to-D map function. -/
theorem independentAllLowerMap (L : LowerSetColimitData T.diagram) (B D : LowerSet P)
    (h : B ≤ D) :
    (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
      ((independentData chi T hP hSource hTarget).lower.map h) ≫
      ((independentData chi T hP hSource hTarget).lowerComparison L).hom.app D =
    ((independentData chi T hP hSource hTarget).lowerComparison L).hom.app B ≫ L.map h :=
  ((independentData chi T hP hSource hTarget).lowerComparison L).hom.naturality (homOfLE h)

/-- All original lower pairs retain the actual entire inverse B-to-D map comparison. -/
theorem independentAllLowerMap_inv (L : LowerSetColimitData T.diagram) (B D : LowerSet P)
    (h : B ≤ D) :
    L.map h ≫ ((independentData chi T hP hSource hTarget).lowerComparison L).inv.app D =
    ((independentData chi T hP hSource hTarget).lowerComparison L).inv.app B ≫
      (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
        ((independentData chi T hP hSource hTarget).lower.map h) :=
  ((independentData chi T hP hSource hTarget).lowerComparison L).inv.naturality (homOfLE h)

/-- Every complete lower-to-predecessor Iso retains the same full native values in both directions. -/
theorem independentAllLowerPredecessor (L : LowerSetColimitData T.diagram) (a : P) :
    (Under.pushout (independentData chi T hP hSource hTarget).rootMap).mapIso
      ((independentData chi T hP hSource hTarget).tree.predecessorIso
        (independentData chi T hP hSource hTarget).lower a) ≪≫
      (independentData chi T hP hSource hTarget).predecessorComparison a =
    ((independentData chi T hP hSource hTarget).lowerComparison L).app (LowerSet.Iio a) ≪≫
      T.predecessorIso L a :=
  (independentData chi T hP hSource hTarget).lower_predecessor_iso L a

/-- The complete lower-to-endpoint Iso retains all actual maps and inverse values. -/
theorem independentAllLowerEndpoint (L : LowerSetColimitData T.diagram) :
    (Under.pushout (independentData chi T hP hSource hTarget).rootMap).mapIso
      ((independentData chi T hP hSource hTarget).tree.endpointIso
        (independentData chi T hP hSource hTarget).lower) ≪≫
      (independentData chi T hP hSource hTarget).endpointComparison =
    ((independentData chi T hP hSource hTarget).lowerComparison L).app ⊤ ≪≫ T.endpointIso L :=
  (independentData chi T hP hSource hTarget).lower_endpoint_iso L

/-- All endpoint legs retain their actual original maps in the independent original universes. -/
theorem independentEndpointLeg (a : P) :
    (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
      ((independentData chi T hP hSource hTarget).tree.inclusion a) ≫
      (independentData chi T hP hSource hTarget).endpointComparison.hom =
    (independentData chi T hP hSource hTarget).comparison.hom.app a ≫ T.inclusion a :=
  (independentData chi T hP hSource hTarget).endpoint_leg a

/-- All endpoint legs retain the complete original inverse comparison as well. -/
theorem independentEndpointLeg_inv (a : P) :
    T.inclusion a ≫ (independentData chi T hP hSource hTarget).endpointComparison.inv =
    (independentData chi T hP hSource hTarget).comparison.inv.app a ≫
      (Under.pushout (independentData chi T hP hSource hTarget).rootMap).map
        ((independentData chi T hP hSource hTarget).tree.inclusion a) :=
  (independentData chi T hP hSource hTarget).endpoint_leg_inv a

/-- The actual whole original endpoint pushout is retained, with arbitrary original X. -/
theorem independentEndpointPushout :
    IsPushout (independentData chi T hP hSource hTarget).tree.hom
      (independentData chi T hP hSource hTarget).rootMap
      (pushout.inl (independentData chi T hP hSource hTarget).tree.hom
        (independentData chi T hP hSource hTarget).rootMap ≫
        (independentData chi T hP hSource hTarget).endpointComparison.hom.right) T.hom :=
  (independentData chi T hP hSource hTarget).endpoint_isPushout

/-- Every actual selected new lower coefficient is presentable at the same original cardinal. -/
theorem independentLowerPresentable (B : LowerSet P) :
    IsCardinalPresentable ((independentData chi T hP hSource hTarget).lower.obj B).right chi :=
  (independentData chi T hP hSource hTarget).lower_presentable B

/-- The actual new root-adjoined endpoint cocone retains the full original colimit UP. -/
abbrev independentAdjoined : ColimitCocone
    (UnderColimits.adjoinedDiagram (Y := (independentData chi T hP hSource hTarget).tree.diagram)) :=
  UnderColimits.adjoinedColimit (independentData chi T hP hSource hTarget).tree.endpoint

/-- The whole actual new root function is retained as the root-adjoined star map. -/
theorem independentAdjoinedStar :
    (independentAdjoined chi T hP hSource hTarget).cocone.ι.app WithInitial.star =
      (independentData chi T hP hSource hTarget).tree.hom :=
  UnderColimits.adjoined_star (independentData chi T hP hSource hTarget).tree.endpoint.cocone

/-- Every actual new vertex inclusion is retained in the root-adjoined C colimit. -/
theorem independentAdjoinedVertex (a : P) :
    (independentAdjoined chi T hP hSource hTarget).cocone.ι.app (WithInitial.of a) =
      ((independentData chi T hP hSource hTarget).tree.inclusion a).right :=
  UnderColimits.adjoined_vertex (independentData chi T hP hSource hTarget).tree.endpoint.cocone a

end IndependentFullUniverses

end CompactRootBaseChangeExamples
