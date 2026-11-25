/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Codex
-/
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.PrefixSystem

/-!
# Common original lower-carrier gluing

The actual complete original prefix system glues on any genuine lower
carrier, preserving all objects, Hom values, source equality, bottom,
successor class membership and original limit colimit witnesses. Whole J
and the strict preceding intervals specialize this single construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.SmallObject.CoherentRetracts
variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C)

namespace PrefixSplitGlue

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C) (U : LowerSet J)
  (x : ((OrderHom.Subtype.val (fun (j : J) => j ∈ (U : Set J))).monotone.functor.op ⋙
      prefixSplitFunctor P F).sections)

/-- The complete original state at an actual lower-carrier label. -/
def state (i : (U : Set J)) : PrefixSplit P F i.1 := x.val (Opposite.op i)

/-- Compatibility identifies the entire original smaller prefix. -/
theorem restrict_state {i j : (U : Set J)} (h : i ≤ j) :
    (state P F U x j).restrict h = state P F U x i :=
  x.property (homOfLE h).op

/-- Each object's point is read from its own original closed prefix. -/
def object (i : (U : Set J)) : SplitObject C := (state P F U x i).D.obj ⟨i.1, le_rfl⟩

/-- An original point agrees with the same point in every later complete prefix. -/
theorem object_in_larger {i j : (U : Set J)} (h : i ≤ j) :
    (state P F U x j).D.obj ⟨i.1, h⟩ = object P F U x i :=
  Functor.congr_obj (congrArg PrefixSplit.D (restrict_state P F U x h)) ⟨i.1, le_rfl⟩

/-- The actual larger original prefix supplies the map between the same two points. -/
def stageMap {i j : (U : Set J)} (h : i ≤ j) : object P F U x i ⟶ object P F U x j :=
  eqToHom (object_in_larger P F U x h).symm ≫
    (state P F U x j).D.map (homOfLE h : (⟨i.1, h⟩ : Set.Iic j.1) ⟶ ⟨j.1, le_rfl⟩)

/-- The complete map is the same Hom value in any later original prefix. -/
theorem stageMap_heq_in_larger {i j k : (U : Set J)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageMap P F U x hij ≍
      (state P F U x k).D.map
        (homOfLE hij : (⟨i.1, hij.trans hjk⟩ : Set.Iic k.1) ⟶ ⟨j.1, hjk⟩) := by
  let f : (⟨i.1, hij⟩ : Set.Iic j.1) ⟶ ⟨j.1, le_rfl⟩ := homOfLE hij
  have hSmall : stageMap P F U x hij ≍ (state P F U x j).D.map f :=
    eqToHom_comp_heq ((state P F U x j).D.map f)
      (object_in_larger P F U x hij).symm
  have hMap := Functor.hcongr_hom
    (congrArg PrefixSplit.D (restrict_state P F U x hjk)).symm f
  exact hSmall.trans hMap

/-- The same-label map is the identity, using its actual original stage equation. -/
theorem stageMap_refl (i : (U : Set J)) :
    stageMap P F U x (le_refl i) = 𝟙 (object P F U x i) := by
  have h := stageMap_heq_in_larger P F U x (le_refl i) (le_refl i)
  exact eq_of_heq (h.trans (heq_of_eq ((state P F U x i).D.map_id
    (⟨i.1, le_rfl⟩ : Set.Iic i.1))))

/-- Original composition is verified in the single complete prefix at the last label. -/
theorem stageMap_comp {i j k : (U : Set J)} (hij : i ≤ j) (hjk : j ≤ k) :
    stageMap P F U x (hij.trans hjk) = stageMap P F U x hij ≫ stageMap P F U x hjk := by
  let f : (⟨i.1, hij.trans hjk⟩ : Set.Iic k.1) ⟶ ⟨j.1, hjk⟩ := homOfLE hij
  let g : (⟨j.1, hjk⟩ : Set.Iic k.1) ⟶ ⟨k.1, le_rfl⟩ := homOfLE hjk
  have hF := stageMap_heq_in_larger P F U x hij hjk
  have hG := stageMap_heq_in_larger P F U x hjk (le_refl k)
  have hFG := stageMap_heq_in_larger P F U x (hij.trans hjk) (le_refl k)
  have hComp := heq_comp
    (object_in_larger P F U x (hij.trans hjk)).symm
    (object_in_larger P F U x hjk).symm
    (object_in_larger P F U x (le_refl k)).symm hF hG
  exact eq_of_heq ((hFG.trans (heq_of_eq ((state P F U x k).D.map_comp f g))).trans hComp.symm)

/-- One complete diagram glues on the same original lower subset. -/
def diagram : (U : Set J) ⥤ SplitObject C where
  obj := object P F U x
  map f := stageMap P F U x (leOfHom f)
  map_id i := stageMap_refl P F U x i
  map_comp f g := stageMap_comp P F U x (leOfHom f) (leOfHom g)

/-- Lower closure includes every original closed prefix in the actual carrier. -/
def prefixInclusion (delta : (U : Set J)) : Set.Iic delta.1 →o (U : Set J) where
  toFun i := ⟨i.1, U.lower i.2 delta.2⟩
  monotone' _ _ hij := hij

/-- Full restriction recovers both objects and all original Hom values literally. -/
theorem diagram_restrict (delta : (U : Set J)) :
    (prefixInclusion U delta).monotone.functor ⋙ diagram P F U x = (state P F U x delta).D := by
  apply Functor.hext
  · intro i
    exact (object_in_larger P F U x (show prefixInclusion U delta i ≤ delta from i.2)).symm
  · intro i j f
    exact stageMap_heq_in_larger P F U x
      (show prefixInclusion U delta i ≤ prefixInclusion U delta j from leOfHom f)
      (show prefixInclusion U delta j ≤ delta from j.2)

/-- The whole source projection retains the original F on objects and every map. -/
theorem diagram_source : diagram P F U x ⋙ SplitObject.sourceFunctor =
    (OrderHom.Subtype.val (fun (j : J) => j ∈ (U : Set J))).monotone.functor ⋙ F := by
  apply Functor.hext
  · intro i
    exact Functor.congr_obj (state P F U x i).source_eq ⟨i.1, le_rfl⟩
  · intro i j f
    have hD := diagram_restrict P F U x j
    have hSource :
        (prefixInclusion U j).monotone.functor ⋙ (diagram P F U x ⋙ SplitObject.sourceFunctor) =
          (Set.initialSegIic j.1).monotone.functor ⋙ F :=
      (congrArg (fun G => G ⋙ SplitObject.sourceFunctor) hD).trans (state P F U x j).source_eq
    exact Functor.hcongr_hom hSource
      (homOfLE (leOfHom f) : (⟨i.1, leOfHom f⟩ : Set.Iic j.1) ⟶ ⟨j.1, le_rfl⟩)

/-- The original bottom splitting is retained whenever bottom belongs to the lower carrier. -/
theorem diagram_bottom (hBot : (⊥ : J) ∈ (U : Set J)) :
    (diagram P F U x).obj ⟨⊥, hBot⟩ = SplitObject.identityObject (F.obj ⊥) :=
  (state P F U x ⟨⊥, hBot⟩).bottom_eq

/-- Every actual original successor inside the lower carrier keeps its pushout membership. -/
theorem diagram_map_mem (i : (U : Set J)) (hSucc : Order.succ i.1 ∈ (U : Set J))
    (hNotMax : ¬ IsMax i.1) :
    P.pushouts (((diagram P F U x).map
      (homOfLE (Order.le_succ i.1) : i ⟶ ⟨Order.succ i.1, hSucc⟩)).right) := by
  let j : (U : Set J) := ⟨Order.succ i.1, hSucc⟩
  let a : Set.Iic (Order.succ i.1) := ⟨i.1, Order.le_succ i.1⟩
  let b : Set.Iic (Order.succ i.1) := ⟨Order.succ i.1, le_rfl⟩
  have hT := congrArg (fun G : Set.Iic (Order.succ i.1) ⥤ SplitObject C =>
    G ⋙ SplitObject.targetFunctor) (diagram_restrict P F U x j)
  exact P.pushouts.of_eq ((state P F U x j).map_mem i.1
    (Order.lt_succ_of_not_isMax hNotMax))
    (Functor.congr_obj hT a).symm (Functor.congr_obj hT b).symm
    (Functor.congr_hom hT (homOfLE (Order.le_succ i.1) : a ⟶ b))

/-- The original preceding interval lies inside a lower carrier containing its endpoint. -/
def precedingInclusion (delta : (U : Set J)) : Set.Iio delta.1 →o (U : Set J) where
  toFun i := ⟨i.1, U.lower i.2.le delta.2⟩
  monotone' _ _ hij := hij

/-- The preceding cocone retains its actual original split endpoint. -/
def precedingCocone (delta : (U : Set J)) :
    Cocone ((precedingInclusion U delta).monotone.functor ⋙
      (diagram P F U x ⋙ SplitObject.targetFunctor)) where
  pt := ((diagram P F U x).obj delta).target
  ι := {
    app i := ((diagram P F U x).map
      (homOfLE i.2.le : precedingInclusion U delta i ⟶ delta)).right
    naturality i j f := by
      let G := diagram P F U x ⋙ SplitObject.targetFunctor
      let a : precedingInclusion U delta i ⟶ precedingInclusion U delta j := homOfLE (leOfHom f)
      let b : precedingInclusion U delta j ⟶ delta := homOfLE j.2.le
      change G.map a ≫ G.map b = G.map (a ≫ b) ≫ 𝟙 _
      rw [Category.comp_id]
      exact (G.map_comp a b).symm }

/-- Every genuine original limit retains the actual preceding target colimit property. -/
theorem diagram_continuous (delta : (U : Set J)) (hLimit : Order.IsSuccLimit delta.1) :
    Nonempty (IsColimit (precedingCocone P F U x delta)) := by
  have hT := congrArg (fun G : Set.Iic delta.1 ⥤ SplitObject C =>
    G ⋙ SplitObject.targetFunctor) (diagram_restrict P F U x delta)
  change (prefixInclusion U delta).monotone.functor ⋙
    (diagram P F U x ⋙ SplitObject.targetFunctor) =
      (state P F U x delta).D ⋙ SplitObject.targetFunctor at hT
  have hc : Nonempty (IsColimit (SmallObject.coconeOfLE
      ((prefixInclusion U delta).monotone.functor ⋙ (diagram P F U x ⋙ SplitObject.targetFunctor))
      (le_refl delta.1))) := by
    rw [hT]
    exact (state P F U x delta).continuous delta.1 hLimit le_rfl
  exact hc

/-- Every original lower-carrier map is the same map in the closed prefix at its target. -/
theorem diagram_map_heq_in_prefix {i j k : (U : Set J)} (f : i ⟶ j) (hjk : j ≤ k) :
    (diagram P F U x).map f ≍
      (state P F U x k).D.map
        (homOfLE (leOfHom f) : (⟨i.1, (leOfHom f).trans hjk⟩ : Set.Iic k.1) ⟶ ⟨j.1, hjk⟩) :=
  stageMap_heq_in_larger P F U x (leOfHom f) hjk

end PrefixSplitGlue

/-- A full glued lower-carrier state retains the source diagram, bottom, successor class and
original limit UPs. -/
structure LowerPrefixSplit (P : MorphismProperty C) (F : J ⥤ C) (U : LowerSet J) where
  /-- The actual whole splitting diagram on the original lower carrier. -/
  D : (U : Set J) ⥤ SplitObject C
  /-- Literal equality of the original source functor, including all maps. -/
  source_eq : D ⋙ SplitObject.sourceFunctor =
    (OrderHom.Subtype.val (fun (j : J) => j ∈ (U : Set J))).monotone.functor ⋙ F
  /-- The original bottom uses both identity maps when it belongs to this carrier. -/
  bottom_eq (h : (⊥ : J) ∈ (U : Set J)) : D.obj ⟨⊥, h⟩ = SplitObject.identityObject (F.obj ⊥)
  /-- Each actual successor within the original carrier retains its pushout membership. -/
  map_mem (i : (U : Set J)) (h : Order.succ i.1 ∈ (U : Set J)) (hn : ¬IsMax i.1) :
    P.pushouts ((D.map (homOfLE (Order.le_succ i.1) : i ⟶ ⟨Order.succ i.1, h⟩)).right)
  /-- Every original limit retains the actual target cocone in its original closed prefix. -/
  continuous (i : (U : Set J)) (hi : Order.IsSuccLimit i.1) :
    Nonempty (IsColimit (SmallObject.coconeOfLE
      ((PrefixSplitGlue.prefixInclusion U i).monotone.functor ⋙ (D ⋙ SplitObject.targetFunctor))
      (le_refl i.1)))

namespace PrefixSplitGlue

variable {C : Type u} [Category.{v} C] {J : Type w}
  [LinearOrder J] [OrderBot J] [SuccOrder J]
  (P : MorphismProperty C) (F : J ⥤ C) (U : LowerSet J)
  (x : ((OrderHom.Subtype.val (fun (j : J) => j ∈ (U : Set J))).monotone.functor.op ⋙
      prefixSplitFunctor P F).sections)

/-- Compatible complete original prefixes construct all clauses of a single lower-carrier state. -/
def glued : LowerPrefixSplit P F U where
  D := diagram P F U x
  source_eq := diagram_source P F U x
  bottom_eq := diagram_bottom P F U x
  map_mem := diagram_map_mem P F U x
  continuous i hi := diagram_continuous P F U x i hi

/-- Each full original closed prefix is recovered from the bundled common gluing construction. -/
theorem glued_restrict (i : (U : Set J)) :
    (prefixInclusion U i).monotone.functor ⋙ (glued P F U x).D = (state P F U x i).D :=
  diagram_restrict P F U x i

/-- Complete states on the original whole order give the common gluing family on its top lower
set. -/
def wholeFamily (x : (prefixSplitFunctor P F).sections) :
    ((OrderHom.Subtype.val (fun (j : J) => j ∈ ((⊤ : LowerSet J) : Set J))).monotone.functor.op ⋙
      prefixSplitFunctor P F).sections where
  val i := x.val (Opposite.op i.unop.1)
  property f := x.property ((OrderHom.Subtype.val
    (fun (j : J) => j ∈ ((⊤ : LowerSet J) : Set J))).monotone.functor.map f.unop).op

/-- The whole-order specialization has exactly the original J as its carrier. -/
def wholeDiagram (x : (prefixSplitFunctor P F).sections) : J ⥤ SplitObject C :=
  let e : J →o ((⊤ : LowerSet J) : Set J) :=
    { toFun := fun j => ⟨j, by trivial⟩, monotone' := fun _ _ h => h }
  e.monotone.functor ⋙ diagram P F (⊤ : LowerSet J) (wholeFamily P F x)

/-- The genuine preceding interval specialization glues through the same lower-set construction. -/
def precedingFamily (gamma : J)
    (x : ((Set.principalSegIio gamma).monotone.functor.op ⋙ prefixSplitFunctor P F).sections) :
    ((OrderHom.Subtype.val (fun (j : J) => j ∈
        ((LowerSet.Iio gamma) : Set J))).monotone.functor.op ⋙
      prefixSplitFunctor P F).sections := x

/-- The original strict preceding interval uses exactly the shared lower-set diagram. -/
def precedingDiagram (gamma : J)
    (x : ((Set.principalSegIio gamma).monotone.functor.op ⋙ prefixSplitFunctor P F).sections) :
    Set.Iio gamma ⥤ SplitObject C :=
  diagram P F (LowerSet.Iio gamma) (precedingFamily P F gamma x)

/-- Every complete original closed prefix is recovered by the whole-order specialization. -/
theorem wholeDiagram_restrict (x : (prefixSplitFunctor P F).sections) (delta : J) :
    (Set.initialSegIic delta).monotone.functor ⋙ wholeDiagram P F x =
        (x.val (Opposite.op delta)).D :=
  diagram_restrict P F (⊤ : LowerSet J) (wholeFamily P F x) ⟨delta, by trivial⟩

/-- The whole-order specialization retains the complete original source functor. -/
theorem wholeDiagram_source (x : (prefixSplitFunctor P F).sections) :
    wholeDiagram P F x ⋙ SplitObject.sourceFunctor = F := by
  apply Functor.hext
  · intro i
    exact Functor.congr_obj (x.val (Opposite.op i)).source_eq ⟨i, le_rfl⟩
  · intro i j f
    have h := congrArg (fun G => G ⋙ SplitObject.sourceFunctor) (wholeDiagram_restrict P F x j)
    have hSource : (Set.initialSegIic j).monotone.functor ⋙
      (wholeDiagram P F x ⋙ SplitObject.sourceFunctor) =
          (Set.initialSegIic j).monotone.functor ⋙ F :=
      h.trans (x.val (Opposite.op j)).source_eq
    exact Functor.hcongr_hom hSource
      (homOfLE (leOfHom f) : (⟨i, leOfHom f⟩ : Set.Iic j) ⟶ ⟨j, le_rfl⟩)

/-- The original bottom splitting is retained on the whole order. -/
theorem wholeDiagram_bottom (x : (prefixSplitFunctor P F).sections) :
    (wholeDiagram P F x).obj ⊥ = SplitObject.identityObject (F.obj ⊥) :=
  diagram_bottom P F (⊤ : LowerSet J) (wholeFamily P F x) (by trivial)

/-- Every whole-order successor is an actual pushout of the arbitrary original class. -/
theorem wholeDiagram_map_mem (x : (prefixSplitFunctor P F).sections) (i : J) (hi : ¬IsMax i) :
    P.pushouts (((wholeDiagram P F x).map (homOfLE (Order.le_succ i))).right) :=
  diagram_map_mem P F (⊤ : LowerSet J) (wholeFamily P F x) ⟨i, by trivial⟩ (by trivial) hi

/-- Every original limit in the whole order retains the actual principal preceding cocone. -/
theorem wholeDiagram_continuous (x : (prefixSplitFunctor P F).sections)
    (delta : J) (hi : Order.IsSuccLimit delta) :
    Nonempty (IsColimit ((Set.principalSegIio delta).cocone
      (wholeDiagram P F x ⋙ SplitObject.targetFunctor))) :=
  diagram_continuous P F (⊤ : LowerSet J) (wholeFamily P F x) ⟨delta, by trivial⟩ hi

/-- Restriction to an entire original closed prefix in a preceding interval is literal. -/
theorem precedingDiagram_restrict (gamma : J)
    (x : ((Set.principalSegIio gamma).monotone.functor.op ⋙ prefixSplitFunctor P F).sections)
    (delta : J) (h : delta < gamma) :
    (prefixInclusion (LowerSet.Iio gamma) ⟨delta, h⟩).monotone.functor ⋙
      precedingDiagram P F gamma x = (x.val (Opposite.op (⟨delta, h⟩ : Set.Iio gamma))).D :=
  diagram_restrict P F (LowerSet.Iio gamma) (precedingFamily P F gamma x) ⟨delta, h⟩

/-- The preceding specialization retains every actual original source map. -/
theorem precedingDiagram_source (gamma : J)
    (x : ((Set.principalSegIio gamma).monotone.functor.op ⋙ prefixSplitFunctor P F).sections) :
    precedingDiagram P F gamma x ⋙ SplitObject.sourceFunctor =
      (Set.principalSegIio gamma).monotone.functor ⋙ F :=
  diagram_source P F (LowerSet.Iio gamma) (precedingFamily P F gamma x)

end PrefixSplitGlue
end CategoryTheory.SmallObject.CoherentRetracts
