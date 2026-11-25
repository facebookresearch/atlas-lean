/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Actual cell-tree reindexing on original label bijections

An original order isomorphism transports every actual vertex, comparison,
predecessor cocone, attaching/cell map and endpoint colimit. The root and
whole endpoint objects are unchanged. This permits the constructed old/new
extension to be placed on its actual original cell-label subset.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.CellTreeOrderReindex

open Limits LowerSetColimits

variable {C : Type u} [Category.{v} C]
  {P Q : Type w} [PartialOrder P] [PartialOrder Q]
  {A : Type t} {s : A → Arrow C} {X : C}
  (e : Q ≃o P) (T : CellTree s X (P := P))

/-- The actual original strict predecessor-label isomorphism under the whole reindexing. -/
def predecessorOrderIso (q : Q) : LowerSet.Iio q ≃o LowerSet.Iio (e q) where
  toFun z := ⟨e z.1, e.strictMono z.2⟩
  invFun z := ⟨e.symm z.1, by simpa using e.symm.strictMono z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_rel_iff' := by intro a b; exact e.le_iff_le

/-- The complete actual vertex diagram through the same original label isomorphism. -/
abbrev diagram : Q ⥤ Under X := e.equivalence.functor ⋙ T.diagram

/-- The entire original predecessor diagram retains the same label/map functions. -/
theorem predecessorDiagram (q : Q) :
    (predecessorOrderIso e q).equivalence.functor ⋙
      restriction T.diagram (LowerSet.Iio (e q)) =
        restriction (diagram e T) (LowerSet.Iio q) := rfl

/-- The actual original selected predecessor cocone is retained on the reindexed labels. -/
abbrev predecessor (q : Q) :
    ColimitCocone (restriction (diagram e T) (LowerSet.Iio q)) where
  cocone :=
    { pt := T.predecessorObj (e q)
      ι := {
        app z := (T.predecessor (e q)).cocone.ι.app ((predecessorOrderIso e q) z)
        naturality a b h := by
          change T.diagram.map (homOfLE (e.monotone (leOfHom h))) ≫
              (T.predecessor (e q)).cocone.ι.app ((predecessorOrderIso e q) b) =
            (T.predecessor (e q)).cocone.ι.app ((predecessorOrderIso e q) a) ≫ 𝟙 _
          rw [Category.comp_id]
          exact (T.predecessor (e q)).cocone.w
            ((predecessorOrderIso e q).equivalence.functor.map h) } }
  isColimit := by
    change IsColimit
      ((T.predecessor (e q)).cocone.whisker (predecessorOrderIso e q).equivalence.functor)
    exact (T.predecessor (e q)).isColimit.whiskerEquivalence
      (predecessorOrderIso e q).equivalence

/-- Both actual predecessor UPs retain precisely the original predecessor descender. -/
theorem predecessorMap_eq (q : Q) :
    cellTreePredecessorMap (diagram e T) q (predecessor e T q) =
      T.predecessorMap (e q) := by
  let newMap : T.predecessorObj (e q) ⟶ T.vertex (e q) :=
    cellTreePredecessorMap (diagram e T) q (predecessor e T q)
  change newMap = T.predecessorMap (e q)
  apply (T.predecessor (e q)).isColimit.hom_ext
  intro z
  obtain ⟨z', rfl⟩ := (predecessorOrderIso e q).surjective z
  have h : (T.predecessor (e q)).cocone.ι.app ((predecessorOrderIso e q) z') ≫
      newMap = T.diagram.map (homOfLE (e.strictMono z'.2).le) :=
    cellTreePredecessorMap_fac (diagram e T) q (predecessor e T q) z'
  exact h.trans (T.predecessorMap_fac (e q) ((predecessorOrderIso e q) z')).symm

/-- The entire actual reindexed tree keeps all original fields and endpoint/root choices. -/
def tree : CellTree s X (P := Q) where
  wellFounded := (InvImage.wf e T.wellFounded).mono (fun _ _ h => e.strictMono h)
  diagram := diagram e T
  label q := T.label (e q)
  predecessor q := predecessor e T q
  attaching q := T.attaching (e q)
  cell q := T.cell (e q)
  isPushout q := by
    rw [predecessorMap_eq]
    exact T.isPushout (e q)
  endpoint :=
    { cocone := T.endpoint.cocone.whisker e.equivalence.functor
      isColimit := T.endpoint.isColimit.whiskerEquivalence e.equivalence }

/-- The original whole endpoint/root under-object is not replaced by reindexing. -/
theorem tree_endpoint : (tree e T).endpointObj = T.endpointObj := rfl

/-- The full actual original root-to-endpoint map remains unchanged. -/
theorem tree_root : (tree e T).hom = T.hom := rfl

/-- All whole original vertex values retain precisely their original labels. -/
theorem tree_vertex_function :
    (fun q : Q => (tree e T).vertex q) = (fun q : Q => T.vertex (e q)) := rfl

/-- The complete generator-label function keeps the actual original label isomorphism. -/
theorem tree_label_function : (tree e T).label = fun q => T.label (e q) := rfl

/-- The full dependent cell-target function retains every original cell map. -/
theorem tree_cell_function :
    (fun q : Q => (tree e T).cell q) = (fun q : Q => T.cell (e q)) := rfl

/-- Goodness is transported through the actual full predecessor-label injection. -/
theorem tree_good (chi : Cardinal.{w}) [Fact chi.IsRegular] (good : T.IsGood chi) :
    (tree e T).IsGood chi where
  presentable_source q := good.presentable_source (e q)
  presentable_target q := good.presentable_target (e q)
  predecessor_lt q := (good.predecessor_lt (e q)).of_injective
    (predecessorOrderIso e q) (predecessorOrderIso e q).injective

end CategoryTheory.SmallObject.CellTreeOrderReindex
