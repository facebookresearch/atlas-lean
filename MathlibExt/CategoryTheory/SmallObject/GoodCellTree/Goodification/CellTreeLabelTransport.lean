/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellTreeOrderReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionOrder

/-!
# Genuine order/tree transport through original label bijections

The constructed order is pulled back along the actual original-label
bijection. Every tree field and the whole original root/endpoint are
transported through that same bijection. This places an actual constructed
extension on its original label carrier without choosing another factor.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.CellTreeLabelTransport

open Limits LowerSetColimits GoodCellExtensionOrder

/-- The complete actual old/new occurrence bijection induced by an original old-label bijection. -/
def indexEquiv {P Q : Type w} (e : Q ≃ P) : Index Q ≃ Index P where
  toFun x := ⟨x.val.map e⟩
  invFun x := ⟨x.val.map e.symm⟩
  left_inv x := by rcases x with ⟨x⟩; cases x <;> simp
  right_inv x := by rcases x with ⟨x⟩; cases x <;> simp

/-- The actual pulled-back partial order, with its full original label function retained. -/
@[instance_reducible]
def pulledOrder {P Q : Type w} [PartialOrder P] (e : Q ≃ P) : PartialOrder Q :=
  PartialOrder.lift e e.injective

/-- The actual original label bijection becomes the constructed order isomorphism. -/
def pulledIso {P Q : Type w} [PartialOrder P] (e : Q ≃ P) :
    letI := pulledOrder e
    Q ≃o P := by
  letI := pulledOrder e
  exact { e with map_rel_iff' := Iff.rfl }

variable {C : Type u} [Category.{v} C]
  {P Q : Type w} [PartialOrder P] {A : Type t} {s : A → Arrow C} {X : C}
  (e : Q ≃ P) (T : CellTree s X (P := P))

/-- The whole actual tree uses the original target label carrier and its constructed order. -/
def tree :
    letI := pulledOrder e
    CellTree s X (P := Q) := by
  letI := pulledOrder e
  exact CellTreeOrderReindex.tree (pulledIso e) T

/-- The whole endpoint under the original root remains the same original object. -/
theorem tree_endpoint :
    letI := pulledOrder e
    (tree e T).endpointObj = T.endpointObj := rfl

/-- The actual original root-to-endpoint map is unchanged after original-label transport. -/
theorem tree_root :
    letI := pulledOrder e
    (tree e T).hom = T.hom := rfl

/-- The complete transported old vertex function uses precisely the same original bijection. -/
theorem tree_vertex_function :
    letI := pulledOrder e
    (fun q : Q => (tree e T).vertex q) = (fun q : Q => T.vertex (e q)) := rfl

/-- Every actual original cell-target map retains its same original dependent label. -/
theorem tree_cell_function :
    letI := pulledOrder e
    (fun q : Q => (tree e T).cell q) = (fun q : Q => T.cell (e q)) := rfl

/-- The full original generator-label function is transported by the same original bijection. -/
theorem tree_label_function :
    letI := pulledOrder e
    (tree e T).label = fun q : Q => T.label (e q) := rfl

/-- Actual old goodness is retained by the complete original predecessor-label bijection. -/
theorem tree_good (chi : Cardinal.{w}) [Fact chi.IsRegular] (good : T.IsGood chi) :
    letI := pulledOrder e
    (tree e T).IsGood chi := by
  let : PartialOrder Q := pulledOrder e
  exact CellTreeOrderReindex.tree_good (pulledIso e) T chi good

end CategoryTheory.SmallObject.CellTreeLabelTransport
