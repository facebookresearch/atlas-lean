/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionTree

/-!
# Actual initial old-tree embeddings in one-cell good-order extensions

All original old comparisons and vertices/maps are preserved. No new
predecessor of an old cell is introduced. The old whole endpoint maps by
the actual original pushout inclusion, with every old vertex leg retained.
These are the compatibility facts required by genuine limit assembly.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.GoodCellExtensionInitialEmbedding

open Limits LowerSetColimits GoodCellExtensionOrder GoodCellExtensionDiagram
  GoodCellExtensionTree GoodCellExtensionColimits

variable {P : Type w} [PartialOrder P] (B : LowerSet P)

/-- The actual old-cell inclusion is a full original-order embedding. -/
def oldEmbedding :
    letI := extensionOrder B
    P ↪o GoodCellExtensionOrder.Index P := by
  letI := extensionOrder B
  exact {
    toFun := GoodCellExtensionOrder.Index.old
    inj' := fun _ _ h => Option.some.inj (congrArg GoodCellExtensionOrder.Index.val h)
    map_rel_iff' := old_le_old B _ _ }

/-- Every whole comparison below an old cell is an actual original old-cell comparison. -/
theorem old_initial (p : P) (x : GoodCellExtensionOrder.Index P) :
    letI := extensionOrder B
    x ≤ GoodCellExtensionOrder.Index.old p ↔
      ∃ q : P, x = GoodCellExtensionOrder.Index.old q ∧ q ≤ p := by
  let : PartialOrder (GoodCellExtensionOrder.Index P) := extensionOrder B
  rcases x with ⟨x⟩
  cases x with
  | none =>
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨q, hq, _⟩
      have hv : (none : Option P) = some q :=
        congrArg GoodCellExtensionOrder.Index.val hq
      cases hv
  | some q =>
    constructor
    · intro h
      exact ⟨q, rfl, h⟩
    · rintro ⟨r, hqr, hr⟩
      have hq : q = r := Option.some.inj (congrArg GoodCellExtensionOrder.Index.val hqr)
      exact hq.symm ▸ hr

/-- The old embedding retains the whole original thin-category comparison function. -/
def oldFunctor :
    letI := extensionOrder B
    P ⥤ GoodCellExtensionOrder.Index P := by
  letI := extensionOrder B
  exact (oldEmbedding B).monotone.functor

variable {C : Type u} [Category.{v} C] [HasPushouts C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (i : A) (a : (s i).left ⟶ (L.obj B).right)

/-- The complete original old vertex diagram is unchanged through the actual old embedding. -/
theorem old_diagram :
    letI := extensionOrder B
    oldFunctor B ⋙ (extensionTree T L B i a).diagram = T.diagram := rfl

/-- Every original old-tree inclusion has the actual original whole pushout factor equation. -/
theorem old_endpoint_leg (p : P) :
    letI := extensionOrder B
    (extensionTree T L B i a).inclusion (GoodCellExtensionOrder.Index.old p) =
      T.inclusion p ≫ endpointStep T L B i a := rfl

/-- The full old endpoint cocone maps through the actual original whole pushout inclusion. -/
def oldEndpointCocone : Cocone T.diagram where
  pt := wholePoint T L B i a
  ι :=
    { app p := T.inclusion p ≫ endpointStep T L B i a
      naturality p q h := by
        change T.diagram.map h ≫ (T.inclusion q ≫ endpointStep T L B i a) =
          (T.inclusion p ≫ endpointStep T L B i a) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, T.inclusion_naturality] }

/-- The original old endpoint descender is exactly the actual whole pushout inclusion. -/
theorem oldEndpoint_desc :
    T.endpoint.isColimit.desc (oldEndpointCocone B T L i a) = endpointStep T L B i a := by
  apply T.endpoint.isColimit.hom_ext
  intro p
  exact T.endpoint.isColimit.fac (oldEndpointCocone B T L i a) p

end CategoryTheory.SmallObject.GoodCellExtensionInitialEmbedding
