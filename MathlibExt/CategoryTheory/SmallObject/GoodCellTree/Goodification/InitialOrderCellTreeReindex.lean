/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderFamilyGlue
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellTreeOrderReindex
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Actual initial-stage trees in the constructed original union order

The literal identity on original stage labels transports every actual
local tree to the inherited global stage order. Both order dictionaries
are explicit. The root, endpoint, vertices, original labels and cell maps
are retained through the same original label function.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.InitialOrderCellTreeReindex

open Limits LowerSetColimits InitialOrderFamilyGlue

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → LowerSet P) (orders : ∀ i : I, PartialOrder (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)
  (hRestrict : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (S j) (orders j).toLE ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩)
  (hInitial : ∀ (i j : I) (_ : i ≤ j) (a b : S j), b.1 ∈ S i →
    @LE.le (S j) (orders j).toLE a b → a.1 ∈ S i)
  (hBelow : ∀ (i : I) (a b : S i),
    @LE.le (S i) (orders i).toLE a b → a.1 ≤ b.1)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)
  {C : Type u} [cCategory : Category.{v} C]
  {A : Type t} {s : A → Arrow C} {X : C}
  (T : ∀ i : I, letI := orders i; CellTree s X (P := S i))

/-- The entire actual local tree is reindexed on its same literal original global stage labels. -/
def tree (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    CellTree s X (P := L i) :=
  @CellTreeOrderReindex.tree C cCategory (S i)
    (lower S orders hDirected hMono hRestrict hBelow hCover i)
    (orders i) (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i)
    A s X (stageIso S orders hDirected hMono hRestrict hInitial hBelow hCover i) (T i)

/-- Every actual stage endpoint under the original root is retained literally. -/
theorem tree_endpoint (i : I) :
    let G := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    G.endpointObj = (letI := orders i; (T i).endpointObj) := rfl

/-- The full actual original vertex function is retained on the same original label subtype. -/
theorem tree_vertex_function (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (fun a : L i => G.vertex a) =
      (fun a : L i => letI := orders i; (T i).vertex ⟨a.1, a.2⟩) := rfl

/-- The entire original attaching-family label function remains the original stage function. -/
theorem tree_label_function (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    G.label = (fun a : L i => letI := orders i; (T i).label ⟨a.1, a.2⟩) := rfl

/-- Every actual original cell map keeps its complete original dependent label and target. -/
theorem tree_cell_function (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (fun a : L i => G.cell a) =
      (fun a : L i => letI := orders i; (T i).cell ⟨a.1, a.2⟩) := rfl

/-- The actual stage goodness survives the literal full predecessor-label order isomorphism. -/
theorem tree_good (i : I) (chi : Cardinal.{w}) [hChi : Fact chi.IsRegular]
    (good : letI := orders i; (T i).IsGood chi) :
    let G := tree S orders hDirected hMono hRestrict hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    G.IsGood chi :=
  @CellTreeOrderReindex.tree_good C cCategory (S i)
    (lower S orders hDirected hMono hRestrict hBelow hCover i)
    (orders i) (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i)
    A s X (stageIso S orders hDirected hMono hRestrict hInitial hBelow hCover i)
    (T i) chi hChi good

end CategoryTheory.SmallObject.InitialOrderCellTreeReindex
