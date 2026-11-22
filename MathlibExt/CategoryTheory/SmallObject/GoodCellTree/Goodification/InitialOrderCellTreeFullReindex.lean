/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.InitialOrderCellTreeReindex
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

namespace CategoryTheory.SmallObject.InitialOrderCellTreeFullReindex

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

/-- The entire actual selected predecessor-point function is retained on original stage labels. -/
theorem predecessor_points (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (fun p : L i => G.predecessorObj p) =
      (fun p : L i => letI := orders i; (T i).predecessorObj ⟨p.1, p.2⟩) := rfl

/-- The entire actual original attaching-map function is retained on original stage labels. -/
theorem attaching_function (i : I) :
    let L := lower S orders hDirected hMono hRestrict hBelow hCover
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    (fun p : L i => G.attaching p) =
      (fun p : L i => letI := orders i; (T i).attaching ⟨p.1, p.2⟩) := rfl

/-- The actual reindexed predecessor descender is the same complete original stage descender. -/
theorem predecessor_map (i : I)
    (p : lower S orders hDirected hMono hRestrict hBelow hCover i) :
    let G := InitialOrderCellTreeReindex.tree S orders hDirected hMono hRestrict
      hInitial hBelow hCover T i
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    G.predecessorMap p = (letI := orders i; (T i).predecessorMap ⟨p.1, p.2⟩) :=
  @CellTreeOrderReindex.predecessorMap_eq C cCategory (S i)
    (lower S orders hDirected hMono hRestrict hBelow hCover i)
    (orders i) (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i)
    A s X (stageIso S orders hDirected hMono hRestrict hInitial hBelow hCover i) (T i) p

end CategoryTheory.SmallObject.InitialOrderCellTreeFullReindex
