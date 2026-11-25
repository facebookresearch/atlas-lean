/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: toskua, Avocado
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The labelled one-step free-filler functor

For an explicit family `j s : K s ⟶ D s`, attach one copy of `D s` for
every pair `(s, a : K s ⟶ X)`. The construction retains the generator
label even when distinct labels specify the same arrow.

This is the terminal-arrow specialization of the native small-object
construction. Reindexing its attachment data gives actual colimit cofans
indexed by the labelled pairs and their actual pushout. The construction
and its double-orthogonality conclusion apply to arbitrary arrow families.
Cisinski's monic-family construction is their source specialization.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace SSet

variable {I : Type u} {K D : I → SSet.{u}} (j : ∀ s, K s ⟶ D s)

/-- Attach one cell for each generator label and each map from its domain. -/
noncomputable def labelledFreeFiller : SSet.{u} ⥤ SSet.{u} :=
  let terminalArrow : SSet.{u} ⥤ Arrow SSet.{u} :=
    { obj X := Arrow.mk (terminal.from X)
      map m := Arrow.homMk m (𝟙 _) (terminal.hom_ext _ _)
      map_id X := by ext <;> simp
      map_comp m n := by ext <;> simp }
  terminalArrow ⋙ SmallObject.functor j ⋙ Arrow.leftFunc

namespace labelledFreeFiller

/-- The actual index of cells, including the generator label. -/
abbrev Index (K : I → SSet.{u}) (X : SSet.{u}) : Type u := Σ s, K s ⟶ X

/-- A labelled domain map specifies exactly one square over a terminal arrow. -/
noncomputable def indexEquiv (X : SSet.{u}) :
    Index K X ≃ SmallObject.FunctorObjIndex j (terminal.from X) where
  toFun x := ⟨x.1, x.2, terminal.from (D x.1), terminal.hom_ext _ _⟩
  invFun x := ⟨x.i, x.t⟩
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨s, a, b, w⟩
    have hb : terminal.from (D s) = b := terminal.hom_ext _ _
    cases hb
    rfl

/-- The natural unit inherited from the native attachment functor. -/
noncomputable def unit : 𝟭 SSet.{u} ⟶ labelledFreeFiller j where
  app X := ((SmallObject.ε j).app (Arrow.mk (terminal.from X))).left
  naturality X Y m :=
    (SmallObject.ιFunctorObj_naturality j (πX := terminal.from X) (πY := terminal.from Y)
      (Arrow.homMk m (𝟙 _) (terminal.hom_ext _ _))).symm

/-- The two labelled coproducts and their pushout, in value universe `u`. -/
noncomputable def attachCells (X : SSet.{u}) :
    AttachCells.{u} j ((unit j).app X) :=
  (SmallObject.attachCellsιFunctorObj j (terminal.from X)).reindex (indexEquiv j X)

/-- The top coproduct map evaluates each labelled attaching map. -/
@[reassoc (attr := simp)]
lemma cofan₁_inj_g₁ (X : SSet.{u}) (s : I) (a : K s ⟶ X) :
    (attachCells j X).cofan₁.inj ⟨s, a⟩ ≫ (attachCells j X).g₁ = a := by
  change Sigma.ι (SmallObject.functorObjSrcFamily j (terminal.from X))
    (indexEquiv j X ⟨s, a⟩) ≫ SmallObject.functorObjTop j (terminal.from X) = a
  simp [SmallObject.functorObjTop, indexEquiv]

/-- The attached codomain map with its original label and boundary map. -/
noncomputable def cell {X : SSet.{u}} (s : I) (a : K s ⟶ X) :
    D s ⟶ (labelledFreeFiller j).obj X :=
  (attachCells j X).cell ⟨s, a⟩

/-- Every labelled cell extends its full prescribed attaching map. -/
@[reassoc (attr := simp)]
lemma cell_boundary {X : SSet.{u}} (s : I) (a : K s ⟶ X) :
    j s ≫ cell j s a = a ≫ (unit j).app X :=
  (indexEquiv j X ⟨s, a⟩).comm

/-- Functor maps keep the generator label and use the identity on its codomain. -/
@[reassoc (attr := simp)]
lemma cell_naturality {X Y : SSet.{u}} (m : X ⟶ Y) (s : I) (a : K s ⟶ X) :
    cell j s a ≫ (labelledFreeFiller j).map m = cell j s (a ≫ m) := by
  let τ : Arrow.mk (terminal.from X) ⟶ Arrow.mk (terminal.from Y) :=
    Arrow.homMk m (𝟙 _) (terminal.hom_ext _ _)
  change (Sigma.ι _ (indexEquiv j X ⟨s, a⟩) ≫ SmallObject.ρFunctorObj j
      (terminal.from X)) ≫ SmallObject.functorMap j τ =
    Sigma.ι _ (indexEquiv j Y ⟨s, a ≫ m⟩) ≫
      SmallObject.ρFunctorObj j (terminal.from Y)
  simpa [SmallObject.functorMap, pushout.map, pushout.inr_desc, SmallObject.ρFunctorObj,
    indexEquiv, τ] using
    SmallObject.ι_functorMapTgt_assoc j τ s a
      (terminal.from (D s)) (terminal.hom_ext _ _)
      (terminal.from (D s)) (by simp [τ]) (a ≫ m) rfl
      (SmallObject.ρFunctorObj j (terminal.from Y))

/-- A unit is a pushout of a `u`-small coproduct of generator arrows. -/
lemma unit_mem (X : SSet.{u}) : (MorphismProperty.ofHoms j).rlp.llp ((unit j).app X) := by
  simpa only [MorphismProperty.rlp_coproducts] using
    (MorphismProperty.coproducts.{u} (MorphismProperty.ofHoms j)).pushouts_le_llp_rlp _
      (attachCells j X).pushouts_coproducts

end labelledFreeFiller

end SSet
