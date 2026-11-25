/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.Quasicategory.SpecialOuterHornGeneral
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting

/-!
# A fixed Kan interval detects the original equivalence edges

Use the existing horn small-object factorization of the original terminal
map out of the interval. Its actual intermediate simplicial set is Kan,
and its actual interval inclusion is anodyne. An equivalence edge of a
quasicategory lands in its original core and extends across that inclusion.
Thus one fixed Kan object detects every original equivalence edge, without
requiring all Kan objects as a family of generators. The chosen object and
inclusion are retained, in the original value universe.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.KanEdgeDetector

/-- The actual intermediate Kan object in the existing horn factorization of the interval's terminal map. -/
def object : SSet.{u} :=
  (modelCategoryQuillen.anodyneFactorizationData (terminal.from (Δ[1] : SSet.{u}))).Z

/-- The actual original interval inclusion selected by that horn factorization. -/
def edge : (Δ[1] : SSet.{u}) ⟶ object.{u} :=
  (modelCategoryQuillen.anodyneFactorizationData (terminal.from (Δ[1] : SSet.{u}))).i

/-- The detector's native interval map is anodyne. -/
theorem edge_anodyne : anodyneExtensions edge.{u} :=
  modelCategoryQuillen.anodyneFactorizationData_mem_anodyne _

/-- The detector is Kan by the actual right factor of the original horn factorization. -/
instance : KanComplex object.{u} := by
  let r := modelCategoryQuillen.anodyneFactorizationData (terminal.from (Δ[1] : SSet.{u}))
  change IsFibrant r.Z
  rw [isFibrant_iff]
  have hp : r.p = terminal.from r.Z := Subsingleton.elim _ _
  rw [← hp]
  exact inferInstanceAs (Fibration (modelCategoryQuillen.anodyneFactorizationData
    (terminal.from (Δ[1] : SSet.{u}))).p)

/-- Every original interval map into a Kan object extends across the same native inclusion. -/
theorem exists_extension_into_kan {X : SSet.{u}} [KanComplex X] (f : (Δ[1] : SSet.{u}) ⟶ X) :
    ∃ g : object.{u} ⟶ X, edge.{u} ≫ g = f :=
  anodyneExtensions.exists_lift_of_isFibrant f edge_anodyne

/-- An original equivalence edge extends into the actual original core, with its whole interval map unchanged. -/
theorem exists_core_extension {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : Edge x y) (he : e.IsEquivalence) :
    ∃ g : object.{u} ⟶ (core X : SSet.{u}),
      edge.{u} ≫ g ≫ (core X).ι = yonedaEquiv.symm e.edge := by
  have hs : e.edge ∈ (core X).obj (op ⦋1⦌) := mem_core_obj_one_iff.mpr (he.of_edge_eq rfl)
  let f : (Δ[1] : SSet.{u}) ⟶ (core X : SSet.{u}) := yonedaEquiv.symm ⟨e.edge, hs⟩
  obtain ⟨g, hg⟩ := exists_extension_into_kan f
  refine ⟨g, ?_⟩
  rw [← Category.assoc, hg]
  exact yonedaEquiv_symm_comp _ _

/-- Native extensions out of this one Kan interval detect exactly the equivalence edges. -/
theorem isEquivalence_iff_extension {X : SSet.{u}} [Quasicategory X]
    (e : X _⦋1⦌) :
    (Edge.mk' e).IsEquivalence ↔
      ∃ g : object.{u} ⟶ X, edge.{u} ≫ g = yonedaEquiv.symm e := by
  constructor
  · intro he
    obtain ⟨g, hg⟩ := exists_core_extension (Edge.mk' e) he
    exact ⟨g ≫ (core X).ι, hg⟩
  · rintro ⟨g, hg⟩
    have he := (Edge.isEquivalence_of_kanComplex (Edge.mk' (yonedaEquiv edge.{u}))).map g
    apply he.of_edge_eq
    change g.app (op ⦋1⦌) (yonedaEquiv edge.{u}) = e
    rw [← yonedaEquiv_comp, hg, Equiv.apply_symm_apply]

end SSet.KanEdgeDetector
