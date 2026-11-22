/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootReplacement
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductSymmetry
import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# The entire original critical-root marked interval prisms

The original subset and its whole critical coface replacement both
include into their actual finite union. This union retains precisely
the same original collapsed maximum. Both genuine natural transformations
therefore give entire maximally marked interval prisms, retaining the
original critical marker, all scalar words and their exact endpoints.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original complete subset and its same original critical replacement form their actual whole finite union. -/
def coneCriticalRootUnionSubset (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    ConeSubset (⊥ : Vertex.{u} (n + 2)) where
  vertices := a.vertices ∪ ((coneCriticalRootReplacementFunctor n).obj a).vertices
  mem := Finset.mem_union_left _ a.mem
  lower _ _ := bot_le

/-- Every original whole subset includes into its same actual full critical union. -/
theorem coneCriticalRootUnion_left (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    a ≤ coneCriticalRootUnionSubset n a := Finset.subset_union_left

/-- Every original whole critical replacement includes into the same actual full union. -/
theorem coneCriticalRootUnion_right (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    (coneCriticalRootReplacementFunctor n).obj a ≤ coneCriticalRootUnionSubset n a := Finset.subset_union_right

/-- The same complete original critical union preserves the actual collapsed maximum at every original subset. -/
theorem coneCriticalRootUnion_collapsedMaximum (n : ℕ) (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) :
    coneCriticalMaximumCollapse n (coneCriticalRootUnionSubset n a).maximum = coneCriticalMaximumCollapse n
      a.maximum := by
  let f := coneCriticalMaximumCollapse n
  let r := (coneCriticalRootReplacementFunctor n).obj a
  let b := coneCriticalRootUnionSubset n a
  apply le_antisymm
  · rcases Finset.mem_union.mp b.maximum_mem with h | h
    · exact f.monotone (a.le_maximum b.maximum h)
    · exact (f.monotone (r.le_maximum b.maximum h)).trans_eq (coneCriticalRootReplacement_collapsedMaximum n a)
  · exact f.monotone (ConeSubset.maximum_mono (coneCriticalRootUnion_left n a))

/-- The complete original critical unions form their genuine whole inclusion functor. -/
def coneCriticalRootUnionFunctor (n : ℕ) :
    ConeSubset (⊥ : Vertex.{u} (n + 2)) ⥤ ConeSubset (⊥ : Vertex.{u} (n + 2)) where
  obj := coneCriticalRootUnionSubset n
  map f := homOfLE (Finset.union_subset_union (leOfHom f)
    (leOfHom ((coneCriticalRootReplacementFunctor n).map f)))

/-- The actual original identity-to-union inclusion is natural on every original whole subset map. -/
def coneCriticalRootUnionIdentityUnit (n : ℕ) :
    𝟭 (ConeSubset (⊥ : Vertex.{u} (n + 2))) ⟶ coneCriticalRootUnionFunctor n where
  app a := homOfLE (coneCriticalRootUnion_left n a)
  naturality _ _ _ := Subsingleton.elim _ _

/-- The same actual original replacement-to-union inclusion is natural on every whole original subset map. -/
def coneCriticalRootUnionReplacementUnit (n : ℕ) :
    coneCriticalRootReplacementFunctor n ⟶ coneCriticalRootUnionFunctor n where
  app a := homOfLE (coneCriticalRootUnion_right n a)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Every original scalar vertex of the identity-to-union cylinder keeps its entire original collapsed maximum. -/
theorem coneCriticalRootIdentityCylinder_collapsedMaximum (n : ℕ)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) (t : Fin 2) :
    coneCriticalMaximumCollapse n (((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj (a, t)).maximum =
      coneCriticalMaximumCollapse n a.maximum := by
  fin_cases t
  · rfl
  · exact coneCriticalRootUnion_collapsedMaximum n a

/-- Every original scalar vertex of the replacement-to-union cylinder retains the same complete original collapsed
maximum. -/
theorem coneCriticalRootReplacementCylinder_collapsedMaximum (n : ℕ)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 2))) (t : Fin 2) :
    coneCriticalMaximumCollapse n (((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj (a, t)).maximum =
      coneCriticalMaximumCollapse n a.maximum := by
  fin_cases t
  · exact coneCriticalRootReplacement_collapsedMaximum n a
  · exact coneCriticalRootUnion_collapsedMaximum n a

/-- The same original union functor is a genuine whole marked critical coefficient map. -/
def coneCriticalRootUnionMap (n : ℕ) :
    coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) ⟶ coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) where
  hom := nerveMap (coneCriticalRootUnionFunctor n)
  preserve {e} he := (coneCriticalRootUnion_collapsedMaximum n (e.obj 0)).trans
    (he.trans (coneCriticalRootUnion_collapsedMaximum n (e.obj 1)).symm)

/-- The whole original identity-to-union cylinder is a genuine maximally parameter marked prism with the exact
original critical coefficient marking. -/
def coneCriticalRootIdentityPrism (n : ℕ) :
    prod (max (Δ[1] : SSet.{u})) (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) ⟶
      coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) where
  hom := (prodSwapIso (max (Δ[1] : SSet.{u})) (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom.hom ≫
    (coneCriticalRootUnionIdentityUnit n).nerveHomotopyMap
  preserve {e} he :=
    (coneCriticalRootIdentityCylinder_collapsedMaximum n (e.2.obj 0) _).trans
      (he.2.trans (coneCriticalRootIdentityCylinder_collapsedMaximum n (e.2.obj 1) _).symm)

/-- The whole original replacement-to-union cylinder is an actual maximally parameter marked prism preserving every
original critical maximum change. -/
def coneCriticalRootReplacementPrism (n : ℕ) :
    prod (max (Δ[1] : SSet.{u})) (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2))) ⟶
      coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)) where
  hom := (prodSwapIso (max (Δ[1] : SSet.{u})) (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom.hom ≫
    (coneCriticalRootUnionReplacementUnit n).nerveHomotopyMap
  preserve {e} he :=
    (coneCriticalRootReplacementCylinder_collapsedMaximum n (e.2.obj 0) _).trans
      (he.2.trans (coneCriticalRootReplacementCylinder_collapsedMaximum n (e.2.obj 1) _).symm)

/-- The actual original source endpoint of the full identity prism is precisely the unchanged whole critical-root
identity. -/
theorem coneCriticalRootIdentityPrism_source (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))) ≫
      coneCriticalRootIdentityPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom ≫ 𝟙 _ := by
  apply Hom.ext
  ext q z
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj
    (z.2.obj t, (1 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = z.2.obj t
  rw [hz]
  rfl

/-- The actual original target endpoint of the full identity prism retains precisely the same whole critical union
map. -/
theorem coneCriticalRootIdentityPrism_target (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))) ≫
      coneCriticalRootIdentityPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom ≫
          coneCriticalRootUnionMap n := by
  apply Hom.ext
  ext q z
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionIdentityUnit n).nerveCylinderFunctor).obj
    (z.2.obj t, (0 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = coneCriticalRootUnionSubset n (z.2.obj t)
  rw [hz]
  rfl

/-- The actual original source endpoint of the full replacement prism retains the entire same original marked
collapse-section composite. -/
theorem coneCriticalRootReplacementPrism_source (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (1 : Fin 2))) (𝟙 (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))) ≫
      coneCriticalRootReplacementPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom ≫
          (coneCriticalRootProjection n ≫ coneCriticalRootSection n) := by
  apply Hom.ext
  ext q z
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj
    (z.2.obj t, (1 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = (coneCriticalRootReplacementFunctor
      n).obj (z.2.obj t)
  rw [hz]
  rfl

/-- The actual original target endpoint of the entire replacement prism is the same whole marked critical union map. -/
theorem coneCriticalRootReplacementPrism_target (n : ℕ) :
    prodMap (maximal.map (SSet.stdSimplex.δ (0 : Fin 2))) (𝟙 (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))) ≫
      coneCriticalRootReplacementPrism n =
        (zeroParameterUnitIso .maximal (coneCriticalWeight n (⊥ : Vertex.{u} (n + 2)))).hom ≫
          coneCriticalRootUnionMap n := by
  apply Hom.ext
  ext q z
  refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  have hz : SSet.stdSimplex.asOrderHom z.1 t = (0 : Fin 1) := Fin.eq_zero _
  change ((coneCriticalRootUnionReplacementUnit n).nerveCylinderFunctor).obj
    (z.2.obj t, (0 : Fin 2).succAbove (SSet.stdSimplex.asOrderHom z.1 t)) = coneCriticalRootUnionSubset n (z.2.obj t)
  rw [hz]
  rfl

end SSet.Marked.CoherentWeight
