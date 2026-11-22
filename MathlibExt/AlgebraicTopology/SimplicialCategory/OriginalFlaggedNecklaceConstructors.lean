/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklaceConcatenationFlags
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedNecklacePoint

/-!
# Actual original flagged necklace constructors

The original zero necklace, whole beads and concatenated necklaces
retain their complete input maps, original endpoint equations and every
coefficient flag. Concatenation uses the proved actual native pushout.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace

open OriginalBead OriginalBead.TerminalFlag
open SSet.OriginalNecklace SSet.OriginalTwoBead.OrdinalCharts

/-- The same complete native bead, with exactly its two original endpoints as joints. -/
abbrev beadData (n : ℕ) : Data where
  dimension := n
  joints := {0, Fin.last n}
  source_joint := Finset.mem_insert_self _ _
  target_joint := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The actual whole standard-simplex chart of the native bead. -/
def beadChart (n : ℕ) : (beadData n).object.{u} ≅ (Δ[n] : SSet.{u}) :=
  SSet.Subcomplex.eqToIso complex_endpoints ≪≫ SSet.Subcomplex.topIso (Δ[n] : SSet.{u})

/-- The whole bead chart retains its same literal standard-simplex inclusion. -/
theorem beadChart_hom (n : ℕ) : (beadChart.{u} n).hom = (complex (beadData n).joints).ι := rfl

/-- The actual full original bead is an object of the same complete flagged-necklace category. -/
abbrev ofBead {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (b : Bead K x y q) : Object K x y q where
  necklace := beadData b.dimension
  input := (beadChart b.dimension).hom ≫ SSet.yonedaEquiv.symm b.simplex
  source_eq := by
    change SSet.yonedaEquiv
      (vertexMap {0, Fin.last b.dimension} 0 ≫
        (complex {0, Fin.last b.dimension}).ι ≫ SSet.yonedaEquiv.symm b.simplex) = x
    rw [← Category.assoc, vertexMap_ι, ← SSet.yonedaEquiv_naturality,
      Equiv.apply_symm_apply]
    exact b.source_eq
  target_eq := by
    change SSet.yonedaEquiv
      (vertexMap {0, Fin.last b.dimension} (Fin.last b.dimension) ≫
        (complex {0, Fin.last b.dimension}).ι ≫ SSet.yonedaEquiv.symm b.simplex) = y
    rw [← Category.assoc, vertexMap_ι, ← SSet.yonedaEquiv_naturality,
      Equiv.apply_symm_apply]
    exact b.target_eq
  coefficient := b.coefficient
  joints j hj := by
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ((NormalForms.coefficient b).obj 0).left
    · have h := Finset.mem_singleton.mp hj
      subst j
      exact ((NormalForms.coefficient b).obj 0).right

/-- The zero-dimensional original necklace at any original input vertex and scalar degree. -/
def unit (K : SSet.{u}) (q : SimplexCategoryᵒᵖ) (x : K _⦋0⦌) : Object K x x q where
  necklace := Point.data
  input := (complex Point.data.joints).ι ≫ SSet.yonedaEquiv.symm x
  source_eq := by
    change SSet.yonedaEquiv
      (vertexMap {0} 0 ≫ (complex {0}).ι ≫ SSet.yonedaEquiv.symm x) = x
    rw [← Category.assoc, vertexMap_ι]
    rw [SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0)) (𝟙 (Δ[0] : SSet.{u})),
      Category.id_comp, Equiv.apply_symm_apply]
  target_eq := by
    change SSet.yonedaEquiv
      (vertexMap {0} 0 ≫ (complex {0}).ι ≫ SSet.yonedaEquiv.symm x) = x
    rw [← Category.assoc, vertexMap_ι]
    rw [SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0)) (𝟙 (Δ[0] : SSet.{u})),
      Category.id_comp, Equiv.apply_symm_apply]
  coefficient := Point.pointCoefficient q
  joints j hj := by
    have h : j = 0 := Finset.mem_singleton.mp hj
    subst j
    exact ((Point.pointCoefficient q).obj 0).left

variable {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}

/-- The exact original equality at the common input vertex of two composable whole necklaces. -/
theorem concat_endpoint_eq (T : Object K x y q) (U : Object K y z q) :
    T.necklace.target ≫ T.input = U.necklace.source ≫ U.input :=
  SSet.yonedaEquiv.injective (T.target_eq.trans U.source_eq.symm)

/-- The entire original concatenated flagged necklace over the same original input. -/
abbrev concat (T : Object K x y q) (U : Object K y z q) : Object K x z q where
  necklace := T.necklace.concat U.necklace
  input := concatInput T.necklace U.necklace T.input U.input (concat_endpoint_eq T U)
  source_eq := by
    rw [← concatLeft_source T.necklace U.necklace, Category.assoc, concatLeft_input]
    exact T.source_eq
  target_eq := by
    rw [← concatRight_target T.necklace U.necklace, Category.assoc, concatRight_input]
    exact U.target_eq
  coefficient := ConcatFlags.coefficient T.coefficient U.coefficient
  joints j hj := by
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨j, hjT, rfl⟩ := Finset.mem_map.mp hj
      exact Or.inl ⟨ULift.up.{u} j, T.joints j hjT, rfl⟩
    · obtain ⟨j, hjU, rfl⟩ := Finset.mem_map.mp hj
      exact Or.inr ⟨ULift.up.{u} j, U.joints j hjU, rfl⟩

/-- The actual original concatenated object retains precisely both original joint images. -/
theorem concat_joints (T : Object K x y q) (U : Object K y z q) :
    (concat T U).necklace.joints =
      T.necklace.joints.map (prefixEmbedding T.necklace.dimension U.necklace.dimension).toEmbedding ∪
        U.necklace.joints.map (suffix T.necklace.dimension U.necklace.dimension).toEmbedding := rfl

/-- The actual concatenated object reads back the same whole first input. -/
theorem concat_first_input (T : Object K x y q) (U : Object K y z q) :
    concatLeft T.necklace U.necklace ≫ (concat T U).input = T.input :=
  concatLeft_input _ _ _ _ _

/-- The actual concatenated object reads back the same whole second input. -/
theorem concat_second_input (T : Object K x y q) (U : Object K y z q) :
    concatRight T.necklace U.necklace ≫ (concat T U).input = U.input :=
  concatRight_input _ _ _ _ _

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace
