/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeUnderlying
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterCore
import MathlibExt.AlgebraicTopology.Quasicategory.CorePullback
import MathlibExt.AlgebraicTopology.Quasicategory.CoreKan

/-!
# Whole original prism equations and cores of fixed-base complexes

Every simplex of the native fixed-base pullback has its original prism
over the supplied source projection. The point coordinate introduces no
different base map. Over a quasicategory base, the existing strict-pullback
equivalence theorem identifies the native core condition with the core
condition on that same whole prism; the zero-parameter projection has only
equivalence edges.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- Each original constant marked base simplex is the original parameter projection followed by the base map. -/
theorem mappingBasePoint_app_hom (k : ParameterMarking) {X Z : Marked.{u}} (r : X ⟶ Z)
    (n : SimplexCategoryᵒᵖ) (t : (Δ[0] : SSet.{u}).obj n) :
    ((mappingBasePoint k r).app n t).hom =
      CartesianMonoidalCategory.snd ((simplexParameter k).obj n.unop).toSSet X.toSSet ≫ r.hom := by
  cases k <;> ext m x <;> rfl

/-- The original unmarked base simplex has the same whole parameter-projection equation. -/
theorem parameterBasePoint_app {X Z : Marked.{u}} (r : X ⟶ Z)
    (n : SimplexCategoryᵒᵖ) (t : (Δ[0] : SSet.{u}).obj n) :
    (parameterBasePoint r).app n t =
      CartesianMonoidalCategory.snd (SSet.stdSimplex.obj n.unop) X.toSSet ≫ r.hom :=
  mappingBasePoint_app_hom .minimal r n t

/-- The whole prism of an original marked relative simplex lies over the supplied source base map. -/
theorem relativeMapping_prism_over (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (t : (relativeMappingComplex k r p).obj n) :
    ((pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app n t).hom ≫ p.hom =
      CartesianMonoidalCategory.snd ((simplexParameter k).obj n.unop).toSSet X.toSSet ≫ r.hom := by
  have h := ConcreteCategory.congr_hom
    (congr_app (pullback.condition (f := mappingComplexPost k X p)
      (g := mappingBasePoint k r)) n) t
  have h' := congrArg Hom.hom h
  change ((pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app n t).hom ≫ p.hom =
    ((mappingBasePoint k r).app n
      ((pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)).app n t)).hom at h'
  rw [mappingBasePoint_app_hom] at h'
  exact h'

/-- The original unmarked relative simplex retains that same literal whole-prism base equation. -/
theorem parameterRelative_prism_over {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (n : SimplexCategoryᵒᵖ)
    (t : (parameterRelative r p).obj n) :
    (pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)).app n t ≫ p.hom =
      CartesianMonoidalCategory.snd (SSet.stdSimplex.obj n.unop) X.toSSet ≫ r.hom := by
  have h := ConcreteCategory.congr_hom
    (congr_app (pullback.condition (f := parameterMappingPost X.toSSet p.hom)
      (g := parameterBasePoint r)) n) t
  change (pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)).app n t ≫ p.hom =
    (parameterBasePoint r).app n
      ((pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)).app n t) at h
  rw [parameterBasePoint_app] at h
  exact h

/-- A relative simplex is in the native core exactly when its original whole prism is in the native function core. -/
theorem mem_core_parameterRelative_iff {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) [InnerFibration p.hom] [Quasicategory Z.toSSet]
    (n : SimplexCategoryᵒᵖ) (t : (parameterRelative r p).obj n) :
    t ∈ (core (parameterRelative r p)).obj n ↔
      (pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)).app n t ∈
        (core (parameterMapping X.toSSet Y.toSSet)).obj n := by
  let a : parameterRelative r p ⟶ parameterMapping X.toSSet Y.toSSet :=
    pullback.fst (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)
  let b : parameterRelative r p ⟶ (Δ[0] : SSet.{u}) :=
    pullback.snd (parameterMappingPost X.toSSet p.hom) (parameterBasePoint r)
  let _ : InnerFibration (parameterMappingPost X.toSSet p.hom) :=
    parameterMappingPost_innerFibration X.toSSet p.hom
  let _ : Quasicategory (parameterMapping X.toSSet Z.toSSet) :=
    parameterMapping_quasicategory X.toSSet Z.toSSet
  let _ : KanComplex (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 (Δ[0] : SSet.{u}))
      SSet.stdSimplex.isTerminalObj₀).mpr (inferInstance : Fibration (𝟙 (Δ[0] : SSet.{u})))
  constructor
  · intro h φ
    exact ((h φ).map a).of_edge_eq (NatTrans.naturality_apply a φ.op t)
  · intro h φ
    let e := Edge.mk' ((parameterRelative r p).map φ.op t)
    apply (Edge.isEquivalence_pullback_iff (parameterMappingPost X.toSSet p.hom)
      (parameterBasePoint r) e).mpr
    refine ⟨?_, Edge.isEquivalence_of_kanComplex (e.map b)⟩
    exact (h φ).of_edge_eq (NatTrans.naturality_apply a φ.op t).symm

end SSet.Marked
