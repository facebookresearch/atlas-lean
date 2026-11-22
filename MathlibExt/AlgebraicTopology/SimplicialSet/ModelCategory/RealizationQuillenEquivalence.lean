/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWUnit
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence

/-!
# The realization--singular Quillen equivalence

In every universe, geometric realization and the singular simplicial set form
a Quillen adjunction and a Quillen equivalence for the selected model
structures on simplicial sets and topological spaces.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section
universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen TopCat.modelCategory

namespace SSet.modelCategoryQuillen

private theorem preservesFibrations_toSSet :
    PreservesFibrations (C := TopCat.{u}) (D := SSet.{u})
      TopCat.toSSet := by
  intro X Y p hp
  rw [fibrations_eq]
  apply (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp
  change TopCat.realizedHornInclusions.rlp p at hp
  exact hp

private theorem preservesTrivialFibrations_toSSet :
    PreservesTrivialFibrations (C := TopCat.{u}) (D := SSet.{u})
      TopCat.toSSet := by
  intro X Y p hp
  have hp' : TopCat.realizedHornInclusions.rlp p ∧
      TopCat.weakHomotopyEquivalences p := by
    change TopCat.realizedHornInclusions.rlp p ∧
      TopCat.weakHomotopyEquivalences p at hp
    exact hp
  have hFib : J.rlp (TopCat.toSSet.map p) :=
    (TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hp'.1
  have hW : SSet.KanComplex.W (TopCat.toSSet.map p) :=
    (TopCat.mem_weakHomotopyEquivalences_iff p).mp hp'.2
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex _
  have hWeak : SSet.realizationWeakEquivalences
      (TopCat.toSSet.map p) :=
    (SSet.KanComplex.W_iff_realizationWeakEquivalence
      (TopCat.toSSet.map p)).mp hW
  change fibrations SSet.{u} (TopCat.toSSet.map p) ∧
    weakEquivalences SSet.{u} (TopCat.toSSet.map p)
  constructor
  · rw [fibrations_eq]
    exact hFib
  · change SSet.realizationWeakEquivalences (TopCat.toSSet.map p)
    exact hWeak

/-- Geometric realization and the singular simplicial set form a Quillen
adjunction for the selected model structures in every universe. -/
noncomputable scoped instance realizationIsQuillenAdjunction :
    CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} := by
  exact
    CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
      (adj := sSetTopAdj)
      preservesFibrations_toSSet
      preservesTrivialFibrations_toSSet

/-- The realization--singular counit is a weak homotopy equivalence. -/
theorem counit_mem_weakHomotopyEquivalences (Y : TopCat.{u}) :
    TopCat.weakHomotopyEquivalences (sSetTopAdj.counit.app Y) := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj
        (TopCat.toSSet.obj Y)) :=
    TopCat.toSSet_obj_kanComplex _
  have hEta : SSet.KanComplex.W
      (sSetTopAdj.unit.app (TopCat.toSSet.obj Y)) :=
    SSet.KanComplex.W.sSetTopAdj_unit_app (TopCat.toSSet.obj Y)
  have hComp : SSet.KanComplex.W
      (sSetTopAdj.unit.app (TopCat.toSSet.obj Y) ≫
        TopCat.toSSet.map (sSetTopAdj.counit.app Y)) := by
    rw [sSetTopAdj.right_triangle_components]
    simpa only [Functor.id_obj] using
      (SSet.KanComplex.W.id (X := TopCat.toSSet.obj Y))
  have hCounit : SSet.KanComplex.W
      (TopCat.toSSet.map (sSetTopAdj.counit.app Y)) :=
    SSet.KanComplex.W.of_precomp hEta hComp
  exact (TopCat.mem_weakHomotopyEquivalences_iff _).mpr hCounit

/-- The realization--singular unit is a realization weak equivalence in every
universe. -/
theorem unit_mem_realizationWeakEquivalences (X : SSet.{u}) :
    SSet.realizationWeakEquivalences (sSetTopAdj.unit.app X) := by
  let RX := TopCat.toSSet.obj (SSet.toTop.obj X)
  let _ : SSet.KanComplex RX := TopCat.toSSet_obj_kanComplex _
  have hEta : SSet.KanComplex.W (sSetTopAdj.unit.app RX) :=
    SSet.KanComplex.W.sSetTopAdj_unit_app RX
  have hCompRight : SSet.KanComplex.W
      (sSetTopAdj.unit.app RX ≫
        TopCat.toSSet.map (sSetTopAdj.counit.app (SSet.toTop.obj X))) := by
    rw [sSetTopAdj.right_triangle_components]
    simpa only [Functor.id_obj] using
      (SSet.KanComplex.W.id (X := RX))
  have hCounit : SSet.KanComplex.W
      (TopCat.toSSet.map (sSetTopAdj.counit.app (SSet.toTop.obj X))) :=
    SSet.KanComplex.W.of_precomp hEta hCompRight
  have hCompEq :
      TopCat.toSSet.map (SSet.toTop.map (sSetTopAdj.unit.app X)) ≫
          TopCat.toSSet.map (sSetTopAdj.counit.app (SSet.toTop.obj X)) =
        𝟙 RX := by
    calc
      _ = TopCat.toSSet.map
          (SSet.toTop.map (sSetTopAdj.unit.app X) ≫
            sSetTopAdj.counit.app (SSet.toTop.obj X)) :=
        (TopCat.toSSet.map_comp _ _).symm
      _ = TopCat.toSSet.map (𝟙 (SSet.toTop.obj X)) :=
        congrArg TopCat.toSSet.map
          (sSetTopAdj.{u}.left_triangle_components X)
      _ = 𝟙 RX := TopCat.toSSet.map_id _
  have hCompLeft : SSet.KanComplex.W
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map
          (sSetTopAdj.unit.app X) ≫
        TopCat.toSSet.map (sSetTopAdj.counit.app (SSet.toTop.obj X))) := by
    change SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (sSetTopAdj.unit.app X)) ≫
        TopCat.toSSet.map (sSetTopAdj.counit.app (SSet.toTop.obj X)))
    rw [hCompEq]
    simpa only [Functor.id_obj] using
      (SSet.KanComplex.W.id (X := RX))
  exact SSet.KanComplex.W.of_postcomp hCounit hCompLeft
/-- Geometric realization and the singular simplicial set form a Quillen
equivalence for the selected model structures in every universe. -/
noncomputable scoped instance realizationIsQuillenEquivalence :
    CategoryTheory.Adjunction.IsQuillenEquivalence sSetTopAdj.{u} := by
  let _ : CategoryTheory.Adjunction.IsQuillenAdjunction sSetTopAdj.{u} :=
    realizationIsQuillenAdjunction
  refine
    { homEquiv_weakEquivalence_iff := ?_ }
  intro X Y _ _ f
  let g : X ⟶ TopCat.toSSet.obj Y := sSetTopAdj.homEquiv X Y f
  have hEta : SSet.realizationWeakEquivalences
      (sSetTopAdj.unit.app X) :=
    unit_mem_realizationWeakEquivalences X
  have hEta' : weakEquivalences SSet.{u}
      (sSetTopAdj.unit.app X) := by
    change SSet.realizationWeakEquivalences (sSetTopAdj.unit.app X)
    exact hEta
  let _ : SSet.KanComplex
      (TopCat.toSSet.obj (SSet.toTop.obj X)) :=
    TopCat.toSSet_obj_kanComplex _
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex _
  have hMap : weakEquivalences TopCat.{u} f ↔
      weakEquivalences SSet.{u} (TopCat.toSSet.map f) := by
    change TopCat.weakHomotopyEquivalences f ↔
      SSet.realizationWeakEquivalences (TopCat.toSSet.map f)
    exact (TopCat.mem_weakHomotopyEquivalences_iff f).trans
      (SSet.KanComplex.W_iff_realizationWeakEquivalence
        (TopCat.toSSet.map f))
  have hHom : g = sSetTopAdj.unit.app X ≫ TopCat.toSSet.map f :=
    sSetTopAdj.homEquiv_unit X Y f
  have hPre := (weakEquivalences SSet.{u}).precomp_iff
    (sSetTopAdj.unit.app X) (TopCat.toSSet.map f) hEta'
  calc
    weakEquivalences TopCat.{u} f ↔
        weakEquivalences SSet.{u} (TopCat.toSSet.map f) := hMap
    _ ↔ weakEquivalences SSet.{u}
        (sSetTopAdj.unit.app X ≫ TopCat.toSSet.map f) := hPre.symm
    _ ↔ weakEquivalences SSet.{u} g := by rw [hHom]

end SSet.modelCategoryQuillen
