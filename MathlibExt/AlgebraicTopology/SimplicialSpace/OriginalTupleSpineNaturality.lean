/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalSpaces
import Mathlib.Tactic.FinCases
import MathlibExt.AlgebraicTopology.SimplicialSpace.MappingFibre
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalTupleSpinePositiveFibres

/-!
# Original ambient-prefix edge restrictions

The model-free induction uses the actual prefix pullback;
no caller preservation, cocone, gluing Iso or homotopical outcome is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace SimplicialSpace.FixedTupleSpinePrefix

/-- Every original simplicial-space arrow acts on the SAME ambient prefix object. -/
def prefixMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) (n r : ℕ) (h : r ≤ n) :
    prefixObject W n r h ⟶ prefixObject V n r h :=
  (discreteSourceMappingMap f).app
    (op (SSet.Rezk.spinePrefixSubcomplex.{u} n r h : SSet.{u}))


/-- Each literal edge restriction retains the original target arrow. -/
theorem prefixMap_edge {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n r : ℕ) (h : r ≤ n) (i : Fin r) :
    prefixMap f n r h ≫ edgeProjection V n r h i =
      edgeProjection W n r h i ≫ f.hom.app (op ⦋1⦌) := by
  unfold prefixMap edgeProjection
  rw [← Category.assoc, ← (discreteSourceMappingMap f).naturality
    (edgeInclusion.{u} n r h i).op, Category.assoc,
    discreteYonedaIso_naturality_target]
  exact (Category.assoc _ _ _).symm


/-- Every vertex restriction retains that SAME original target arrow. -/
theorem prefixMap_vertex {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r) (i : Fin (r + 1)) :
    prefixMap f n r h ≫ vertexProjection V n r h hr i =
      vertexProjection W n r h hr i ≫ f.hom.app (op ⦋0⦌) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [vertexProjection, Fin.cases_zero]
    rw [← Category.assoc, prefixMap_edge, Category.assoc,
      ← SimplicialObject.δ_naturality, ← Category.assoc]
  · simp only [vertexProjection, Fin.cases_succ]
    rw [← Category.assoc, prefixMap_edge, Category.assoc,
      ← SimplicialObject.δ_naturality, ← Category.assoc]


private theorem tupleVertexMap_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r) :
    tupleVertexMap W n r h hr ≫ CategoryTheory.Limits.Pi.map
        (fun _ : Fin (r + 1) => f.hom.app (op ⦋0⦌)) =
      prefixMap f n r h ≫ tupleVertexMap V n r h hr := by
  apply Pi.hom_ext
  intro i
  simpa only [Category.assoc, CategoryTheory.Limits.Pi.map_π, tupleVertexMap,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc] using (prefixMap_vertex f n r h hr i).symm


private theorem tuplePoint_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (r : ℕ) (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePoint W r x ≫ CategoryTheory.Limits.Pi.map (fun _ : Fin (r + 1) => f.hom.app (op ⦋0⦌)) =
      tuplePoint V r (fun i => mappingVertexMap f (x i)) := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, CategoryTheory.Limits.Pi.map_π, tuplePoint,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc, SSet.yonedaEquiv_symm_comp, mappingVertexMap]


/-- The original tuple fibre map carries EVERY prescribed vertex through the original arrow. -/
def tuplePrefixFibreMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePrefixFibre W n r h hr x ⟶
      tuplePrefixFibre V n r h hr (fun i => mappingVertexMap f (x i)) :=
  pullback.lift (pullback.fst _ _ ≫ prefixMap f n r h) (pullback.snd _ _)
    (by
      rw [Category.assoc, ← tupleVertexMap_naturality, ← Category.assoc,
        pullback.condition, Category.assoc, tuplePoint_naturality])


/-- The full forward Iso square preserves every original target arrow and adjacent MF map. -/
theorem tuplePrefixFibreIso_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePrefixFibreMap f n r h hr x ≫
        (tuplePrefixFibreIso V n r h hr (fun i => mappingVertexMap f (x i))).hom =
      (tuplePrefixFibreIso W n r h hr x).hom ≫
        CategoryTheory.Limits.Pi.map (fun i : Fin r => mappingFibre.map f
          (x := x i.castSucc) (y := x i.succ) rfl rfl) := by
  apply Pi.hom_ext
  intro i
  dsimp only [tuplePrefixFibreIso, fibreProductHom]
  rw [Category.assoc, Pi.lift_comp_π, Category.assoc, CategoryTheory.Limits.Pi.map_π,
    ← Category.assoc, Pi.lift_comp_π]
  apply pullback.hom_ext
  · dsimp only [fibreToEdge, mappingFibre.map, mappingFibre, pullback.map]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    dsimp only [tuplePrefixFibreMap]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, prefixMap_edge]
  · dsimp only [fibreToEdge, mappingFibre.map, mappingFibre, pullback.map]
    simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullback.lift_snd _ _ _


/-- The full inverse Iso square preserves the SAME original target arrow as well. -/
theorem tuplePrefixFibreIso_inv_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    CategoryTheory.Limits.Pi.map (fun i : Fin r => mappingFibre.map f
        (x := x i.castSucc) (y := x i.succ) rfl rfl) ≫
      (tuplePrefixFibreIso V n r h hr (fun i => mappingVertexMap f (x i))).inv =
    (tuplePrefixFibreIso W n r h hr x).inv ≫ tuplePrefixFibreMap f n r h hr x := by
  apply (cancel_epi (tuplePrefixFibreIso W n r h hr x).hom).mp
  rw [← Category.assoc, ← tuplePrefixFibreIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]



/-- The final original ambient prefix compares to the existing chosen full-spine cospan limit. -/
def fullPrefixChosenIso (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k) :
    prefixObject W k k le_rfl ≅ limit (segalMappingCospan W k hk) :=
  ((discreteSourceMapping W).mapIso
    (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_full.{u} k)).op).symm ≪≫
      segalSpineMappingIso W k hk


private theorem finalEdgeInclusion_transport (k : ℕ) (i : Fin k) :
    edgeInclusion.{u} k k le_rfl i ≫
      (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_full.{u} k)).hom =
        SSet.Rezk.spineEdgeInclusion k i := by
  apply (cancel_mono (SSet.Rezk.spineSubcomplex.{u} k).ι).mp
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  rfl


/-- Every edge of the transported chosen limit is EXACTLY the existing original edge projection. -/
theorem fullPrefixChosenIso_edge (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (i : Fin k) :
    (fullPrefixChosenIso W k hk).inv ≫ edgeProjection W k k le_rfl i =
      segalStrictEdgeProjection W k hk i := by
  unfold fullPrefixChosenIso edgeProjection segalStrictEdgeProjection
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, Iso.op_hom,
    Category.assoc]
  rw [← Category.assoc ((discreteSourceMapping W).map _)
      ((discreteSourceMapping W).map _) _, ← Functor.map_comp, ← op_comp,
    finalEdgeInclusion_transport]


/-- The existing chosen full-spine limit carries all actual original tuple vertices. -/
def chosenSpineVertexMap (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k) :
    limit (segalMappingCospan W k hk) ⟶ tupleVertexBase W k :=
  (fullPrefixChosenIso W k hk).inv ≫ tupleVertexMap W k k le_rfl (by omega)


/-- The original all-vertex fibre of the actual chosen full-spine limit. -/
abbrev chosenSpineTupleFibre (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (chosenSpineVertexMap W k hk) (tuplePoint W k x)


/-- The original chosen full-spine fibre maps to its exact ambient-prefix fibre with both pullback
legs. -/
def chosenFibreToPrefix (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    chosenSpineTupleFibre W k hk x ⟶ tuplePrefixFibre W k k le_rfl (by omega) x :=
  pullback.lift (pullback.fst _ _ ≫ (fullPrefixChosenIso W k hk).inv)
    (pullback.snd _ _)
    (by
      refine (Category.assoc _ _ _).trans ?_
      exact pullback.condition (f := chosenSpineVertexMap W k hk) (g := tuplePoint W k x))


/-- The exact ambient-prefix fibre maps back to the original chosen full-spine fibre. -/
def prefixFibreToChosen (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePrefixFibre W k k le_rfl (by omega) x ⟶ chosenSpineTupleFibre W k hk x :=
  pullback.lift (pullback.fst _ _ ≫ (fullPrefixChosenIso W k hk).hom)
    (pullback.snd _ _)
    (by
      dsimp only [chosenSpineVertexMap]
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact pullback.condition)


/-- The two actual chosen-spine/prefix fibre maps form the original whole comparison Iso. -/
def chosenFibrePrefixIso (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    chosenSpineTupleFibre W k hk x ≅ tuplePrefixFibre W k k le_rfl (by omega) x where
  hom := chosenFibreToPrefix W k hk x
  inv := prefixFibreToChosen W k hk x
  hom_inv_id := by
    apply pullback.hom_ext
    · dsimp only [chosenFibreToPrefix, prefixFibreToChosen]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · dsimp only [chosenFibreToPrefix, prefixFibreToChosen]
      simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · dsimp only [chosenFibreToPrefix, prefixFibreToChosen]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · dsimp only [chosenFibreToPrefix, prefixFibreToChosen]
      simp only [Category.assoc, pullback.lift_snd, Category.id_comp]


/-- The actual existing chosen full-spine fibre is the product of EVERY original adjacent fibre. -/
def chosenSpineTupleFibreIso (W : SimplicialSpace.{u}) (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    chosenSpineTupleFibre W k hk x ≅ tupleFibreProduct W k x :=
  chosenFibrePrefixIso W k hk x ≪≫ tuplePrefixFibreIso W k k le_rfl (by omega) x



end SimplicialSpace.FixedTupleSpinePrefix
