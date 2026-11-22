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
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalTupleSpineVertexBoundaries

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

/-- The actual product of ALL original vertex objects of the fixed prefix. -/
abbrev tupleVertexBase (W : SimplicialSpace.{u}) (r : ℕ) : SSet.{u} :=
  ∏ᶜ (fun _ : Fin (r + 1) => W.diagram _⦋0⦌)


/-- The original full tuple point, retaining Delta0 as point source. -/
def tuplePoint (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ tupleVertexBase W r :=
  Pi.lift (fun i => SSet.yonedaEquiv.symm (x i))


/-- The original all-vertex projection of a nonempty prefix. -/
def tupleVertexMap (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r) :
    prefixObject W n r h ⟶ tupleVertexBase W r :=
  Pi.lift (vertexProjection W n r h hr)


/-- The SAME chosen pullback over ALL original tuple vertices. -/
abbrev tuplePrefixFibre (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (tupleVertexMap W n r h hr) (tuplePoint W r x)


/-- The actual product of all original adjacent mapping fibres at the fixed tuple. -/
abbrev tupleFibreProduct (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  ∏ᶜ (fun i : Fin r => mappingFibre W (x i.castSucc) (x i.succ))


private theorem tuplePrefixFibre_vertex (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin (r + 1)) :
    pullback.fst (tupleVertexMap W n r h hr) (tuplePoint W r x) ≫
        vertexProjection W n r h hr i =
      pullback.snd (tupleVertexMap W n r h hr) (tuplePoint W r x) ≫
        SSet.yonedaEquiv.symm (x i) := by
  have heq := congrArg (fun q => q ≫ Pi.π _ i)
    (pullback.condition (f := tupleVertexMap W n r h hr) (g := tuplePoint W r x))
  simpa only [Category.assoc, tupleVertexMap, tuplePoint, Pi.lift_comp_π] using heq


/-- The actual i-th tuple-fibre map is the native pullback lift retaining its edge and point. -/
def fibreToEdge (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    tuplePrefixFibre W n r h hr x ⟶ mappingFibre W (x i.castSucc) (x i.succ) :=
  pullback.lift
    (pullback.fst _ _ ≫ edgeProjection W n r h i) (pullback.snd _ _)
    (by
      apply prod.hom_ext
      · rw [Category.assoc, mappingEndpoint_fst, Category.assoc,
          edgeProjection_source, Category.assoc, mappingPointPair_fst]
        exact tuplePrefixFibre_vertex W n r h hr x i.castSucc
      · rw [Category.assoc, mappingEndpoint_snd, Category.assoc,
          edgeProjection_target, Category.assoc, mappingPointPair_snd]
        exact tuplePrefixFibre_vertex W n r h hr x i.succ)


/-- The actual forward whole tuple-fibre map is built from every original edge pullback lift. -/
def fibreProductHom (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePrefixFibre W n r h hr x ⟶ tupleFibreProduct W r x :=
  Pi.lift (fibreToEdge W n r h hr x)


/-- Each original mapping-fibre factor projects to its actual edge in the SAME product. -/
def productEdge (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    tupleFibreProduct W r x ⟶ W.diagram _⦋1⦌ :=
  Pi.π _ i ≫ mappingFibre.fst W (x i.castSucc) (x i.succ)


/-- The whole adjacent-fibre product has the actual SAME terminal Delta0 point map. -/
def productPoint (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tupleFibreProduct W r x ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from _


private theorem productPoint_eq (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    Pi.π _ i ≫ mappingFibre.snd W (x i.castSucc) (x i.succ) = productPoint W r x :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _


private theorem productEdge_source (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    productEdge W r x i ≫ W.diagram.δ (1 : Fin 2) =
      productPoint W r x ≫ SSet.yonedaEquiv.symm (x i.castSucc) := by
  rw [productEdge, Category.assoc, mappingFibre.source_eq, ← Category.assoc,
    productPoint_eq]


private theorem productEdge_target (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    productEdge W r x i ≫ W.diagram.δ (0 : Fin 2) =
      productPoint W r x ≫ SSet.yonedaEquiv.symm (x i.succ) := by
  rw [productEdge, Category.assoc, mappingFibre.target_eq, ← Category.assoc,
    productPoint_eq]


private theorem productEdge_adjacent (W : SimplicialSpace.{u}) (r : ℕ)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) : Adjacent (productEdge W r x) := by
  intro j hj
  rw [productEdge_target, productEdge_source]
  rfl


/-- The original product edge family is internally glued into the SAME ambient prefix. -/
def gluedPrefix (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tupleFibreProduct W r x ⟶ prefixObject W n r h :=
  prefixLift W n r h hr (productEdge W r x) (productEdge_adjacent W r x)


private theorem gluedPrefix_vertex (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin (r + 1)) :
    gluedPrefix W n r h hr x ≫ vertexProjection W n r h hr i =
      productPoint W r x ≫ SSet.yonedaEquiv.symm (x i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [vertexProjection, Fin.cases_zero]
    rw [← Category.assoc]
    dsimp only [gluedPrefix]
    rw [prefixLift_edge, productEdge_source]
    rfl
  · simp only [vertexProjection, Fin.cases_succ]
    rw [← Category.assoc]
    dsimp only [gluedPrefix]
    rw [prefixLift_edge, productEdge_target]


/-- The actual inverse whole tuple-fibre map glues every original edge at the SAME terminal
point. -/
def fibreProductInv (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tupleFibreProduct W r x ⟶ tuplePrefixFibre W n r h hr x :=
  pullback.lift (gluedPrefix W n r h hr x) (productPoint W r x)
    (by
      apply Pi.hom_ext
      intro i
      simpa only [Category.assoc, tupleVertexMap, tuplePoint, Pi.lift_comp_π] using
        gluedPrefix_vertex W n r h hr x i)


/-- The SAME full positive-prefix tuple fibre is the product of ALL its original adjacent fibres. -/
def tuplePrefixFibreIso (W : SimplicialSpace.{u}) (n r : ℕ) (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tuplePrefixFibre W n r h hr x ≅ tupleFibreProduct W r x where
  hom := fibreProductHom W n r h hr x
  inv := fibreProductInv W n r h hr x
  hom_inv_id := by
    apply pullback.hom_ext
    · apply edgeProjection_hom_ext W n r h hr
      intro i
      dsimp only [fibreProductInv]
      simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      dsimp only [gluedPrefix]
      rw [prefixLift_edge]
      dsimp only [productEdge, fibreProductHom]
      rw [← Category.assoc, Pi.lift_comp_π]
      dsimp only [fibreToEdge]
      dsimp only [mappingFibre.fst, mappingFibre]
      rw [pullback.lift_fst]
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    apply pullback.hom_ext
    · dsimp only [fibreProductHom]
      rw [Category.assoc, Pi.lift_comp_π]
      dsimp only [fibreToEdge]
      dsimp only [mappingFibre.fst, mappingFibre]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
      dsimp only [fibreProductInv]
      rw [pullback.lift_fst]
      dsimp only [gluedPrefix]
      rw [prefixLift_edge]
      rfl
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _



/-- The forward whole prefix Iso retains BOTH original mapping-fibre pullback legs. -/
theorem tuplePrefixFibreIso_hom_legs (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    (tuplePrefixFibreIso W n r h hr x).hom ≫ Pi.π _ i ≫
        mappingFibre.fst W (x i.castSucc) (x i.succ) =
      pullback.fst (tupleVertexMap W n r h hr) (tuplePoint W r x) ≫
        edgeProjection W n r h i ∧
    (tuplePrefixFibreIso W n r h hr x).hom ≫ Pi.π _ i ≫
        mappingFibre.snd W (x i.castSucc) (x i.succ) =
      pullback.snd (tupleVertexMap W n r h hr) (tuplePoint W r x) := by
  constructor
  · dsimp only [tuplePrefixFibreIso, fibreProductHom]
    rw [← Category.assoc, Pi.lift_comp_π]
    exact pullback.lift_fst _ _ _
  · dsimp only [tuplePrefixFibreIso, fibreProductHom]
    rw [← Category.assoc, Pi.lift_comp_π]
    exact pullback.lift_snd _ _ _


/-- The inverse whole prefix Iso retains the original edge and SAME terminal-point projections. -/
theorem tuplePrefixFibreIso_inv_legs (W : SimplicialSpace.{u}) (n r : ℕ)
    (h : r ≤ n) (hr : 1 ≤ r)
    (x : Fin (r + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin r) :
    (tuplePrefixFibreIso W n r h hr x).inv ≫
        pullback.fst (tupleVertexMap W n r h hr) (tuplePoint W r x) ≫
          edgeProjection W n r h i =
      Pi.π _ i ≫ mappingFibre.fst W (x i.castSucc) (x i.succ) ∧
    (tuplePrefixFibreIso W n r h hr x).inv ≫
        pullback.snd (tupleVertexMap W n r h hr) (tuplePoint W r x) =
      Pi.π _ i ≫ mappingFibre.snd W (x i.castSucc) (x i.succ) := by
  constructor
  · dsimp only [tuplePrefixFibreIso, fibreProductInv]
    rw [← Category.assoc, pullback.lift_fst]
    dsimp only [gluedPrefix]
    rw [prefixLift_edge]
    rfl
  · dsimp only [tuplePrefixFibreIso, fibreProductInv]
    rw [pullback.lift_snd]
    exact (productPoint_eq W r x i).symm


end SimplicialSpace.FixedTupleSpinePrefix
