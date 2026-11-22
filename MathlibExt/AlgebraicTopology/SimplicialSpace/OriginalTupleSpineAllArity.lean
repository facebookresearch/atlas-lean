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
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalTupleSpineNaturality

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

/-- The full chosen-spine Iso retains the actual original arrow between its finite cospans. -/
theorem fullPrefixChosenIso_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (hk : 2 ≤ k) :
    prefixMap f k k le_rfl ≫ (fullPrefixChosenIso V k hk).hom =
      (fullPrefixChosenIso W k hk).hom ≫ lim.map (segalMappingCospanMap f k hk) := by
  have hn := (discreteSourceMappingMap f).naturality
    (SSet.Subcomplex.eqToIso (SSet.Rezk.spinePrefixSubcomplex_full.{u} k)).op.inv
  simp only [Iso.op_inv] at hn
  unfold prefixMap fullPrefixChosenIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv]
  rw [← Category.assoc, ← hn, Category.assoc, segalSpineMappingIso_naturality]
  exact (Category.assoc _ _ _).symm


private theorem fullPrefixChosenIso_inv_naturality {W V : SimplicialSpace.{u}}
    (f : W ⟶ V) (k : ℕ) (hk : 2 ≤ k) :
    lim.map (segalMappingCospanMap f k hk) ≫ (fullPrefixChosenIso V k hk).inv =
      (fullPrefixChosenIso W k hk).inv ≫ prefixMap f k k le_rfl := by
  apply (cancel_epi (fullPrefixChosenIso W k hk).hom).mp
  rw [← Category.assoc, ← fullPrefixChosenIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]


/-- The existing finite chosen full-spine map acts on the exact all-vertex pullback. -/
def chosenSpineTupleFibreMap {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    chosenSpineTupleFibre W k hk x ⟶
      chosenSpineTupleFibre V k hk (fun i => mappingVertexMap f (x i)) :=
  chosenFibreToPrefix W k hk x ≫
    tuplePrefixFibreMap f k k le_rfl (by omega) x ≫
      prefixFibreToChosen V k hk (fun i => mappingVertexMap f (x i))


/-- BOTH original pullback legs of the full chosen-spine map remain exact. -/
theorem chosenSpineTupleFibreMap_legs {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    chosenSpineTupleFibreMap f k hk x ≫
        pullback.fst (chosenSpineVertexMap V k hk)
          (tuplePoint V k (fun i => mappingVertexMap f (x i))) =
      pullback.fst (chosenSpineVertexMap W k hk) (tuplePoint W k x) ≫
        lim.map (segalMappingCospanMap f k hk) ∧
    chosenSpineTupleFibreMap f k hk x ≫
        pullback.snd (chosenSpineVertexMap V k hk)
          (tuplePoint V k (fun i => mappingVertexMap f (x i))) =
      pullback.snd (chosenSpineVertexMap W k hk) (tuplePoint W k x) := by
  constructor
  · unfold chosenSpineTupleFibreMap prefixFibreToChosen tuplePrefixFibreMap chosenFibreToPrefix
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [fullPrefixChosenIso_naturality, Iso.inv_hom_id_assoc]
  · unfold chosenSpineTupleFibreMap prefixFibreToChosen tuplePrefixFibreMap chosenFibreToPrefix
    simp only [Category.assoc, pullback.lift_snd]


/-- The full chosen-spine Iso is natural for every original target arrow at fixed arity. -/
theorem chosenSpineTupleFibreIso_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    chosenSpineTupleFibreMap f k hk x ≫
        (chosenSpineTupleFibreIso V k hk (fun i => mappingVertexMap f (x i))).hom =
      (chosenSpineTupleFibreIso W k hk x).hom ≫
        CategoryTheory.Limits.Pi.map (fun i : Fin k => mappingFibre.map f
          (x := x i.castSucc) (y := x i.succ) rfl rfl) := by
  unfold chosenSpineTupleFibreMap chosenSpineTupleFibreIso
  simp only [Iso.trans_hom, chosenFibrePrefixIso]
  rw [Category.assoc, Category.assoc]
  have hc : prefixFibreToChosen V k hk (fun i => mappingVertexMap f (x i)) ≫
      chosenFibreToPrefix V k hk (fun i => mappingVertexMap f (x i)) = 𝟙 _ :=
    (chosenFibrePrefixIso V k hk (fun i => mappingVertexMap f (x i))).inv_hom_id
  rw [← Category.assoc (prefixFibreToChosen _ _ _ _) _ _, hc, Category.id_comp,
    Category.assoc, tuplePrefixFibreIso_naturality]


/-- The inverse full chosen-spine square preserves the same original arrow too. -/
theorem chosenSpineTupleFibreIso_inv_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (hk : 2 ≤ k)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    CategoryTheory.Limits.Pi.map (fun i : Fin k => mappingFibre.map f
        (x := x i.castSucc) (y := x i.succ) rfl rfl) ≫
      (chosenSpineTupleFibreIso V k hk (fun i => mappingVertexMap f (x i))).inv =
    (chosenSpineTupleFibreIso W k hk x).inv ≫ chosenSpineTupleFibreMap f k hk x := by
  apply (cancel_epi (chosenSpineTupleFibreIso W k hk x).hom).mp
  rw [← Category.assoc, ← chosenSpineTupleFibreIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]



end SimplicialSpace.FixedTupleSpinePrefix

namespace SimplicialSpace.FixedTupleSpine
open FixedTupleSpinePrefix FixedTupleSpineBoundary

/-- The actual all-k tuple-spine fibre uses A0, A1, and the existing higher chosen cospan limit. -/
def tupleSpineFibre (W : SimplicialSpace.{u}) :
    (k : ℕ) → (Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) → SSet.{u} := fun k => match k with
  | 0 => fun x => literalZeroEdgeTupleFibre W x
  | 1 => fun x => oneEdgeTupleFibre W x
  | j + 2 => fun x => chosenSpineTupleFibre W (j + 2) (by omega) x


/-- Every original arity has the SAME whole tuple-fibre/product Iso, with k0 and k1 constructed. -/
def tupleSpineFibreIso (W : SimplicialSpace.{u}) :
    (k : ℕ) → (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) →
      tupleSpineFibre W k x ≅
        ∏ᶜ (fun i : Fin k => mappingFibre W (x i.castSucc) (x i.succ)) := fun k => match k with
  | 0 => fun x =>
    literalZeroEdgeTupleFibreIso W x ≪≫ zeroEdgeTupleFibreIso W (x 0) ≪≫
      SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso (emptyProductIsTerminal _)
  | 1 => fun x =>
    oneEdgeTupleFibreIso W x ≪≫
      (productUniqueIso (fun i : Fin 1 => mappingFibre W (x i.castSucc) (x i.succ))).symm
  | j + 2 => fun x => chosenSpineTupleFibreIso W (j + 2) (by omega) x



/-- The original all-k tuple map uses only the actual zero, one, and chosen higher carriers. -/
def tupleSpineFibreMap {W V : SimplicialSpace.{u}} (f : W ⟶ V) :
    (k : ℕ) → (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) →
      tupleSpineFibre W k x ⟶
        tupleSpineFibre V k (fun i => mappingVertexMap f (x i)) := fun k => match k with
  | 0 => fun x =>
    (literalZeroEdgeTupleFibreIso W x).hom ≫ (zeroEdgeTupleFibreIso W (x 0)).hom ≫
      (zeroEdgeTupleFibreIso V (mappingVertexMap f (x 0))).inv ≫
        (literalZeroEdgeTupleFibreIso V (fun i => mappingVertexMap f (x i))).inv
  | 1 => fun x =>
    (oneEdgeTupleFibreIso W x).hom ≫
      mappingFibre.map f (x := x 0) (y := x 1) rfl rfl ≫
        (oneEdgeTupleFibreIso V (fun i => mappingVertexMap f (x i))).inv
  | j + 2 => fun x => chosenSpineTupleFibreMap f (j + 2) (by omega) x


/-- The SAME all-k tuple Iso commutes with every original target arrow and every MF component. -/
theorem tupleSpineFibreIso_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    tupleSpineFibreMap f k x ≫
        (tupleSpineFibreIso V k (fun i => mappingVertexMap f (x i))).hom =
      (tupleSpineFibreIso W k x).hom ≫
        CategoryTheory.Limits.Pi.map (fun i : Fin k => mappingFibre.map f
          (x := x i.castSucc) (y := x i.succ) rfl rfl) := by
  cases k with
  | zero =>
    apply Pi.hom_ext
    intro i
    exact Fin.elim0 i
  | succ k =>
    cases k with
    | zero =>
      apply Pi.hom_ext
      intro i
      have hi : i = (0 : Fin 1) := by
        apply Fin.ext
        omega
      subst i
      dsimp only [tupleSpineFibreIso, tupleSpineFibreMap, tupleSpineFibre]
      simp only [Iso.trans_hom, Category.assoc,
        Iso.inv_hom_id_assoc, CategoryTheory.Limits.Pi.map_π]
      simp
    | succ j => exact chosenSpineTupleFibreIso_naturality f (j + 2) (by omega) x


/-- The all-k inverse square retains every original target arrow as well. -/
theorem tupleSpineFibreIso_inv_naturality {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (k : ℕ) (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) :
    CategoryTheory.Limits.Pi.map (fun i : Fin k => mappingFibre.map f
        (x := x i.castSucc) (y := x i.succ) rfl rfl) ≫
      (tupleSpineFibreIso V k (fun i => mappingVertexMap f (x i))).inv =
    (tupleSpineFibreIso W k x).inv ≫ tupleSpineFibreMap f k x := by
  apply (cancel_epi (tupleSpineFibreIso W k x).hom).mp
  rw [← Category.assoc, ← tupleSpineFibreIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]



/-- Each actual chosen spine has its original edge projection, with no fake zero edge. -/
def spineEdgeProjection (W : SimplicialSpace.{u}) :
    (k : ℕ) → Fin k →
      ((match k with
        | 0 => W.diagram _⦋0⦌
        | 1 => W.diagram _⦋1⦌
        | j + 2 => limit (segalMappingCospan W (j + 2) (by omega))) ⟶
        W.diagram _⦋1⦌) := fun k => match k with
  | 0 => fun i => Fin.elim0 i
  | 1 => fun _ => 𝟙 _
  | j + 2 => fun i => segalStrictEdgeProjection W (j + 2) (by omega) i


/-- The original whole edge projection out of the SAME all-k tuple fibre. -/
def tupleSpineEdge (W : SimplicialSpace.{u}) :
    (k : ℕ) → (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) →
      Fin k → (tupleSpineFibre W k x ⟶ W.diagram _⦋1⦌) := fun k => match k with
  | 0 => fun _ i => Fin.elim0 i
  | 1 => fun x _ => pullback.fst _ _
  | j + 2 => fun x i => pullback.fst _ _ ≫ segalStrictEdgeProjection W (j + 2) (by omega) i


/-- Every arity retains the SAME original point projection to Delta0. -/
def tupleSpinePoint (W : SimplicialSpace.{u}) :
    (k : ℕ) → (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) →
      (tupleSpineFibre W k x ⟶ (Δ[0] : SSet.{u})) := fun k => match k with
  | 0 => fun _x => pullback.snd _ _
  | 1 => fun _x => pullback.snd _ _
  | _j + 2 => fun _x => pullback.snd _ _


/-- Every forward factor of the all-k Iso retains its original edge and point projections. -/
theorem tupleSpineFibreIso_hom_legs (W : SimplicialSpace.{u}) (k : ℕ)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin k) :
    (tupleSpineFibreIso W k x).hom ≫ Pi.π _ i ≫
        mappingFibre.fst W (x i.castSucc) (x i.succ) = tupleSpineEdge W k x i ∧
    (tupleSpineFibreIso W k x).hom ≫ Pi.π _ i ≫
        mappingFibre.snd W (x i.castSucc) (x i.succ) = tupleSpinePoint W k x := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    cases k with
    | zero =>
      have hi : i = (0 : Fin 1) := by
        apply Fin.ext
        omega
      subst i
      constructor
      · dsimp only [tupleSpineFibreIso, tupleSpineFibre]
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
          productUniqueIso_inv_π_assoc]
        change (oneEdgeTupleFibreIso W x).hom ≫ mappingFibre.fst W (x 0) (x 1) =
          pullback.fst _ _
        dsimp only [oneEdgeTupleFibreIso, oneEdgeTupleFibre, mappingFibre.fst,
          mappingFibre, pullbackPostIso]
        dsimp only [id]
        simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
          pullback.map, pullback.lift_fst, Category.comp_id]
      · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    | succ j =>
      constructor
      · dsimp only [tupleSpineFibreIso, chosenSpineTupleFibreIso, tupleSpineEdge, tupleSpineFibre]
        rw [Iso.trans_hom, Category.assoc,
          (tuplePrefixFibreIso_hom_legs W (j + 2) (j + 2) le_rfl (by omega) x i).1]
        dsimp only [chosenFibrePrefixIso, chosenFibreToPrefix]
        rw [← Category.assoc, pullback.lift_fst, Category.assoc,
          fullPrefixChosenIso_edge]
      · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _


/-- Every direct inverse factor retains the original edge and SAME point of the all-k fibre. -/
theorem tupleSpineFibreIso_inv_legs (W : SimplicialSpace.{u}) (k : ℕ)
    (x : Fin (k + 1) → (W.diagram _⦋0⦌) _⦋0⦌) (i : Fin k) :
    (tupleSpineFibreIso W k x).inv ≫ tupleSpineEdge W k x i =
      Pi.π _ i ≫ mappingFibre.fst W (x i.castSucc) (x i.succ) ∧
    (tupleSpineFibreIso W k x).inv ≫ tupleSpinePoint W k x =
      Pi.π _ i ≫ mappingFibre.snd W (x i.castSucc) (x i.succ) := by
  have h := tupleSpineFibreIso_hom_legs W k x i
  constructor
  · apply (cancel_epi (tupleSpineFibreIso W k x).hom).mp
    rw [Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using h.1.symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _


end SimplicialSpace.FixedTupleSpine
