/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LatentProjection

/-!
# Tests for latent projection

Concrete projections on `Fin 3`: a latent middle node of a chain creates a
directed edge, a latent fork root creates a bidirected edge, and an observed
fork root creates none.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity

namespace BayesNet

/-- Parents of the chain `0 → 1 → 2` on `Fin 3`. -/
def chainPaCC : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {1}

/-- Parents of the fork `0 → 1`, `0 → 2` on `Fin 3`. -/
def forkPaCC : (k : Fin 3) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}
  | ⟨2, _⟩ => {0}

/-- Chain with `1` latent: the projection has a directed edge `0 → 2`. -/
theorem latentChain_dir {α : Type*}
    (cpt : (k : Fin 3) → (chainPaCC k → α) → StdSimplex ℝ α) :
    ((BayesNet.mk chainPaCC cpt).latentProjection {1}).dir
      ⟨0, by decide⟩ ⟨2, by decide⟩ := by
  have e01 : (BayesNet.mk chainPaCC cpt).Edge 0 1 := by
    show ∃ _h : (0 : Fin 3).val < (1 : Fin 3).val,
      (⟨(0 : Fin 3).val, _h⟩ : Fin (1 : Fin 3).val) ∈ chainPaCC 1
    refine ⟨?_, ?_⟩
    · decide
    · decide
  have e12 : (BayesNet.mk chainPaCC cpt).Edge 1 2 := by
    show ∃ _h : (1 : Fin 3).val < (2 : Fin 3).val,
      (⟨(1 : Fin 3).val, _h⟩ : Fin (2 : Fin 3).val) ∈ chainPaCC 2
    refine ⟨?_, ?_⟩
    · decide
    · decide
  have h1 : (1 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by decide
  exact ⟨1, Relation.ReflTransGen.single ⟨e01, h1⟩, e12⟩

/-- Fork with `0` latent: the projection has a bidirected edge `1 ↔ 2`. -/
theorem latentFork_bidir {α : Type*}
    (cpt : (k : Fin 3) → (forkPaCC k → α) → StdSimplex ℝ α) :
    ((BayesNet.mk forkPaCC cpt).latentProjection {0}).bidir.Adj
      ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  have e01 : (BayesNet.mk forkPaCC cpt).Edge 0 1 := by
    show ∃ _h : (0 : Fin 3).val < (1 : Fin 3).val,
      (⟨(0 : Fin 3).val, _h⟩ : Fin (1 : Fin 3).val) ∈ forkPaCC 1
    refine ⟨?_, ?_⟩
    · decide
    · decide
  have e02 : (BayesNet.mk forkPaCC cpt).Edge 0 2 := by
    show ∃ _h : (0 : Fin 3).val < (2 : Fin 3).val,
      (⟨(0 : Fin 3).val, _h⟩ : Fin (2 : Fin 3).val) ∈ forkPaCC 2
    refine ⟨?_, ?_⟩
    · decide
    · decide
  have h0 : (0 : Fin 3) ∈ ({0} : Finset (Fin 3)) := by decide
  refine ⟨by decide, 0, h0, ⟨0, Relation.ReflTransGen.refl, e01⟩,
    ⟨0, Relation.ReflTransGen.refl, e02⟩⟩

/-- Fork with `0` observed: no bidirected edge `1 ↔ 2`. -/
theorem observedFork_not_bidir {α : Type*}
    (cpt : (k : Fin 3) → (forkPaCC k → α) → StdSimplex ℝ α) :
    ¬ ((BayesNet.mk forkPaCC cpt).latentProjection ∅).bidir.Adj
      ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  intro h
  obtain ⟨-, t, ht, _, _⟩ := h
  exact (Finset.notMem_empty t) ht

end BayesNet

end Cslib.MachineLearning.GraphicalModels
