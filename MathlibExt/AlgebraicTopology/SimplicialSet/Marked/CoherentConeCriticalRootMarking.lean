/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOperators
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceVertices
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# The original last critical edge in the whole cone coefficient marking

The original final degeneracy identifies precisely the last two original
maximum vertices. Pulling back the original constant-maximum marking
along this same whole cone operator marks the original constant-maximum
edges and the original critical last-edge change. Every original subset,
scalar word and underlying cone-operator map remains unchanged.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original final simplex degeneracy collapses exactly the original critical last-edge pair. -/
def coneCriticalMaximumCollapse (n : ℕ) : Vertex.{u} (n + 2) →o Vertex.{u} (n + 1) :=
  (SimplexCategory.σ (Fin.last (n + 1))).toOrderHom.uliftMap

/-- The original critical final edge starts at the same original penultimate vertex. -/
def coneCriticalPrevious (n : ℕ) : Vertex.{u} (n + 2) := ULift.up (Fin.last (n + 1)).castSucc

/-- The original critical final edge ends at the same original last vertex. -/
def coneCriticalLast (n : ℕ) : Vertex.{u} (n + 2) := ULift.up (Fin.last (n + 2))

/-- Every original vertex below the final one keeps its exact original index under the actual final degeneracy. -/
theorem coneCriticalMaximumCollapse_castSucc (n : ℕ) (i : Fin (n + 2)) :
    coneCriticalMaximumCollapse.{u} n (ULift.up i.castSucc) = ULift.up i := by
  change ULift.up ((Fin.last (n + 1)).predAbove i.castSucc) = ULift.up i
  exact congrArg ULift.up Fin.predAbove_last_castSucc

/-- The actual final degeneracy sends the original last vertex to the same original critical predecessor. -/
theorem coneCriticalMaximumCollapse_last (n : ℕ) :
    coneCriticalMaximumCollapse.{u} n (coneCriticalLast n) = ULift.up (Fin.last (n + 1)) := by
  change ULift.up ((Fin.last (n + 1)).predAbove (Fin.last (n + 2))) = ULift.up (Fin.last (n + 1))
  exact congrArg ULift.up Fin.predAbove_right_last

/-- The same original critical predecessor has exactly the same collapsed maximum as the original final vertex. -/
theorem coneCriticalMaximumCollapse_previous (n : ℕ) :
    coneCriticalMaximumCollapse.{u} n (coneCriticalPrevious n) = ULift.up (Fin.last (n + 1)) :=
  coneCriticalMaximumCollapse_castSucc n (Fin.last (n + 1))

/-- The whole original final degeneracy fixes the same original root. -/
theorem coneCriticalMaximumCollapse_root (n : ℕ) :
    coneCriticalMaximumCollapse.{u} n (⊥ : Vertex.{u} (n + 2)) = ⊥ :=
  coneCriticalMaximumCollapse_castSucc n (0 : Fin (n + 2))

/-- On every original increasing maximum pair the actual final degeneracy identifies precisely an original constant
pair or the same original critical final edge. -/
theorem coneCriticalMaximumCollapse_eq_iff (n : ℕ) (i j : Vertex.{u} (n + 2)) (hij : i ≤ j) :
    coneCriticalMaximumCollapse n i = coneCriticalMaximumCollapse n j ↔
      i = j ∨ (i = coneCriticalPrevious n ∧ j = coneCriticalLast n) := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  change i ≤ j at hij
  cases i using Fin.lastCases with
  | last =>
    have h : j = Fin.last (n + 2) := le_antisymm (Fin.le_last j) hij
    subst j
    simp only [eq_self, true_or]
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      have hlast : coneCriticalMaximumCollapse.{u} n (ULift.up (Fin.last (n + 2))) = ULift.up (Fin.last (n + 1)) :=
        coneCriticalMaximumCollapse_last n
      rw [coneCriticalMaximumCollapse_castSucc, hlast]
      simp only [coneCriticalPrevious, coneCriticalLast, ULift.up_inj, Fin.castSucc_ne_last,
        Fin.castSucc_inj, false_or, eq_self, and_true]
    | cast j =>
      simp only [coneCriticalMaximumCollapse_castSucc, coneCriticalPrevious, coneCriticalLast,
        ULift.up_inj, Fin.castSucc_inj, Fin.castSucc_ne_last, and_false, or_false]

/-- The same entire original cone coefficient marks precisely its original maximum after the actual critical
last-edge collapse. -/
def coneCriticalWeight (n : ℕ) (i : Vertex.{u} (n + 2)) : Marked.{u} where
  toSSet := nerve (ConeSubset i)
  marking := {e | coneCriticalMaximumCollapse n (e.obj 0).maximum =
    coneCriticalMaximumCollapse n (e.obj 1).maximum}
  degenerate_mem _ := rfl

/-- The original whole constant-maximum coefficient enters the critical marking by its literal underlying identity. -/
def coneCriticalMark (n : ℕ) (i : Vertex.{u} (n + 2)) : coneWeight i ⟶ coneCriticalWeight n i where
  hom := 𝟙 _
  preserve he := congrArg (coneCriticalMaximumCollapse n) he

/-- The same actual final-degeneracy cone operator carries the complete critical coefficient to its original
constant-maximum target. -/
def coneCriticalProjection (n : ℕ) (i : Vertex.{u} (n + 2)) :
    coneCriticalWeight n i ⟶ coneWeight (coneCriticalMaximumCollapse n i) where
  hom := (coneImage (coneCriticalMaximumCollapse n) i).hom
  preserve {e} he := by
    change ((e.obj 0).image (coneCriticalMaximumCollapse n)).maximum =
      ((e.obj 1).image (coneCriticalMaximumCollapse n)).maximum
    exact (ConeSubset.image_maximum _ _).trans (he.trans (ConeSubset.image_maximum _ _).symm)

/-- The entire original constant-maximum to critical marking retains precisely the original whole final-degeneracy
cone map. -/
theorem coneCriticalMark_projection (n : ℕ) (i : Vertex.{u} (n + 2)) :
    coneCriticalMark n i ≫ coneCriticalProjection n i = coneImage (coneCriticalMaximumCollapse n) i := Hom.ext rfl

/-- The complete critical coefficient is genuinely the same original cone carrier with the original constant-maximum
marking pulled back along the exact original final-degeneracy map. -/
def coneCriticalWeightComapIso (n : ℕ) (i : Vertex.{u} (n + 2)) :
    coneCriticalWeight n i ≅ comap (coneWeight (coneCriticalMaximumCollapse n i))
      (coneImage (coneCriticalMaximumCollapse n) i).hom :=
  isoMk (Iso.refl _) (fun e => by
    change (coneCriticalMaximumCollapse n (e.obj 0).maximum = coneCriticalMaximumCollapse n (e.obj 1).maximum) ↔
      ((e.obj 0).image (coneCriticalMaximumCollapse n)).maximum = ((e.obj 1).image (coneCriticalMaximumCollapse
        n)).maximum
    simp only [ConeSubset.image_maximum])

/-- Every full original critical marked edge is precisely an original maximum-preserving edge or the same original
critical penultimate-to-final maximum change. -/
theorem coneCriticalWeight_marked_iff (n : ℕ) (i : Vertex.{u} (n + 2))
    (e : (nerve (ConeSubset i)) _⦋1⦌) :
    e ∈ (coneCriticalWeight n i).marking ↔
      (e.obj 0).maximum = (e.obj 1).maximum ∨
        ((e.obj 0).maximum = coneCriticalPrevious n ∧ (e.obj 1).maximum = coneCriticalLast n) :=
  coneCriticalMaximumCollapse_eq_iff n _ _
    (ConeSubset.maximum_mono (leOfHom (e.map (homOfLE (show (0 : Fin 2) ≤ 1 from Fin.zero_le _)))))

end SSet.Marked.CoherentWeight
