/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltrationPrism

/-!
# The exact original marked cylinder of a cone maximum stage

The new upper maximum layer is maximally marked. The bottom retains its
original constant-maximum marking, and all cross-layer edges remain
unmarked. Thus the entire original bounded cone, including every mark,
is the genuine top-marked cylinder of its preceding stage. The same
whole simplex maps give both inverse marked maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

private theorem interval_min_marked_iff (e : (Δ[1] : SSet.{u}) _⦋1⦌) :
    e ∈ (min (Δ[1] : SSet.{u})).marking ↔ e 0 = e 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro h
    refine ⟨(Δ[1] : SSet.{u}).δ 0 e, ?_⟩
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j
    · exact h.symm
    · rfl

/-- The whole original constant-maximum edge predicate is exactly the cylinder's bottom marking together
  with its maximal original top layer. -/
theorem coneFiltrationPrism_marking_iff {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (e : (coneAtMostWeight i k).toSSet _⦋1⦌) :
    e ∈ (coneAtMostWeight i k).marking ↔
      (coneFiltrationPrism hi).app (op ⦋1⦌) e ∈ (topMarkedCylinder (coneBeforeWeight i k)).marking := by
  constructor
  · intro he
    change (e.obj 0).val.maximum = (e.obj 1).val.maximum at he
    by_cases h0 : (e.obj 0).val.maximum = k
    · have h1 : (e.obj 1).val.maximum = k := he.symm.trans h0
      refine Or.inr ⟨e ⋙ coneEraseTopFunctor hi, ?_⟩
      apply Prod.ext
      · rfl
      · apply SSet.stdSimplex.ext
        intro j
        change (1 : Fin 2) = (coneFiltrationLevel (e.obj j)).down
        fin_cases j
        · simp [coneFiltrationLevel, h0]
        · simp [coneFiltrationLevel, h1]
    · have h1 : (e.obj 1).val.maximum ≠ k := fun h => h0 (he.trans h)
      have ht0 := lt_of_le_of_ne (e.obj 0).property h0
      have ht1 := lt_of_le_of_ne (e.obj 1).property h1
      refine Or.inl ⟨?_, ?_⟩
      · change (coneEraseTop hi (e.obj 0)).val.maximum = (coneEraseTop hi (e.obj 1)).val.maximum
        rw [coneEraseTop_before hi _ ht0, coneEraseTop_before hi _ ht1]
        exact he
      · apply (interval_min_marked_iff _).mpr
        change (coneFiltrationLevel (e.obj 0)).down = (coneFiltrationLevel (e.obj 1)).down
        simp [coneFiltrationLevel, h0, h1]
  · intro he
    change (e.obj 0).val.maximum = (e.obj 1).val.maximum
    rcases he with he | ⟨a, ha⟩
    · have hl := (interval_min_marked_iff _).mp he.2
      change (coneFiltrationLevel (e.obj 0)).down = (coneFiltrationLevel (e.obj 1)).down at hl
      by_cases h0 : (e.obj 0).val.maximum = k
      · by_cases h1 : (e.obj 1).val.maximum = k
        · exact h0.trans h1.symm
        · simp [coneFiltrationLevel, h0, h1] at hl
      · by_cases h1 : (e.obj 1).val.maximum = k
        · simp [coneFiltrationLevel, h0, h1] at hl
        · have ht0 := lt_of_le_of_ne (e.obj 0).property h0
          have ht1 := lt_of_le_of_ne (e.obj 1).property h1
          have hm := he.1
          change (coneEraseTop hi (e.obj 0)).val.maximum = (coneEraseTop hi (e.obj 1)).val.maximum at hm
          rw [coneEraseTop_before hi _ ht0, coneEraseTop_before hi _ ht1] at hm
          exact hm
    · have h0 := congrArg (fun z : (topMarkedCylinder (coneBeforeWeight i k)).toSSet _⦋1⦌ =>
        (SSet.stdSimplex.objEquiv z.2).toOrderHom 0) ha
      have h1 := congrArg (fun z : (topMarkedCylinder (coneBeforeWeight i k)).toSSet _⦋1⦌ =>
        (SSet.stdSimplex.objEquiv z.2).toOrderHom 1) ha
      change (1 : Fin 2) = (coneFiltrationLevel (e.obj 0)).down at h0
      change (1 : Fin 2) = (coneFiltrationLevel (e.obj 1)).down at h1
      have ht0 : (e.obj 0).val.maximum = k := by
        by_contra h
        simp [coneFiltrationLevel, h] at h0
      have ht1 : (e.obj 1).val.maximum = k := by
        by_contra h
        simp [coneFiltrationLevel, h] at h1
      exact ht0.trans ht1.symm

/-- The original bounded cone is its exact top-marked preceding-stage cylinder, through the same whole
  native simplex isomorphism. -/
def coneFiltrationCylinderIso {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    coneAtMostWeight i k ≅ topMarkedCylinder (coneBeforeWeight i k) :=
  isoMk (coneFiltrationPrismIso hi) (coneFiltrationPrism_marking_iff hi)

end SSet.Marked.CoherentWeight
