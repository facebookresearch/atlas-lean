/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteUnionWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexWeakEquivalences

/-!
# Actual original nonempty faces and the two outer-face union

Every nonempty original face is its native representable simplex,
with the SAME original face inclusion map. Standard ordinal weakness
and actual finite-union gluing prove the full union of the two original
outer faces weak in dimensions at least two. Empty intersections are
excluded by the explicit dimension bound.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial
namespace SSet.stdSimplex

/-- EVERY same original nonempty face inclusion is realization weak. -/
theorem face_inclusion_weak {n : ℕ} (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    realizationWeakEquivalences (face.{u} S).ι := by
  classical
  let m := S.card - 1
  have hc : S.card = m + 1 := by
    have hp := Finset.card_pos.mpr hS
    dsimp [m]
    omega
  let e : (Δ[m] : SSet.{u}) ≅ (face S : SSet.{u}) :=
    isoOfRepresentableBy (faceRepresentableBy S m (S.orderIsoOfFin hc))
  let α : ⦋m⦌ ⟶ ⦋n⦌ := SSet.stdSimplex.preimage (e.hom ≫ (face S).ι)
  have hα : SSet.stdSimplex.map α = e.hom ≫ (face S).ι := SSet.stdSimplex.map_preimage _
  apply realizationWeakEquivalences.of_precomp e.hom (face S).ι
    (realizationWeakEquivalences.of_isIso e.hom)
  rw [← hα]
  exact SSet.stdSimplex_map_mem_realizationWeakEquivalences (SSet.stdSimplex.map α)

/-- The actual original union of both outer faces is weak, with EVERY original
vertex and simplex retained and the nonempty intersection ensured by dimension. -/
theorem outerFaces_union_weak (n : ℕ) :
    realizationWeakEquivalences
      (face.{u} {(0 : Fin (n + 3))}ᶜ ⊔ face {Fin.last (n + 2)}ᶜ).ι := by
  apply Subcomplex.realizationWeakEquivalences_union
  · apply face_inclusion_weak
    exact ⟨(1 : Fin (n + 3)), by simp⟩
  · apply face_inclusion_weak
    exact ⟨(0 : Fin (n + 3)), by simp⟩
  · rw [face_inter_face]
    apply face_inclusion_weak
    refine ⟨(1 : Fin (n + 3)), ?_⟩
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_compl.mpr (by simp)
    · apply Finset.mem_compl.mpr
      simp only [Finset.mem_singleton]
      intro h
      have he := congrArg Fin.val h
      change 1 = n + 2 at he
      omega

/-- The SAME original outer-face union inclusion is weak at EVERY dimension at least two. -/
theorem outerFaces_union_weak_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    realizationWeakEquivalences (face.{u} {(0 : Fin (n + 1))}ᶜ ⊔ face {Fin.last n}ᶜ).ι := by
  have he : ∃ k, n = k + 2 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨k, by omega⟩
  obtain ⟨k, rfl⟩ := he
  exact outerFaces_union_weak.{u} k

end SSet.stdSimplex
