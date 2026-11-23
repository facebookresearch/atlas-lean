/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialComplex.SimplicialApproximation

/-!
# Actual relative approximation consumers

A finite edge with infinitely many unused ambient labels admits an actual
approximation relative to both prescribed endpoints. Target endpoint labels
may coincide. The geometrically empty source also maps to an empty target
without an inhabited target vertex type.
-/

open PreAbstractSimplicialComplex

noncomputable section

namespace ActualSimplicialApproximationConsumer

abbrev finiteEdge : PreAbstractSimplicialComplex ℕ := restrictVertices ⊤ {0, 1}

def endZero : Vertex finiteEdge := ⟨0, by
  change ({0} : Finset ℕ).Nonempty ∧ ({0} : Finset ℕ) ⊆ {0, 1}
  simp⟩

def endOne : Vertex finiteEdge := ⟨1, by
  change ({1} : Finset ℕ).Nonempty ∧ ({1} : Finset ℕ) ⊆ {0, 1}
  simp⟩

def pointZero : Realization finiteEdge := Realization.vertex _ endZero.val endZero.property

def pointOne : Realization finiteEdge := Realization.vertex _ endOne.val endOne.property

/-- Both endpoint restrictions survive the actual finite subdivision and
give an ordinary homotopy relative to the original two-point subset. -/
theorem endpointRelativeApproximation {W : Type*} (Q : PreAbstractSimplicialComplex W)
    (f : C(Realization finiteEdge, Realization Q)) (w₀ w₁ : Vertex Q)
    (h₀ : f pointZero = Realization.vertex Q w₀.val w₀.property)
    (h₁ : f pointOne = Realization.vertex Q w₁.val w₁.property) :
    ∃ n : ℕ, ∃ g : Morphism (subdivisionIter finiteEdge n) Q,
      Nonempty (ContinuousMap.HomotopyRel f
        (g.realization.comp (subdivisionRealizationInverse finiteEdge n)) {pointZero, pointOne}) ∧
        g.vertexMap (persistentVertex finiteEdge n endZero) = w₀ ∧
          g.vertexMap (persistentVertex finiteEdge n endOne) = w₁ := by
  obtain ⟨n, g, H, _, _, hfixed⟩ := exists_simplicialApproximation finiteEdge Q f
  refine ⟨n, g, ⟨{ toHomotopy := H, prop' := ?_ }⟩,
    (hfixed endZero w₀ h₀).1, (hfixed endOne w₁ h₁).1⟩
  intro t x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact (hfixed endZero w₀ h₀).2 t
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact (hfixed endOne w₁ h₁).2 t

def infiniteTargetVertex : Vertex (⊤ : PreAbstractSimplicialComplex ℕ) :=
  ⟨0, Finset.singleton_nonempty 0⟩

/-- The full theorem allows the two original endpoints to fold to one
literal vertex of a genuinely infinite weak target. -/
example :
    ∃ n : ℕ, ∃ g : Morphism (subdivisionIter finiteEdge n)
      (⊤ : PreAbstractSimplicialComplex ℕ),
      Nonempty (ContinuousMap.HomotopyRel
        (ContinuousMap.const _ (Realization.vertex _ infiniteTargetVertex.val
          infiniteTargetVertex.property))
        (g.realization.comp (subdivisionRealizationInverse finiteEdge n)) {pointZero, pointOne}) ∧
        g.vertexMap (persistentVertex finiteEdge n endZero) = infiniteTargetVertex ∧
          g.vertexMap (persistentVertex finiteEdge n endOne) = infiniteTargetVertex := by
  obtain ⟨n, g, H, h₀, h₁⟩ := endpointRelativeApproximation _
    (ContinuousMap.const _ (Realization.vertex _ infiniteTargetVertex.val
      infiniteTargetVertex.property))
    infiniteTargetVertex infiniteTargetVertex rfl rfl
  exact ⟨n, g, H, h₀, h₁⟩

def emptyGhostComplex : PreAbstractSimplicialComplex ℕ := ⊥

instance : IsEmpty (Face emptyGhostComplex) := ⟨fun s => s.property⟩

def emptyMap : C(Realization emptyGhostComplex,
    Realization (⊥ : PreAbstractSimplicialComplex Empty)) where
  toFun x := False.elim x.support_mem
  continuous_toFun := by
    rw [Realization.continuous_iff]
    intro s
    exact s.property.elim

/-- A ghost ambient source needs neither a target vertex nor a default image. -/
example : ∃ n : ℕ, ∃ g : Morphism (subdivisionIter emptyGhostComplex n)
    (⊥ : PreAbstractSimplicialComplex Empty),
    Nonempty (ContinuousMap.Homotopy emptyMap
      (g.realization.comp (subdivisionRealizationInverse emptyGhostComplex n))) := by
  obtain ⟨n, g, H, _, _, _⟩ := exists_simplicialApproximation _ _ emptyMap
  exact ⟨n, g, ⟨H⟩⟩

end ActualSimplicialApproximationConsumer

end
