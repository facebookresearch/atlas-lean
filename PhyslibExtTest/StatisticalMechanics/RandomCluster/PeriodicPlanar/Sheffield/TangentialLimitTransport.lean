/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.TangentialLimitTransport

/-!
# Tests for `Sheffield.TangentialLimitTransport`

Module under test: `Sheffield.TangentialLimitTransport` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* All four tangential transport lemmas applied to the Dirac mass on the all-open configuration
  (translation invariance proved here, `allOpen_translationInvariant`) with the zero translation
  `z = 0` and unchanged rectangles; the limit hypothesis stays an argument.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace TangentialLimitTransport

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

/-- The all-open bond configuration. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- Every Dirac mass on bond configurations is FKG. -/
theorem isFKG_dirac {V : Type*} (ω : ConfigSpace (Sym2 V)) : IsFKG (Measure.dirac ω) := by
  intro A B hA hB _ _
  rw [Measure.real, Measure.real, Measure.real, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

/-- The Dirac mass on the all-open configuration is translation invariant. -/
theorem allOpen_translationInvariant {V : Type*} [DecidableEq V] (P : PeriodicGraph V) :
    P.IsTranslationInvariant (Measure.dirac allOpen) := fun z =>
  ⟨P.measurable_configTranslate z, by
    rw [Measure.map_dirac' (P.measurable_configTranslate z)]
    rfl⟩

/-- On a connected infinite periodic graph, the all-open configuration has a unique infinite
cluster, so its Dirac mass gives the uniqueness event probability one. -/
theorem allOpen_unique {V : Type*} [DecidableEq V] [Infinite V] (P : PeriodicGraph V)
    (hconn : P.graph.Connected) :
    Measure.dirac allOpen {ω | P.HasUniqueInfiniteCluster ω} = 1 := by
  have hG : P.openSubgraph allOpen = P.graph := by
    ext x y
    simp [PeriodicGraph.openSubgraph, allOpen]
  have hcl : ∀ x, P.cluster allOpen x = Set.univ := fun x => by
    ext y
    simp only [PeriodicGraph.cluster, hG, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hconn.preconnected x y
  refine Measure.dirac_apply_of_mem ⟨⟨hconn.nonempty.some, ?_⟩, fun x y _ _ => ?_⟩
  · rw [hcl]
    exact Set.infinite_univ
  · rw [hG]
    exact hconn.preconnected x y

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- Left side, zero translation.
example (E : PeriodicPlaneEmbedding P) (a b c d : ℕ → ℝ)
    (S : ℕ → Set V) :=
  E.rectLeftConnection_tangential_tendsto_one (Measure.dirac allOpen)
    (allOpen_translationInvariant P) (fun _ => 0)
    (fun _ => rfl) a b c d b c d S (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)

-- Right side, zero translation.
example (E : PeriodicPlaneEmbedding P) (a b c d : ℕ → ℝ)
    (S : ℕ → Set V) :=
  E.rectRightConnection_tangential_tendsto_one (Measure.dirac allOpen)
    (allOpen_translationInvariant P) (fun _ => 0)
    (fun _ => rfl) a b c d a c d S (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)

-- Bottom side, zero translation.
example (E : PeriodicPlaneEmbedding P) (a b c d : ℕ → ℝ)
    (S : ℕ → Set V) :=
  E.rectBottomConnection_tangential_tendsto_one (Measure.dirac allOpen)
    (allOpen_translationInvariant P) (fun _ => 0)
    (fun _ => rfl) a b c d a b d S (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)

-- Top side, zero translation.
example (E : PeriodicPlaneEmbedding P) (a b c d : ℕ → ℝ)
    (S : ℕ → Set V) :=
  E.rectTopConnection_tangential_tendsto_one (Measure.dirac allOpen)
    (allOpen_translationInvariant P) (fun _ => 0)
    (fun _ => rfl) a b c d a b c S (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)

end TangentialLimitTransport
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
