/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.HalfPlaneJoinedArms

/-!
# Tests for `Sheffield.HalfPlaneJoinedArms`

Module under test: `Sheffield.HalfPlaneJoinedArms` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* The hypotheses `IsFKG`, translation invariance and almost-sure uniqueness are discharged
  together by the Dirac mass on the all-open configuration of any connected infinite periodic
  graph (`isFKG_dirac`, `allOpen_translationInvariant`, `allOpen_unique`, proved here).
* `PeriodicPlaneEmbedding.`
  `exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt`
  applied to that measure with `r = R` and `ε = 1/2`.
* `PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent` is an event at explicit parameters, and
  `finiteJoinedBoundaryArmEvent_barrierReady` applies with arc bound `1`, `c = 0 < 1 = d`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace HalfPlaneJoinedArms

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

-- The joined arm event at explicit parameters.
example (E : PeriodicPlaneEmbedding P) (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  E.finiteJoinedBoundaryArmEvent 0 (-1) 1 2 L R

-- Barrier-ready geometry from joined arms, arc bound `1`, `c = 0 < 1 = d`.
example (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) (r : ℝ) (n : ℕ)
    (L R : Finset V)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ 1)
    (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + 1))
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r 0 1 n L R) :=
  E.finiteJoinedBoundaryArmEvent_barrierReady hB zero_lt_one hLdeep h

-- Inward separated joined arms for the all-open Dirac mass (`r = R`, `ε = 1/2`).
example [Infinite V] (E : PeriodicPlaneEmbedding P) (hconn : P.graph.Connected)
    (R s : ℝ) (t : ℤ) (L : Finset V) :=
  E.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
    (Measure.dirac allOpen)
    (isFKG_dirac _) (allOpen_translationInvariant P) (allOpen_unique P hconn)
    (le_refl R) s t L (by norm_num : (0 : ℝ) < 1 / 2)

end HalfPlaneJoinedArms
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
