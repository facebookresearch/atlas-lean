/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.EdmondsKarp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Importing and kernel-checked tests for Edmonds-Karp. -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.EdmondsKarpTests

open EdmondsKarp

private theorem value_eq_sourceCapacity {n : Nat}
    (capacity : Fin n → Fin n → Nat) (source sink : Fin n)
    (source_ne_sink : source ≠ sink) (candidate : Flow n)
    (candidate_feasible : IsFeasible capacity source sink candidate)
    (candidate_value :
      flowValue source candidate = (sourceCapacity capacity source : Int)) :
    flowValue source (edmondsKarp capacity source sink) =
      (sourceCapacity capacity source : Int) := by
  have lower := edmondsKarp_maximal capacity source_ne_sink candidate candidate_feasible
  have upper := flowValue_le_sourceCapacity
    (edmondsKarp_feasible capacity source sink)
  omega

private def zeroCapacity : Fin 2 → Fin 2 → Nat := fun _ _ => 0

example : flowValue 0 (edmondsKarp zeroCapacity 0 1) = 0 := by
  have result := value_eq_sourceCapacity zeroCapacity 0 1 (by decide)
    (zeroFlow 2) (zeroFlow_feasible zeroCapacity 0 1) (by decide)
  exact result

private def onePathCapacity : Fin 3 → Fin 3 → Nat
  | 0, 1 => 3
  | 1, 2 => 3
  | _, _ => 0

private def onePathFlow : Flow 3
  | 0, 1 => 3
  | 1, 0 => -3
  | 1, 2 => 3
  | 2, 1 => -3
  | _, _ => 0

private theorem onePathFlow_feasible :
    IsFeasible onePathCapacity 0 2 onePathFlow := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · intro v vertex_ne_source vertex_ne_sink
    fin_cases v
    · exact False.elim (vertex_ne_source rfl)
    · decide
    · exact False.elim (vertex_ne_sink rfl)

example : pathBottleneck onePathCapacity (zeroFlow 3) [0, 1, 2] = 3 := by
  norm_num [pathBottleneck, residualAmount, onePathCapacity, zeroFlow]

example : flowValue 0 (edmondsKarp onePathCapacity 0 2) = 3 := by
  have result := value_eq_sourceCapacity onePathCapacity 0 2 (by decide)
    onePathFlow onePathFlow_feasible (by decide)
  have sourceCapacity_eq : sourceCapacity onePathCapacity 0 = 3 := by
    decide
  simpa [sourceCapacity_eq] using result

private def highCapacityDeadEnd : Fin 3 → Fin 3 → Nat
  | 0, 1 => 1_000_000_000
  | _, _ => 0

private def highCapacitySameEndpoint : Fin 1 → Fin 1 → Nat
  | 0, 0 => 1_000_000_000

example : edmondsKarp highCapacitySameEndpoint 0 0 = zeroFlow 1 := by
  rfl

private theorem highCapacityDeadEnd_unreachable :
    ¬ (residualGraph highCapacityDeadEnd (zeroFlow 3)).Reachable 0 2 := by
  intro reachable
  have endpoint_ne_sink : ∀ {vertex : Fin 3},
      (residualGraph highCapacityDeadEnd (zeroFlow 3)).Reachable 0 vertex →
        vertex ≠ 2 := by
    intro vertex path
    induction path with
    | refl => decide
    | @tail middle target path edge induction =>
        rw [residualGraph_edge_iff] at edge
        fin_cases middle <;> fin_cases target <;>
          norm_num [highCapacityDeadEnd, zeroFlow] at edge
        decide
  exact endpoint_ne_sink reachable rfl

example : run highCapacityDeadEnd 0 2 1_000_000_001 (zeroFlow 3) = zeroFlow 3 := by
  apply run_eq_of_no_path
  rw [shortestPath_eq_none_iff_not_reachable]
  exact highCapacityDeadEnd_unreachable

private def sparseLongPath : Fin 10 → Fin 10 → Nat
  | 9, 8 | 8, 7 | 7, 6 | 6, 5 | 5, 4 | 4, 3 | 3, 2 | 2, 1 | 1, 0 => 1
  | _, _ => 0

private def sparseDistance : Fin 10 → Option Nat
  | 0 => some 0
  | 1 => some 1
  | 2 => some 2
  | 3 => some 3
  | 4 => some 4
  | 5 => some 5
  | 6 => some 6
  | 7 => some 7
  | 8 => some 8
  | 9 => some 9

example :
    pathFromDistances (residualGraph sparseLongPath (zeroFlow 10))
      sparseDistance 0 9 9 = some [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] := by
  decide

/-- Four-vertex network used by the importing maximum-flow tests. -/
def branchingCapacity : Fin 4 → Fin 4 → Nat
  | 0, 1 => 3
  | 0, 2 => 2
  | 1, 2 => 1
  | 1, 3 => 2
  | 2, 3 => 3
  | _, _ => 0

private def branchingFlow : Flow 4
  | 0, 1 => 3
  | 1, 0 => -3
  | 0, 2 => 2
  | 2, 0 => -2
  | 1, 2 => 1
  | 2, 1 => -1
  | 1, 3 => 2
  | 3, 1 => -2
  | 2, 3 => 3
  | 3, 2 => -3
  | _, _ => 0

private theorem branchingFlow_feasible :
    IsFeasible branchingCapacity 0 3 branchingFlow := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · intro v vertex_ne_source vertex_ne_sink
    fin_cases v
    · exact False.elim (vertex_ne_source rfl)
    · decide
    · decide
    · exact False.elim (vertex_ne_sink rfl)

example : flowValue 0 (edmondsKarp branchingCapacity 0 3) = 5 := by
  have result := value_eq_sourceCapacity branchingCapacity 0 3 (by decide)
    branchingFlow branchingFlow_feasible (by decide)
  have sourceCapacity_eq : sourceCapacity branchingCapacity 0 = 5 := by
    decide
  simpa [sourceCapacity_eq] using result

private def aggregatedParallelCapacity : Fin 2 → Fin 2 → Nat
  | 0, 1 => 2 + 3
  | _, _ => 0

private def aggregatedParallelFlow : Flow 2
  | 0, 1 => 5
  | 1, 0 => -5
  | _, _ => 0

private theorem aggregatedParallelFlow_feasible :
    IsFeasible aggregatedParallelCapacity 0 1 aggregatedParallelFlow := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · intro u v
    fin_cases u <;> fin_cases v <;> decide
  · intro v vertex_ne_source vertex_ne_sink
    fin_cases v
    · exact False.elim (vertex_ne_source rfl)
    · exact False.elim (vertex_ne_sink rfl)

example : flowValue 0 (edmondsKarp aggregatedParallelCapacity 0 1) = 5 := by
  have result := value_eq_sourceCapacity aggregatedParallelCapacity 0 1 (by decide)
    aggregatedParallelFlow aggregatedParallelFlow_feasible
      (by decide)
  have sourceCapacity_eq : sourceCapacity aggregatedParallelCapacity 0 = 5 := by
    decide
  simpa [sourceCapacity_eq] using result

private def cancellationCapacity : Fin 6 → Fin 6 → Nat
  | 0, 1 | 0, 2 | 1, 3 | 1, 4 | 2, 3 | 3, 5 | 4, 5 => 1
  | _, _ => 0

private def cancellationFirst : Flow 6 :=
  augment (zeroFlow 6) [0, 1, 3, 5] 1

private def cancellationFinal : Flow 6 :=
  augment cancellationFirst [0, 2, 3, 1, 4, 5] 1

private theorem cancellationFirstPath :
    IsPath (residualGraph cancellationCapacity (zeroFlow 6)) 0 5
      [0, 1, 3, 5] := by
  have edge01 : (residualGraph cancellationCapacity (zeroFlow 6)).Edge 0 1 := by
    rw [residualGraph_edge_iff]
    decide
  have edge13 : (residualGraph cancellationCapacity (zeroFlow 6)).Edge 1 3 := by
    rw [residualGraph_edge_iff]
    decide
  have edge35 : (residualGraph cancellationCapacity (zeroFlow 6)).Edge 3 5 := by
    rw [residualGraph_edge_iff]
    decide
  have tail : [5].IsChainFromTo
      (residualGraph cancellationCapacity (zeroFlow 6)).Edge 5 5 :=
    List.isChainFromTo_singleton
  exact ⟨((tail.cons edge35).cons edge13).cons edge01, by decide⟩

example : (residualGraph cancellationCapacity cancellationFirst).Edge 3 1 := by
  rw [residualGraph_edge_iff]
  decide

private theorem cancellationReroutingPath :
    IsPath (residualGraph cancellationCapacity cancellationFirst) 0 5
      [0, 2, 3, 1, 4, 5] := by
  have edge02 : (residualGraph cancellationCapacity cancellationFirst).Edge 0 2 := by
    rw [residualGraph_edge_iff]
    decide
  have edge23 : (residualGraph cancellationCapacity cancellationFirst).Edge 2 3 := by
    rw [residualGraph_edge_iff]
    decide
  have edge31 : (residualGraph cancellationCapacity cancellationFirst).Edge 3 1 := by
    rw [residualGraph_edge_iff]
    decide
  have edge14 : (residualGraph cancellationCapacity cancellationFirst).Edge 1 4 := by
    rw [residualGraph_edge_iff]
    decide
  have edge45 : (residualGraph cancellationCapacity cancellationFirst).Edge 4 5 := by
    rw [residualGraph_edge_iff]
    decide
  have tail : [5].IsChainFromTo
      (residualGraph cancellationCapacity cancellationFirst).Edge 5 5 :=
    List.isChainFromTo_singleton
  exact ⟨(((((tail.cons edge45).cons edge14).cons edge31).cons edge23).cons edge02),
    by decide⟩

example : cancellationFinal 1 3 = 0 := by
  decide

example : flowValue 0 cancellationFinal = 2 := by
  decide

private theorem cancellationFinal_feasible :
    IsFeasible cancellationCapacity 0 5 cancellationFinal := by
  have firstFeasible := augment_pathBottleneck_feasible cancellationCapacity 0 5
    (zeroFlow 6) (zeroFlow_feasible cancellationCapacity 0 5)
    [0, 1, 3, 5] cancellationFirstPath
  have firstBottleneck :
      pathBottleneck cancellationCapacity (zeroFlow 6) [0, 1, 3, 5] = 1 := by
    norm_num [pathBottleneck, residualAmount, cancellationCapacity, zeroFlow]
  rw [firstBottleneck] at firstFeasible
  change IsFeasible cancellationCapacity 0 5 cancellationFirst at firstFeasible
  have finalFeasible := augment_pathBottleneck_feasible cancellationCapacity 0 5
    cancellationFirst firstFeasible [0, 2, 3, 1, 4, 5] cancellationReroutingPath
  have finalBottleneck :
      pathBottleneck cancellationCapacity cancellationFirst [0, 2, 3, 1, 4, 5] = 1 := by
    norm_num [pathBottleneck, residualAmount, cancellationFirst, augment,
      cancellationCapacity, zeroFlow, edgeDelta, localDelta]
  rw [finalBottleneck] at finalFeasible
  exact finalFeasible

private theorem cancellationResult_value :
    flowValue 0 (edmondsKarp cancellationCapacity 0 5) = 2 := by
  have result := value_eq_sourceCapacity cancellationCapacity 0 5 (by decide)
    cancellationFinal cancellationFinal_feasible (by decide)
  have sourceCapacity_eq : sourceCapacity cancellationCapacity 0 = 2 := by
    decide
  simpa [sourceCapacity_eq] using result

example : flowValue 0 (edmondsKarp cancellationCapacity 0 5) = 2 :=
  cancellationResult_value

example : (edmondsKarp cancellationCapacity 0 5) 1 3 = 0 := by
  let flow := edmondsKarp cancellationCapacity 0 5
  change flow 1 3 = 0
  have feasible : IsFeasible cancellationCapacity 0 5 flow := by
    exact edmondsKarp_feasible cancellationCapacity 0 5
  have value : flowValue 0 flow = 2 := by
    exact cancellationResult_value
  have conservation2 := feasible.2.2 (2 : Fin 6) (by decide) (by decide)
  have conservation3 := feasible.2.2 (3 : Fin 6) (by decide) (by decide)
  have bound00 := feasible.capacity_bounds (0 : Fin 6) (0 : Fin 6)
  have bound01 := feasible.capacity_bounds (0 : Fin 6) (1 : Fin 6)
  have bound02 := feasible.capacity_bounds (0 : Fin 6) (2 : Fin 6)
  have bound03 := feasible.capacity_bounds (0 : Fin 6) (3 : Fin 6)
  have bound04 := feasible.capacity_bounds (0 : Fin 6) (4 : Fin 6)
  have bound05 := feasible.capacity_bounds (0 : Fin 6) (5 : Fin 6)
  have bound20 := feasible.capacity_bounds (2 : Fin 6) (0 : Fin 6)
  have bound21 := feasible.capacity_bounds (2 : Fin 6) (1 : Fin 6)
  have bound22 := feasible.capacity_bounds (2 : Fin 6) (2 : Fin 6)
  have bound23 := feasible.capacity_bounds (2 : Fin 6) (3 : Fin 6)
  have bound24 := feasible.capacity_bounds (2 : Fin 6) (4 : Fin 6)
  have bound25 := feasible.capacity_bounds (2 : Fin 6) (5 : Fin 6)
  have bound30 := feasible.capacity_bounds (3 : Fin 6) (0 : Fin 6)
  have bound31 := feasible.capacity_bounds (3 : Fin 6) (1 : Fin 6)
  have bound32 := feasible.capacity_bounds (3 : Fin 6) (2 : Fin 6)
  have bound33 := feasible.capacity_bounds (3 : Fin 6) (3 : Fin 6)
  have bound34 := feasible.capacity_bounds (3 : Fin 6) (4 : Fin 6)
  have bound35 := feasible.capacity_bounds (3 : Fin 6) (5 : Fin 6)
  have skew02 := feasible.1 (0 : Fin 6) (2 : Fin 6)
  have skew13 := feasible.1 (1 : Fin 6) (3 : Fin 6)
  have skew23 := feasible.1 (2 : Fin 6) (3 : Fin 6)
  simp only [flowValue, Fin.sum_univ_six] at value conservation2 conservation3
  norm_num [cancellationCapacity] at bound00 bound01 bound02 bound03 bound04 bound05
  norm_num [cancellationCapacity] at bound20 bound21 bound22 bound23 bound24 bound25
  norm_num [cancellationCapacity] at bound30 bound31 bound32 bound33 bound34 bound35
  omega

example : IsFeasible branchingCapacity 0 3 (edmondsKarp branchingCapacity 0 3) :=
  edmondsKarp_feasible branchingCapacity 0 3

example (candidate : Flow 4) (feasible : IsFeasible branchingCapacity 0 3 candidate) :
    flowValue 0 candidate ≤ flowValue 0 (edmondsKarp branchingCapacity 0 3) :=
  edmondsKarp_maximal branchingCapacity (by decide) candidate feasible

end Cslib.Algorithms.Lean.EdmondsKarpTests
