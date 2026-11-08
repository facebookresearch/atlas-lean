/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Basic

import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Execution
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Simplify
import all CSLibExt.Algorithms.Lean.Graph.ShortestPath.FloydWarshall.Internal.Stage

/-!
# Floyd-Warshall correctness

Stage-optimality, all-pairs shortest-distance correctness, reachability, and sound negative-cycle
detection for the executable recurrence.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.FloydWarshall

open Internal

/-- Under the no-negative-cycle hypothesis, the final cell is the minimum over all paths. -/
theorem floydWarshall_distance_spec {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n)
    (hNoCycle : NoNegativeCycle weight) :
    IsStageShortestPathWeight weight n source target
      ((floydWarshall weight).ret source target) := by
  rw [floydWarshall_ret]
  exact stageValue_spec weight hNoCycle n (by omega) source target

/-- Every finite output distance is realized by a concrete weighted path. -/
theorem floydWarshall_distance_realized {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n) (distance : Int)
    (hDistance : (floydWarshall weight).ret source target = (distance : WithTop Int)) :
    ∃ path, IsWeightedPath weight source target path ∧
      pathWeight weight path = (distance : WithTop Int) := by
  rw [floydWarshall_ret] at hDistance
  obtain ⟨path, hpath, _, hweight⟩ :=
    stageValue_realized weight n (by omega) source target distance hDistance
  exact ⟨path, hpath, hweight⟩

/-- Under the no-negative-cycle hypothesis, no concrete path is cheaper than the output. -/
theorem floydWarshall_distance_minimal {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n)
    (path : List (Fin n)) (hNoCycle : NoNegativeCycle weight)
    (hPath : IsWeightedPath weight source target path) :
    (floydWarshall weight).ret source target ≤ pathWeight weight path := by
  rw [floydWarshall_ret]
  apply stageValue_le_of_noNegativeCycle weight hNoCycle n (by omega) hPath
  intro vertex _
  exact vertex.isLt

/-- An output cell is infinite exactly when no weighted path connects its endpoints. -/
theorem floydWarshall_distance_eq_top_iff {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (source target : Fin n) :
    (floydWarshall weight).ret source target = ⊤ ↔
      ¬∃ path, IsWeightedPath weight source target path := by
  constructor
  · intro htop
    rintro ⟨path, hpath⟩
    obtain ⟨simple, hsimple, hnodup⟩ := hpath.exists_nodup
    have hbound : InternalVerticesBelow n simple := by
      intro vertex _
      exact vertex.isLt
    have hle := stageValue_le_nodup weight n (by omega) hsimple hnodup hbound
    rw [floydWarshall_ret] at htop
    rw [htop] at hle
    exact pathWeight_ne_top weight hsimple (top_unique hle)
  · intro hnoPath
    by_contra hnotTop
    obtain ⟨distance, hdistance⟩ := WithTop.ne_top_iff_exists.mp hnotTop
    obtain ⟨path, hpath, _⟩ := floydWarshall_distance_realized weight source target distance
      hdistance.symm
    exact hnoPath ⟨path, hpath⟩

/-- A negative diagonal entry in the computed matrix implies a simple negative cycle. -/
theorem floydWarshall_hasNegativeDiagonal_sound {n : Nat}
    (weight : Fin n → Fin n → WithTop Int)
    (hNegative : hasNegativeDiagonal (floydWarshall weight).ret = true) :
    HasNegativeCycle weight := by
  obtain ⟨vertex, hdiagonal⟩ :=
    (hasNegativeDiagonal_eq_true_iff (floydWarshall weight).ret).mp hNegative
  have hnotTop : (floydWarshall weight).ret vertex vertex ≠ ⊤ := ne_top_of_lt hdiagonal
  obtain ⟨distance, hdistance⟩ := WithTop.ne_top_iff_exists.mp hnotTop
  obtain ⟨path, hpath, hpathWeight⟩ :=
    floydWarshall_distance_realized weight vertex vertex distance hdistance.symm
  have hpathNegative : pathWeight weight path < 0 := by
    rw [hpathWeight, hdistance]
    exact hdiagonal
  rcases negativeCycle_or_simplifies weight hpath with hcycle | ⟨simple, hsimple,
      hnodup, hweight, _⟩
  · exact hcycle
  · have hsimpleNegative : pathWeight weight simple < 0 := hweight.trans_lt hpathNegative
    have hclosed : simple.head hsimple.ne_nil = simple.getLast hsimple.ne_nil := by
      rw [hsimple.head_eq, hsimple.getLast_eq]
    obtain ⟨point, hpoint⟩ :=
      (List.Nodup.head_eq_getLast_iff hsimple.ne_nil hnodup).mp hclosed
    subst simple
    simp [pathWeight] at hsimpleNegative

/-- No negative cycle implies that the diagonal detector is false. -/
theorem floydWarshall_hasNegativeDiagonal_eq_false {n : Nat}
    (weight : Fin n → Fin n → WithTop Int) (hNoCycle : NoNegativeCycle weight) :
    hasNegativeDiagonal (floydWarshall weight).ret = false := by
  cases hflag : hasNegativeDiagonal (floydWarshall weight).ret with
  | false => rfl
  | true => exact False.elim (hNoCycle (floydWarshall_hasNegativeDiagonal_sound weight hflag))

end Cslib.Algorithms.Lean.FloydWarshall
