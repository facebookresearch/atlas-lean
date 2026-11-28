/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsDefs

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted
open MetaMathlibExt.BitstringEncoding

/-- A natural-number flow that respects the capacities and is conserved away from `s` and `t`
is a feasible real flow. -/
private theorem feasible_of_nat {n : ℕ} (cap f : Fin n → Fin n → ℕ) (s t : Fin n)
    (hcap : ∀ u v, f u v ≤ cap u v)
    (hcons : ∀ v, v ≠ s → v ≠ t → ∑ u, f u v = ∑ w, f v w) :
    IsFeasibleFlow (fun u v => (cap u v : ℝ)) s t (fun u v => (f u v : ℝ)) :=
  ⟨fun _ _ => Nat.cast_nonneg _, fun u v => by dsimp only; exact_mod_cast hcap u v,
    fun v hs ht => by dsimp only; exact_mod_cast hcons v hs ht⟩

/-- The net flow into `t`, computed in `ℕ`. -/
private theorem value_of_nat {n : ℕ} (f : Fin n → Fin n → ℕ) (t : Fin n) (R : ℕ)
    (h : R + ∑ w, f t w ≤ ∑ u, f u t) :
    (R : ℝ) ≤ (∑ u, (f u t : ℝ)) - ∑ w, (f t w : ℝ) := by
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at h'
  exact le_sub_iff_add_le.mpr h'

private theorem sum_three {M : Type} [AddCommMonoid M] (g : Fin 3 → M) :
    ∑ i, g i = g 0 + (g 1 + (g 2 + 0)) := rfl

/-- The flow that sends `x` along `u → v` for each listed `(u, v, x)`, and `0` elsewhere. -/
private def flowOf (l : List (ℕ × ℕ × ℕ)) {n : ℕ} (u v : Fin n) : ℕ :=
  ((l.find? fun e => e.1 = u.val ∧ e.2.1 = v.val).map fun e => e.2.2).getD 0

/-- The path `0 - 1 - 2`, each edge with lower bound `1` and capacity `2`, from `0` to `2`
with requirement `2`. -/
private abbrev path : UndirectedFlowWithLowerBoundsInstance :=
  (3, [(0, 1, 1, 2), (1, 2, 1, 2)], 0, 2, 2)

/-- Two units along `0 → 1 → 2`. -/
private def pathFlow : Fin 3 → Fin 3 → ℕ := flowOf [(0, 1, 2), (1, 2, 2)]

private theorem path_wellFormed : WellFormed path := by unfold WellFormed endpoints; decide

/-- `path` is feasible: two units along `0 → 1 → 2` meet both lower bounds and are conserved
at `1`. -/
private theorem path_feasible : UndirectedFlowWithLowerBoundsFeasible path := by
  refine ⟨by decide, by decide, pathFlow, feasible_of_nat _ _ _ _ ?_ ?_, ?_, ?_⟩
  · decide
  · decide
  · have h : ∀ u v : Fin 3, (pathFlow u v = 0 ∨ pathFlow v u = 0) ∧
        lowerBound path u v ≤ max (pathFlow u v) (pathFlow v u) := by decide
    exact fun u v _ => h u v
  · exact value_of_nat pathFlow 2 2 (by decide)

/-- From `0` to `1` with requirement `1`, through the edge `{0, 1}` (lower bound `0`, capacity
`1`), plus a dead end `{0, 2}` with lower bound `l` and capacity `1`. -/
private abbrev deadEnd (l : ℕ) : UndirectedFlowWithLowerBoundsInstance :=
  (3, [(0, 1, 0, 1), (0, 2, l, 1)], 0, 1, 1)

private theorem deadEnd_zero_wellFormed : WellFormed (deadEnd 0) := by
  unfold WellFormed endpoints; decide

/-- `deadEnd 1` is well formed too: its lower bound does not exceed its capacity. -/
example : WellFormed (deadEnd 1) := by unfold WellFormed endpoints; decide

/-- Without the lower bound the dead end is harmless: one unit along `0 → 1`. -/
private theorem deadEnd_zero_feasible : UndirectedFlowWithLowerBoundsFeasible (deadEnd 0) := by
  refine ⟨by decide, by decide, flowOf [(0, 1, 1)],
    feasible_of_nat _ _ _ _ ?_ ?_, ?_, ?_⟩
  · decide
  · decide
  · have h : ∀ u v : Fin 3, (flowOf [(0, 1, 1)] u v = 0 ∨ flowOf [(0, 1, 1)] v u = 0) ∧
        lowerBound (deadEnd 0) u v ≤ max (flowOf [(0, 1, 1)] u v) (flowOf [(0, 1, 1)] v u) := by
      decide
    exact fun u v _ => h u v
  · exact value_of_nat _ 1 1 (by decide)

/-- With lower bound `1` on the dead end it is infeasible: flow into `2` must leave along the
same edge, by conservation, so using only one direction leaves `{0, 2}` empty. Only the lower
bound differs from the feasible `deadEnd 0`. -/
private theorem deadEnd_one_infeasible : ¬ UndirectedFlowWithLowerBoundsFeasible (deadEnd 1) := by
  rintro ⟨_, _, f, hfeas, hdir, -⟩
  obtain ⟨-, hcap, hcons⟩ := hfeas
  have hc : ∀ u v : Fin 3, f u v ≤ capacity (deadEnd 1) u v := fun u v => by
    have h := hcap u v
    dsimp only at h
    exact_mod_cast h
  have h12 := hc 1 2
  have h21 := hc 2 1
  have k12 : capacity (deadEnd 1) ((1 : Fin 3) : ℕ) ((2 : Fin 3) : ℕ) = 0 := by decide
  have k21 : capacity (deadEnd 1) ((2 : Fin 3) : ℕ) ((1 : Fin 3) : ℕ) = 0 := by decide
  have l02 : lowerBound (deadEnd 1) ((0 : Fin 3) : ℕ) ((2 : Fin 3) : ℕ) = 1 := by decide
  rw [k12] at h12
  rw [k21] at h21
  have hc2 : ∑ u : Fin 3, f u 2 = ∑ w : Fin 3, f 2 w := by
    have h := hcons 2 (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    dsimp only at h
    exact_mod_cast h
  have hd := hdir 0 2 (by simp [Graph, endpoints, Cslib.Complexity.Karp.edgeGraph])
  rw [l02] at hd
  rw [sum_three, sum_three] at hc2
  omega

/-- The sink `5` is not a vertex; every other field is that of `path`. -/
private abbrev badSink : UndirectedFlowWithLowerBoundsInstance :=
  (3, [(0, 1, 1, 2), (1, 2, 1, 2)], 0, 5, 2)

/-- A lower bound above the capacity is malformed. -/
example : ¬ WellFormed ((2, [(0, 1, 3, 2)], 0, 1, 1) : UndirectedFlowWithLowerBoundsInstance) := by
  unfold WellFormed endpoints; decide

/-- The decision problem accepts the encoding of `path`. -/
example : undirectedFlowWithLowerBoundsDec (bitEncode path) = true := by
  simp [undirectedFlowWithLowerBoundsDec, path_wellFormed, path_feasible]

/-- It accepts the encoding of `deadEnd 0`. -/
example : undirectedFlowWithLowerBoundsDec (bitEncode (deadEnd 0)) = true := by
  simp [undirectedFlowWithLowerBoundsDec, deadEnd_zero_wellFormed,
    deadEnd_zero_feasible]

/-- It rejects the encoding of the well-formed but infeasible `deadEnd 1`. -/
example : undirectedFlowWithLowerBoundsDec (bitEncode (deadEnd 1)) = false := by
  simp [undirectedFlowWithLowerBoundsDec, deadEnd_one_infeasible]

/-- It rejects `badSink`: the feasibility predicate itself requires the sink to be a
vertex. -/
example : undirectedFlowWithLowerBoundsDec (bitEncode badSink) = false := by
  have h : ¬ UndirectedFlowWithLowerBoundsFeasible badSink := fun ⟨_, ht, _⟩ =>
    absurd ht (by decide)
  simp [undirectedFlowWithLowerBoundsDec, h]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : undirectedFlowWithLowerBoundsDec [true] = false := by
  have h : bitDecode (α := UndirectedFlowWithLowerBoundsInstance) [true] = none := rfl
  simp [undirectedFlowWithLowerBoundsDec, h]

end MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds
