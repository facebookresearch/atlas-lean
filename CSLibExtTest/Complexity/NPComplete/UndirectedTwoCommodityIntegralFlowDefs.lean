/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlowDefs

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted
open MetaMathlibExt.BitstringEncoding

private theorem sum_two {M : Type} [AddCommMonoid M] (g : Fin 2 → M) :
    ∑ i, g i = g 0 + (g 1 + 0) := rfl

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

/-- The flow that sends `x` along `u → v` for each listed `(u, v, x)`, and `0` elsewhere. -/
private def flowOf (l : List (ℕ × ℕ × ℕ)) {n : ℕ} (u v : Fin n) : ℕ :=
  ((l.find? fun e => e.1 = u.val ∧ e.2.1 = v.val).map fun e => e.2.2).getD 0

/-- One edge `{0, 1}` of capacity `c`, and two commodities from `0` to `1` with requirement
`1` each. -/
private abbrev edge (c : ℕ) : UndirectedTwoCommodityIntegralFlowInstance :=
  (2, [(0, 1, c)], (0, 1, 1), (0, 1, 1))

private theorem edge_two_wellFormed : WellFormed (edge 2) := by
  unfold WellFormed endpoints; decide

private theorem edge_one_wellFormed : WellFormed (edge 1) := by
  unfold WellFormed endpoints; decide

private theorem unit_value :
    1 + ∑ w : Fin 2, flowOf [(0, 1, 1)] 1 w ≤ ∑ u : Fin 2, flowOf [(0, 1, 1)] u 1 := by decide

/-- One unit along `0 → 1` is a flow for either commodity of `edge c` when `1 ≤ c`. -/
private theorem unit_commodityFlow (c : ℕ) (hc : 1 ≤ c) :
    CommodityFlow (edge c) (0, 1, 1) (flowOf [(0, 1, 1)]) := by
  have hcap : ∀ u v : Fin 2, flowOf [(0, 1, 1)] u v ≤ capacity (edge c) u v := by
    intro u v
    fin_cases u <;> fin_cases v <;> simp [flowOf, capacity, hc]
  refine ⟨show 0 < 2 by decide, show 1 < 2 by decide, feasible_of_nat _ _ _ _ hcap ?_, ?_⟩
  · intro v h0 h1
    fin_cases v
    · exact absurd rfl h0
    · exact absurd rfl h1
  · exact value_of_nat _ 1 1 unit_value

/-- With capacity `2` both commodities fit, one unit each. -/
private theorem edge_two_feasible : UndirectedTwoCommodityIntegralFlowFeasible (edge 2) := by
  refine ⟨flowOf [(0, 1, 1)], flowOf [(0, 1, 1)], ?_, unit_commodityFlow 2 (by decide),
    unit_commodityFlow 2 (by decide)⟩
  have h : ∀ u v : Fin 2, flowOf [(0, 1, 1)] u v + flowOf [(0, 1, 1)] v u +
      flowOf [(0, 1, 1)] u v + flowOf [(0, 1, 1)] v u ≤ capacity (edge 2) u v := by decide
  exact fun u v _ => h u v

/-- Any flow of `edge c` meeting requirement `1` into `1` sends at least one unit along
`0 → 1`. -/
private theorem commodity_uses_edge (c : ℕ) (f : Fin 2 → Fin 2 → ℕ)
    (h : CommodityFlow (edge c) (0, 1, 1) f) : 1 ≤ f 0 1 := by
  obtain ⟨_, _, -, hR⟩ := h
  have hR' : ((1 : ℕ) : ℝ) ≤ (∑ u : Fin 2, (f u 1 : ℝ)) - ∑ w : Fin 2, (f 1 w : ℝ) := hR
  rw [sum_two, sum_two] at hR'
  have hR'' : ((1 + f 1 0 + f 1 1 : ℕ) : ℝ) ≤ ((f 0 1 + f 1 1 : ℕ) : ℝ) := by
    push_cast
    have := le_sub_iff_add_le.mp hR'
    simpa [add_assoc, add_comm, add_left_comm] using this
  have := (Nat.cast_le (α := ℝ)).mp hR''
  omega

/-- With capacity `1` the two commodities do not fit: each needs a unit along `0 → 1`, and
the edge carries at most one unit in total. Only the capacity differs from `edge 2`. -/
private theorem edge_one_infeasible : ¬ UndirectedTwoCommodityIntegralFlowFeasible (edge 1) := by
  rintro ⟨f₁, f₂, hcap, h₁, h₂⟩
  have a := commodity_uses_edge 1 f₁ h₁
  have b := commodity_uses_edge 1 f₂ h₂
  have k : capacity (edge 1) ((0 : Fin 2) : ℕ) ((1 : Fin 2) : ℕ) = 1 := by decide
  have hc := hcap 0 1 (by simp [Graph, endpoints, Cslib.Complexity.Karp.edgeGraph])
  rw [k] at hc
  omega

/-- Each commodity alone fits in `edge 1`: the joint capacity constraint is what fails. -/
example : CommodityFlow (edge 1) (0, 1, 1) (flowOf [(0, 1, 1)]) :=
  unit_commodityFlow 1 le_rfl

/-- A commodity whose sink `5` is not a vertex is malformed, and has no flow either. -/
example : ¬ WellFormed ((2, [(0, 1, 2)], (0, 1, 1), (0, 5, 1)) :
    UndirectedTwoCommodityIntegralFlowInstance) := by
  unfold WellFormed endpoints; decide

/-- The decision problem accepts the encoding of `edge 2`. -/
example : undirectedTwoCommodityIntegralFlowDec (bitEncode (edge 2)) = true := by
  simp [undirectedTwoCommodityIntegralFlowDec, edge_two_wellFormed, edge_two_feasible]

/-- It rejects the encoding of the well-formed but infeasible `edge 1`. -/
example : undirectedTwoCommodityIntegralFlowDec (bitEncode (edge 1)) = false := by
  simp [undirectedTwoCommodityIntegralFlowDec, edge_one_infeasible]

/-- `edge 1` is well formed, so `edge_one_infeasible` is what rejects it. -/
example : WellFormed (edge 1) := edge_one_wellFormed

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : undirectedTwoCommodityIntegralFlowDec [true] = false := by
  have h : bitDecode (α := UndirectedTwoCommodityIntegralFlowInstance) [true] = none := rfl
  simp [undirectedTwoCommodityIntegralFlowDec, h]

end MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow
