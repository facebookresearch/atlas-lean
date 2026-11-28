/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumQuadraticCostFlowDefs
import Mathlib.Algebra.BigOperators.Fin

namespace MetaMathlibExt.Complexity.NPComplete.MinimumQuadraticCostFlow

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted (IsFeasibleFlow)

private theorem dec_bitEncode (i : MinimumQuadraticCostFlowInstance) :
    minimumQuadraticCostFlowDec (bitEncode i) = true ↔
      WellFormed i ∧ MinimumQuadraticCostFlowFeasible i := by
  simp [minimumQuadraticCostFlowDec, bitDecode_bitEncode]

/-- One arc `0 → 1` of capacity `2` and cost `1 · f² + 0 · f`, from `s = 0` to `t = 1`, with
requirement `R = 2` and bound `B = 4`: two units on the arc cost `4`. -/
example :
    minimumQuadraticCostFlowDec
      (bitEncode ((2, [(0, 1, 2, (1, 0), (0, 0))], 0, 1, 2, 4) :
        MinimumQuadraticCostFlowInstance)) = true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed arcs; decide, by decide, by decide,
    fun u v => if (u : ℕ) = 0 ∧ (v : ℕ) = 1 then 2 else 0, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u v
    exact Nat.cast_nonneg _
  · intro u v
    revert u v
    simp [Fin.forall_fin_two, arcData]
  · intro v hs ht
    rcases Fin.exists_fin_two.1 ⟨v, rfl⟩ with h | h <;> simp_all [Fin.ext_iff]
  · simp
  · simp [Fin.sum_univ_two, arcData, intOf]

/-- The same network with `B = 3`: meeting `R = 2` forces two units on the arc, of quadratic
cost `4 > 3` (a linear cost `1 · f` would be `2`). -/
example :
    minimumQuadraticCostFlowDec
      (bitEncode ((2, [(0, 1, 2, (1, 0), (0, 0))], 0, 1, 2, 3) :
        MinimumQuadraticCostFlowInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, hs, ht, f, ⟨-, hcap, -⟩, hreq, hcost⟩
  have h10 := hcap 1 0
  simp [arcData] at h10
  simp [Fin.sum_univ_two, h10] at hreq
  simp [Fin.sum_univ_two, arcData, intOf] at hcost
  have h2 : (2 : ℤ) ≤ f 0 1 := by exact_mod_cast hreq
  have h4 : (4 : ℤ) ≤ (f 0 1 : ℤ) ^ 2 := by
    simpa using pow_le_pow_left₀ (by norm_num) h2 2
  omega

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MinimumQuadraticCostFlowInstance) bits = none) :
    minimumQuadraticCostFlowDec bits = false := by
  simp [minimumQuadraticCostFlowDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumQuadraticCostFlowDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.MinimumQuadraticCostFlow
