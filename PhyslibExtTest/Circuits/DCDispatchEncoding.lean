/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.DCDispatchEncoding
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Two-bus fixture: one line from bus `0` to bus `1` with susceptance
`b = 10`, one generator at bus `0` with cost `3`, demand `d = (0, 1)`,
reference bus `0`, flow limits `-5 ≤ f ≤ 5`. With generator limits
`0 ≤ pg ≤ 2` the dispatch `pg = 1`, `θ = (0, -1/10)` is feasible and
encodes to a feasible LP point of objective `-3`. With `pmax = 1/2`
the balance forces `pg = 1`, so neither the dispatch problem nor the
canonical LP is feasible.
-/

@[expose] public section

namespace PhyslibExtTest.Circuits.DCDispatchEncoding

open Matrix
open PhyslibExt.Circuits.ArcPortSigns
open PhyslibExt.Circuits.LosslessDCFlowModel
open PhyslibExt.Circuits.DCDispatchEncoding

/-- The line leaves bus `0`. -/
def tl : Fin 1 → Fin 2 := fun _ => 0

/-- The line enters bus `1`. -/
def hd : Fin 1 → Fin 2 := fun _ => 1

/-- Line susceptance `10`. -/
noncomputable def bb : Fin 1 → ℝ := fun _ => 10

/-- The generator sits at bus `0`. -/
def gb : Fin 1 → Fin 2 := fun _ => 0

/-- Demand `1` at bus `1`. -/
noncomputable def dd : Fin 2 → ℝ := ![0, 1]

/-- Angles with bus `0` as the reference. -/
noncomputable def th : Fin 2 → ℝ := ![0, -1 / 10]

/-- Generation `1`. -/
noncomputable def pg0 : Fin 1 → ℝ := fun _ => 1

lemma lap : weightedLaplacian 2 1 tl hd bb = !![10, -10; -10, 10] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weightedLaplacian, electricalIncidence,
      MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix, Matrix.mul_apply,
      Matrix.diagonal, tl, hd, bb]

lemma flow : dcBranchFlow 2 1 tl hd bb th = fun _ => 1 := by
  funext e
  fin_cases e
  rw [dcBranchFlow_apply]
  norm_num [tl, hd, bb, th]

/-! ### Feasible case -/

/-- The dispatch `pg = 1`, `θ = (0, -1/10)` is feasible with
`0 ≤ pg ≤ 2`. -/
lemma feasible : IsDispatchFeasible 2 1 1 tl hd bb gb dd 0 (fun _ => 0) (fun _ => 2)
    (fun _ => -5) (fun _ => 5) pg0 th := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lap]
    funext v
    fin_cases v <;>
      simp [generatorIncidence, gb, pg0, th, dd, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two] <;>
      norm_num
  · simp [th]
  · intro g
    norm_num [pg0]
  · intro e
    rw [flow]
    norm_num

lemma cost_pg0 : dispatchCost 1 (fun _ => 3) pg0 = 3 := by
  simp [dispatchCost, dotProduct, pg0]

/-- The encoded dispatch is a feasible LP point that decodes back, with
LP objective `-3`, minus the dispatch cost. -/
example :
    (∀ i, 0 ≤ encode 2 1 pg0 th i) ∧
    (∀ j, (lpMatrix 2 1 1 tl hd bb gb 0 *ᵥ encode 2 1 pg0 th) j ≤
      lpRhs 2 1 1 dd (fun _ => 0) (fun _ => 2) (fun _ => -5) (fun _ => 5) j) ∧
    decodeGeneration 2 1 (encode 2 1 pg0 th) = pg0 ∧
    decodeAngle 2 1 (encode 2 1 pg0 th) = th ∧
    lpObjective 2 1 (fun _ => 3) ⬝ᵥ encode 2 1 pg0 th = -3 := by
  obtain ⟨hnn, hle, hg, ha, hobj⟩ :=
    (dispatch_encoding_correct 2 1 1 tl hd bb gb dd 0 (fun _ => 0) (fun _ => 2)
      (fun _ => -5) (fun _ => 5) (fun _ => 3)).1 pg0 th feasible
  exact ⟨hnn, hle, hg, ha, by rw [hobj, cost_pg0]⟩

/-- The encoded point is LP-optimal, and its decoding is a minimum-cost
dispatch. -/
example :
    ∀ x' : Fin (numVars 2 1) → ℝ, (∀ i, 0 ≤ x' i) →
      (∀ j, (lpMatrix 2 1 1 tl hd bb gb 0 *ᵥ x') j ≤
        lpRhs 2 1 1 dd (fun _ => 0) (fun _ => 2) (fun _ => -5) (fun _ => 5) j) →
      lpObjective 2 1 (fun _ => 3) ⬝ᵥ x' ≤ -3 := by
  intro x' hx' hAx'
  have hdec := decode_feasible 2 1 1 tl hd bb gb dd 0 (fun _ => 0) (fun _ => 2)
    (fun _ => -5) (fun _ => 5) x' hx' hAx'
  rw [lpObjective_dotProduct]
  simp only [dispatchCost, dotProduct, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  have hbal := congrFun hdec.1 1
  have hbal0 := congrFun hdec.1 0
  rw [lap] at hbal hbal0
  simp [generatorIncidence, gb, dd, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    at hbal hbal0
  linarith

/-! ### Infeasible-capacity case -/

/-- With `pmax = 1/2` no dispatch is feasible: the two balance rows force
`pg = 1`. -/
lemma capacity_infeasible : ¬ ∃ pg θ, IsDispatchFeasible 2 1 1 tl hd bb gb dd 0
    (fun _ => 0) (fun _ => 1 / 2) (fun _ => -5) (fun _ => 5) pg θ := by
  rintro ⟨pg, θ, hbal, -, hgen, -⟩
  have h0 := congrFun hbal 0
  have h1 := congrFun hbal 1
  rw [lap] at h0 h1
  simp [generatorIncidence, gb, dd, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have := (hgen 0).2
  linarith

/-- With `pmax = 1/2` the canonical LP has no feasible point. -/
example : ¬ ∃ x : Fin (numVars 2 1) → ℝ, (∀ i, 0 ≤ x i) ∧
    ∀ j, (lpMatrix 2 1 1 tl hd bb gb 0 *ᵥ x) j ≤
      lpRhs 2 1 1 dd (fun _ => 0) (fun _ => 1 / 2) (fun _ => -5) (fun _ => 5) j := by
  rw [← dispatch_nonempty_iff_lp_nonempty]
  exact capacity_infeasible

end PhyslibExtTest.Circuits.DCDispatchEncoding
