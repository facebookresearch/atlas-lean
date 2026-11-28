/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.KeyTheorems.Parameterized
import CSLibExt.Computability.Complexity.MapFirst

open MetaMathlibExt.Complexity.KeyTheorems.Parameterized
open MetaMathlibExt.BitstringEncoding

-- The original target uses the machine-based reduction and the circuit definition of W[1].
example :
    (CliqueParam ∈ WLevel 1 ∧ ∀ P ∈ WLevel 1, FPTReduces P CliqueParam) ∧
    (∀ P : ParamProblem, FPT P → P ∈ WLevel 1) ∧
    ∀ t : ℕ, WLevel t ⊆ WLevel (t + 1) :=
  parameterized_clique_w1_complete

-- A subsequent Clique-to-Q reduction can now establish W[1]-hardness of Q.
example {Q : ParamProblem} (r : FPTReduces CliqueParam Q) :
    ∀ P ∈ WLevel 1, FPTReduces P Q :=
  fun P hP => (clique_wOne_hard P hP).trans r

-- The edgeless graph has a one-vertex clique even when the header dwarfs its edge list.
example : WeightedCircuitSat 1 3
    (CliqueMembership.reduce (bitEncode ((2 ^ 100 : ℕ), ([] : List (ℕ × ℕ))))) 1 := by
  apply (CliqueMembership.reduce_correct _ _).mp
  simp only [CliqueParam, bitDecode_bitEncode, decide_eq_true_eq]
  exact ⟨[0], by simp, rfl, by simp, by simp⟩

-- The TM2 time bound also bounds the number of bits written on every raw input.
example : ∃ p : Polynomial ℕ, ∀ x, (CliqueMembership.reduce x).length ≤ p.eval x.length :=
  CliqueMembership.reduce_isPolyTime.length_bound

-- The probe has large fan-in even on a one-gate circuit. The relay still reads gate zero.
example : promoteWeft (bitEncode ((0, [(1, [1])]) : ℕ × List WCGate)) =
    bitEncode ((0, [(1, [1]), (3, [0, 0, 0, 0]), (4, [0])]) : ℕ × List WCGate) := by
  decide

-- Only variable 2 is active. Compression renumbers it to 0, adds one dummy, and lowers the weight.
example : Support.compact (bitEncode ((3, [(0, [2])]) : ℕ × List WCGate), 2) =
    (bitEncode ((2, [(0, [0])]) : ℕ × List WCGate), 1) := by
  have h : Support.labels 3 2 [(0, [2])] = [2, 3] := by
    change (insert 2 ({3} : Finset ℕ)).sort = [2, 3]
    rw [Finset.sort_insert (· ≤ ·) (by aesop) (by decide), Finset.sort_singleton]
  simp [Support.compact, Support.reindexGate, h, Support.active, Support.inputOf]

-- A repeated vertex in a surjective listing preserves clique queries of every size.
example (G : SimpleGraph Bool) [DecidableRel G.Adj] (k : ℕ) :
    CliqueParam (GraphWriter.writeGraph [false, true, false] fun a b => decide (G.Adj a b)) k ↔
      ∃ s, G.IsNClique k s := by
  apply GraphWriter.writeGraph_correct _ G id _ k
  rintro (_ | _)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
