/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GraphColoring
import CSLibExt.Complexity.NPComplete.GraphColoring.Hardness
import CSLibExt.Complexity.NPComplete.GraphColoring.Membership
meta import CSLibExt.Complexity.NPComplete.GraphColoring.Hardness
meta import CSLibExt.Complexity.NPComplete.GraphColoring.Membership
meta import MathlibExt.Computability.Complexity

/-! # Tests for the NP-completeness of GRAPH COLORING -/

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoring

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

-- The original statement, with its exact type.
example :
    graphColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L graphColoringDec :=
  graphColoring_npComplete

example : graphColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  Verification.graphColoringDec_mem_NP

example (L : MetaMathlibExt.ComplexityTheory.DecisionProblem)
    (hL : L ∈ MetaMathlibExt.ComplexityTheory.NP) :
    Cslib.CookLevin.PolyManyOneRed L graphColoringDec :=
  graphColoring_npHard L hL

example : Cslib.CookLevin.PolyManyOneRed Cslib.CookLevin.satDec graphColoringDec :=
  satDec_polyManyOneRed_graphColoringDec

example (x : List Bool) : graphColoringDec x = true ↔
    ∃ w : List Bool, w.length ≤ Verification.witnessBound.eval x.length ∧
      Verification.gcCheck x w = true :=
  Verification.graphColoringDec_iff x

example (n : ℕ) : Verification.witnessBound.eval n = 15 * (n + 1) ^ 2 :=
  Verification.eval_witnessBound n

private theorem accepts_encoding (i : GraphColoringInstance) :
    graphColoringDec (bitEncode i) = true ↔ WellFormed i ∧ GraphColoringFeasible i := by
  simp [graphColoringDec, bitDecode_bitEncode]

private theorem rejects_malformed (i : GraphColoringInstance) (h : ¬ WellFormed i) :
    graphColoringDec (bitEncode i) = false := by
  simp [graphColoringDec, bitDecode_bitEncode, h]

/-- The triangle on `0, 1, 2` with the bound `K`. -/
private abbrev triangle (K : ℕ) : GraphColoringInstance := (3, [(0, 1), (1, 2), (0, 2)], K)

/-- Three colors suffice for the triangle: give each vertex its own color. -/
example : graphColoringDec (bitEncode (triangle 3)) = true :=
  (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    ⟨SimpleGraph.Coloring.mk (fun v => v) fun {_ _} h => h.ne⟩⟩

/-- Two colors do not suffice for the triangle: two of its three vertices would share a color. -/
example : graphColoringDec (bitEncode (triangle 2)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, ⟨C⟩⟩ := (accepts_encoding _).1 h
  obtain ⟨i, j, hij, hc⟩ := Fintype.exists_ne_map_eq_of_card_lt C (by simp)
  refine C.valid ?_ hc
  simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj]
  refine ⟨hij, ?_⟩
  fin_cases i <;> fin_cases j <;> simp_all

/-- A lone continuation bit is a truncated instance encoding. -/
example : graphColoringDec [true] = false := by
  have h : bitDecode (α := GraphColoringInstance) [true] = none := rfl
  simp [graphColoringDec, h]

/-- An edge listed in both directions is malformed, though its graph is 2-colorable. -/
example : graphColoringDec (bitEncode ((2, [(0, 1), (1, 0)], 2) : GraphColoringInstance)) =
    false :=
  rejects_malformed _ (by unfold WellFormed; decide)

/-- A repeated edge is malformed. -/
example : graphColoringDec (bitEncode ((2, [(0, 1), (0, 1)], 2) : GraphColoringInstance)) =
    false :=
  rejects_malformed _ (by unfold WellFormed; decide)

/-- A self-loop is malformed. -/
example : graphColoringDec (bitEncode ((2, [(1, 1)], 2) : GraphColoringInstance)) = false :=
  rejects_malformed _ (by unfold WellFormed; decide)

/-- An endpoint outside `{0, …, n - 1}` is malformed. -/
example : graphColoringDec (bitEncode ((2, [(0, 2)], 3) : GraphColoringInstance)) = false :=
  rejects_malformed _ (by unfold WellFormed; decide)

/-- The empty graph on no vertices is colorable with no colors. -/
example : graphColoringDec (bitEncode ((0, [], 0) : GraphColoringInstance)) = true :=
  (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    ⟨SimpleGraph.Coloring.mk (fun v => v.elim0) fun {v} => v.elim0⟩⟩

/-- One vertex and no colors: no coloring. -/
example : graphColoringDec (bitEncode ((1, [], 0) : GraphColoringInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, ⟨C⟩⟩ := (accepts_encoding _).1 h
  exact (C 0).elim0

/-- A sparse instance: a million vertices, one edge, two colors. -/
private abbrev sparse : GraphColoringInstance := (1000000, [(0, 1)], 2)

example : graphColoringDec (bitEncode sparse) = true :=
  (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    ⟨SimpleGraph.Coloring.mk (fun v => if v.val = 0 then 0 else 1) fun {v w} h => by
      simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj,
        List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨-, ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩⟩ := h <;> simp [h₁, h₂]⟩⟩

-- The verifier: the colors of the two endpoints of every edge, in edge order.
#guard Verification.gcCheck (bitEncode (triangle 3)) (bitEncode [(0, 1), (1, 2), (0, 2)])
-- Equal colors on an edge.
#guard !Verification.gcCheck (bitEncode (triangle 3)) (bitEncode [(0, 0), (1, 2), (0, 2)])
-- A vertex with two colors.
#guard !Verification.gcCheck (bitEncode (triangle 3)) (bitEncode [(0, 1), (2, 2), (0, 2)])
-- A color outside `{0, …, K - 1}`.
#guard !Verification.gcCheck (bitEncode (triangle 2)) (bitEncode [(0, 1), (1, 2), (0, 2)])
-- Too few color pairs.
#guard !Verification.gcCheck (bitEncode (triangle 3)) (bitEncode [(0, 1), (1, 2)])
-- A malformed instance with a consistent certificate.
#guard !Verification.gcCheck (bitEncode ((2, [(0, 1), (1, 0)], 2) : GraphColoringInstance))
  (bitEncode [(0, 1), (1, 0)])
-- The sparse instance with a one-pair certificate.
#guard Verification.gcCheck (bitEncode sparse) (bitEncode [(0, 1)])
-- An undecodable instance.
#guard !Verification.gcCheck [true] []

-- The edge gadget: every edge `(u, v)` becomes six edges on three fresh vertices, so a repeated
-- edge of a 3-COLOR instance gives a well-formed GRAPH COLORING instance with `K = 3`.
example : Hardness.target 2 [(0, 1), (0, 1)] = (8, [(0, 2), (0, 3), (2, 3), (4, 2), (4, 3),
    (4, 1), (0, 5), (0, 6), (5, 6), (7, 5), (7, 6), (7, 1)], 3) := rfl

example : WellFormed (Hardness.target 2 [(0, 1), (0, 1)]) := by
  unfold WellFormed
  decide

example : ¬ WellFormed ((2, [(0, 1), (0, 1)], 3) : GraphColoringInstance) := by
  unfold WellFormed
  decide

-- The transducer computes the gadget instance from the unary graph encoding.
example : Transducer.convF (Cslib.Complexity.Karp.encodeE 2 [(0, 1), (0, 1)]) =
    bitEncode (Hardness.target 2 [(0, 1), (0, 1)]) :=
  Hardness.convF_encodeE 2 [(0, 1), (0, 1)]

#guard Transducer.convF (Cslib.Complexity.Karp.encodeE 2 [(0, 1)]) ==
  bitEncode (Hardness.target 2 [(0, 1)])
-- Input that ends inside an edge gives the empty string, which no instance encodes.
#guard Transducer.convF [false, true] == []

end MetaMathlibExt.Complexity.NPComplete.GraphColoring
