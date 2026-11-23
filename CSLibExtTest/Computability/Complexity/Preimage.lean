/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.Preimage
import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete

/-! # Consumers of canonical polynomial preimage closure -/

open MetaMathlibExt.ComplexityTheory Cslib.CookLevin
open Cslib.Complexity Cslib.Complexity.Karp

-- A real encoded Karp map can be lifted while preserving its certificate.
example : IsPolyTime (fun p : List Bool × List Bool =>
    (reduce3 p.1, p.2)) := isPolyTime_reduce3.map_fst

-- Canonical SAT preimages and arbitrary NP preimages use the same API.
example : satDec ∘ reduce3 ∈ NP := satDec_comp_mem_NP isPolyTime_reduce3

example (L : DecisionProblem) (hL : L ∈ NP) : L ∘ reduce3 ∈ NP :=
  comp_mem_NP hL isPolyTime_reduce3

example (L : DecisionProblem) (hL : L ∈ coNP) : L ∘ reduce3 ∈ coNP :=
  comp_mem_coNP hL isPolyTime_reduce3

example : PolyManyOneRed satDecᶜ sat3Decᶜ :=
  satDec_polyManyOneRed_sat3Dec.compl

-- Malformed input is rejected even with a long certificate.
example : (satVerifier ([], List.replicate 100 true)).ret = false := by decide

-- The empty conjunction has a zero-length certificate.
example : (satVerifier (encodeCNF [], [])).ret = true := by decide

-- An empty clause stays false regardless of surplus certificate bits.
example : (satVerifier (encodeCNF [[]], List.replicate 100 true)).ret =
    false := by decide

-- Surplus witness bits are allowed, but acceptance still implies SAT.
example : (satVerifier (encodeCNF [[(0, true)]],
    List.replicate 100 true)).ret = true := by decide
