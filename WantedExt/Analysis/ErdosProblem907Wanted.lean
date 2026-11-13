/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 907
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Basic

@[expose] public section

namespace MathlibExt.Analysis.ErdosProblem907Wanted

/-! Source record `FC-ErdosProblem907`, ported from FormalConjectures
`ErdosProblems/907.lean` (`theorem erdos_907`) and checked against
erdosproblems.com/907. The upstream `answer(True)` is dropped; the
right-hand side is stated directly. Status: resolved true (de Bruijn [dB51]);
the registry links a proof-bearing external Lean development. -/

/-- If every difference `f(· + h) - f(·)` is continuous, then `f` is the sum
of a continuous function and an additive function. -/
def conjecture : Prop :=
  ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) →
    ∃ g a : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧ f = g + a

/--
Resolved true: Answered yes by de Bruijn; a proof is available in an external Lean development.
Source: N. G. de Bruijn, Functions whose differences belong to a given class, Nieuw Archief voor
Wiskunde (2) (1951), 194–218, https://mathscinet.ams.org/mathscinet-getitem?mr=43870; External
Lean proof of Erdős Problem 907, plby/lean-proofs at commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos907.lean.
Moved from `OpenConjectures/Analysis/ErdosProblem907`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ErdosProblem907Wanted
