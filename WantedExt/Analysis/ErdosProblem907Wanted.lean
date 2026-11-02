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
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Basic

@[expose] public section

namespace MathlibExt.Analysis.ErdosProblem907Wanted

/-! Source record `FC-ErdosProblem907`, ported from FormalConjectures
`ErdosProblems/907.lean` (`theorem erdos_907`) and checked against
erdosproblems.com/907. The upstream `answer(True)` is dropped; the
right-hand side is stated directly. Status: resolved true (de Bruijn [dB51]);
the registry links a proof-bearing external Lean development. -/

/-- **Erdős Problem 907.** The statement that every function $f : \mathbb{R} \to \mathbb{R}$
such that $x \mapsto f(x + h) - f(x)$ is continuous for every $h > 0$ can be written as
$f = g + a$ with $g : \mathbb{R} \to \mathbb{R}$ continuous and $a : \mathbb{R} \to \mathbb{R}$
additive, that is, $a(x + y) = a(x) + a(y)$ for all real $x$ and $y$. -/
def conjecture : Prop :=
  ∀ f : ℝ → ℝ, (∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) →
    ∃ g a : ℝ → ℝ, Continuous g ∧ (∀ x y, a (x + y) = a x + a y) ∧ f = g + a

/--
**De Bruijn's theorem on continuous differences (Erdős Problem 907).** Let
$f : \mathbb{R} \to \mathbb{R}$ be a function such that for every $h > 0$ the function
$x \mapsto f(x + h) - f(x)$ is continuous. Then there are functions
$g, a : \mathbb{R} \to \mathbb{R}$ with $g$ continuous and $a$ additive, that is,
$a(x + y) = a(x) + a(y)$ for all real $x$ and $y$, such that $f = g + a$.

Source: N. G. de Bruijn, Functions whose differences belong to a given class, Nieuw Archief voor
Wiskunde (2) (1951), 194–218, https://mathscinet.ams.org/mathscinet-getitem?mr=43870; External
Lean proof of Erdős Problem 907, plby/lean-proofs at commit
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos907.lean.
Moved from `OpenConjectures/Analysis/ErdosProblem907`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ErdosProblem907Wanted
