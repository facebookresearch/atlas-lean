/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A surjective non-injective Rota-Baxter operator (Kourovka Notebook Problem 20.125)

Kourovka Notebook, Problem 20.125 (V. G. Bardakov), marked solved in the 21st issue: does there
exist a non-abelian group `G` and a Rota-Baxter operator `B : G → G` such that `B` is surjective but
not injective?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.SurjectiveRotaBaxterOperatorKourovka20Problem125Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.125 (V. G. Bardakov). UnsolvedMath
record UM-00701783 (`KOU-20.125`), dataset ulamai/UnsolvedMath v1.8.0.

A Rota-Baxter operator (of weight `1`) satisfies `B(g) B(h) = B(g B(g) h B(g)⁻¹)`, the definition of
Guo-Lang-Sheng and Bardakov-Gubarev used in the resolving preprints.
-/

/-- A Rota-Baxter operator (of weight `1`) on a group `G`: a map `B : G → G` with
`B(g) B(h) = B(g B(g) h B(g)⁻¹)` for all `g, h ∈ G`. -/
def IsRotaBaxterOperator {G : Type} [Group G] (B : G → G) : Prop :=
  ∀ g h : G, B g * B h = B (g * B g * h * (B g)⁻¹)

/-- Kourovka 20.125 (V. G. Bardakov): there exist a non-abelian group `G` and a Rota-Baxter
operator on `G` that is surjective but not injective. -/
def surjectiveNonInjectiveRotaBaxterOperatorExists : Prop :=
  ∃ (G : Type) (_ : Group G), (∃ x y : G, x * y ≠ y * x) ∧
    ∃ B : G → G, IsRotaBaxterOperator B ∧ Function.Surjective B ∧ ¬ Function.Injective B

/--
Resolved true: the Kourovka Notebook (21st issue) answers 20.125 "Yes, it does exist", by an
AI-generated solution of Monticone confirmed by V. G. Bardakov; van Doorn, Judin, Monticone and
Morrison (Theorem 5.1) take `G = S₃ × ℤ^ℕ` and `B(σ, f) = (σ⁻¹, s(f))` with `s` the left shift,
which is surjective and not injective. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
20.125 (V. G. Bardakov); resolution: P. Monticone, Kourovka Notebook Problem 20.125, solution note,
23 March 2026; W. van Doorn, E. Judin, P. Monticone and D. Morrison, On some problems from the
Kourovka Notebook, preprint, arXiv:2607.17477 (2026), van Doorn-Judin-Monticone-Morrison, Theorem
5.1: G = S3 × Z^N with B(σ, f) = (σ⁻¹, s(f)), s the left shift; the Kourovka Notebook (21st issue)
marks 20.125 solved (AI solution confirmed by V. G. Bardakov), https://arxiv.org/abs/2607.17477.
-/
public theorem_wanted surjectiveNonInjectiveRotaBaxterOperatorExists_holds :
    surjectiveNonInjectiveRotaBaxterOperatorExists

end MathlibExt.GroupTheory.SurjectiveRotaBaxterOperatorKourovka20Problem125Wanted
