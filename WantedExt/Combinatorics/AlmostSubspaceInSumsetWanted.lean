/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Almost subspace inside A + A over F_2^n

`AIM-COMBINATORICS-0031` (AIM Additive combinatorics and its
applications, item 2.5): every `A ⊆ F₂ⁿ` of density `α` admits a
subspace `V` of codimension `log^O(1)(ε⁻¹ α⁻¹)` with
`|V ∩ (A + A)| ≥ (1 - ε) |V|`.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.AlmostSubspaceInSumsetWanted

/-! UnsolvedMath record `AIM-COMBINATORICS-0031` (AIM Problem Lists,
Additive combinatorics and its applications, item 2.5,
<http://aimpl.org/addcombapp/2/>). -/

open scoped BigOperators

/-- Almost containment of a subspace in `A + A`: there are absolute
constants `C, E > 0` such that for every `A ⊆ F₂ⁿ` of density `α` and
every `ε ∈ (0, 1)` there is a subspace `V` of codimension at most
`C * (log (ε⁻¹ α⁻¹) + 1)ᴱ` (the source's `log^O(1)(ε⁻¹ α⁻¹)`) with
`|V ∩ (A + A)| ≥ (1 - ε) |V|`. Codimension is the base-2 logarithm of
the subgroup index. Cites [AIM-COMBINATORICS-0031],
aim-combinatorics-notes.json notes[30]. -/
def conjecture : Prop :=
  ∃ (C E : ℝ), 0 < C ∧ 0 < E ∧
    ∀ (n : ℕ) (A : Finset (Fin n → ZMod 2)) (α ε : ℝ),
      0 < α → 0 < ε → ε < 1 →
      (A.card : ℝ) / 2 ^ n = α →
      ∃ V : AddSubgroup (Fin n → ZMod 2),
        Real.logb 2 ((Fintype.card (Fin n → ZMod 2) : ℝ) / (V.carrier.ncard : ℝ)) ≤
          C * (Real.log (ε⁻¹ * α⁻¹) + 1) ^ E ∧
        ((V.carrier ∩ {x | ∃ a ∈ A, ∃ b ∈ A, a + b = x}).ncard : ℝ) ≥
          (1 - ε) * (V.carrier.ncard : ℝ)

/--
Resolved true: Resolved. Kelley and Meka (Strong bounds for 3-progressions, FOCS 2023,
arXiv:2302.05537, Lemma 1.5) show that every A in F_q^n of density at least 2^-d contains A'
whose affine span V + theta has codimension O(d^5 log(1/tau)^4) and |A' + A'| >= (1 - tau)|V +
theta|; they note this answers the Hatami-Hosseini-Lovett question for the approximate
Bogolyubov problem for 2A. Over F_2, A' + A' lies in the linear subspace V, so |V ∩ (A + A)| >=
(1 - tau)|V| with polylogarithmic codimension, as formalized. Bloom and Sisask improve the
codimension to O(L(alpha)^5 L(gamma)^2) (arXiv:2309.02353, Theorem 3). Source: Zander Kelley and
Raghu Meka, Strong bounds for 3-progressions, FOCS 2023, arXiv:2302.05537,
https://arxiv.org/abs/2302.05537. Moved from
`OpenConjectures/Combinatorics/AlmostSubspaceInSumset`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.AlmostSubspaceInSumsetWanted
