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

/-- **Almost-subspace-in-$A + A$ conjecture.** The statement that there are real constants $C > 0$
and $E > 0$ such that for every $n \in \mathbb{N}$, every set $A \subseteq \mathbb{F}_2^n$ and all
real numbers $\alpha$ and $\varepsilon$ with $\alpha > 0$, $0 < \varepsilon < 1$ and
$|A| / 2^n = \alpha$, there is an additive subgroup $V$ of $\mathbb{F}_2^n$ whose codimension
$\log_2(2^n / |V|)$ is at most $C \, (\log(\varepsilon^{-1} \alpha^{-1}) + 1)^E$ and which
satisfies $|V \cap (A + A)| \ge (1 - \varepsilon) |V|$. Here $A + A = \{a + b : a, b \in A\}$ and
$\log$ is the natural logarithm; the constants $C$ and $E$ express the source's codimension bound
$\log^{O(1)}(\varepsilon^{-1} \alpha^{-1})$.

Source: cites [AIM-COMBINATORICS-0031], aim-combinatorics-notes.json notes[30]. -/
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
**A subspace almost inside $A + A$ (Kelley–Meka).** There are real constants $C > 0$ and
$E > 0$ such that for every $n \in \mathbb{N}$, every set $A \subseteq \mathbb{F}_2^n$ and all real
numbers $\alpha$ and $\varepsilon$ with $\alpha > 0$, $0 < \varepsilon < 1$ and
$|A| / 2^n = \alpha$, there is an additive subgroup $V$ of $\mathbb{F}_2^n$ whose codimension
$\log_2(2^n / |V|)$ is at most $C \, (\log(\varepsilon^{-1} \alpha^{-1}) + 1)^E$ and which
satisfies $|V \cap (A + A)| \ge (1 - \varepsilon) |V|$. Here $A + A = \{a + b : a, b \in A\}$ and
$\log$ is the natural logarithm.

Kelley and Meka (Lemma 1.5 of arXiv:2302.05537) show that, over a finite field $\mathbb{F}_q$,
every set $A \subseteq \mathbb{F}_q^n$ of density at least $2^{-d}$ and every error parameter
$\tau$ admit a set $A' \subseteq A$ whose affine span $V + \theta$ has codimension
$O(d^5 \log(1/\tau)^4)$ and $|A' + A'| \ge (1 - \tau)|V + \theta|$, answering the question of
Hatami, Hosseini and Lovett. Over $\mathbb{F}_2$ the sumset $A' + A'$ lies in the subspace $V$,
which gives the statement. Bloom and Sisask improve this codimension bound (arXiv:2309.02353,
Theorem 3).

Source: Zander Kelley and
Raghu Meka, Strong bounds for 3-progressions, FOCS 2023, arXiv:2302.05537,
https://arxiv.org/abs/2302.05537. Moved from
`OpenConjectures/Combinatorics/AlmostSubspaceInSumset`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.AlmostSubspaceInSumsetWanted
