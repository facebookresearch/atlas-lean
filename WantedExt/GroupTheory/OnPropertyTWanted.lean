/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On property (T) for Aut(F_n) and SL_n(Z)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.OnPropertyT` — annals_on_property_t (manifest `manifests/problems/annals_on_property_t.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.OnPropertyTWanted` namespace. Mathematical
statements are unchanged. Source: M. Kaluba, D. Kielak, and P. W. Nowak, `On property (T) for Aut(F_n) and SL_n(Z)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-OnPropertyT.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.OnPropertyTWanted
/-!
# Main Statement from On property (T) for Aut(F_n) and SL_n(Z)

We formalise the statement of the main result from M. Kaluba, D. Kielak, and P. W. Nowak,
`On property (T) for Aut(F_n) and SL_n(Z)`, Annals of Math, 193 (2) 2021.
-/

set_option autoImplicit false

namespace OnPropertyT

/-- **Laplacian of a finite subset of a group.** For a group $G$ and a finite subset
$S \subseteq G$, the Laplacian of $S$ is the element $\Delta_S = |S| - \sum_{s \in S} s$ of the
real group ring $\mathbb{R}G$, where $|S|$ is the number of elements of $S$, taken as $|S|$ times
the identity element of $\mathbb{R}G$. When $S$ is a symmetric generating set of $G$, this is the
Laplacian of Equation (1) in the paper of Kaluba, Kielak and Nowak on property (T) for
$\operatorname{Aut}(F_n)$ and $\operatorname{SL}_n(\mathbb{Z})$. -/
noncomputable def Laplacian {G : Type*} [Group G] (S : Finset G) : MonoidAlgebra ℝ G :=
  Nat.card S - ∑ s ∈ S, MonoidAlgebra.of ℝ G s

/-- **Involution of the real group ring.** For a group $G$, the involution of the real group ring
$\mathbb{R}G$ is the $\mathbb{R}$-linear map $\mathbb{R}G \to \mathbb{R}G$ that sends
$\sum_{g \in G} a_g g$ to $\sum_{g \in G} a_g g^{-1}$, that is, the linear extension of inversion
on $G$. -/
noncomputable def groupRingInvolution {G : Type*} [Group G] (x : MonoidAlgebra ℝ G) :
    MonoidAlgebra ℝ G :=
  MonoidAlgebra.mapDomain (· ⁻¹) x

/-- **Property (T).** Let $G$ be a group. For a finite subset $S \subseteq G$, write
$\Delta_S = |S| - \sum_{s \in S} s$ for the Laplacian of $S$ in the real group ring $\mathbb{R}G$,
and write $\xi \mapsto \xi^{\star}$ for the involution of $\mathbb{R}G$ that extends inversion on
$G$ linearly. The group $G$ has Kazhdan's property (T) when there exist a finite subset
$S \subseteq G$ with $S^{-1} = S$ that generates $G$, a real number $\lambda > 0$, and a finite set
$\Xi$ of elements of $\mathbb{R}G$ such that
$\Delta_S^2 - \lambda \Delta_S = \sum_{\xi \in \Xi} \xi^{\star} \xi$.

This is Ozawa's characterization of property (T) for finitely generated groups, used as the
definition in Equation (2) of Kaluba, Kielak and Nowak. -/
def PropertyT (G : Type*) [Group G] : Prop :=
  ∃ S : Finset G, (S : Set G)⁻¹ = S ∧ Subgroup.closure (S : Set G) = ⊤ ∧ ∃ Λ : ℝ, Λ > 0 ∧
    ∃ ξ : Finset (MonoidAlgebra ℝ G), Laplacian S ^ 2 - Λ • Laplacian S = ∑ ξi ∈ ξ, groupRingInvolution ξi * ξi

/--
**Property (T) for automorphism groups of free groups of rank at least 6.** For every natural
number $n \ge 6$, the automorphism group $\operatorname{Aut}(F_n)$ of the free group $F_n$ on $n$
generators has property (T).

Source: M. Kaluba, D. Kielak, and P. W. Nowak, `On property (T) for Aut(F_n) and SL_n(Z)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-OnPropertyT.lean Via leanprover/lean-eval@38361be, problem `annals_on_property_t`.
-/
public theorem_wanted theorem_1 (n : ℕ) (hn : n ≥ 6) : PropertyT (MulAut (FreeGroup (Fin n)))

end OnPropertyT

end MathlibExt.GroupTheory.OnPropertyTWanted
