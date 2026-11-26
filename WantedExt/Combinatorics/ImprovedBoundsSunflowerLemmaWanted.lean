/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Improved bounds for the sunflower lemma

Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer

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
38361be884302c7edce1908c4aef8296eb2cb27e, module
`LeanEval.Combinatorics.ImprovedBoundsSunflowerLemma`
(problem `annals_improved_bounds_sunflower_lemma`, manifest
`manifests/problems/annals_improved_bounds_sunflower_lemma.toml`, rev 1, submitter Justus Springer,
status active), distributed under the Apache License, Version 2.0. lean-eval ships no `NOTICE` file.
Changes made: converted the `@[eval_problem]` theorem into a Batteries `theorem_wanted`,
replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any `LeanEval` helper
modules, and placed the declarations in the namespace
`MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted`. The theorem's size hypothesis now
uses the unchanged bound formula and an explicit admissible constant from
`MathlibExt.Combinatorics.SetFamily.ImprovedSunflowerBound`.
Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SetFamily.ImprovedSunflowerBound

@[expose] public section

namespace MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted
/-!
# Main Statement from Improved bounds for the sunflower lemma

We formalise the statement of the main result from R. Alweiss, S. Lovett, K. Wu, and J. Zhang,
`Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

namespace Set

variable {X : Type*}

/-- **Sunflower.** Let $r \in \mathbb{N}$ and let $S$ be a family of subsets of a type $X$. Then
$S$ is an $r$-sunflower if $S$ has exactly $r$ members (its cardinality is taken to be $0$ when
$S$ is infinite) and any two distinct members $A \ne B$ of $S$ satisfy $A \cap B = \bigcap S$,
the intersection of all members of $S$.

Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, *Improved bounds for the sunflower lemma*,
Annals of Math 194 (3), 2021, Definition 1.1. -/
def IsSunflower (r : ℕ) (S : Set (Set X)) : Prop :=
  S.ncard = r ∧ S.Pairwise (fun A B ↦ A ∩ B = ⋂₀ S)

/-- **Bounded-size set systems.** Let $w \in \mathbb{N}$ and let $\mathcal{F}$ be a family of
subsets of a type $X$. Then $\mathcal{F}$ is a $w$-set system if every member $A \in \mathcal{F}$
has at most $w$ elements, where the size of an infinite set is taken to be $0$.

Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, *Improved bounds for the sunflower lemma*,
Annals of Math 194 (3), 2021, second sentence of the introduction. -/
def IsSystem (w : ℕ) (ℱ : Set (Set X)) : Prop := ∀ A ∈ ℱ, A.ncard ≤ w

end Set

namespace ImprovedBoundsSunflowerLemma

open MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemma (lowerBound C)

/--
**Alweiss–Lovett–Wu–Zhang sunflower bound.** Let $C=2^{14}$, an admissible choice of the
absolute constant. Let $r \ge 3$ and $w \ge 2$ be natural numbers, let $X$ be a finite
type, and let $\mathcal{F}$ be a $w$-set system of subsets of $X$, that is, every member of
$\mathcal{F}$ has at most $w$ elements. If $\mathcal{F}$ has at least
$$\left(C\, r^3 \log_{1.9} w \, \log_{1.9}(\log_{1.9} w)\right)^w$$
members, then some subfamily $S \subseteq \mathcal{F}$ is an $r$-sunflower: $S$ has exactly $r$
members and any two distinct members of $S$ intersect in $\bigcap S$.

This is the bound of Theorem 1.4 with an explicit choice of constant obtained from Kupavskii
and Zakharov, §2, (1). The logarithms are to base $1.9$ as in Theorem 1.4; $w\ge2$ ensures
$\log\log w>0$.

Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean Via leanprover/lean-eval@38361be, problem `annals_improved_bounds_sunflower_lemma`.
-/
public theorem_wanted theorem_1_4 (r : ℕ) (hr : r ≥ 3) (X : Type*) [Finite X]
    (ℱ : Set (Set X)) (w : ℕ) (hw : w ≥ 2) (hℱ₁ : Set.IsSystem w ℱ) :
    ℱ.ncard ≥ lowerBound r C w → ∃ S ⊆ ℱ, Set.IsSunflower r S

end ImprovedBoundsSunflowerLemma

end MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted
