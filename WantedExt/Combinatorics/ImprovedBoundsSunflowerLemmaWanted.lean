/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Improved bounds for the sunflower lemma

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.ImprovedBoundsSunflowerLemma` — annals_improved_bounds_sunflower_lemma (manifest `manifests/problems/annals_improved_bounds_sunflower_lemma.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted` namespace. Mathematical
statements are unchanged. Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Base

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

open Real

/-- **Sunflower lower bound.** For natural numbers $r$ and $w$ and a real number $C$, the lower
bound is the real number
$$\left(C\, r^3 \log_{1.9} w \, \log_{1.9}(\log_{1.9} w)\right)^w,$$
where $\log_{1.9} x = \ln x / \ln 1.9$, with the convention $\ln 0 = 0$.

Following the authors, logarithms are taken to base $1.9$; see the paragraph directly after
Theorem 1.4 of Alweiss, Lovett, Wu, and Zhang, *Improved bounds for the sunflower lemma*. -/
noncomputable def lowerBound (r : ℕ) (C : ℝ) (w : ℕ) : ℝ :=
  (C * r ^ 3 * logb 1.9 w * logb 1.9 (logb 1.9 w)) ^ w

/- The absolute constant `C` in Theorem 1.4. Although not explicitly stated in the paper,
the constant `C` doesn't depend on `r`. -/
/-- **Sunflower constant.** An unspecified real number $C$, the absolute constant in the
Alweiss–Lovett–Wu–Zhang sunflower bound (Theorem 1.4); it does not depend on $r$ or $w$.

Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean Via leanprover/lean-eval@38361be, problem `annals_improved_bounds_sunflower_lemma`. -/
public def_wanted C : ℝ

/--
**Alweiss–Lovett–Wu–Zhang sunflower bound.** Let $C$ be the sunflower constant, a real number
not depending on $r$ or $w$. Let $r \ge 3$ and $w \ge 2$ be natural numbers, let $X$ be a finite
type, and let $\mathcal{F}$ be a $w$-set system of subsets of $X$, that is, every member of
$\mathcal{F}$ has at most $w$ elements. If $\mathcal{F}$ has at least
$$\left(C\, r^3 \log_{1.9} w \, \log_{1.9}(\log_{1.9} w)\right)^w$$
members, then some subfamily $S \subseteq \mathcal{F}$ is an $r$-sunflower: $S$ has exactly $r$
members and any two distinct members of $S$ intersect in $\bigcap S$.

This is Theorem 1.4 (main theorem, sunflowers); logarithms are to base $1.9$, as in the paper.
We require $w \ge 2$, as the paper assumes $\log \log w > 0$.

Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean Via leanprover/lean-eval@38361be, problem `annals_improved_bounds_sunflower_lemma`.
-/
public theorem_wanted theorem_1_4 (r : ℕ) (hr : r ≥ 3) (X : Type*) [Finite X] (ℱ : Set (Set X)) (w : ℕ)
      (hw : w ≥ 2) (hℱ₁ : Set.IsSystem w ℱ) :
      ℱ.ncard ≥ lowerBound r ❰C❱ w → ∃ S ⊆ ℱ, Set.IsSunflower r S

end ImprovedBoundsSunflowerLemma

end MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted
