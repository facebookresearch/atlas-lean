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

/-- A `r`-sunflower is a finite collection of `r` sets so that the intersection of each pair is
equal to the intersection of all of them. See Definition 1.1. -/
def IsSunflower (r : ℕ) (S : Set (Set X)) : Prop :=
  S.ncard = r ∧ S.Pairwise (fun A B ↦ A ∩ B = ⋂₀ S)

/-- The condition that `ℱ` is a `w`-set system, namely that each element has size at most `w`
(see second sentence of the introduction). -/
def IsSystem (w : ℕ) (ℱ : Set (Set X)) : Prop := ∀ A ∈ ℱ, A.ncard ≤ w

end Set

namespace ImprovedBoundsSunflowerLemma

open Real

/-- The lower bound from Theorem 1.4. We follow the convention of the authors and use the
logarithm in base 1.9; see the paragraph directly after Theorem 1.4. -/
noncomputable def lowerBound (r : ℕ) (C : ℝ) (w : ℕ) : ℝ :=
  (C * r ^ 3 * logb 1.9 w * logb 1.9 (logb 1.9 w)) ^ w

/- The absolute constant `C` in Theorem 1.4. Although not explicitly stated in the paper,
the constant `C` doesn't depend on `r`. -/
/-- Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean Via leanprover/lean-eval@38361be, problem `annals_improved_bounds_sunflower_lemma`. -/
public def_wanted C : ℝ

/--
Statement of Theorem 1.4 (Main theorem, sunflowers):

Let `r ≥ 3`. For some constant `C`, any `w`-set system `F` of size
`|F| ≥ (C * r ^ 3 * log w * log log w) ^ w` contains an `r`-sunflower.

Note: We require `w ≥ 2`, as the paper assumes `log log w > 0`.
Source: R. Alweiss, S. Lovett, K. Wu, and J. Zhang, `Improved bounds for the sunflower lemma`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-ImprovedBoundsSunflowerLemma.lean Via leanprover/lean-eval@38361be, problem `annals_improved_bounds_sunflower_lemma`.
-/
public theorem_wanted theorem_1_4 (r : ℕ) (hr : r ≥ 3) (X : Type*) [Finite X] (ℱ : Set (Set X)) (w : ℕ)
      (hw : w ≥ 2) (hℱ₁ : Set.IsSystem w ℱ) :
      ℱ.ncard ≥ lowerBound r ❰C❱ w → ∃ S ⊆ ℱ, Set.IsSunflower r S

end ImprovedBoundsSunflowerLemma

end MathlibExt.Combinatorics.ImprovedBoundsSunflowerLemmaWanted
