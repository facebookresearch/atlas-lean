/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Decidability of consequences of group laws (Kourovka Notebook Problem 3.4)

Kourovka Notebook, Archive of Solved Problems, Problem 3.4 (L. A. Bokut'): (well-known problems) (a)
is there an algorithm that decides, for any set of group words `f₁, …, fₘ` (in a fixed set of
variables `x₁, x₂, …`) and a separate word `f`, whether `f = 1` is a consequence of `f₁ = 1, …, fₘ =
1`? (b) Given words `f₁, …, fₘ`, is there an algorithm that decides, for any word `f`, whether `f =
1` is a consequence of `f₁ = 1, …, fₘ = 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.GroupLawConsequenceDecidableKourovka3Problem4Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.4 (L. A.
Bokut'). UnsolvedMath record UM-00700158 (`KOU-3.4`), dataset ulamai/UnsolvedMath v1.8.0.

Consequence is meant for identities (laws), as in Kleiman's resolution: every group satisfying the
laws `fᵢ = 1` satisfies `f = 1` (by Birkhoff's theorem the same as derivability). Words are lists of
letters `(i, b)` (a `Primcodable` type) read through `FreeGroup.mk`; decidability is
`ComputablePred`.
-/

/-- The law `f = 1` is a consequence of the laws `f₁ = 1, …, fₘ = 1` (as identities): every group
satisfying the laws `fᵢ = 1` satisfies `f = 1`. Words in the variables `x₀, x₁, …` are lists of
letters `(i, b)` read through `FreeGroup.mk` (`(i, true)` is `xᵢ`, `(i, false)` is `xᵢ⁻¹`), and a
group satisfies the law `w = 1` when `φ w = 1` for every `φ : FreeGroup ℕ →* G`. -/
def IsLawConsequence (fs : List (List (ℕ × Bool))) (f : List (ℕ × Bool)) : Prop :=
  ∀ (G : Type) [Group G], (∀ w ∈ fs, ∀ φ : FreeGroup ℕ →* G, φ (FreeGroup.mk w) = 1) →
    ∀ φ : FreeGroup ℕ →* G, φ (FreeGroup.mk f) = 1

/-- Kourovka 3.4(a) (L. A. Bokut'): there is an algorithm deciding, for any words `f₁, …, fₘ` and
`f`, whether `f = 1` is a consequence of `f₁ = 1, …, fₘ = 1`. -/
def lawConsequenceUniformlyDecidable : Prop :=
  ComputablePred fun p : List (List (ℕ × Bool)) × List (ℕ × Bool) => IsLawConsequence p.1 p.2

/-- Kourovka 3.4(b) (L. A. Bokut'): for all words `f₁, …, fₘ` there is an algorithm deciding, for
any word `f`, whether `f = 1` is a consequence of `f₁ = 1, …, fₘ = 1`. -/
def lawConsequenceDecidable : Prop :=
  ∀ fs : List (List (ℕ × Bool)), ComputablePred (IsLawConsequence fs)

/--
Resolved false: the Kourovka Archive answers 3.4 "No, in both cases", citing Kleiman (Soviet Math.
Dokl. 20 (1979)): there is no uniform algorithm deciding consequence of finitely many group laws.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.4 (L. A.
Bokut'); resolution: Yu. G. Kleiman, Soviet Math. Dokl. 20 (1979), 115-119, Kourovka Archive,
Problem 3.4: No, in both cases, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted lawConsequenceUniformlyDecidable_refuted : ¬ lawConsequenceUniformlyDecidable

/--
Resolved false: the Kourovka Archive answers 3.4 "No, in both cases", citing Kleiman (Soviet Math.
Dokl. 20 (1979)): some finite list of laws `f₁, …, fₘ` (a finitely based variety) has an undecidable
set of consequences. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 3.4 (L. A. Bokut'); resolution: Yu. G. Kleiman, Soviet Math. Dokl. 20 (1979), 115-119,
Kourovka Archive, Problem 3.4: No, in both cases, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted lawConsequenceDecidable_refuted : ¬ lawConsequenceDecidable

end MathlibExt.GroupTheory.GroupLawConsequenceDecidableKourovka3Problem4Wanted
