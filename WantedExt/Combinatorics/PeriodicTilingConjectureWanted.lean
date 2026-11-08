/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counterexample to the periodic tiling conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.PeriodicTilingConjecture` — annals_periodic_tiling_conjecture (manifest `manifests/problems/annals_periodic_tiling_conjecture.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.PeriodicTilingConjectureWanted` namespace. Mathematical
statements are unchanged. Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.PeriodicTilingConjectureWanted
/-!
# Main Statements from A counterexample to the periodic tiling conjecture

We formalise the statements of the main results from R. Greenfeld and T. Tao,
`A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024.
-/

set_option autoImplicit false

namespace PeriodicTilingConjecture

open Filter Bornology MeasureTheory

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

/-- Given an abelian group `G`, we say that `F ⊆ G` is a tiling of `G` with tiling set `A ⊆ G` if
the translates of `F` by elements `a ∈ A` form a partition of `G`. In other words the map
`A × F → G` defined by `fun (a,f) ↦ a + f` is a bijection. -/
abbrev IsTiling (F A : Set G) : Prop := AddSubgroup.IsComplement A F

/-- We say that a tiling set `A ⊆ G` is periodic if there exists a finite index subgroup `H` of
`G` such that `A` can be written as the union of finitely many cosets of `H`. -/
def IsPeriodicTilingSet (A : Set G) : Prop :=
  ∃ H : AddSubgroup G, H.FiniteIndex ∧ ∃ s : Finset G, A = s + H

/-- Given an abelian group `G`, and a set `F ⊆ G` we say that `F` forms an aperiodic tiling equation
if there exists `A ⊆ G` such that `F` tiles `G` with tiling set `A` but all such `A` are not
periodic. -/
structure IsAperiodicTilingEquation (F : Set G) where
  solvable : ∃ A, IsTiling F A
  aperiodic : ∀ A, IsTiling F A → ¬ IsPeriodicTilingSet A

/--
Statement of Theorem 1.4 (Counterexample to Conjecture 1.2, I):

There exists a finite abelian group `G₀` and a finite non-empty `F ⊆ ℤ² × G₀` such that
`F` forms an aperiodic tiling equation.
Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_periodic_tiling_conjecture`.
-/
public theorem_wanted theorem_1_4 : ∃ (G₀ : Type) (_ : AddCommGroup G₀) (_ : Finite G₀),
    ∃ F : Set (ℤ × ℤ × G₀), F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F

/--
Statement of Corollary 1.6 (Counterexample to Conjecture 1.2, II):

For all sufficiently large `d`, there exists a finite non-empty `F ⊆ ℤᵈ` such that
`F` forms an aperiodic tiling equation.
Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_periodic_tiling_conjecture`.
-/
public theorem_wanted corollary_1_6 : ∀ᶠ d in atTop, ∃ (F : Set (Fin d → ℤ)),
    F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F

variable {d : ℕ}

/-- We say that `σ ⊆ ℝᵈ` is a continuous tiling of `ℝᵈ` with tiling set `Λ` if the translates of
`σ` by elements `v ∈ Λ` partition `ℝᵈ` up to null sets. In other words for almost all `x ∈ ℝᵈ`,
there exists a unique `v ∈ Λ` such that `x ∈ (v + σ)`. -/
def IsContinuousTiling (σ Λ : Set (Fin d → ℝ)) : Prop := ∀ᵐ x, ∃! v ∈ Λ, x ∈ (v +ᵥ σ)

/-- We say that a (continuous) tiling set `Λ ⊆ ℝᵈ` is periodic if there exists a lattice `L`
of `ℝᵈ` such that `Λ` can be written as the union of finitely many cosets of `L`. -/
def IsPeriodicContinuousTilingSet (Λ : Set (Fin d → ℝ)) : Prop :=
    ∃ (L : Submodule ℤ (Fin d → ℝ)) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
      ∃ s : Finset (Fin d → ℝ), Λ = s + L

/-- We say that a set `σ ⊆ ℝᵈ` forms an aperiodic continuous tiling equation if there exists
`Λ ⊆ ℝᵈ` such that `σ` (continuously) tiles `ℝᵈ` with tiling set `Λ` but all such `Λ` are not
periodic. -/
structure IsAperiodicContinuousTilingEquation (σ : Set (Fin d → ℝ)) where
  solvable : ∃ Λ, IsContinuousTiling σ Λ
  aperiodic : ∀ Λ, IsContinuousTiling σ Λ → ¬ IsPeriodicContinuousTilingSet Λ

/--
Statement of Corollary 1.7 (Counterexample to Conjecture 1.3):

For all sufficiently large `d`, there exists a bounded measurable set `σ ⊆ ℝᵈ` of positive
measure such that `σ` forms an aperiodic continuous tiling equation.
Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_periodic_tiling_conjecture`.
-/
public theorem_wanted corollary_1_7 : ∀ᶠ d in atTop, ∃ σ : Set (Fin d → ℝ), IsBounded σ ∧ MeasurableSet σ ∧
    0 < volume σ ∧ IsAperiodicContinuousTilingEquation σ

end PeriodicTilingConjecture

end MathlibExt.Combinatorics.PeriodicTilingConjectureWanted
