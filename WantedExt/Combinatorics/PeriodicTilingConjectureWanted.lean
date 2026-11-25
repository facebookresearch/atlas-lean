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

/-- **Tiling of an abelian group by translates.** Let $G$ be an abelian group and let
$F, A \subseteq G$. Then $F$ tiles $G$ with tiling set $A$ if the map $A \times F \to G$,
$(a, f) \mapsto a + f$, is a bijection; equivalently, every element of $G$ lies in $a + F$ for
exactly one $a \in A$. -/
abbrev IsTiling (F A : Set G) : Prop := AddSubgroup.IsComplement A F

/-- **Periodic tiling set.** A subset $A$ of an abelian group $G$ is periodic if there exist a
subgroup $H$ of $G$ of finite index and a finite set $S \subseteq G$ such that $A = S + H$, that
is, $A$ is the union of finitely many cosets of $H$. -/
def IsPeriodicTilingSet (A : Set G) : Prop :=
  ∃ H : AddSubgroup G, H.FiniteIndex ∧ ∃ s : Finset G, A = s + H

/-- **Aperiodic tiling equation.** Let $G$ be an abelian group. A set $F \subseteq G$ forms an
aperiodic tiling equation if $F$ tiles $G$ with some tiling set $A \subseteq G$, and no tiling
set $A \subseteq G$ with which $F$ tiles $G$ is periodic. -/
structure IsAperiodicTilingEquation (F : Set G) where
  solvable : ∃ A, IsTiling F A
  aperiodic : ∀ A, IsTiling F A → ¬ IsPeriodicTilingSet A

/--
**Greenfeld–Tao counterexample to the periodic tiling conjecture.** There exist a finite abelian
group $G_0$ and a finite non-empty set $F \subseteq \mathbb{Z}^2 \times G_0$ that forms an
aperiodic tiling equation in the group $\mathbb{Z}^2 \times G_0$.

Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_periodic_tiling_conjecture`.
-/
public theorem_wanted theorem_1_4 : ∃ (G₀ : Type) (_ : AddCommGroup G₀) (_ : Finite G₀),
    ∃ F : Set (ℤ × ℤ × G₀), F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F

/--
**Aperiodic tiling equations in high-dimensional integer lattices.** There is a natural number
$d_0$ such that for every natural number $d \ge d_0$ there exists a finite non-empty set
$F \subseteq \mathbb{Z}^d$ that forms an aperiodic tiling equation in $\mathbb{Z}^d$.

Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_periodic_tiling_conjecture`.
-/
public theorem_wanted corollary_1_6 : ∀ᶠ d in atTop, ∃ (F : Set (Fin d → ℤ)),
    F.Finite ∧ F.Nonempty ∧ IsAperiodicTilingEquation F

variable {d : ℕ}

/-- **Continuous tiling of Euclidean space.** For $d \in \mathbb{N}$, a set
$\sigma \subseteq \mathbb{R}^d$ continuously tiles $\mathbb{R}^d$ with tiling set
$\Lambda \subseteq \mathbb{R}^d$ if for almost every $x \in \mathbb{R}^d$ (with respect to
Lebesgue measure) there is exactly one $v \in \Lambda$ with $x \in v + \sigma$. -/
def IsContinuousTiling (σ Λ : Set (Fin d → ℝ)) : Prop := ∀ᵐ x, ∃! v ∈ Λ, x ∈ (v +ᵥ σ)

/-- **Periodic continuous tiling set.** For $d \in \mathbb{N}$, a set
$\Lambda \subseteq \mathbb{R}^d$ is periodic if there exist a lattice $L \subseteq \mathbb{R}^d$,
that is, a discrete additive subgroup that spans $\mathbb{R}^d$ over $\mathbb{R}$, and a finite
set $S \subseteq \mathbb{R}^d$ such that $\Lambda = S + L$, so that $\Lambda$ is the union of
finitely many cosets of $L$. -/
def IsPeriodicContinuousTilingSet (Λ : Set (Fin d → ℝ)) : Prop :=
    ∃ (L : Submodule ℤ (Fin d → ℝ)) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
      ∃ s : Finset (Fin d → ℝ), Λ = s + L

/-- **Aperiodic continuous tiling equation.** For $d \in \mathbb{N}$, a set
$\sigma \subseteq \mathbb{R}^d$ forms an aperiodic continuous tiling equation if $\sigma$
continuously tiles $\mathbb{R}^d$ with some tiling set $\Lambda \subseteq \mathbb{R}^d$, and no
tiling set $\Lambda$ with which $\sigma$ continuously tiles $\mathbb{R}^d$ is periodic. -/
structure IsAperiodicContinuousTilingEquation (σ : Set (Fin d → ℝ)) where
  solvable : ∃ Λ, IsContinuousTiling σ Λ
  aperiodic : ∀ Λ, IsContinuousTiling σ Λ → ¬ IsPeriodicContinuousTilingSet Λ

/--
**Aperiodic continuous tiling equations in high-dimensional Euclidean space.** There is a natural
number $d_0$ such that for every natural number $d \ge d_0$ there exists a bounded measurable set
$\sigma \subseteq \mathbb{R}^d$ of positive Lebesgue measure that forms an aperiodic continuous
tiling equation.

Source: R. Greenfeld and T. Tao, `A counterexample to the periodic tiling conjecture`, Annals of Math, 200 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-1-PeriodicTilingConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_periodic_tiling_conjecture`.
-/
public theorem_wanted corollary_1_7 : ∀ᶠ d in atTop, ∃ σ : Set (Fin d → ℝ), IsBounded σ ∧ MeasurableSet σ ∧
    0 < volume σ ∧ IsAperiodicContinuousTilingEquation σ

end PeriodicTilingConjecture

end MathlibExt.Combinatorics.PeriodicTilingConjectureWanted
