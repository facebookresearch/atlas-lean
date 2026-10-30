/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Dimension subgroups modulo the lower central series (Kourovka Notebook Problem 12.22)

Kourovka Notebook, Archive of Solved Problems, Problem 12.22 (N. D. Gupta, Yu. V. Kuz'min): let
`Δ(G)` be the augmentation ideal of `ℤG` and `D_n(G) = G ∩ (1 + Δⁿ(G)) ⊇ γ_n(G)`. (a) Is `D_n(G) /
γ_n(G)` central in `G / γ_n(G)`? (b) Does `D_n(G) / γ_n(G)` have exponent dividing 2?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace MathlibExt.GroupTheory.DimensionSubgroupLowerCentralKourovka12Problem22Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.22 (N. D.
Gupta, Yu. V. Kuz'min). UnsolvedMath record UM-00700841 (`KOU-12.22`), dataset ulamai/UnsolvedMath
v1.8.0.

`Δ(G)` is the `ℤ`-span of the `g - 1` in `MonoidAlgebra ℤ G` and `Δⁿ` its `n`-th power as a
`ℤ`-submodule, the span of `n`-fold products, which is the two-sided ideal power. `γ_n(G)` is `(⊤ :
Subgroup G).lowerCentralSeries (n - 1)` and `n ≥ 1`. Centrality and exponent 2 are stated
elementwise, without quotients: commutators `x g x⁻¹ g⁻¹` and squares `x²` of `x ∈ D_n(G)` lie in
`γ_n(G)`.
-/

/-- The augmentation ideal `Δ(G)` of the integral group ring `ℤG`: the `ℤ`-span of the elements
`g - 1`, which is the kernel of the augmentation map. -/
noncomputable def augmentationIdeal (G : Type*) [Group G] : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1)

/-- `g` lies in the `n`-th dimension subgroup `D_n(G) = G ∩ (1 + Δⁿ(G))`; `Δⁿ` is the `n`-th power
of `Δ` (the span of `n`-fold products), the two-sided ideal power. -/
def MemDimensionSubgroup {G : Type*} [Group G] (n : ℕ) (g : G) : Prop :=
  MonoidAlgebra.of ℤ G g - 1 ∈ augmentationIdeal G ^ n

/-- Kourovka 12.22(a) (N. D. Gupta, Yu. V. Kuz'min): for every group `G` and `n ≥ 1`,
`D_n(G) / γ_n(G)` is central in `G / γ_n(G)`; here `(⊤ : Subgroup G).lowerCentralSeries (n - 1)`
is `γ_n(G)`. -/
def dimensionQuotientCentral : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ), 1 ≤ n → ∀ x : G, MemDimensionSubgroup n x →
    ∀ g : G, x * g * x⁻¹ * g⁻¹ ∈ (⊤ : Subgroup G).lowerCentralSeries (n - 1)

/-- Kourovka 12.22(b) (N. D. Gupta, Yu. V. Kuz'min): for every group `G` and `n ≥ 1`,
`D_n(G) / γ_n(G)` has exponent dividing 2. -/
def dimensionQuotientExponentTwo : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ), 1 ≤ n → ∀ x : G, MemDimensionSubgroup n x →
    x ^ 2 ∈ (⊤ : Subgroup G).lowerCentralSeries (n - 1)

/--
Resolved false: Gupta and Kuz'min show that `D_n(G) / γ_n(G)` need not be central in `G / γ_n(G)`,
and need not lie in any term of bounded index of its upper central series; the Kourovka Archive
answers 12.22(a) "No, not always". Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems
in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 12.22 (N. D. Gupta, Yu. V. Kuz'min); resolution: N. D. Gupta and Yu. V. Kuz'min,
J. Pure Appl. Algebra 104, no. 1 (1995), 191-197 (part a); L. Bartholdi and R. Mikhailov, J.
Topology 16, no. 2 (2023), 822-853 (part b), Kourovka Archive, Problem 12.22: "a) No, not always;
moreover, `D_n(G)/γ_n(G)` need not be contained in any term of the upper central series of
`G/γ_n(G)` with fixed number" and "b) No, not always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted dimensionQuotientCentral_refuted : ¬ dimensionQuotientCentral

/--
Resolved false: Bartholdi and Mikhailov show that `D_n(G) / γ_n(G)` need not have exponent dividing
2; the Kourovka Archive answers 12.22(b) "No, not always". Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 12.22 (N. D. Gupta, Yu. V. Kuz'min); resolution: N. D.
Gupta and Yu. V. Kuz'min, J. Pure Appl. Algebra 104, no. 1 (1995), 191-197 (part a); L. Bartholdi
and R. Mikhailov, J. Topology 16, no. 2 (2023), 822-853 (part b), Kourovka Archive, Problem 12.22:
"a) No, not always; moreover, `D_n(G)/γ_n(G)` need not be contained in any term of the upper central
series of `G/γ_n(G)` with fixed number" and "b) No, not always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted dimensionQuotientExponentTwo_refuted : ¬ dimensionQuotientExponentTwo

end MathlibExt.GroupTheory.DimensionSubgroupLowerCentralKourovka12Problem22Wanted
