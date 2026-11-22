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

/-- **Augmentation ideal of the integral group ring.** For a group $G$, the augmentation ideal
$\Delta(G)$ of the integral group ring $\mathbb{Z}G$ is the $\mathbb{Z}$-submodule spanned by the
elements $g - 1$ for $g \in G$. It is the kernel of the augmentation map
$\mathbb{Z}G \to \mathbb{Z}$, $\sum_g a_g g \mapsto \sum_g a_g$. -/
noncomputable def augmentationIdeal (G : Type*) [Group G] : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1)

/-- **Dimension subgroups.** Let $\Delta(G)$ be the augmentation ideal of the integral group ring
$\mathbb{Z}G$ of a group $G$, and for $n \in \mathbb{N}$ let $\Delta(G)^n$ be its $n$-th power, the
$\mathbb{Z}$-span of all products of $n$ elements of $\Delta(G)$. An element $g \in G$ lies in the
$n$-th dimension subgroup $D_n(G) = G \cap (1 + \Delta(G)^n)$ when $g - 1 \in \Delta(G)^n$. -/
def MemDimensionSubgroup {G : Type*} [Group G] (n : ℕ) (g : G) : Prop :=
  MonoidAlgebra.of ℤ G g - 1 ∈ augmentationIdeal G ^ n

/-- **Gupta–Kuz'min centrality question (Kourovka 12.22(a)).** The statement that for every group
$G$, every $n \ge 1$, every element $x$ of the $n$-th dimension subgroup $D_n(G)$ and every
$g \in G$, the commutator $x g x^{-1} g^{-1}$ lies in $\gamma_n(G)$, the $n$-th term of the lower
central series of $G$, indexed so that $\gamma_1(G) = G$ and
$\gamma_{k+1}(G) = [\gamma_k(G), G]$. Equivalently, the image of $D_n(G)$ in $G/\gamma_n(G)$ is
central. -/
def dimensionQuotientCentral : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ), 1 ≤ n → ∀ x : G, MemDimensionSubgroup n x →
    ∀ g : G, x * g * x⁻¹ * g⁻¹ ∈ (⊤ : Subgroup G).lowerCentralSeries (n - 1)

/-- **Gupta–Kuz'min exponent question (Kourovka 12.22(b)).** The statement that for every group
$G$, every $n \ge 1$ and every element $x$ of the $n$-th dimension subgroup $D_n(G)$, the square
$x^2$ lies in $\gamma_n(G)$, the $n$-th term of the lower central series of $G$, indexed so that
$\gamma_1(G) = G$ and $\gamma_{k+1}(G) = [\gamma_k(G), G]$. Equivalently, the image of $D_n(G)$ in
$G/\gamma_n(G)$ has exponent dividing $2$. -/
def dimensionQuotientExponentTwo : Prop :=
  ∀ (G : Type) [Group G] (n : ℕ), 1 ≤ n → ∀ x : G, MemDimensionSubgroup n x →
    x ^ 2 ∈ (⊤ : Subgroup G).lowerCentralSeries (n - 1)

/--
**Dimension quotients need not be central.** There exist a group $G$, an integer $n \ge 1$, an
element $x$ of the $n$-th dimension subgroup $D_n(G)$ and an element $g \in G$ such that the
commutator $x g x^{-1} g^{-1}$ does not lie in $\gamma_n(G)$, the $n$-th term of the lower central
series of $G$ (indexed so that $\gamma_1(G) = G$). That is, the answer to Kourovka Problem 12.22(a)
is negative: the image of $D_n(G)$ in $G/\gamma_n(G)$ need not be central.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.22 (N. D.
Gupta, Yu. V. Kuz'min); resolution: N. D. Gupta and Yu. V. Kuz'min, J. Pure Appl. Algebra 104, no. 1
(1995), 191-197 (part a); L. Bartholdi and R. Mikhailov, J. Topology 16, no. 2 (2023), 822-853 (part
b), Kourovka Archive, Problem 12.22: "a) No, not always; moreover, `D_n(G)/γ_n(G)` need not be
contained in any term of the upper central series of `G/γ_n(G)` with fixed number" and "b) No, not
always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted dimensionQuotientCentral_refuted : ¬ dimensionQuotientCentral

/--
**Dimension quotients need not have exponent dividing 2.** There exist a group $G$, an integer
$n \ge 1$ and an element $x$ of the $n$-th dimension subgroup $D_n(G)$ such that $x^2$ does not lie
in $\gamma_n(G)$, the $n$-th term of the lower central series of $G$ (indexed so that
$\gamma_1(G) = G$). That is, the answer to Kourovka Problem 12.22(b) is negative: the image of
$D_n(G)$ in $G/\gamma_n(G)$ need not have exponent dividing $2$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.22 (N. D.
Gupta, Yu. V. Kuz'min); resolution: N. D. Gupta and Yu. V. Kuz'min, J. Pure Appl. Algebra 104, no. 1
(1995), 191-197 (part a); L. Bartholdi and R. Mikhailov, J. Topology 16, no. 2 (2023), 822-853 (part
b), Kourovka Archive, Problem 12.22: "a) No, not always; moreover, `D_n(G)/γ_n(G)` need not be
contained in any term of the upper central series of `G/γ_n(G)` with fixed number" and "b) No, not
always", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted dimensionQuotientExponentTwo_refuted : ¬ dimensionQuotientExponentTwo

end MathlibExt.GroupTheory.DimensionSubgroupLowerCentralKourovka12Problem22Wanted
