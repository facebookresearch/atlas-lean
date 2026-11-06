/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-16167-018: Does Cleary's golden-ratio Thompson group F_tau embed
in Thompson's group F? (The poset-structure question is not
formalized.)
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.GoldenRatioThompsonEmbedWanted

/-! Source record `OWR-16167-018`. Following Hyde and Moore (arXiv:2103.14911, Section 7), both
groups are subgroups of `PL₊(I)`: orientation-preserving piecewise-linear homeomorphisms of
`I = [0, 1]` with finitely many breakpoints, viewed as permutations of `ℝ` that are the identity
outside `I`. -/

/-- **Dyadic rationals.** A real number $x$ is dyadic when $x = a / 2^n$ for some integer $a$ and
some natural number $n$, that is, when $x$ lies in $\mathbb{Z}[1/2]$. -/
def IsDyadic (x : ℝ) : Prop :=
  ∃ (a : ℤ) (n : ℕ), x = a / 2 ^ n

/-- **Golden integers.** Let $\tau = (1 + \sqrt{5})/2$ be the golden ratio. A real number $x$ is a
golden integer when $x = a + b\tau$ for some integers $a$ and $b$. Since $\tau^2 = \tau + 1$, these
are exactly the elements of $\mathbb{Z}[\tau]$. -/
def IsGoldenInteger (x : ℝ) : Prop :=
  ∃ a b : ℤ, x = a + b * Real.goldenRatio

/-- **Piecewise-linear maps with prescribed breakpoints and slopes.** Let $B$ and $S$ be sets of
real numbers. A permutation $f$ of $\mathbb{R}$ is piecewise linear with breakpoints in $B$ and
slopes in $S$ when $f(x) = x$ for every $x \notin [0, 1]$, and there are a natural number $n$
and points $0 = t_0 < t_1 < \dots < t_{n+1} = 1$, all in $B$, such that for each $i \le n$ there
is $s \in S$ with $f(x) = f(t_i) + s (x - t_i)$ for all $x \in [t_i, t_{i+1}]$.

Adjacent pieces agree at the shared point, so $f$ restricts to a piecewise-linear homeomorphism
of $[0, 1]$ when the slopes are positive. -/
def IsPLHomeoWith (B S : Set ℝ) (f : Equiv.Perm ℝ) : Prop :=
  (∀ x, x ∉ Set.Icc (0 : ℝ) 1 → f x = x) ∧
    ∃ (n : ℕ) (t : Fin (n + 2) → ℝ), StrictMono t ∧ t 0 = 0 ∧ t (Fin.last _) = 1 ∧
      (∀ i, t i ∈ B) ∧
      ∀ i : Fin (n + 1), ∃ s ∈ S, ∀ x ∈ Set.Icc (t i.castSucc) (t i.succ),
        f x = f (t i.castSucc) + s * (x - t i.castSucc)

/-- **Thompson's group F.** Thompson's group $F$ is the set of permutations $f$ of $\mathbb{R}$
such that $f(x) = x$ for every $x \notin [0, 1]$, and there are a natural number $n$ and points
$0 = t_0 < t_1 < \dots < t_{n+1} = 1$, each of the form $a / 2^m$ with $a \in \mathbb{Z}$ and
$m \in \mathbb{N}$, such that on each interval $[t_i, t_{i+1}]$ the map $f$ is affine with slope
$2^k$ for some integer $k$, that is, $f(x) = f(t_i) + 2^k (x - t_i)$ for all
$x \in [t_i, t_{i+1}]$. -/
def thompsonF : Set (Equiv.Perm ℝ) :=
  {f | IsPLHomeoWith {x | IsDyadic x} (Set.range fun k : ℤ => (2 : ℝ) ^ k) f}

/-- **Cleary's golden-ratio Thompson group.** Let $\tau = (1 + \sqrt{5})/2$ be the golden
ratio. Cleary's group $F_\tau$ is the set of permutations $f$ of $\mathbb{R}$ such that
$f(x) = x$ for every $x \notin [0, 1]$, and there are a natural number $n$ and points
$0 = t_0 < t_1 < \dots < t_{n+1} = 1$, each of the form $a + b\tau$ with $a, b \in \mathbb{Z}$,
such that on each interval $[t_i, t_{i+1}]$ the map $f$ is affine with slope $\tau^k$ for some
integer $k$, that is, $f(x) = f(t_i) + \tau^k (x - t_i)$ for all $x \in [t_i, t_{i+1}]$. -/
def clearyFTau : Set (Equiv.Perm ℝ) :=
  {f | IsPLHomeoWith {x | IsGoldenInteger x} (Set.range fun k : ℤ => Real.goldenRatio ^ k) f}

/-- **Golden-ratio Thompson embedding conjecture.** The proposition that there is a map
$\varphi$ from permutations of $\mathbb{R}$ to permutations of $\mathbb{R}$ that sends every
element of Cleary's golden-ratio Thompson group $F_\tau$ into Thompson's group $F$, is injective
on $F_\tau$, and satisfies $\varphi(g h) = \varphi(g) \varphi(h)$ for all $g, h \in F_\tau$,
where the product of permutations is composition.

Since $F_\tau$ is a group under composition, this says that $F_\tau$ embeds in $F$ as a group.

Source: record OWR-16167-018. -/
def conjecture : Prop :=
  ∃ φ : Equiv.Perm ℝ → Equiv.Perm ℝ, (∀ g ∈ clearyFTau, φ g ∈ thompsonF) ∧
    Set.InjOn φ clearyFTau ∧ ∀ g ∈ clearyFTau, ∀ h ∈ clearyFTau, φ (g * h) = φ g * φ h

/--
**Cleary's golden-ratio group does not embed in Thompson's group F.** There is no map $\varphi$
from permutations of $\mathbb{R}$ to permutations of $\mathbb{R}$ that sends every element of
Cleary's golden-ratio Thompson group $F_\tau$ into Thompson's group $F$, is injective on
$F_\tau$, and satisfies $\varphi(g h) = \varphi(g) \varphi(h)$ for all $g, h \in F_\tau$, where
the product of permutations is composition. In other words, the golden-ratio Thompson embedding
conjecture is false: $F_\tau$ does not embed in $F$ as a group.

Hyde and Moore proved this by introducing F-obstructions (Corollary 1.4; Corollary 1 in arXiv v1).

Source: J. Hyde, J. T. Moore,
Subgroups of PL+I which do not embed into Thompson's group F, Groups, Geometry, and Dynamics 17
(2023) 533-554, arXiv:2103.14911, https://arxiv.org/abs/2103.14911. Moved from
`OpenConjectures/GroupTheory/GoldenRatioThompsonEmbed`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.GoldenRatioThompsonEmbedWanted
