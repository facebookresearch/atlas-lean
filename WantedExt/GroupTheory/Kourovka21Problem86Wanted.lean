/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Kourovka Notebook Problem 21.86
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GroupTheory.Kourovka21Problem86Wanted

/-! Source record `KOU-21.86` (Kourovka Notebook Problem 21.86). -/

/-- **Hamming distance for sofic approximations.** For a natural number $n$ and permutations
$\sigma$, $\tau$ of $\{0, \dots, n-1\}$, the normalized Hamming distance $d(\sigma, \tau)$ is the
number of points $i < n$ with $\sigma(i) \ne \tau(i)$, divided by $n$, as a real number; for
$n = 0$ it is $0$. It is used in the definition of sofic groups [KOU-21.86]. -/
noncomputable def soficHammingDist {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : ℝ :=
  ((Finset.univ.filter (fun i => σ i ≠ τ i)).card : ℝ) / (n : ℝ)

/-- **Sofic groups.** Let $d$ denote the normalized Hamming distance on permutations. A group
$G$ is sofic if for every finite subset $F \subseteq G$ with $1 \in F$ and every real
$\varepsilon > 0$ there are an integer $n \ge 1$ and a map $\varphi$ from $F$ to the permutations
of $\{0, \dots, n-1\}$ such that $\varphi(1)$ is the identity,
$d(\varphi(gh), \varphi(g)\varphi(h)) < \varepsilon$ for all $g, h \in F$ with $gh \in F$, and
$\varphi(g)$ has no fixed point for every $g \in F$ with $g \ne 1$ [KOU-21.86]. -/
def IsSofic (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (h1 : 1 ∈ F) (ε : ℝ), 0 < ε →
    ∃ (n : ℕ) (_ : 1 ≤ n) (φ : ↥F → Equiv.Perm (Fin n)),
      φ ⟨1, h1⟩ = 1 ∧
      (∀ (g h : ↥F) (hmem : g.val * h.val ∈ F),
        soficHammingDist (φ ⟨g.val * h.val, hmem⟩) (φ g * φ h) < ε) ∧
      ∀ (g : ↥F), g.val ≠ 1 → ∀ (i : Fin n), φ g i ≠ i

/-- **Soficity problem (Kourovka Notebook Problem 21.86).** The statement that every group $G$ is
sofic [KOU-21.86]. -/
def conjecture : Prop :=
  ∀ (G : Type*) [Group G], IsSofic G

/--
**Not every group is sofic.** The soficity problem (Kourovka Notebook Problem 21.86) has a
negative answer: there exists a group that is not sofic.

OpenAI announced the first example, the unit group of the binary Leavitt algebra. G. Kun and
A. Thom (Theorems A and E) prove that $(\mathbb{Z}/2\mathbb{Z}) \wr_{G/\Gamma} G$ and
$G *_\Gamma G$ are not sofic for explicit residually finite Kazhdan pairs $\Gamma < G$. The
Kourovka Notebook (arXiv:1401.0300v49) marks Problem 21.86 solved.

Source: G. Kun and A. Thom, Nonsofic wreath products of residually finite groups,
arXiv:2608.06222 (2026), https://arxiv.org/abs/2608.06222; OpenAI, A counterexample to the
soficity conjecture, in Ten advances in mathematics and theoretical computer science, Chapter 3,
2026, https://cdn.openai.com/pdf/ten-proofs-oai.pdf; E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (20
October 2026), Problem 21.86, https://arxiv.org/abs/1401.0300v49. Moved from
`OpenConjectures/GroupTheory/Kourovka21Problem86`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.Kourovka21Problem86Wanted
