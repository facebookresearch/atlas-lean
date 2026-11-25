/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Blocks of defect zero of `p`-soluble groups (Kourovka Notebook Problem 12.26)

Kourovka Notebook, Archive of Solved Problems, Problem 12.26 (Shi Shengming; Jiping Zhang): is it
true that a finite `p`-soluble group `G` has a `p`-block of defect zero if and only if some element
`x ∈ O_{p'}(G)` has a centralizer `C_G(x)` that is a `p'`-subgroup?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

namespace MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.26 (Shi
Shengming; Jiping Zhang). UnsolvedMath record UM-00700845 (`KOU-12.26`), dataset ulamai/UnsolvedMath
v1.8.0.

A `p`-block of defect zero is encoded by its unique irreducible complex character `χ`, which is
characterized by `|G|ₚ ∣ χ(1)` (Brauer): `G` has one exactly when some irreducible complex
representation has degree divisible by `p^{vₚ(|G|)}`. `O_{p'}(G)` is the largest normal subgroup of
order prime to `p`, so `x ∈ O_{p'}(G)` is stated as `x ∈ N` for some normal subgroup `N` of order
prime to `p`. `p`-soluble means a subnormal series whose factors are `p`-groups or have order prime
to `p`.
-/

/-- **$p$-soluble groups.** Let $p$ be a natural number. A group $G$ is $p$-soluble when it has a
subnormal series $1 = H_0 \le H_1 \le \dots \le H_n = G$, each $H_i$ normal in $H_{i+1}$, whose
factors $H_{i+1}/H_i$ are $p$-groups or have order prime to $p$. Here an infinite factor is taken
to have order $0$. -/
def IsPSoluble (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (n : ℕ) (H : Fin (n + 1) → Subgroup G), H 0 = ⊥ ∧ H (Fin.last n) = ⊤ ∧
    ∀ i : Fin n, H i.castSucc ≤ H i.succ ∧
      ∃ _ : ((H i.castSucc).subgroupOf (H i.succ)).Normal,
        IsPGroup p (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ)) ∨
          (Nat.card (H i.succ ⧸ (H i.castSucc).subgroupOf (H i.succ))).Coprime p

/-- **Groups with a $p$-block of defect zero.** Let $p$ be a natural number. A group $G$ has a
$p$-block of defect zero when some irreducible finite-dimensional complex representation of $G$ has
degree divisible by $p^{v_p(|G|)}$, where $v_p(|G|)$ is the exponent of $p$ in the prime
factorization of the order $|G|$ of $G$ (this exponent is $0$ when $p$ is not prime or $G$ is
infinite). For a prime $p$ and a finite group $G$, the number $p^{v_p(|G|)}$ is $|G|_p$, the largest
power of $p$ dividing $|G|$.

By Brauer's theory the $p$-blocks of defect zero are exactly the singletons $\{\chi\}$ with $\chi$
irreducible and $|G|_p \mid \chi(1)$. -/
def HasDefectZeroBlock (p : ℕ) (G : Type) [Group G] : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
    (ρ : Representation ℂ G V), ρ.IsIrreducible ∧
      p ^ (Nat.card G).factorization p ∣ Module.finrank ℂ V

/-- **Kourovka Problem 12.26.** This is the proposition (Shi Shengming) that for every prime $p$ and
every finite $p$-soluble group $G$, the group $G$ has a $p$-block of defect zero if and only if some
normal subgroup $N$ of $G$ of order prime to $p$ contains an element $x$ whose centralizer $C_G(x)$
in $G$ has order prime to $p$.

Equivalently, some $x \in O_{p'}(G)$ has a centralizer of order prime to $p$, since $O_{p'}(G)$ is
the largest normal subgroup of $G$ of order prime to $p$. -/
def defectZeroBlockIffPRegularCentralizer : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (G : Type) [Group G] [Finite G], IsPSoluble p G →
    (HasDefectZeroBlock p G ↔
      ∃ N : Subgroup G, N.Normal ∧ (Nat.card N).Coprime p ∧
        ∃ x ∈ N, (Nat.card (Subgroup.centralizer {x})).Coprime p)

/--
**Refutation of Kourovka Problem 12.26.** The proposition of Kourovka Problem 12.26 is false:
it is not the case that for every prime $p$ and every finite $p$-soluble group $G$, the group $G$
has a $p$-block of defect zero if and only if some normal subgroup $N$ of $G$ of order prime to $p$
contains an element $x$ whose centralizer $C_G(x)$ in $G$ has order prime to $p$.

V. I. Zenkov's counterexample: the group $G = 3^2.\mathrm{GL}_2(3)$ of order $432$ is soluble and
has a $2$-block of defect zero (an irreducible character of degree $16$), but the centralizer of
every element of $O_{2'}(G) = 3^2$, the largest normal subgroup of $G$ of odd order, has even order.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.26 (Shi Shengming; Jiping Zhang);
resolution: V. I. Zenkov, Trudy Inst. Mat. i Mekh. UrO RAN 3 (1995), 36-40 (Russian), Kourovka
Archive, Problem 12.26: No; G = 3^2.GL_2(3), p = 2.
-/
public theorem_wanted defectZeroBlockIffPRegularCentralizer_refuted :
    ¬ defectZeroBlockIffPRegularCentralizer

end MathlibExt.GroupTheory.DefectZeroBlockCentralizerKourovka12Problem26Wanted
