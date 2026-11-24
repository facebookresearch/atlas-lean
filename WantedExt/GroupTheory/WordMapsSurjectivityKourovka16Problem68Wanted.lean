/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Word maps on `PSL(2, ℝ)`, `PSL(2, ℂ)` and `SO(3, ℝ)` (Kourovka Notebook Problem 16.68)

Kourovka Notebook, Problem 16.68 (J. Mycielski): let `W(x, y)` be a non-trivial reduced group word,
and `G` one of the groups `PSL(2, ℝ)`, `PSL(2, ℂ)`, or `SO(3, ℝ)`. Are all the maps `W : G × G → G`
surjective?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.68 (J. Mycielski). UnsolvedMath record
UM-00701260 (`KOU-16.68`), dataset ulamai/UnsolvedMath v1.8.0.

One target per group. A non-trivial reduced word is a nontrivial element `w` of the free group `F₂`
on `x₀`, `x₁`, and its word map sends `(x, y)` to the image of `w` under the homomorphism `x₀ ↦ x`,
`x₁ ↦ y`. `PSL(2, K)` is Mathlib's `Matrix.ProjectiveSpecialLinearGroup (Fin 2) K` and `SO(3, ℝ)` is
`Matrix.specialOrthogonalGroup (Fin 3) ℝ`.
-/

/-- **Word map.** For a group $G$ and an element $w$ of the free group $F_2$ on two generators
$x_0, x_1$, the word map of $w$ is the map $G \times G \to G$ sending $(x, y)$ to $w(x, y)$, the
image of $w$ under the group homomorphism $F_2 \to G$ with $x_0 \mapsto x$ and $x_1 \mapsto y$. -/
def wordMap (G : Type*) [Group G] (w : FreeGroup (Fin 2)) (xy : G × G) : G :=
  FreeGroup.lift ![xy.1, xy.2] w

/-- **Surjectivity of word maps on $\mathrm{PSL}(2, \mathbb{R})$ (Kourovka 16.68(a)).** The
statement, asked about by J. Mycielski, that for every nontrivial element $w$ of the free group
$F_2$ on two generators, the word map
$\mathrm{PSL}(2, \mathbb{R}) \times \mathrm{PSL}(2, \mathbb{R}) \to \mathrm{PSL}(2, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is surjective. -/
def psl2RealWordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) w)

/-- **Surjectivity of word maps on $\mathrm{PSL}(2, \mathbb{C})$ (Kourovka 16.68(b)).** The
statement, asked about by J. Mycielski, that for every nontrivial element $w$ of the free group
$F_2$ on two generators, the word map
$\mathrm{PSL}(2, \mathbb{C}) \times \mathrm{PSL}(2, \mathbb{C}) \to \mathrm{PSL}(2, \mathbb{C})$,
$(x, y) \mapsto w(x, y)$, is surjective. -/
def psl2ComplexWordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) w)

/-- **Surjectivity of word maps on $\mathrm{SO}(3, \mathbb{R})$ (Kourovka 16.68(c)).** The
statement, asked about by J. Mycielski, that for every nontrivial element $w$ of the free group
$F_2$ on two generators, the word map
$\mathrm{SO}(3, \mathbb{R}) \times \mathrm{SO}(3, \mathbb{R}) \to \mathrm{SO}(3, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is surjective. -/
def so3WordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.specialOrthogonalGroup (Fin 3) ℝ) w)

/--
**Some nontrivial word map on $\mathrm{PSL}(2, \mathbb{R})$ is not surjective (Kourovka 16.68(a)).**
There is a nontrivial element $w$ of the free group $F_2$ on two generators whose word map
$\mathrm{PSL}(2, \mathbb{R}) \times \mathrm{PSL}(2, \mathbb{R}) \to \mathrm{PSL}(2, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is not surjective. That is, Mycielski's question has a negative answer
for $\mathrm{PSL}(2, \mathbb{R})$.

Nilradical (Theorem 2) gives an explicit nontrivial word $W$ (cyclically reduced length 44) with
$\operatorname{tr} W(A, B) > 7/4$ for all $A, B \in \mathrm{SL}(2, \mathbb{R})$; a nonidentity
involution of $\mathrm{PSL}(2, \mathbb{R})$ lifts to a matrix of trace $0$, so the word map of
$W$ misses it. The Kourovka Notebook (21st issue) records the negative answer for
$\mathrm{PSL}(2, \mathbb{R})$ (AI solution confirmed by A. Thom).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.68 (J. Mycielski); resolution:
Nilradical v1.0.0, Word maps on PSL2: real and complex cases, result notes (21 September 2026); A.
Thom, Convergent sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, Nilradical,
Theorem 1 (every w ≠ 1 in F_2 induces a surjective map PSL_2(K)² → PSL_2(K) for K algebraically
closed of characteristic 0) and Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈
SL_2(ℝ)); Thom, Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u,
v ∈ U(n)), for SO(3, ℝ); the Kourovka Notebook (21st issue) marks 16.68 solved (AI solution
confirmed by A. Thom; SO(3, ℝ) from Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted psl2RealWordMapsSurjective_refuted : ¬ psl2RealWordMapsSurjective

/--
**Nontrivial word maps on $\mathrm{PSL}(2, \mathbb{C})$ are surjective (Kourovka 16.68(b)).**
For every nontrivial element $w$ of the free group $F_2$ on two generators, the word map
$\mathrm{PSL}(2, \mathbb{C}) \times \mathrm{PSL}(2, \mathbb{C}) \to \mathrm{PSL}(2, \mathbb{C})$,
$(x, y) \mapsto w(x, y)$, is surjective. That is, Mycielski's question has an affirmative answer
for $\mathrm{PSL}(2, \mathbb{C})$.

Nilradical (Theorem 1) proves that for every algebraically closed field $K$ of characteristic
zero, in particular $\mathbb{C}$, every nontrivial word $w \in F_2$ induces a surjective map
$\mathrm{PSL}(2, K)^2 \to \mathrm{PSL}(2, K)$; the Kourovka Notebook (21st issue) records the
affirmative answer for $\mathrm{PSL}(2, \mathbb{C})$ (AI solution confirmed by A. Thom).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.68 (J. Mycielski); resolution:
Nilradical v1.0.0, Word maps on PSL2: real and complex cases, result notes (21 September 2026); A.
Thom, Convergent sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, Nilradical,
Theorem 1 (every w ≠ 1 in F_2 induces a surjective map PSL_2(K)² → PSL_2(K) for K algebraically
closed of characteristic 0) and Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈
SL_2(ℝ)); Thom, Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u,
v ∈ U(n)), for SO(3, ℝ); the Kourovka Notebook (21st issue) marks 16.68 solved (AI solution
confirmed by A. Thom; SO(3, ℝ) from Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted psl2ComplexWordMapsSurjective_holds : psl2ComplexWordMapsSurjective

/--
**Some nontrivial word map on $\mathrm{SO}(3, \mathbb{R})$ is not surjective (Kourovka 16.68(c)).**
There is a nontrivial element $w$ of the free group $F_2$ on two generators whose word map
$\mathrm{SO}(3, \mathbb{R}) \times \mathrm{SO}(3, \mathbb{R}) \to \mathrm{SO}(3, \mathbb{R})$,
$(x, y) \mapsto w(x, y)$, is not surjective. That is, Mycielski's question has a negative answer
for $\mathrm{SO}(3, \mathbb{R})$.

The Kourovka Notebook (21st issue) answers 16.68 negatively for $\mathrm{SO}(3, \mathbb{R})$,
noting that this follows from Thom (2013), whose Corollary 1.2 gives, for every
$\varepsilon > 0$, a nontrivial word $w$ with $\|1 - w(u, v)\| \le \varepsilon$ for all unitary
$u, v$, in particular for all $u, v \in \mathrm{SO}(3, \mathbb{R})$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 16.68 (J. Mycielski); resolution:
Nilradical v1.0.0, Word maps on PSL2: real and complex cases, result notes (21 September 2026); A.
Thom, Convergent sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, Nilradical,
Theorem 1 (every w ≠ 1 in F_2 induces a surjective map PSL_2(K)² → PSL_2(K) for K algebraically
closed of characteristic 0) and Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈
SL_2(ℝ)); Thom, Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u,
v ∈ U(n)), for SO(3, ℝ); the Kourovka Notebook (21st issue) marks 16.68 solved (AI solution
confirmed by A. Thom; SO(3, ℝ) from Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted so3WordMapsSurjective_refuted : ¬ so3WordMapsSurjective

end MathlibExt.GroupTheory.WordMapsSurjectivityKourovka16Problem68Wanted
