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

/-- The word map `G × G → G` of `w ∈ F₂`: `(x, y) ↦ w(x, y)`. -/
def wordMap (G : Type*) [Group G] (w : FreeGroup (Fin 2)) (xy : G × G) : G :=
  FreeGroup.lift ![xy.1, xy.2] w

/-- Kourovka 16.68(a) (J. Mycielski): every nontrivial word map `PSL(2, ℝ)² → PSL(2, ℝ)` is
surjective. -/
def psl2RealWordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ) w)

/-- Kourovka 16.68(b) (J. Mycielski): every nontrivial word map `PSL(2, ℂ)² → PSL(2, ℂ)` is
surjective. -/
def psl2ComplexWordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) w)

/-- Kourovka 16.68(c) (J. Mycielski): every nontrivial word map `SO(3, ℝ)² → SO(3, ℝ)` is
surjective. -/
def so3WordMapsSurjective : Prop :=
  ∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Function.Surjective (wordMap (Matrix.specialOrthogonalGroup (Fin 3) ℝ) w)

/--
Resolved false: Nilradical (Theorem 2) gives an explicit nontrivial word `W` (cyclically reduced
length 44) with `tr W(A, B) > 7/4` for all `A, B ∈ SL(2, ℝ)`; a nonidentity involution of `PSL(2,
ℝ)` lifts to a matrix of trace `0`, so the word map of `W` misses it. The Kourovka Notebook (21st
issue) records the negative answer for `PSL(2, ℝ)` (AI solution confirmed by A. Thom). Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 16.68 (J. Mycielski); resolution: Nilradical v1.0.0, Word
maps on PSL2: real and complex cases, result notes (21 September 2026); A. Thom, Convergent
sequences in discrete groups, Canad. Math. Bull. 56 (2013), 424-433, Nilradical, Theorem 1 (every w
≠ 1 in F_2 induces a surjective map PSL_2(K)² → PSL_2(K) for K algebraically closed of
characteristic 0) and Theorem 2 (an explicit W ≠ 1 with tr W(A, B) > 7/4 for all A, B ∈ SL_2(ℝ));
Thom, Corollary 1.2 (for every n and ε > 0 a word w ≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u, v ∈ U(n)),
for SO(3, ℝ); the Kourovka Notebook (21st issue) marks 16.68 solved (AI solution confirmed by A.
Thom; SO(3, ℝ) from Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted psl2RealWordMapsSurjective_refuted : ¬ psl2RealWordMapsSurjective

/--
Resolved true: Nilradical (Theorem 1) proves that for every algebraically closed field `K` of
characteristic zero, in particular `ℂ`, every nontrivial word `w ∈ F₂` induces a surjective map
`PSL(2, K)² → PSL(2, K)`; the Kourovka Notebook (21st issue) records the affirmative answer for
`PSL(2, ℂ)` (AI solution confirmed by A. Thom). Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 16.68 (J. Mycielski); resolution: Nilradical v1.0.0, Word maps on PSL2: real and complex
cases, result notes (21 September 2026); A. Thom, Convergent sequences in discrete groups, Canad.
Math. Bull. 56 (2013), 424-433, Nilradical, Theorem 1 (every w ≠ 1 in F_2 induces a surjective map
PSL_2(K)² → PSL_2(K) for K algebraically closed of characteristic 0) and Theorem 2 (an explicit W ≠
1 with tr W(A, B) > 7/4 for all A, B ∈ SL_2(ℝ)); Thom, Corollary 1.2 (for every n and ε > 0 a word w
≠ 1 with ‖1 - w(u, v)‖ ≤ ε for all u, v ∈ U(n)), for SO(3, ℝ); the Kourovka Notebook (21st issue)
marks 16.68 solved (AI solution confirmed by A. Thom; SO(3, ℝ) from Thom 2013),
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/nilradical-kourovka-16-68-69.pdf.
-/
public theorem_wanted psl2ComplexWordMapsSurjective_holds : psl2ComplexWordMapsSurjective

/--
Resolved false: the Kourovka Notebook (21st issue) answers 16.68 negatively for `SO(3, ℝ)`, noting
that this follows from Thom (2013), whose Corollary 1.2 gives, for every `ε > 0`, a nontrivial word
`w` with `‖1 - w(u, v)‖ ≤ ε` for all unitary `u, v`, in particular for all `u, v ∈ SO(3, ℝ)`.
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
