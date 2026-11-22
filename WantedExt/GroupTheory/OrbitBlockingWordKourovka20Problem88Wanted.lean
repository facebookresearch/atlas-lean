/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Words blocking the automorphic orbit of a free group element (Kourovka Notebook Problem 20.88)

Kourovka Notebook, Problem 20.88 (V. Shpilrain), marked solved in the 21st issue: let `u` be an
element of a free group `F_r`. Is it true that there is `v ∈ F_r` (that depends on `u`) that cannot
be a subword of any cyclically reduced word `φ(u)`, where `φ` is an automorphism of `F_r`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

@[expose] public section

namespace MathlibExt.GroupTheory.OrbitBlockingWordKourovka20Problem88Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.88 (V. Shpilrain). UnsolvedMath record
UM-00701746 (`KOU-20.88`), dataset ulamai/UnsolvedMath v1.8.0.

Elements are compared through their reduced words `FreeGroup.toWord`; subword means contiguous
factor (`List.IsInfix`), and cyclically reduced is Mathlib's `FreeGroup.IsCyclicallyReduced`. The
rank is `r ≥ 1`: in the trivial group `F₀` the only candidate `v = 1` has the empty word, a subword
of every word.
-/

/-- **Kourovka Problem 20.88 (statement).** The statement that for every $r \ge 1$ and every
element $u$ of the free group $F_r$ on $r$ generators there is $v \in F_r$ such that, for every
automorphism $\varphi$ of $F_r$ for which the reduced word of $\varphi(u)$ is cyclically reduced,
the reduced word of $v$ is not a subword (a contiguous factor) of the reduced word of $\varphi(u)$.
-/
def existsOrbitBlockingWord : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ u : FreeGroup (Fin r), ∃ v : FreeGroup (Fin r),
    ∀ φ : MulAut (FreeGroup (Fin r)), FreeGroup.IsCyclicallyReduced (φ u).toWord →
      ¬ v.toWord <:+: (φ u).toWord

/--
**Orbit-blocking words exist (Kourovka Problem 20.88).** For every $r \ge 1$ and every element $u$
of the free group $F_r$ on $r$ generators there is $v \in F_r$ such that, for every automorphism
$\varphi$ of $F_r$ for which the reduced word of $\varphi(u)$ is cyclically reduced, the reduced
word of $v$ is not a subword (a contiguous factor) of the reduced word of $\varphi(u)$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 20.88 (V. Shpilrain); resolution: L.
Koch-Hyde, S. O'Connor, É. Olive and V. Shpilrain, Orbit-blocking words in free groups, preprint,
arXiv:2505.00477 (2025), Theorem 6.1 and Section 6: for every w ∈ F_r there are w-orbit-blocking
words, i.e. words v that are not subwords of the cyclic reduction of φ(w) for any automorphism φ
(built from primitivity-blocking words such as x₁² ⋯ x_r² x₁); Kourovka Notebook (21st issue),
Problem 20.88: Yes, it is true, https://arxiv.org/abs/2505.00477.
-/
public theorem_wanted existsOrbitBlockingWord_holds : existsOrbitBlockingWord

end MathlibExt.GroupTheory.OrbitBlockingWordKourovka20Problem88Wanted
