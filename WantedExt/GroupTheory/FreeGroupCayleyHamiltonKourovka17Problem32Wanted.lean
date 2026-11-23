/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Cayley-Hamilton analogue for free groups (Kourovka Notebook Problem 17.32)

Kourovka Notebook, Problem 17.32 (O. V. Bogopolski): is the following analogue of the
Cayley-Hamilton theorem true for the free group `Fₙ` of rank `n`: if `w ∈ Fₙ` and `φ ∈ Aut(Fₙ)` are
such that `⟨w, φ(w), …, φⁿ(w)⟩ = Fₙ`, then `⟨w, φ(w), …, φⁿ⁻¹(w)⟩ = Fₙ`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupCayleyHamiltonKourovka17Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.32 (O. V. Bogopolski). UnsolvedMath
record UM-00701334 (`KOU-17.32`), dataset ulamai/UnsolvedMath v1.8.0.

`Fₙ = FreeGroup (Fin n)`, `Aut(Fₙ) = MulAut (FreeGroup (Fin n))` and `φⁱ` is the `i`-th power in
`MulAut`; the target quantifies over all `n`.
-/

/-- **Bogopolski's Cayley–Hamilton question for free groups (Kourovka 17.32).** The assertion
that for every natural number $n$, every element $w$ of the free group $F_n$ of rank $n$ and every
automorphism $\varphi$ of $F_n$, if $w, \varphi(w), \dots, \varphi^n(w)$ generate $F_n$, then
already $w, \varphi(w), \dots, \varphi^{n-1}(w)$ generate $F_n$. -/
def freeGroupCayleyHamilton : Prop :=
  ∀ (n : ℕ) (w : FreeGroup (Fin n)) (φ : MulAut (FreeGroup (Fin n))),
    Subgroup.closure {x | ∃ i ≤ n, x = (φ ^ i) w} = ⊤ →
      Subgroup.closure {x | ∃ i < n, x = (φ ^ i) w} = ⊤

/--
**Bogopolski's Cayley–Hamilton analogue fails for free groups (Kourovka 17.32).** There are a
natural number $n$, an element $w$ of the free group $F_n$ of rank $n$ and an automorphism
$\varphi$ of $F_n$ such that $w, \varphi(w), \dots, \varphi^n(w)$ generate $F_n$ but
$w, \varphi(w), \dots, \varphi^{n-1}(w)$ do not.

Ionin and Semidetnov (Answer 8.2) give the example $n = 2$, $F_2 = \langle x, y \rangle$, $w = xy$
and $\varphi(x) = yx$, $\varphi(y) = x$. The Kourovka Notebook (21st issue) answers 17.32 "No, it
is not true", citing their preprint and a preprint of O. Kharlampovich.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.32 (O. V. Bogopolski); resolution: V.
Ionin and A. Semidetnov, On some more problems from the Kourovka Notebook, preprint,
arXiv:2608.29219 (2026; solutions found with the assistance of large language models and checked by
the authors, per its abstract); O. Kharlampovich, preprint (2026), Ionin-Semidetnov, Answer 8.2 (the
assertion fails for n = 2: w = xy, φ(x) = yx, φ(y) = x); the Kourovka Notebook (21st issue) marks
17.32 solved (No, it is not true), https://arxiv.org/abs/2608.29219.
-/
public theorem_wanted freeGroupCayleyHamilton_refuted : ¬ freeGroupCayleyHamilton

end MathlibExt.GroupTheory.FreeGroupCayleyHamiltonKourovka17Problem32Wanted
