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

/-- Kourovka 17.32 (O. V. Bogopolski), an analogue of the Cayley-Hamilton theorem for the free group
`Fₙ`: if `w ∈ Fₙ` and `φ ∈ Aut(Fₙ)` satisfy `⟨w, φ(w), …, φⁿ(w)⟩ = Fₙ`, then
`⟨w, φ(w), …, φⁿ⁻¹(w)⟩ = Fₙ`. -/
def freeGroupCayleyHamilton : Prop :=
  ∀ (n : ℕ) (w : FreeGroup (Fin n)) (φ : MulAut (FreeGroup (Fin n))),
    Subgroup.closure {x | ∃ i ≤ n, x = (φ ^ i) w} = ⊤ →
      Subgroup.closure {x | ∃ i < n, x = (φ ^ i) w} = ⊤

/--
Resolved false: Ionin and Semidetnov (Answer 8.2) show that the assertion fails for `n = 2`, with
`F₂ = ⟨x, y⟩`, `w = xy` and the automorphism `φ(x) = yx`, `φ(y) = x`. The Kourovka Notebook (21st
issue) answers 17.32 "No, it is not true", citing their preprint and a preprint of O. Kharlampovich.
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
