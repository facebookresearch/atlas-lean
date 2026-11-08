/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free products of subgroups of `Aut(Fₙ)` (Kourovka Notebook Problem 18.11)

Kourovka Notebook, Problem 18.11 (V. G. Bardakov): let `G` and `H` be subgroups of the automorphism
group `Aut(Fₙ)` of a free group `Fₙ` of rank `n ≥ 2`. Is it true that the free product `G ∗ H`
embeds in the automorphism group `Aut(Fₘ)` for some `m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.11 (V. G. Bardakov). UnsolvedMath record
UM-00701440 (`KOU-18.11`), dataset ulamai/UnsolvedMath v1.8.0.

`Aut(Fₙ) = MulAut (FreeGroup (Fin n))` and the free product is Mathlib's `Monoid.Coprod`; no
finiteness assumption is made on `G` and `H`.
-/

/-- Kourovka 18.11 (V. G. Bardakov): for any subgroups `G, H` of `Aut(Fₙ)`, `n ≥ 2`, the free
product `G ∗ H` embeds in `Aut(Fₘ)` for some `m`. -/
def freeProductAutFreeGroupEmbeds : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ G H : Subgroup (MulAut (FreeGroup (Fin n))),
    ∃ (m : ℕ) (f : Monoid.Coprod G H →* MulAut (FreeGroup (Fin m))), Function.Injective f

/--
Resolved true: Jayadevan constructs, for subgroups `G ≤ Aut(Fₙ)` and `H ≤ Aut(Fₘ)` with no
finite-generation hypothesis, an embedding of `G ∗ H` in `Aut(F_{n+m+3})`; the Kourovka Notebook
(21st issue) answers 18.11 "Yes, it is true" (AI solution confirmed by V. G. Bardakov). Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Problem 18.11 (V. G. Bardakov); resolution: A. Jayadevan, Free
products of free-group automorphism groups: a finite-rank embedding by separating cocycles,
preprint, Zenodo record 22722085 (2026), abstract (for G ≤ Aut(F_n), H ≤ Aut(F_m), G ∗ H embeds in
Aut(F_{n+m+3}); no finite-generation hypothesis); the Kourovka Notebook (21st issue) marks 18.11
solved (Yes, it is true; AI solution confirmed by V. G. Bardakov),
https://zenodo.org/records/22722085.
-/
public theorem_wanted freeProductAutFreeGroupEmbeds_holds : freeProductAutFreeGroupEmbeds

end MathlibExt.GroupTheory.FreeProductAutFreeGroupEmbeddingKourovka18Problem11Wanted
