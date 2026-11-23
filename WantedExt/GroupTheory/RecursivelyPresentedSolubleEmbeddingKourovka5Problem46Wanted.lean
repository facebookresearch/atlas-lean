/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Recursively presented soluble groups (Kourovka Notebook Problem 5.46)

Kourovka Notebook, Archive of Solved Problems, Problem 5.46 (V. N. Remeslennikov): is every
recursively presented soluble group embeddable in a group finitely presented in the variety of all
soluble groups of derived length n, for suitable n?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.RecursivelyPresentedSolubleEmbeddingKourovka5Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.46 (V. N.
Remeslennikov). UnsolvedMath record UM-00700327 (`KOU-5.46`), dataset ulamai/UnsolvedMath v1.8.0.

A recursively presented group is taken finitely generated: `G` is the image of `φ : FreeGroup (Fin
m) →* G` whose set of relator words (lists of letters mapping to `1`) is recursively enumerable,
equivalently `G` has a presentation with `m` generators and a recursively enumerable set of
relators. A group finitely presented in the variety `Aⁿ` of soluble groups of derived length at most
`n` is `F / (R^F · F^(n))` for a free group `F` of finite rank and a finite set `R` of words,
`F^(n)` being the verbal subgroup of `Aⁿ`.
-/

/-- Kourovka 5.46 (V. N. Remeslennikov): every finitely generated recursively presented soluble
group `G` (given by `φ : FreeGroup (Fin m) →* G` onto `G` whose set of relator words is recursively
enumerable) embeds in a group `H` finitely presented in the variety `Aⁿ` of soluble groups of
derived length at most `n`, for some `n`: `H = F / (R^F · F^(n))` for a free group `F` of finite
rank and a finite set `R` of words. -/
def recursivelyPresentedSolubleEmbeds : Prop :=
  ∀ (G : Type) [Group G] (m : ℕ) (φ : FreeGroup (Fin m) →* G), Function.Surjective φ →
    REPred (fun w : List (Fin m × Bool) => φ (FreeGroup.mk w) = 1) → Group.IsSolvable G →
      ∃ (n k : ℕ) (R : List (List (Fin k × Bool))) (H : Type) (_ : Group H)
        (ψ : FreeGroup (Fin k) →* H), Function.Surjective ψ ∧
        ψ.ker = Subgroup.normalClosure {w | ∃ l ∈ R, w = FreeGroup.mk l} ⊔
          derivedSeries (FreeGroup (Fin k)) n ∧
        ∃ f : G →* H, Function.Injective f

/--
Resolved true: the Kourovka Archive answers 5.46 "Yes, it is", citing Kukin (Soviet Math. Dokl. 21
(1980), 378-381). Stated for finitely generated recursively presented soluble groups. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.46 (V. N. Remeslennikov);
resolution: G. P. Kukin, Soviet Math. Dokl. 21 (1980), 378-381, Kourovka Archive, Problem 5.46: Yes,
it is (Kukin), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted recursivelyPresentedSolubleEmbeds_holds : recursivelyPresentedSolubleEmbeds

end MathlibExt.GroupTheory.RecursivelyPresentedSolubleEmbeddingKourovka5Problem46Wanted
