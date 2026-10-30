/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Free-group words outside subgroups of logarithmic index (Kourovka Notebook Problem 15.35)

Kourovka Notebook, Archive of Solved Problems, Problem 15.35 (O. V. Bogopolski): is there `C = C(r)`
such that every reduced word of length `n > 1` in the free group of rank `r` lies outside some
subgroup of index at most `C log n`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

namespace MathlibExt.GroupTheory.FreeGroupLogIndexSeparationKourovka15Problem35Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.35 (O. V.
Bogopolski). UnsolvedMath record UM-00701123 (`KOU-15.35`), dataset ulamai/UnsolvedMath v1.8.0.

Ranks `r ≥ 2` only: for `r = 1` the answer is yes (the least non-divisor of `n` is `O(log n)`) and
for `r = 0` it is vacuous. The target is stated for some rank `r ≥ 2`, so its refutation says that
no rank `r ≥ 2` admits such a `C`. Word length is `FreeGroup.norm` (reduced word length); the
subgroup must have finite index, since `Subgroup.index` is `0` for infinite index.
-/

/-- Kourovka 15.35 (O. V. Bogopolski), for some rank `r ≥ 2`: there is `C = C(r)` such that every
reduced word `w` of length `n > 1` in the free group `F_r` lies outside some subgroup of finite
index at most `C log n`. -/
def logIndexSeparation : Prop :=
  ∃ r : ℕ, 2 ≤ r ∧ ∃ C : ℝ, ∀ w : FreeGroup (Fin r), 1 < w.norm →
    ∃ H : Subgroup (FreeGroup (Fin r)), H.FiniteIndex ∧ w ∉ H ∧
      (H.index : ℝ) ≤ C * Real.log w.norm

/--
Resolved false: Bou-Rabee and McReynolds (Theorem 1.4) prove that for every rank `m > 1` the maximal
divisibility function of `F_m` on words of length at most `n` is not `O(log n)`, which rules out
every `C`; the Kourovka Archive answers 15.35 "No, it is not true". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.35 (O. V. Bogopolski); resolution:
K. Bou-Rabee and D. B. McReynolds, Asymptotic growth and least common multiples in groups, Bull.
London Math. Soc. 43 (2011), 1059-1068, arXiv:0907.3681, Theorem 1.4 (for m > 1, max D_{F_m}(n) is
not bounded by O(log n)), https://arxiv.org/abs/0907.3681.
-/
public theorem_wanted logIndexSeparation_refuted : ¬ logIndexSeparation

end MathlibExt.GroupTheory.FreeGroupLogIndexSeparationKourovka15Problem35Wanted
