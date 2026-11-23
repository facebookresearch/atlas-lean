/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Batteries.Util.ProofWanted
import MathlibExt.NumberTheory.CoveringSystem

/-!
# Covering systems with arbitrarily large distinct moduli

Open Garden problem OPG-493 asks whether, for every lower bound `N`, the
integers admit a finite covering by residue classes with pairwise distinct
moduli, all at least `N`.
-/

namespace MathlibExt.NumberTheory.LargeModulusCoveringSystemsWanted

/-- **Covering systems with arbitrarily large distinct moduli (OPG-493).** The statement that
for every natural number $N$ there are finitely many residue classes $a_1 \bmod m_1, \dots,
a_k \bmod m_k$ that cover $\mathbb{Z}$ (every integer lies in at least one of them) whose moduli
are pairwise distinct and all at least $N$. -/
def conjecture : Prop :=
  ∀ N : ℕ, ∃ classes : Finset (ℤ × ℕ),
    Int.IsCoveringSystem classes ∧
      (∀ c ∈ classes, N ≤ c.2) ∧
      ∀ c₁ ∈ classes, ∀ c₂ ∈ classes, c₁.2 = c₂.2 → c₁ = c₂

/--
**Hough's minimum modulus theorem.** There is a natural number $N$ such that no finite set of
residue classes covering $\mathbb{Z}$ has pairwise distinct moduli that are all at least $N$.
Hence the conjecture of Open Garden problem OPG-493 is false.

Source: Bob Hough, Solution of the minimum modulus problem for covering systems, Annals of
Mathematics 181 (2015), 361-382; arXiv:1307.0874, https://arxiv.org/abs/1307.0874. Moved from
`OpenConjectures/NumberTheory/LargeModulusCoveringSystems`.
-/
theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.LargeModulusCoveringSystemsWanted
