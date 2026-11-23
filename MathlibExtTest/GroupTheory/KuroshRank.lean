/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumers reproduce the theorem types from
`Theorems/Thm_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean` and
`Theorems/Thm_Monoid_CoprodI_isTree_cosetGraph.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.GroupTheory.KuroshRank

@[expose] public section

private theorem exactSource {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ (i : Fin 2) (g : Monoid.CoprodI G) (x : G i),
      g⁻¹ * Monoid.CoprodI.of x * g ∈ H → x = 1) :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - H.index / Nat.card (G 0) - H.index / Nat.card (G 1))) H) :=
  Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank H hH

theorem exactSourceIsTree {G : Fin 2 → Type*} [∀ i, Group (G i)] :
    (SimpleGraph.fromRel fun v w : (i : Fin 2) ×
        (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range) =>
        v.1 ≠ w.1 ∧ ∃ g : Monoid.CoprodI G,
          v.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸
            (Monoid.CoprodI.of (M := G) (i := v.1)).range) ∧
          w.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸
            (Monoid.CoprodI.of (M := G) (i := w.1)).range)).IsTree :=
  Monoid.CoprodI.isTree_cosetGraph

/-- The rank formula in a higher universe. -/
private theorem exactSourceTypeOne {G : Fin 2 → Type 1} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ (i : Fin 2) (g : Monoid.CoprodI G) (x : G i),
      g⁻¹ * Monoid.CoprodI.of x * g ∈ H → x = 1) :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - H.index / Nat.card (G 0) - H.index / Nat.card (G 1))) H) :=
  Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank H hH
