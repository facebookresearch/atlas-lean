/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzGlobalDecrease

/-! # Weighted Weyl normal form over the finite torus

For `n : ℕ` and `[Field F]`, a coefficient-carrying Weyl word `wc` whose label
projection has permutation product one factors head-left as
`weightedWeylProd wc = c * t`, with `c` in `torusCocycleSubgroup` and `t` in
`finiteTorusSubgroup n`.

The proof is induction on the word length via `Nat.strongRecOn`, with the
motive generalized over both the length `m` and the paired word. The empty
projection gives `wc = []` and witnesses `1, 1`. Otherwise the global
strict-decrease step shortens the word by exactly two letters while exposing
one cocycle defect and one transported torus residual; the induction hypothesis
splits the shortened word, defects combine as `c * c'`, torus factors combine
as `t' * T`, and the product equation closes by rewriting with the induction
hypothesis and reassociating multiplication. No centrality is needed. The
empty case covers ranks `n = 0, 1` with no nonempty hypothesis.

Nonclaims: this is only the normal-form induction; no kernel generation,
finite-stage/`List.ofFn` bridge, inverse identity, naturality, TWT, or
Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

variable {F : Type u} [Field F]

/-- Weighted Weyl normal form over the finite torus.

Purpose: factor the head-left product of a coefficient-carrying Weyl word
whose label projection has permutation product one as `c * t`, with `c` in
the torus cocycle subgroup and `t` in the rank-`n` finite torus subgroup.
Orientation is head-left throughout, matching `weightedWeylProd`.
Hypotheses: `[Field F]` only, a paired word `wc`, and product one of its
label projection. The factors are existential.

Nonclaims: normal form only; no kernel generation, finite-stage/`List.ofFn`
bridge, inverse identity, naturality, TWT, or Matsumoto claim. -/
public theorem weightedWeylProd_mem_torusCocycle_mul_finiteTorus
    {n : ℕ} (wc : List (SwapLabel n × Fˣ))
    (hprod : wordProd (wc.map Prod.fst) = 1) :
    ∃ c t : StableSteinberg F,
      c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
      t ∈ StableSteinberg.finiteTorusSubgroup (R := F) n ∧
      weightedWeylProd wc = c * t := by
  suffices key : ∀ (m : ℕ) (wc : List (SwapLabel n × Fˣ)),
      wc.length = m → wordProd (wc.map Prod.fst) = 1 →
      ∃ c t : StableSteinberg F,
        c ∈ StableSteinberg.torusCocycleSubgroup (F := F) ∧
        t ∈ StableSteinberg.finiteTorusSubgroup (R := F) n ∧
        weightedWeylProd wc = c * t from
    key wc.length wc rfl hprod
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro wc hlen hprod
    by_cases hempty : wc.map Prod.fst = []
    · have hwc : wc = [] := List.map_eq_nil_iff.mp hempty
      subst hwc
      refine ⟨1, 1, Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
      simp only [weightedWeylProd, List.map_nil, List.prod_nil, mul_one]
    · obtain ⟨wcShort, c, a', r', hprodShort, hlenDrop, hc, hmem, hstep⟩ :=
        exists_weighted_hurwitz_global_strict_decrease wc hempty hprod
      have hlt : wcShort.length < m := by omega
      obtain ⟨c', t', hc', ht', hIH⟩ :=
        ih wcShort.length hlt wcShort rfl hprodShort
      refine ⟨c * c', t' * StableSteinberg.torus (R := F) a'.val.1.val
        a'.val.2.val (fun h => a'.property (Fin.ext h)) r',
        Subgroup.mul_mem _ hc hc', Subgroup.mul_mem _ ht' hmem, ?_⟩
      rw [hstep, hIH]
      simp only [mul_assoc]

end AlgebraicKTheory

end
