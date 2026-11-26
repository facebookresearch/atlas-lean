/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean`
and
`P2M/Sol/S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.AbsoluteValue.Equivalence

@[expose] public section

namespace AbsoluteValue

/-- **Weak approximation for absolute values.** Let $K$ be a field and let
$(v_i)_{i \in \iota}$ be a finite family of absolute values $v_i : K \to \mathbb R$, each
nontrivial ($v_i(y) \ne 1$ for some nonzero $y \in K$), that are pairwise inequivalent: for
$i \ne j$, $v_i$ and $v_j$ are not equivalent, where $v$ and $w$ are equivalent when
$v(x) \le v(y) \iff w(x) \le w(y)$ for all $x, y \in K$. Then for every family
$(a_i)_{i \in \iota}$ of elements of $K$ and every real $\varepsilon > 0$ there is $x \in K$
with $v_i(x - a_i) < \varepsilon$ for every $i \in \iota$.

This is the $\varepsilon$-form of `AbsoluteValue.denseRange_algebraMap_pi`: the diagonal image of
$K$ is dense in the product over $i$ of $K$ with the topology of $v_i$. -/
public theorem exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K]
    {ι : Type*} [Finite ι] {v : ι → AbsoluteValue K ℝ}
    (hv : ∀ i, (v i).IsNontrivial)
    (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, ∀ i, v i (x - a i) < ε := by
  have := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ := Metric.denseRange_iff.mp (denseRange_algebraMap_pi hv hne)
    (fun i => WithAbs.toAbs (v i) (a i)) ε hε
  refine ⟨x, fun i => ?_⟩
  have hi : dist (WithAbs.toAbs (v i) (a i)) (WithAbs.toAbs (v i) x) < ε :=
    (dist_le_pi_dist _ (algebraMap K ((i : ι) → WithAbs (v i)) x) i).trans_lt hx
  rwa [dist_comm, dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at hi

end AbsoluteValue
