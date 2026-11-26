/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Matroid.StrongMason

/-!
# Mason's conjecture: log-concavity of independent set numbers

K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of Math.
188 (2018), 381–452 (arXiv:1511.02888v2), Conjecture 1.2 and Theorem 9.9 (3): the numbers
`f_k(M)` of `k`-element independent sets of a matroid form a log-concave sequence (the
Welsh–Mason conjecture). The ultra log-concave strengthening is
`MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason.strong_mason_conjecture`,
proved in `MathlibExt.Combinatorics.Matroid.StrongMason`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.WeakMasonWanted

open MathlibExt.Combinatorics.StrongMasonWanted.Combinatorics.StrongMason

/-- **Log-concavity of the independent set numbers of a matroid** (Adiprasito, Huh and Katz,
*Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Theorem 9.9 (3),
answering Conjecture 1.2 of Welsh and Mason). For every finite matroid `M` and every `k ≥ 1`,
`f_{k-1}(M) f_{k+1}(M) ≤ f_k(M)^2`, where `f_k(M)` is the number of independent sets of size
`k`. (AHK state `1 ≤ k ≤ r`, where `r + 1` is the rank; for larger `k` the factor
`f_{k+1}(M)` vanishes, so the inequality is trivial.) -/
theorem_wanted independentSetCount_logConcave {α : Type*} (M : _root_.Matroid α) [M.Finite]
    (k : ℕ) (hk : 1 ≤ k) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) ≤ independentSetCount M k ^ 2

end MathlibExt.Combinatorics.WeakMasonWanted
