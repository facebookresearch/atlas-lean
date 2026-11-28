/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientInversePsiThreeDissection
public import MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientSixNineIdentity
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer

namespace MetaMathlibExt

@[expose] public section

/-- **Liang's congruences modulo 512 for overpartitions.** For all natural numbers $\alpha$ and $n$,
the number $\overline{p}(m)$ of overpartitions of $m$ satisfies
$\overline{p}(3^{8\alpha+7}(24n+5)) \equiv 0 \pmod{512}$ and
$\overline{p}(3^{8\alpha+7}(24n+13)) \equiv 0 \pmod{512}$.

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Theorem 1 (`integers-2025-A76-thm-1`). -/
public theorem_wanted overpartition_three_pow_congr_zero_mod_512 (α n : ℕ) :
    512 ∣ Nat.card (Nat.Overpartition (3 ^ (8 * α + 7) * (24 * n + 5))) ∧
      512 ∣ Nat.card (Nat.Overpartition (3 ^ (8 * α + 7) * (24 * n + 13)))

end

end MetaMathlibExt
