/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.UpperDensitySumsetPartition

namespace MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted

open Set
open scoped Pointwise

-- The even numbers form a proper subset whose sumset has density one half.
example : ∃ S T : Set ℕ, Disjoint S T ∧ S ∪ T = {n | Even n} ∧
    0 < (S + S).upperDensity ∧ 0 < (T + T).upperDensity := by
  let E : Set ℕ := {n | Even n}
  apply upperDensitySumsetSplits_holds E
  have hadd : E + E = E := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Even.add hx hy
    · exact fun x hx ↦ ⟨x, hx, 0, ⟨0, rfl⟩, Nat.add_zero _⟩
  have hd : E.upperDensity = 1 / 2 := Nat.hasDensity_even.limsup_eq
  rw [hadd, hd]
  norm_num

-- A finite set cannot satisfy the positive-upper-density hypothesis.
example {A : Set ℕ} (hA : A.Finite) : (A + A).upperDensity = 0 := by
  exact (Nat.hasDensity_zero_of_finite (hA.add hA)).limsup_eq

end MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted
