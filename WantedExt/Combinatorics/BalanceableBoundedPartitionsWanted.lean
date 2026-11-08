/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Balanceable k-bounded partitions

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.BalanceableBoundedPartitions` — balanceable_bounded_partitions (manifest `manifests/problems/balanceable_bounded_partitions.toml`, rev 1, submitter Julia M. Himmel, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.BalanceableBoundedPartitionsWanted` namespace. Mathematical
statements are unchanged. Source: https://projecteuler.net/problem=772
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.GCDMonoid.Finset

@[expose] public section

namespace MathlibExt.Combinatorics.BalanceableBoundedPartitionsWanted
namespace Combinatorics

/--
A partition is `k`-bounded if all of its members are at most `k`.

For example, `12 = 3 + 2 + 2 + 2 + 2 + 1` is a `3`-bounded partition
of `12`.
-/
def Bounded {n : ℕ} (k : ℕ) (p : n.Partition) : Prop :=
  ∀ i ∈ p.parts, i ≤ k

/--
A partition is balanceable if it can be decomposed into two multisets of
the same size.

For example, `12 = (3 + 2 + 1) + (2 + 2 + 2)` is a balanceable partition
of `12`.
-/
def Balanceable {n : ℕ} (p : n.Partition) : Prop :=
  ∃ s₁ s₂, s₁ + s₂ = p.parts ∧ s₁.sum = s₂.sum

/--
For any `k`, the smallest `n` such that any `k`-bounded partition of `n` is
also balanceable is given by `2 * lcm(1, ..., k)`.
Source: https://projecteuler.net/problem=772 Via leanprover/lean-eval@38361be, problem `balanceable_bounded_partitions`.
-/
public theorem_wanted minimal_balanceable_of_bounded (k : ℕ) (hk : 0 < k) :
    Minimal (fun n => 0 < n ∧ ∀ p : n.Partition, Bounded k p → Balanceable p) (2 * (Finset.Icc 1 k).lcm id)

end Combinatorics

end MathlibExt.Combinatorics.BalanceableBoundedPartitionsWanted
