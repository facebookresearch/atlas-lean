/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A competition programming problem about permuting a permutation to be unimodal

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ProgramVerification.PermuteToUnimodal` — permute_to_unimodal (manifest `manifests/problems/permute_to_unimodal.toml`, rev 1, submitter Julia M. Himmel, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.TheoryOfComputation.PermuteToUnimodalWanted` namespace. Mathematical
statements are unchanged. Source: NWERC 2025 Problem G, see https://2025.nwerc.eu/problem-set.pdf
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.TheoryOfComputation.PermuteToUnimodalWanted
namespace ProgramVerification

/-!
Given an array `arr` which is a permutation of the numbers from `1` to `arr.size`,
`minRearrange` computes the size of the smallest subset of indices within the array
that may be permuted such that the array becomes first increasing and then decreasing.
For example, `minRearrange #[1, 6, 4, 3, 2, 5] = 2` since we can swap the first and
the last element to achieve the desired property.

The given efficient implementation computes the answer in `O(n log n)`.

Examples:
* `minRearrange #[] = 0`
* `minRearrange #[1, 6, 4, 3, 2, 5] = 2`
* `minRearrange #[4, 3, 2, 1, 5] = 4`
* `minRearrange #[1, 2, 4, 3] = 0`
* `minRearrange #[1, 2, 7, 4, 5, 6, 3, 8, 9, 10] = 2`
-/

def minRearrange (arr : Array Nat) : Nat :=
  let n := arr.size
  let v :=
    (arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map (fun (a, i) => (2 * i + 1, 2 * (a - i - 1))) ++
    (arr.zipIdx.filter (fun (a, i) => n ≤ a + i)).map (fun (a, i) => (2 * (a + i - n), 2 * (n - i) - 1))
  let vv := (v.toList.mergeSort (le := fun a b => a = b ∨ Prod.Lex (· < ·) (· < ·) a b)).toArray
  n - lis (vv.map (·.2))
where
  lis (arr : Array Nat) : Nat :=
    if h : arr = #[] then
      0
    else
      let dp := Array.replicate arr.size (arr.max h + 1)
      loop arr 0 0 dp (by grind)
  loop (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) : Nat :=
    if hi' : i = arr.size then
      ans
    else
      let pos := upperBound arr[i] dp
      loop arr (max ans (pos + 1)) (i + 1) (dp.set! pos (arr[i])) (by grind)
  upperBound (needle : Nat) (arr : Array Nat) : Nat :=
    go needle arr 0 arr.size
  go (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size := by omega) : Nat :=
    if h : lo < hi then
      let mid := lo + (hi - lo) / 2
      if arr[mid] ≤ needle then
        go needle arr (mid + 1) hi
      else
        go needle arr lo mid
    else lo

/--
Property stating that the array can be decomposed into a strictly increasing and a strictly
decreasing part.
-/
def Unimodal (arr : Array Nat) : Prop :=
  ∃ b b', arr = b ++ b' ∧ b.toList.Pairwise (· < ·) ∧ b'.toList.Pairwise (· > ·)

/--
The number of indices at which the two given vectors differ
-/
def differences {n : Nat} (a b : Vector Nat n) : Nat :=
  (List.finRange n).filter (fun i => a[i] ≠ b[i]) |>.length

/--
`minRearrange` correctly computes the smallest number of indices that need to be permuted in order to
turn `arr` into a unimodal permutation.
Source: NWERC 2025 Problem G, see https://2025.nwerc.eu/problem-set.pdf Via leanprover/lean-eval@38361be, problem `permute_to_unimodal`.
-/
public theorem_wanted minRearrange_correct {arr : Array Nat} :
    arr.Perm (1...=arr.size).toArray →
      (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector = minRearrange arr) ∧
      (∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x → minRearrange arr ≤ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector)

end ProgramVerification

end MathlibExt.TheoryOfComputation.PermuteToUnimodalWanted
