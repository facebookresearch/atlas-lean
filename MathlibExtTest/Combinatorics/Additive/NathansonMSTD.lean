/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.NathansonMSTD

open scoped Pointwise
open MetaMathlibExt (nathanson_mstd_construction)

private def baseSet (m d k : ℤ) : Finset ℤ :=
  let B := (Finset.Icc 0 (m - 1)).erase d
  B ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
    B.image (fun b => (k + 1) * m - 2 * d - b)

/-- The larger `k` bound applies when the hole is the right endpoint. -/
example :
    let S := baseSet 4 3 4
    let A := insert 4 S
    (A - A).card < (A + A).card ∧ 8 ∈ A + A ∧ 8 ∉ S + S ∧ S - {4} ⊆ S - S :=
  nathanson_mstd_construction (m := 4) (d := 3) (k := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- A hole below the midpoint permits `k = 3`. -/
example :
    let A := insert 4 (baseSet 4 1 3)
    (A - A).card < (A + A).card :=
  (nathanson_mstd_construction (m := 4) (d := 1) (k := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).1
