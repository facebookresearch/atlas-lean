/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small cap-set and Roth numbers

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
the values below are taken from the "Known values" tables of
leansolving/SqueezeBench at commit e2e19eef093a77882da57f348def029533ec2d5e
(`SqueezeBench/Problems/CapSet/README.md` and
`SqueezeBench/Problems/Roth/README.md`; authors P. Manrique, H. Xia,
S. Szeider), distributed under the Apache License, Version 2.0. SqueezeBench
ships no `NOTICE` file. Changes made: SqueezeBench's `CapSet.f` and `Roth.f`
are Mathlib's `addRothNumber` on `Fin n → ZMod 3` and `rothNumberNat`, pinned
to `0` below `n = 1`; the statements use the Mathlib functions directly. The
values SqueezeBench marks as reporting only become Batteries `theorem_wanted`
declarations. The values SqueezeBench already checks by `decide`
(cap sets for `n ≤ 2`, Roth numbers for `n ≤ 4`) are omitted.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ZMod.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted

/-!
A cap in `F₃ⁿ` is a subset with no three distinct collinear points. Over
`ZMod 3` this is Mathlib's `ThreeAPFree`, so the maximum cap size in dimension
`n` is `addRothNumber (Finset.univ : Finset (Fin n → ZMod 3))` (OEIS A090245).
The Roth number `rothNumberNat n` is the largest size of a subset of
`{0, …, n - 1}` with no three-term arithmetic progression (OEIS A003002).
The asymptotic cap-set constant is the open problem
`OpenConjectures.Combinatorics.CapSetConstant`.
-/

/-- The largest cap in `F₃³` has `9` points.

Source: exhaustive search; OEIS A090245; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/CapSet/README.md`. -/
public theorem_wanted capSet_dim_three :
    addRothNumber (Finset.univ : Finset (Fin 3 → ZMod 3)) = 9

/-- The largest cap in `F₃⁴` has `20` points.

Source: G. Pellegrino, *Sul massimo ordine delle calotte in S₄,₃*, Matematiche
(Catania) 25 (1970), 149–157; OEIS A090245; listed in SqueezeBench
`SqueezeBench/Problems/CapSet/README.md`. -/
public theorem_wanted capSet_dim_four :
    addRothNumber (Finset.univ : Finset (Fin 4 → ZMod 3)) = 20

/-- The largest cap in `F₃⁵` has `45` points.

Source: Y. Edel, S. Ferret, I. Landjev, and L. Storme, *The classification of
the largest caps in AG(5,3)*, J. Combin. Theory Ser. A 99 (2002), 95–110;
OEIS A090245; listed in SqueezeBench `SqueezeBench/Problems/CapSet/README.md`. -/
public theorem_wanted capSet_dim_five :
    addRothNumber (Finset.univ : Finset (Fin 5 → ZMod 3)) = 45

/-- The largest cap in `F₃⁶` has `112` points.

Source: A. Potechin, *Maximal caps in AG(6,3)*, Des. Codes Cryptogr. 46
(2008), 243–259; OEIS A090245; listed in SqueezeBench
`SqueezeBench/Problems/CapSet/README.md`. -/
public theorem_wanted capSet_dim_six :
    addRothNumber (Finset.univ : Finset (Fin 6 → ZMod 3)) = 112

/-- Roth numbers `r₃(n)` for `5 ≤ n ≤ 14`: `4, 4, 4, 4, 5, 5, 6, 6, 7, 8`.

Source: OEIS A003002; listed in SqueezeBench
`SqueezeBench/Problems/Roth/README.md`. -/
public theorem_wanted rothNumberNat_five_to_fourteen :
    (List.range 10).map (fun i => rothNumberNat (i + 5)) = [4, 4, 4, 4, 5, 5, 6, 6, 7, 8]

end MathlibExt.Combinatorics.Additive.ThreeAPFreeValuesWanted
