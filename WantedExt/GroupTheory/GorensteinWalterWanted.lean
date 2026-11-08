/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gorenstein–Walter theorem (dihedral Sylow 2-subgroup)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.GroupTheory.GorensteinWalter` — gorenstein_walter (manifest `manifests/problems/gorenstein_walter.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.GorensteinWalterWanted` namespace. Mathematical
statements are unchanged. Source: D. Gorenstein and J. H. Walter, The characterization of finite groups with dihedral Sylow 2-subgroups, J. Algebra 2 (1965), 85-151, 218-270, 354-393. https://doi.org/10.1016/0021-8693(65)90027-X
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

@[expose] public section

namespace MathlibExt.GroupTheory.GorensteinWalterWanted
namespace GroupTheory

open scoped MatrixGroups

/-!
# Gorenstein–Walter theorem (dihedral Sylow 2-subgroup)

Let `G` be a finite nonabelian simple group whose Sylow 2-subgroups are
dihedral. Then `G` is isomorphic to either:

* `PSL₂(q)` for some odd prime power `q ≥ 5`, or
* the alternating group `A₇`.

D. Gorenstein and J. H. Walter, "The characterization of finite groups
with dihedral Sylow 2-subgroups", J. Algebra 2 (1965); a famously long
paper, the first major application of the Bender method in CFSG.

The conclusion is captured in two clauses:
* `Nonempty (G ≃* alternatingGroup (Fin 7))`, or
* an existential over a prime `p`, an exponent `k`, and an isomorphism
  `G ≃* PSL(2, GaloisField p k)` with `p` odd and `p^k ≥ 5`.

Since `GaloisField p k` requires the typeclass `Fact p.Prime`, the
existential binds a `Fact p.Prime` term directly (rather than the bare
`p.Prime`), so the typeclass is available where `GaloisField` is used.
-/

/- **Gorenstein–Walter theorem.** -/
/-- Source: D. Gorenstein and J. H. Walter, The characterization of finite groups with dihedral Sylow 2-subgroups, J. Algebra 2 (1965), 85-151, 218-270, 354-393. https://doi.org/10.1016/0021-8693(65)90027-X Via leanprover/lean-eval@38361be, problem `gorenstein_walter`. -/
public theorem_wanted gorenstein_walter
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      (letI := _hp; Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))

end GroupTheory

end MathlibExt.GroupTheory.GorensteinWalterWanted
