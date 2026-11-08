/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mazur's torsion theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.MazurTorsion` — mazur_torsion (manifest `manifests/problems/mazur_torsion.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.MazurTorsionWanted` namespace. Mathematical
statements are unchanged. Source: B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. IHÉS 47 (1977). Knill, *Some fundamental theorems in mathematics*, §139.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.MazurTorsionWanted
namespace NumberTheory.MazurTorsion

/-!
# Mazur's torsion theorem

`mazur_torsion` (Mazur 1977): the torsion subgroup of `E(ℚ)` for an elliptic
curve over `ℚ` is one of the fifteen groups `ℤ/n` (`n ∈ {1,…,10,12}`) or
`ℤ/2 × ℤ/2m` (`m ∈ {1,2,3,4}`). Trusted helper `IsInMazurClass` (non-hole).
Mathlib has Weierstrass curves and their point groups but not Mazur's theorem
(which rests on the geometry of the modular curves `X₁(N)`).
Category-(b) candidate from §139 of the Knill survey.
-/

open scoped WeierstrassCurve

/-- The **Mazur class**: isomorphic to `ℤ/n` (`n ∈ {1,…,10,12}`) or
`ℤ/2 × ℤ/2m` (`m ∈ {1,2,3,4}`). -/
def IsInMazurClass (T : Type*) [AddCommGroup T] : Prop :=
  (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty (T ≃+ ZMod n)) ∨
  (∃ m ∈ ({2, 4, 6, 8} : Finset ℕ),
      Nonempty (T ≃+ (ZMod 2 × ZMod m)))

/- **Mazur's torsion theorem.** The torsion subgroup of `E(ℚ)` lies in the
Mazur class. -/
/-- Source: B. Mazur, *Modular curves and the Eisenstein ideal*, Publ. IHÉS 47 (1977). Knill, *Some fundamental theorems in mathematics*, §139. Via leanprover/lean-eval@38361be, problem `mazur_torsion`. -/
public theorem_wanted mazur_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    IsInMazurClass ↥(AddCommGroup.torsion (WeierstrassCurve.Affine.Point E))

end NumberTheory.MazurTorsion

end MathlibExt.NumberTheory.MazurTorsionWanted
