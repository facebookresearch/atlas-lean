/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hadwiger's theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ConvexGeometry.Hadwiger` — hadwiger (manifest `manifests/problems/hadwiger.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.HadwigerWanted` namespace. Mathematical
statements are unchanged. Source: H. Hadwiger (1937). Listed as §31 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.HadwigerWanted
namespace ConvexGeometry

/-!
# Hadwiger's theorem

§31 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. The real
vector space of continuous, rigid-motion-invariant valuations on convex
bodies in `ℝⁿ` has dimension `n + 1` (a basis being the intrinsic volumes,
the coefficients of the Steiner polynomial `Vol(K + tB)`).

mathlib has `ConvexBody V` with its Hausdorff `MetricSpace`, but no
valuations on convex bodies, no intrinsic volumes, and no Hadwiger's
theorem; a search found no formalization of it in any other proof assistant.
The problem defines the `IsValuation` predicate and the `valuations`
submodule.

The additivity clause is stated over four convex bodies `A B C D` with
`↑A = ↑C ∪ ↑D`, `↑B = ↑C ∩ ↑D`; when `C ∩ D` is empty no body `B` exists
and that case is dropped (mathlib's `ConvexBody` is nonempty).
-/

open scoped Classical

/-- The model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A continuous, rigid-motion-invariant, additive real valuation on the
convex bodies of `ℝⁿ`: continuity in the Hausdorff metric, inclusion–
exclusion additivity, and invariance under linear isometries and
translations. -/
def IsValuation {n : ℕ} (f : ConvexBody (E n) → ℝ) : Prop :=
  Continuous f ∧
  (∀ A B C D : ConvexBody (E n),
      (A : Set (E n)) = (C : Set (E n)) ∪ (D : Set (E n)) →
      (B : Set (E n)) = (C : Set (E n)) ∩ (D : Set (E n)) →
      f A + f B = f C + f D) ∧
  (∀ A B : ConvexBody (E n), ∀ e : E n ≃ₗᵢ[ℝ] E n,
      (B : Set (E n)) = e '' (A : Set (E n)) → f B = f A) ∧
  (∀ A B : ConvexBody (E n), ∀ t : E n,
      (B : Set (E n)) = (· + t) '' (A : Set (E n)) → f A = f B)

/-- The valuations form an `ℝ`-subspace of `ConvexBody ℝⁿ → ℝ`. -/
noncomputable def valuations (n : ℕ) : Submodule ℝ (ConvexBody (E n) → ℝ) where
  carrier := {f | IsValuation f}
  add_mem' := by
    rintro f g ⟨hfc, hfa, hfi, hft⟩ ⟨hgc, hga, hgi, hgt⟩
    refine ⟨hfc.add hgc, fun A B C D hU hI => ?_, fun A B e hB => ?_, fun A B t hB => ?_⟩
    · have h₁ := hfa A B C D hU hI
      have h₂ := hga A B C D hU hI
      simp only [Pi.add_apply]
      linarith
    · simp only [Pi.add_apply, hfi A B e hB, hgi A B e hB]
    · simp only [Pi.add_apply, hft A B t hB, hgt A B t hB]
  zero_mem' :=
    ⟨continuous_zero, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨hfc, hfa, hfi, hft⟩
    refine ⟨hfc.const_smul c, fun A B C D hU hI => ?_, fun A B e hB => ?_, fun A B t hB => ?_⟩
    · have h := hfa A B C D hU hI
      simp only [Pi.smul_apply]
      rw [← smul_add, ← smul_add, h]
    · simp only [Pi.smul_apply, hfi A B e hB]
    · simp only [Pi.smul_apply, hft A B t hB]

/- **Hadwiger's theorem.** The space of continuous rigid-motion-invariant
valuations on convex bodies in `ℝⁿ` is `(n+1)`-dimensional. -/
/-- Source: H. Hadwiger (1937). Listed as §31 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `hadwiger`. -/
public theorem_wanted hadwiger (n : ℕ) : Module.finrank ℝ (valuations n) = n + 1

end ConvexGeometry

end MathlibExt.Geometry.HadwigerWanted
