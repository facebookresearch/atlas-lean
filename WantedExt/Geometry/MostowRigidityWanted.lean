/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Mostow rigidity

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.MostowRigidity` — mostow_rigidity (manifest `manifests/problems/mostow_rigidity.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.MostowRigidityWanted` namespace. Mathematical
statements are unchanged. Source: https://en.wikipedia.org/wiki/Mostow_rigidity_theorem#Algebraic_form and Gopal Prasad, *Strong rigidity of ℚ-rank 1 lattices*, Invent. Math. 21 (1973), 255–286.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.MostowRigidityWanted
/-!
# Mostow rigidity

A common form of Mostow's rigidity theorem says that two complete, finite-volume hyperbolic
manifolds of dimension at least three must be isometric if they have isomorphic fundamental
groups. Since the group of isometries of the hyperbolic space ℍⁿ is isomorphic to the
projective orthogonal group PO(n,1), this can be shown to be equivalent to the following
algebraic statement: two lattices (subgroups of finite covolume) in PO(n,1) with n ≥ 3 are
isomorphic iff they are conjugate in PO(n,1). In this file we define the group PO(n,1) and
state this algebraic form of Mostow rigidity.

References:
* https://en.wikipedia.org/wiki/Mostow_rigidity_theorem#Algebraic_form
* Riccardo Benedetti, Carlo Petronio. *Lectures on Hyperbolic Geometry*, Chapter C
  (proof of geometric form in compact case in 50 pages).
* Gopal Prasad, *Strong rigidity of ℚ-rank 1 lattices*, Invent. Math. 21 (1973), 255–286.
-/

namespace Geometry.MostowRigidity

universe u

variable (p q : Type u) (α : Type*)

def MatrixSum : Type _ := Matrix (p ⊕ q) (p ⊕ q) α

variable [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [Ring α]

instance : Ring (MatrixSum p q α) := inferInstanceAs (Ring (Matrix ..))

variable {p q α} in
def MatrixSum.ofMatrix : Matrix (p ⊕ q) (p ⊕ q) α ≃+* MatrixSum p q α := .refl _

variable {p q α} in
def pmOneMat : Matrix (p ⊕ q) (p ⊕ q) α := .fromBlocks 1 0 0 (-1)

theorem pmOneMat_mul_pmOneMat : pmOneMat * pmOneMat = (1 : Matrix (p ⊕ q) _ α) := by
  simp [pmOneMat, Matrix.fromBlocks_multiply]

open MatrixSum Matrix

section Star

variable [StarRing α]

omit [Fintype p] [Fintype q] in
@[simp] theorem conjTranspose_pmOneMat : (pmOneMat : Matrix (p ⊕ q) _ α)ᴴ = pmOneMat := by
  simp_rw [pmOneMat, conjTranspose, fromBlocks_transpose, fromBlocks_map]
  simp [Matrix.map_neg]

instance : StarRing (MatrixSum p q α) where
  star A := .ofMatrix (pmOneMat * (ofMatrix.symm A).conjTranspose * pmOneMat)
  star_involutive A := by
    simp [← mul_assoc pmOneMat, mul_assoc (ofMatrix.symm A), pmOneMat_mul_pmOneMat]
  star_mul A B := by
    conv_lhs => rw [map_mul _ A, conjTranspose_mul, ← mul_one _ᴴ, ← pmOneMat_mul_pmOneMat]
    simp [mul_assoc]
  star_add A B := by simp [add_mul, mul_add]

end Star

section Topology

variable [TopologicalSpace α]

instance : TopologicalSpace (MatrixSum p q α) := inferInstanceAs (TopologicalSpace (Matrix ..))

instance [T1Space α] : T1Space (MatrixSum p q α) := inferInstanceAs (T1Space (_ → _))

instance [LocallyCompactSpace α] : LocallyCompactSpace (MatrixSum p q α) :=
  inferInstanceAs (LocallyCompactSpace (_ → _))

@[fun_prop] theorem MatrixSum.continuous_ofMatrix : Continuous (@ofMatrix p q α _ _ _ _ _) :=
  continuous_id

@[fun_prop] theorem MatrixSum.continuous_ofMatrix_symm : Continuous (@ofMatrix p q α ..).symm :=
  continuous_id

variable [IsTopologicalRing α]

instance [Star α] [ContinuousStar α] : IsTopologicalRing (MatrixSum p q α) :=
  inferInstanceAs (IsTopologicalRing (Matrix ..))

variable [StarRing α] [ContinuousStar α]

instance : ContinuousStar (MatrixSum p q α) where
  continuous_star := by rw [star]; fun_prop

theorem MatrixSum.isClosed_unitary [T1Space α] :
    IsClosed (SetLike.coe <| unitary (MatrixSum p q α)) :=
  .inter (isClosed_singleton.preimage <| by fun_prop) (isClosed_singleton.preimage <| by fun_prop)

instance [T1Space α] [LocallyCompactSpace α] :
    LocallyCompactSpace (unitary (MatrixSum p q α)) :=
  (MatrixSum.isClosed_unitary ..).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : IsTopologicalGroup (unitary (MatrixSum p q α)) where
  continuous_inv := by simp_rw [Inv.inv, star]; fun_prop

end Topology

variable (p q : ℕ)

/-- `PO p q` is the projective indefinite orthogonal group PO(p,q) over the reals. -/
@[reducible]
def PO := unitary (MatrixSum (Fin p) (Fin q) ℝ) ⧸ Subgroup.center _

instance : MeasurableSpace (PO p q) := borel _
instance : BorelSpace (PO p q) := ⟨rfl⟩

open MeasureTheory

noncomputable instance : MeasureSpace (PO p q) := ⟨.haar⟩

end Geometry.MostowRigidity

namespace Geometry.MostowRigidity

open MeasureTheory

/-- Source: https://en.wikipedia.org/wiki/Mostow_rigidity_theorem#Algebraic_form and Gopal Prasad, *Strong rigidity of ℚ-rank 1 lattices*, Invent. Math. 21 (1973), 255–286. Via leanprover/lean-eval@38361be, problem `mostow_rigidity`. -/
public theorem_wanted mostow_rigidity (n : ℕ) (hn : 3 ≤ n) (Γ Λ : Subgroup (PO n 1))
    (disc_Γ : IsDiscrete (SetLike.coe Γ)) (disc_Λ : IsDiscrete (SetLike.coe Λ))
    [HasFundamentalDomain Γ (PO n 1)] [HasFundamentalDomain Λ (PO n 1)]
    (covol_Γ : covolume Γ (PO n 1) ≠ ⊤) (covol_Λ : covolume Λ (PO n 1) ≠ ⊤)
    (f : Γ ≃* Λ) : ∃ g : PO n 1, ∀ γ : Γ, f γ = g * γ * g⁻¹

end Geometry.MostowRigidity

end MathlibExt.Geometry.MostowRigidityWanted
