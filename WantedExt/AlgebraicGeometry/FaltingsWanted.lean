/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Faltings' theorem (Mordell conjecture)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.AlgebraicGeometry.Faltings` — faltings (manifest `manifests/problems/faltings.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.FaltingsWanted` namespace. Mathematical
statements are unchanged. Source:
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.FaltingsWanted
/-!
# Faltings' theorem (Mordell conjecture)

This file defines basic objects associated to function fields of one variable following
[Stichtenoth] just enough to state Faltings' theorem.

The repository https://github.com/vaca22/riemann-roch-function-fields contains more
advanced development of the theory of function fields.

[Stichtenoth] Henning Stichtenoth, *Algebraic Function Fields and Codes*, Second Edition.
-/

namespace AlgebraicGeometry.Faltings

section ValuationSubalgebra

variable (R F : Type*) [CommSemiring R] [Field F] [Algebra R F]

@[ext] structure ValuationSubalgebra extends Subalgebra R F, ValuationSubring F

end ValuationSubalgebra

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

class BundledFunctionField extends
  Algebra (RatFunc K) F, IsScalarTower K (RatFunc K) F, FunctionField K F

/-- The type of places of a 1-dimensional function field. See [Stichtenoth,
Definition 1.1.4 and 1.1.8]. We omit the condition `toSubalgebra ≠ ⊥` since it is automatic. -/
@[ext] structure Place extends ValuationSubalgebra K F where
  ne_top : toSubalgebra ≠ ⊤

instance : SetLike (Place K F) F where
  coe v := v.carrier
  coe_injective _ _ := Place.ext

instance : SMulMemClass (Place K F) K F where
  smul_mem {v} r _ h := v.smul_mem h r

instance : SubringClass (Place K F) F where
  mul_mem {v} := v.mul_mem
  one_mem {v} := v.one_mem
  add_mem {v} := v.add_mem
  zero_mem {v} := v.zero_mem
  neg_mem {v} := v.toValuationSubring.neg_mem _

variable (v : Place K F)

instance : HasMemOrInvMem v where
  mem_or_inv_mem := v.mem_or_inv_mem'

instance : Algebra v F := inferInstanceAs (Algebra v.toSubalgebra F)
instance : IsScalarTower K v F := inferInstanceAs (IsScalarTower K v.toSubalgebra F)
instance : IsFractionRing v F := inferInstanceAs (IsFractionRing v.toValuationSubring F)
instance : ValuationRing v := inferInstanceAs (ValuationRing v.toValuationSubring)

variable {F}

/- [Stichtenoth, Corollary 1.3.4] (finitely many poles). -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted finite_setOf_place_notMem [BundledFunctionField K F] (x : F) :
    {v : Place K F | x ∉ v}.Finite

variable (F)

open scoped RestrictedProduct

/-- [Stichtenoth, Definition 1.5.2]. -/
abbrev Adele : Type _ :=
  RestrictedProduct (fun _ ↦ F) (fun v : Place K F ↦ (v : Set F)) Filter.cofinite

instance : CommRing (Adele K F) := RestrictedProduct.instCommRingCoeOfSubringClass ..

open RestrictedProduct

variable {F}

/- The principal adele associated to an element in the function field: the diagonal
embedding, well defined by finiteness of poles (`finite_setOf_place_notMem` above). It is
recorded as a hole because ordinary definitions cannot use a `theorem_wanted` in their
bodies; its coordinate formula is `Adele.principal_apply` below. -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public def_wanted Adele.principal [BundledFunctionField K F] : F →+* Adele K F

/- The coordinates of a principal adele are constant. -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted Adele.principal_apply [BundledFunctionField K F] (x : F)
    (v : Place K F) : (❰Adele.principal❱ K x) v = x

variable (F)

/-- The `F`-algebra structure on the adeles, specified by `instAlgebraAdele_algebraMap`
below to be the one whose algebra map is the principal embedding.
Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public instance_wanted instAlgebraAdele [BundledFunctionField K F] : Algebra F (Adele K F)

/-- The algebra map of the adele algebra is the principal embedding.
Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted instAlgebraAdele_algebraMap [BundledFunctionField K F] :
    algebraMap F (Adele K F) = ❰Adele.principal❱ K

-- TODO: generalize this to RestrictedProduct
instance : Algebra K (Adele K F) where
  __ := RestrictedProduct.instModuleCoeOfSMulMemClass ..
  algebraMap.toFun x := ⟨fun _ ↦ algebraMap K F x, .of_forall fun _ ↦ algebraMap_mem ..⟩
  algebraMap.map_one' := by ext; exact (algebraMap K F).map_one
  algebraMap.map_mul' _ _ := by ext; exact (algebraMap K F).map_mul ..
  algebraMap.map_add' _ _ := by ext; exact (algebraMap K F).map_add ..
  algebraMap.map_zero' := by ext; exact (algebraMap K F).map_zero
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := by ext; apply Algebra.smul_def

/-- The scalar tower for the adele algebra, whose algebra map is pinned to the principal
embedding by `instAlgebraAdele_algebraMap`.
Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public instance_wanted instIsScalarTowerAdele [BundledFunctionField K F] :
    IsScalarTower K F (Adele K F)

/-- The $K$-subspace $\mathcal{A}_F(0)$, see [Stichtenoth, Definition 1.5.3]. -/
def integralAdele : Submodule K (Adele K F) where
  carrier := {x | ∀ v, x v ∈ v}
  add_mem' h₁ h₂ v := add_mem (h₁ v) (h₂ v)
  zero_mem' _ := zero_mem _
  smul_mem' _ _ h v := v.smul_mem (h v) _

/- The genus of a function field, [Stichtenoth, Corollary 1.5.5]: defined by the finrank
formula in `genus_eq` below. The formula cannot be the body of an ordinary definition here
because it uses the wanted scalar-tower instance above, so the genus itself is recorded as a
hole of the same displayed type. -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public noncomputable def_wanted genus [BundledFunctionField K F] : ℕ

/- The genus is the finrank of the adele class quotient. -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted genus_eq [BundledFunctionField K F] :
    ❰genus❱ = Module.finrank K
      (Adele K F ⧸ integralAdele K F ⊔ (IsScalarTower.toAlgHom K F _).toLinearMap.range)

/- Every function field of genus at least 2 (equivalently, every curve of geometric genus
at least 2) over a number field has only finitely many rational points.
Note: if K is not the full constant field of F/K then there are no rational points, because
every place contains the full constant field. -/
/-- Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted faltings [NumberField K] [BundledFunctionField K F] :
    2 ≤ ❰genus❱ K F →
    {v : Place K F | Module.rank K (IsLocalRing.ResidueField v) = 1}.Finite

end AlgebraicGeometry.Faltings

end MathlibExt.AlgebraicGeometry.FaltingsWanted
