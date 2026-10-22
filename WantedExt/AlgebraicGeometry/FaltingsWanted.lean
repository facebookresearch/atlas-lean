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

/-- **Place.** Let $F$ be a field and $K$ a field with $F$ a $K$-algebra. A place of $F/K$ is a
valuation ring of $F$ containing $K$ and different from $F$: a $K$-subalgebra $\mathcal{O}$ of
$F$ with $\mathcal{O} \neq F$ such that $z \in \mathcal{O}$ or $z^{-1} \in \mathcal{O}$ for
every $z \in F$. See [Stichtenoth, Definition 1.1.4 and 1.1.8].

Stichtenoth calls the maximal ideal of $\mathcal{O}$ the place, which determines $\mathcal{O}$,
and also requires $\mathcal{O} \neq K$; that condition is omitted since it is automatic. -/
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
/-- **Finitely many poles.** Let $F$ be a function field over a field $K$, that is, a finite
extension of the rational function field $K(t)$. For every $x \in F$, there are only finitely
many places $P$ of $F/K$ whose valuation ring $\mathcal{O}_P$ does not contain $x$, that is,
$x$ has only finitely many poles. See [Stichtenoth, Corollary 1.3.4].

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted finite_setOf_place_notMem [BundledFunctionField K F] (x : F) :
    {v : Place K F | x ∉ v}.Finite

variable (F)

open scoped RestrictedProduct

/-- **Adele ring.** Let $F$ be a field and $K$ a field with $F$ a $K$-algebra. The adele ring
$\mathcal{A}_F$ of $F/K$ is the restricted product of copies of $F$ indexed by the places $P$
of $F/K$, with respect to their valuation rings $\mathcal{O}_P$ and the cofinite filter: its
elements are the families $\alpha = (\alpha_P)_P$ with $\alpha_P \in F$ for every place $P$
and $\alpha_P \in \mathcal{O}_P$ for all but finitely many $P$. See [Stichtenoth, Definition
1.5.2]. -/
abbrev Adele : Type _ :=
  RestrictedProduct (fun _ ↦ F) (fun v : Place K F ↦ (v : Set F)) Filter.cofinite

instance : CommRing (Adele K F) := RestrictedProduct.instCommRingCoeOfSubringClass ..

open RestrictedProduct

variable {F}

/- The principal adele associated to an element in the function field: the diagonal
embedding, well defined by finiteness of poles (`finite_setOf_place_notMem` above). It is
recorded as a hole because ordinary definitions cannot use a `theorem_wanted` in their
bodies; its coordinate formula is `Adele.principal_apply` below. -/
/-- **Principal adele map.** Let $F$ be a function field over a field $K$, that is, a finite
extension of the rational function field $K(t)$. The principal adele map is a ring homomorphism
from $F$ to the adele ring $\mathcal{A}_F$ of $F/K$. It is meant to be the diagonal embedding
sending $x \in F$ to the adele whose coordinate at every place $P$ of $F/K$ is $x$, which is
well defined since $x$ has only finitely many poles; this coordinate formula is stated
separately.

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public def_wanted Adele.principal [BundledFunctionField K F] : F →+* Adele K F

/- The coordinates of a principal adele are constant. -/
/-- **Coordinates of a principal adele.** Let $F$ be a function field over a field $K$, that is,
a finite extension of the rational function field $K(t)$. For every $x \in F$ and every place
$P$ of $F/K$, the coordinate at $P$ of the principal adele of $x$ is $x$.

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted Adele.principal_apply [BundledFunctionField K F] (x : F)
    (v : Place K F) : (❰Adele.principal❱ K x) v = x

variable (F)

/-- The `F`-algebra structure on the adeles, specified by `instAlgebraAdele_algebraMap`
below to be the one whose algebra map is the principal embedding.
Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public instance_wanted instAlgebraAdele [BundledFunctionField K F] : Algebra F (Adele K F)

/-- **The adele algebra map is the principal embedding.** Let $F$ be a function field over a
field $K$, that is, a finite extension of the rational function field $K(t)$. The algebra map
$F \to \mathcal{A}_F$ of the $F$-algebra structure on the adele ring $\mathcal{A}_F$ equals the
principal adele map $F \to \mathcal{A}_F$.

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

/-- **Integral adeles.** Let $F$ be a field and $K$ a field with $F$ a $K$-algebra. The integral
adeles $\mathcal{A}_F(0)$ form the $K$-subspace of the adele ring $\mathcal{A}_F$ of $F/K$
consisting of the adeles $\alpha = (\alpha_P)_P$ whose coordinate $\alpha_P$ lies in the
valuation ring $\mathcal{O}_P$ of $P$ for every place $P$ of $F/K$. See [Stichtenoth,
Definition 1.5.3]. -/
def integralAdele : Submodule K (Adele K F) where
  carrier := {x | ∀ v, x v ∈ v}
  add_mem' h₁ h₂ v := add_mem (h₁ v) (h₂ v)
  zero_mem' _ := zero_mem _
  smul_mem' _ _ h v := v.smul_mem (h v) _

/- The genus of a function field, [Stichtenoth, Corollary 1.5.5]: defined by the finrank
formula in `genus_eq` below. The formula cannot be the body of an ordinary definition here
because it uses the wanted scalar-tower instance above, so the genus itself is recorded as a
hole of the same displayed type. -/
/-- **Genus of a function field.** For a function field $F$ over a field $K$, that is, a finite
extension of the rational function field $K(t)$, the genus of $F/K$ is a natural number $g$,
specified by the separately stated formula $g = \dim_K \mathcal{A}_F / (\mathcal{A}_F(0) + F)$,
where $\mathcal{A}_F$ is the adele ring and $\mathcal{A}_F(0)$ the integral adeles.
See [Stichtenoth, Corollary 1.5.5].

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public noncomputable def_wanted genus [BundledFunctionField K F] : ℕ

/- The genus is the finrank of the adele class quotient. -/
/-- **Genus as the dimension of the adele class space.** Let $F$ be a function field over a
field $K$, that is, a finite extension of the rational function field $K(t)$. The genus $g$ of
$F/K$ equals the dimension over $K$ of the quotient
$\mathcal{A}_F / (\mathcal{A}_F(0) + F)$, where $\mathcal{A}_F$ is the adele ring,
$\mathcal{A}_F(0)$ the integral adeles, and $F$ is embedded in $\mathcal{A}_F$ by the algebra
map of the $F$-algebra structure on the adeles (stated separately to be the principal
embedding). See [Stichtenoth, Corollary 1.5.5].

The dimension is the finite rank, taken to be $0$ if the quotient is infinite-dimensional.

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted genus_eq [BundledFunctionField K F] :
    ❰genus❱ = Module.finrank K
      (Adele K F ⧸ integralAdele K F ⊔ (IsScalarTower.toAlgHom K F _).toLinearMap.range)

/- Every function field of genus at least 2 (equivalently, every curve of geometric genus
at least 2) over a number field has only finitely many rational points.
Note: if K is not the full constant field of F/K then there are no rational points, because
every place contains the full constant field. -/
/-- **Faltings' theorem (Mordell conjecture).** Let $K$ be a number field and $F$ a function
field over $K$, that is, a finite extension of the rational function field $K(t)$. If the genus
of $F/K$ is at least $2$, then $F/K$ has only finitely many places of degree one, that is,
places $P$ whose residue field (the quotient of the valuation ring of $P$ by its maximal ideal)
has dimension $1$ over $K$.

Source: see manifest Via leanprover/lean-eval@38361be, problem `faltings`. -/
public theorem_wanted faltings [NumberField K] [BundledFunctionField K F] :
    2 ≤ ❰genus❱ K F →
    {v : Place K F | Module.rank K (IsLocalRing.ResidueField v) = 1}.Finite

end AlgebraicGeometry.Faltings

end MathlibExt.AlgebraicGeometry.FaltingsWanted
