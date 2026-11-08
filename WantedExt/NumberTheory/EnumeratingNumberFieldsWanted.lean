/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Enumerating number fields

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.EnumeratingNumberFields` — annals_enumerating_number_fields (manifest `manifests/problems/annals_enumerating_number_fields.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.EnumeratingNumberFieldsWanted` namespace. Mathematical
statements are unchanged, except that `theorem_2` adds an explicit
`Finite (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H)` conjunct:
upstream's bare `Nat.card` bound is vacuous for an infinite type, while
finiteness is part of Couveignes' theorem. Source: J.-M. Couveignes, `Enumerating number fields`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-EnumeratingNumberFields.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.EnumeratingNumberFieldsWanted
/-!
# Main Statements from Enumerating number fields

We formalise the statements of the main results from J.-M. Couveignes,
`Enumerating number fields`, Annals of Math, 192 (2) 2020.
-/

set_option autoImplicit false

namespace EnumeratingNumberFields

open AlgebraicGeometry Module NumberField Real Scheme

section theorem_1

/-- The type of all number fields of degree `= n`. -/
structure NumberFieldOfDegree (n : ℕ) where
  /-- The elements of the number field. -/
  carrier : Type
  /-- The field structure of the number field. -/
  field : Field carrier
  numberField : NumberField carrier
  degree : finrank ℚ carrier = n

instance (n : ℕ) : CoeSort (NumberFieldOfDegree n) Type :=
  ⟨fun F ↦ F.carrier⟩

instance (n : ℕ) (F : NumberFieldOfDegree n) : Field F :=
  F.field

instance (n : ℕ) (F : NumberFieldOfDegree n) : NumberField F :=
  F.numberField

noncomputable section

variable {r : ℕ} (E : Fin r → MvPolynomial (Fin r) ℚ)

/-- The quotient ring `ℚ[x₁,…,xᵣ]/(E₁,…,Eᵣ)`. -/
def quotientRing : Type :=
  (MvPolynomial (Fin r) ℚ) ⧸ Ideal.span (Set.range E)
deriving CommRing, IsNoetherianRing

/-- The element `det (∂Eᵢ/∂xⱼ)` of the quotient ring `ℚ[x₁,…,xᵣ]/(E₁,…,Eᵣ)`. -/
def jacobian : quotientRing E :=
  Ideal.Quotient.mk _ <| Matrix.det <| fun i j ↦ MvPolynomial.pderiv j (E i)

/-- The open subscheme of `Spec ℚ[x₁,…,xᵣ]/(E₁,…,Eᵣ)` defined by `det (∂Eᵢ/∂xⱼ) ≠ 0`. -/
def nonsingularOpen : Scheme :=
  (Spec (.of (quotientRing E))).basicOpen <|
    (ΓSpecIso _).symm.commRingCatIsoToRingEquiv <| jacobian E
deriving IsAffine

set_option backward.isDefEq.respectTransparency false in
instance : IsNoetherian (nonsingularOpen E) := by
  rw [isNoetherian_iff]
  refine ⟨?_, (nonsingularOpen E).compactSpace_of_isAffine⟩
  suffices IsLocallyNoetherian (Spec (.of (quotientRing E))) from
    isLocallyNoetherian_of_isOpenImmersion (Opens.ι _)
  rw [isLocallyNoetherian_Spec]
  infer_instance

end

/--
Statement of Theorem 1 (Number fields have small models):

There exists a positive constant `Q` such that the following is true. Let `K` be a number field
of degree `n ≥ Q` and root discriminant `δ` over `ℚ`. Then there exist integers `r ≤ Q log n` and
`d ≤ Q log n` such that `(d + r) choose r ≤ Q n log n`, and there exist `r` polynomials
`E₁, ..., Eᵣ` of degree `≤ d` in `ℤ[x₁, ..., xᵣ]` all having coefficients bounded in absolute value
by `(n δ) ^ (Q log n)` such that the (smooth and zero-dimensional affine) scheme with equations
`E₁ = ... = Eᵣ = 0` and `det (∂Eᵢ/∂xⱼ) ≠ 0` contains `Spec K` as one of its irreducible components.
Source: J.-M. Couveignes, `Enumerating number fields`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-EnumeratingNumberFields.lean Via leanprover/lean-eval@38361be, problem `annals_enumerating_number_fields`.
-/
public theorem_wanted theorem_1 : ∃ Q > 0, ∀ n ≥ Q, ∀ K : NumberFieldOfDegree n, ∃ (r d : ℕ),
    r ≤ Q * log n ∧ d ≤ Q * log n ∧ (d + r).choose r ≤ Q * n * log n ∧
      ∃ E : Fin r → MvPolynomial (Fin r) ℤ, (∀ i, (E i).totalDegree ≤ d) ∧
        (∀ i j, |(E i).coeff j| ≤ (n * rootDiscr K) ^ (Q * log n)) ∧
          letI X := nonsingularOpen fun i ↦ (E i).map (algebraMap ℤ ℚ)
          ∃ Z, ∃ hZ : Z ∈ irreducibleComponents X,
            Nonempty (X.irreducibleComponent Z hZ ≅ Spec (.of K))

end theorem_1

section theorem_2

/-- The type of all number fields of degree `n` and discriminant `≤ H`. -/
structure NumberFieldOfBoundedDiscriminant (n H : ℕ) extends NumberFieldOfDegree n where
  discr : |discr carrier| ≤ H

instance (n H : ℕ) : CoeSort (NumberFieldOfBoundedDiscriminant n H) Type :=
  ⟨fun F ↦ F.carrier⟩

instance (n H : ℕ) (F : NumberFieldOfBoundedDiscriminant n H) : Field F :=
  F.field

/-- The relation of two number fields being isomorphic. -/
def NumberFieldOfBoundedDiscriminant.iso (n H : ℕ) (K L : NumberFieldOfBoundedDiscriminant n H) :=
  Nonempty (K ≃+* L)

/-- The type of all number fields of degree `n` and discriminant `≤ H`, up to isomorphism. -/
def NumberFieldOfBoundedDiscriminantUpToIsomorphism (n H : ℕ) :=
  Quot (NumberFieldOfBoundedDiscriminant.iso n H)

/--
Statement of Theorem 2 (Number fields with bounded discriminant):

There exists a positive constant `Q` such that the following is true. Let `n ≥ Q` be an integer.
Let `H ≥ 1` be an integer. The number of isomorphism classes of number fields
with degree `n` and discriminant `≤ H` is `≤ n^(Q n log^3 n) H^(Q log^3 n)`.
Source: J.-M. Couveignes, `Enumerating number fields`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-EnumeratingNumberFields.lean Via leanprover/lean-eval@38361be, problem `annals_enumerating_number_fields`.
-/
public theorem_wanted theorem_2 : ∃ Q > 0, ∀ n ≥ Q, ∀ H ≥ 1,
    Finite (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) ∧
    (Nat.card (NumberFieldOfBoundedDiscriminantUpToIsomorphism n H) : ℝ) ≤
      n ^ (Q * n * log n ^ 3) * H ^ (Q * log n ^ 3)

end theorem_2

end EnumeratingNumberFields

end MathlibExt.NumberTheory.EnumeratingNumberFieldsWanted
