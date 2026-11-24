/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CuspForm_PrimitiveFormGamma1.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import MathlibExt.NumberTheory.ModularForms.CuspFormConj

@[expose] public section

open CongruenceSubgroup ModularFormClass UpperHalfPlane

open scoped MatrixGroups

namespace CuspForm

variable {M : ℕ} {k : ℤ}

/-- A cusp form has nebentypus `ε` when it transforms under `Gamma0 M` by
the character evaluated at the lower-right entry. -/
public def HasNebentypus (ε : DirichletCharacter ℂ M)
    (g : CuspForm (Gamma1 M) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
    g (γ • τ) =
      ε ((γ 1 1 : ℤ) : ZMod M) *
        ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ)

/-- A cusp form is an eigenform with nebentypus `ε` when its first
Fourier coefficient is `1`, its coefficients satisfy the Hecke
recurrences away from and at the level, and it has nebentypus `ε`. -/
public def IsEigenformWith (ε : DirichletCharacter ℂ M)
    (g : CuspForm (Gamma1 M) k) : Prop :=
  qCoeff g 1 = 1 ∧
  (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ,
    qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n) ∧
  HasNebentypus ε g

/-- The eigenvalue packet of an eigenform occurs at level `M'` when some
eigenform at that level has the same Hecke eigenvalues away from a finite
set of primes. -/
public def EigenpacketOccursAt (k : ℤ) (a e : ℕ → ℂ) (M' : ℕ) : Prop :=
  ∃ (ε' : DirichletCharacter ℂ M') (h : CuspForm (Gamma1 M') k),
    h ≠ 0 ∧ HasNebentypus ε' h ∧
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ε' (p : ZMod M') = e p ∧
      ∀ n : ℕ,
        qCoeff h (p * n) +
            ε' (p : ZMod M') * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then qCoeff h (n / p) else 0) =
          a p * qCoeff h n

/-- A cusp form is primitive when it is an eigenform whose eigenvalue
packet does not occur at any proper divisor of its level. -/
public def IsPrimitiveForm (ε : DirichletCharacter ℂ M)
    (g : CuspForm (Gamma1 M) k) : Prop :=
  IsEigenformWith ε g ∧
    ∀ M' : ℕ, M' ∣ M → M' ≠ M →
      ¬ EigenpacketOccursAt k (fun n => qCoeff g n)
        (fun n => ε (n : ZMod M)) M'

/-- The first Fourier coefficient of an eigenform is `1`. -/
public theorem IsEigenformWith.qCoeff_one {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsEigenformWith ε g) :
    qCoeff g 1 = 1 :=
  h.1

/-- The Hecke recurrence away from the level for an eigenform. -/
public theorem IsEigenformWith.hecke_of_not_dvd {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsEigenformWith ε g) {p : ℕ}
    (hp : p.Prime) (hpM : ¬ p ∣ M) (n : ℕ) :
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n :=
  h.2.1 p hp hpM n

/-- The Hecke recurrence at the level for an eigenform. -/
public theorem IsEigenformWith.hecke_of_dvd {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsEigenformWith ε g) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (n : ℕ) :
    qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n :=
  h.2.2.1 ℓ hℓ hℓM n

/-- An eigenform has its stated nebentypus. -/
public theorem IsEigenformWith.hasNebentypus {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsEigenformWith ε g) :
    HasNebentypus ε g :=
  h.2.2.2

/-- A primitive form is an eigenform. -/
public theorem IsPrimitiveForm.isEigenformWith {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsPrimitiveForm ε g) :
    IsEigenformWith ε g :=
  h.1

/-- The eigenvalue packet of a primitive form does not occur at a proper
divisor of its level. -/
public theorem IsPrimitiveForm.not_eigenpacketOccursAt
    {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsPrimitiveForm ε g) {M' : ℕ} (hM' : M' ∣ M) (hne : M' ≠ M) :
    ¬ EigenpacketOccursAt k (fun n => qCoeff g n)
      (fun n => ε (n : ZMod M)) M' :=
  h.2 M' hM' hne

/-- The eigenvalue packet of a nonzero eigenform occurs at its own level. -/
public theorem IsEigenformWith.eigenpacketOccursAt
    {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) (hM : M ≠ 0) (hg : g ≠ 0) :
    EigenpacketOccursAt k (fun n => qCoeff g n)
      (fun n => ε (n : ZMod M)) M :=
  ⟨ε, g, hg, h.hasNebentypus, Nat.divisors M, fun _ hp hpS => ⟨rfl, fun n =>
    h.hecke_of_not_dvd hp (fun hpM => hpS (Nat.mem_divisors.2 ⟨hpM, hM⟩)) n⟩⟩

end CuspForm
