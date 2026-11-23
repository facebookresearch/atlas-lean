/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.CuspFormConj

@[expose] public section

open UpperHalfPlane

-- exactSource consumer: the original binders apply verbatim.
example (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k →
        CuspForm (CongruenceSubgroup.Gamma0 N) k,
      ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ),
        ModularFormClass.qCoeff (ρ f) n =
          (starRingEnd ℂ) (ModularFormClass.qCoeff f n) :=
  CuspForm.exists_qCoeff_conj N k

-- The bundled conjugation operation itself satisfies the coefficient identity.
example (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.conjForm N k f) n =
      (starRingEnd ℂ) (ModularFormClass.qCoeff f n) :=
  CuspForm.qCoeff_conjForm N k f n

-- Boundary: the zero cusp form is fixed coefficientwise; its `0`-th
-- coefficient is `0`, unlike a constant modular form, whose `0`-th
-- coefficient is its constant value. This is the coefficient that the cusp
-- condition forces to vanish.
example (N : ℕ) [NeZero N] (k : ℤ) :
    ModularFormClass.qCoeff (CuspForm.conjForm N k (0 : CuspForm
      (CongruenceSubgroup.Gamma0 N) k)) 0 = 0 := by
  rw [CuspForm.qCoeff_conjForm]
  simp [UpperHalfPlane.qExpansion_zero]

-- Higher-universe consumer is not applicable: all types are concrete
-- (`ℍ`, `ℂ`, `ℕ`, `ℤ`), so there is no universe to generalize.
