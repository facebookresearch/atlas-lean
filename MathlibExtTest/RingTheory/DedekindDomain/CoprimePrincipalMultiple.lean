/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClassGroup.CoprimeRepresentative
import Mathlib.Tactic.NormNum

/-!
# Integer clients of the coprime principal multiple API

The existing `Ideal.exists_isCoprime_mul_isPrincipal` proves Lemma 3.16.
These tests extract its principal generator and retain the explicit span
properties for prescribed ideals `(35)`, `(2)`, and `⊤`.
-/

@[expose] public section

open Ideal

private theorem span_singleton_ne_bot_of_ne {n : ℤ} (hn : n ≠ 0) :
    Ideal.span {n} ≠ ⊥ := by
  show ¬ (Ideal.span {n} = ⊥)
  rw [Ideal.span_singleton_eq_bot]
  exact hn

private theorem exists_coprime_principal_span {I I' : Ideal ℤ}
    (hI : I ≠ ⊥) (hI' : I' ≠ ⊥) :
    ∃ (J : Ideal ℤ) (x : ℤ), IsCoprime J I' ∧ I * J = Ideal.span {x} := by
  obtain ⟨J, hcoprime, hprincipal⟩ :=
    Ideal.exists_isCoprime_mul_isPrincipal I I' hI hI'
  letI : Submodule.IsPrincipal (I * J) := hprincipal
  exact ⟨J, Submodule.IsPrincipal.generator (I * J), hcoprime,
    (Ideal.span_singleton_generator (I * J)).symm⟩

-- The theorem applies in `ℤ`: every nonzero ideal has a principal
-- multiple by an ideal coprime to a prescribed nonzero ideal.
example :
    ∃ (J : Ideal ℤ) (x : ℤ), IsCoprime J (Ideal.span {35}) ∧
      Ideal.span {6} * J = Ideal.span {x} :=
  exists_coprime_principal_span
    (span_singleton_ne_bot_of_ne (by norm_num))
    (span_singleton_ne_bot_of_ne (by norm_num))

-- The coprime ideal can share no prime factor with the prescribed
-- ideal: with `I' = (2)`, the witness `J` is coprime to `(2)`.
example :
    ∃ (J : Ideal ℤ) (x : ℤ), IsCoprime J (Ideal.span {2}) ∧
      Ideal.span {6} * J = Ideal.span {x} :=
  exists_coprime_principal_span
    (span_singleton_ne_bot_of_ne (by norm_num))
    (span_singleton_ne_bot_of_ne (by norm_num))

-- Degenerate case: the prescribed ideal is the whole ring.
example :
    ∃ (J : Ideal ℤ) (x : ℤ), IsCoprime J (⊤ : Ideal ℤ) ∧
      Ideal.span {6} * J = Ideal.span {x} :=
  exists_coprime_principal_span
    (span_singleton_ne_bot_of_ne (by norm_num)) (by simp)

#print axioms exists_coprime_principal_span
#print axioms Ideal.exists_isCoprime_mul_isPrincipal
