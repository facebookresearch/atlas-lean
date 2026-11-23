/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

/-
# Equality through STLC normalization by evaluation
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCanonical
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.NbeCorrectness

/-!
# Equality through STLC normalization by evaluation

This file exposes equality of computed eta-long normal forms as a relation on
typed terms.  It records the exact canonical representative of each
equivalence class and connects normalization equality to the model-independent
semantic equality proved by the correctness layer.

The semantic implication is intentionally one-way: completeness of arbitrary
set-theoretic model equality is not assumed here.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.Stlc

open scoped CslibStlc

universe u

variable {Base : Type u}
variable {A : Ty Base}
variable {Γ : List (Ty Base)}

/-- Two terms are NbE-equivalent when they compute to the same eta-long normal
form. -/
def NbeEq (t u : Tm Γ A) : Prop := normalizeNf t = normalizeNf u

namespace NbeEq

theorem refl (t : Tm Γ A) : NbeEq t t := rfl

theorem symm {t u : Tm Γ A} (h : NbeEq t u) : NbeEq u t := Eq.symm h

theorem trans {t u v : Tm Γ A} (htu : NbeEq t u) (huv : NbeEq u v) :
    NbeEq t v := Eq.trans htu huv

/-- NbE equivalence is equivalently equality of the erased canonical terms. -/
theorem iff_normalizeTm_eq {t u : Tm Γ A} :
    NbeEq t u ↔ normalizeTm t = normalizeTm u := by
  constructor
  · exact fun h => congrArg Nf.toTm h
  · intro h
    exact Nf.toTm_injective h

/-- Every term is equivalent to its computed canonical representative. -/
theorem normalize_right (t : Tm Γ A) : NbeEq t (normalizeTm t) := by
  apply Nf.toTm_injective
  simp only [normalizeTm, normalizeNf_toTm]

theorem normalize_left (t : Tm Γ A) : NbeEq (normalizeTm t) t :=
  (normalize_right t).symm

/-- Equal source terms are NbE-equivalent. -/
theorem of_eq {t u : Tm Γ A} (h : t = u) : NbeEq t u := h ▸ refl t

/-- Equality of canonical forms is sound in every set-theoretic model. -/
theorem modelEq {t u : Tm Γ A} (h : NbeEq t u) : ModelEq t u :=
  modelEq_of_normalizeTm_eq (iff_normalizeTm_eq.mp h)

/-- NbE-equivalent canonical terms are syntactically equal. -/
theorem eq_of_isCanonical {t u : Tm Γ A} (ht : IsCanonical t)
    (hu : IsCanonical u) (h : NbeEq t u) : t = u := by
  rw [isCanonical_iff_normalizeTm_eq] at ht hu
  rw [← ht, ← hu]
  exact iff_normalizeTm_eq.mp h

/-- The normal form itself is the unique canonical term NbE-equivalent to the
source term. -/
theorem canonical_unique (t c : Tm Γ A) (hc : IsCanonical c) (h : NbeEq t c) :
    c = normalizeTm t := by
  apply eq_of_isCanonical hc (isCanonical_normalizeTm t)
  exact (symm h).trans (normalize_right t)

end NbeEq

/-- NbE equality is an equivalence relation on intrinsically typed terms. -/
theorem nbeEq_equivalence : Equivalence (@NbeEq Base A Γ) :=
  ⟨NbeEq.refl, NbeEq.symm, NbeEq.trans⟩

end Cslib.Languages.LambdaCalculus.Stlc
