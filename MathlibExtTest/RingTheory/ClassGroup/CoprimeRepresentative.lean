/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.ClassGroup.CoprimeRepresentative

@[expose] public section

open Ideal

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

example (c : ClassGroup A) (a : Ideal A) (ha : a ≠ ⊥) :
    ∃ (I : Ideal A) (hI : I ≠ ⊥),
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩ = c ∧
        IsCoprime I a := by
  obtain ⟨⟨I, hI⟩, hc, hcop⟩ := ClassGroup.exists_mk0_eq_and_isCoprime c ha
  exact ⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI, hc, hcop⟩

example (I a : Ideal A) (hI : I ≠ ⊥) (ha : a ≠ ⊥) :
    ∃ J : Ideal A, IsCoprime J a ∧ Submodule.IsPrincipal (I * J) := by
  exact Ideal.exists_isCoprime_mul_isPrincipal I a hI ha

example (a : Ideal A) (ha : a ≠ ⊥) :
    ∃ J : Ideal A, IsCoprime J a ∧ Submodule.IsPrincipal ((⊤ : Ideal A) * J) := by
  exact Ideal.exists_isCoprime_mul_isPrincipal ⊤ a top_ne_bot ha
