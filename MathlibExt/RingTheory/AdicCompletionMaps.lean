/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Fixed maps on actual adic quotient towers

All maps use the specified ring homomorphism and ideal inclusion. A
completion-map model is normalized on every actual quotient projection;
its map is consequently unique. This is an original native adapter for
the usual adic-completion universal property, not a new theorem request.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.AdicCompletionMaps

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
variable (I : Ideal A) (J : Ideal B) (K : Ideal C)

/-- The fixed map of actual ideal-power quotient rings. -/
def quotientMap (f : A →+* B) (h : I.map f ≤ J) (n : ℕ) :
    (A ⧸ I ^ n) →+* (B ⧸ J ^ n) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (J ^ n)).comp f) (by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hpow : (I ^ n).map f ≤ J ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' h n
    exact hpow (Ideal.mem_map_of_mem _ ha))

@[simp] theorem quotientMap_mk (f : A →+* B) (h : I.map f ≤ J)
    (n : ℕ) (a : A) :
    quotientMap I J f h n (Ideal.Quotient.mk (I ^ n) a) =
      Ideal.Quotient.mk (J ^ n) (f a) := rfl

/-- The quotient map preserves the actual quotient-tower restriction. -/
theorem quotientMap_factor (f : A →+* B) (h : I.map f ≤ J)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp (quotientMap I J f h n) =
      (quotientMap I J f h m).comp (Ideal.Quotient.factorPow I hmn) := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- Source integration data for the uniquely fixed completion map. -/
structure Map (f : A →+* B) (h : I.map f ≤ J) where
  hom : AdicCompletion I A →+* AdicCompletion J B
  projection : ∀ n : ℕ,
    (AdicCompletion.evalₐ J n).toRingHom.comp hom =
      (quotientMap I J f h n).comp (AdicCompletion.evalₐ I n).toRingHom

/-- Every quotient projection fixes the map, so this model cannot vary. -/
@[ext] theorem Map.ext {f : A →+* B} {h : I.map f ≤ J}
    (u v : Map I J f h) : u = v := by
  have hh : u.hom = v.hom := by
    apply RingHom.ext
    intro a
    apply AdicCompletion.ext_evalₐ
    intro n
    have hu := RingHom.congr_fun (u.projection n) a
    have hv := RingHom.congr_fun (v.projection n) a
    exact hu.trans hv.symm
  cases u
  cases v
  cases hh
  rfl

end MathlibExt.RingTheory.AdicCompletionMaps
