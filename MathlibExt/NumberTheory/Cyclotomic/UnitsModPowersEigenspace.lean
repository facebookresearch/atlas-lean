/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ClassGroup_GaloisAction.lean` and
`Definitions/Def_ExtCitation_CyclotomicUnits.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import MathlibExt.NumberTheory.Cyclotomic.Stickelberger

/-!
# Galois actions on the class group and on the units of `ℚ(ζ_p)` modulo `p`-th powers

For a prime `p` and a `p`-th cyclotomic extension `K / ℚ`, this file transports the Galois
group `(ZMod p)ˣ ≃ Gal(K / ℚ)` to ring automorphisms of `𝓞 K` and lets it act on the class
group modulo `p` (`Stickelberger.clGalAction`) and on the group `E / E ^ p`, where `E` is the
full unit group of `𝓞 (ℚ(ζ_p))` (not the subgroup of cyclotomic units, nor the units of the
maximal real subfield), as `Stickelberger.unitsGalAction`. It defines the `ω ^ i` eigenspace of
`E / E ^ p` and the projector `Stickelberger.omegaIdempotent = (p - 1)⁻¹ ∑_d d⁻ⁱ ρ(d)`.

## Main results

* `Stickelberger.clGalAction_clProj_mk0`: the action on the class of an ideal.
* `Stickelberger.omegaIdempotent_comp_self`: `omegaIdempotent` is idempotent.
* `Stickelberger.isOmegaEigenvector_omegaIdempotent`: its image consists of `ω ^ i`
  eigenvectors, which it fixes (`omegaIdempotent_apply_of_isOmegaEigenvector`).

## References

The eigenspace idempotents are those of L. C. Washington, *Introduction to Cyclotomic
Fields*, 2nd ed., GTM 83, §6.3, written for an arbitrary `(ZMod p)ˣ`-module.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors
open Polynomial

namespace Stickelberger

section GalRestrict

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
  [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]

/-- For a commutative ring `A` with fraction field `K`, an algebraic extension `L / K` and an
integral closure `B` of `A` in `L`, the restriction of `Gal(L / K)` to ring automorphisms of `B`,
as a monoid hom. -/
noncomputable def galRestrictRingAut : (L ≃ₐ[K] L) →* (B ≃+* B) :=
  (MulSemiringAction.toRingAut (B ≃ₐ[A] B) B).comp (galRestrict A K L B).toMonoidHom

@[simp] lemma galRestrictRingAut_apply (g : L ≃ₐ[K] L) (x : B) :
    galRestrictRingAut A K L B g x = galRestrict A K L B g x :=
  rfl

end GalRestrict

end Stickelberger


namespace Stickelberger


section ClassGroupCarrier

variable (p : ℕ) [NeZero p]

section DedekindAction

variable (R : Type*) [CommRing R]

variable {R} in
variable [IsDedekindDomain R] in
omit [NeZero p] in
theorem clEnd_clProj_mk0 (g : R ≃+* R) (P : (Ideal R)⁰) :
    clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p R (Additive.ofMul (ClassGroup.mk0 ⟨(P : Ideal R).map g,
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective g.injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp P.2)⟩)) :=
  (clEnd_clProj p g _).trans
    (congrArg (fun C => clProj p R (Additive.ofMul C)) (ClassGroup.mulEquiv_mk0 g P))

variable {R} in
variable [IsDomain R] in
/-- `clEnd` as a monoid hom from the ring automorphisms of `R`. -/
noncomputable def clEndHom : (R ≃+* R) →* Module.End (ZMod p) (ClGalModule p R) where
  toFun := clEnd p
  map_one' := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [one_apply_eq_self]
    change clProj p R (Additive.ofMul (ClassGroup.mulEquiv (RingEquiv.refl R) C.toMul)) =
      clProj p R C
    have hrefl : ClassGroup.mulEquiv (RingEquiv.refl R) C.toMul = C.toMul := by
      rw [ClassGroup.mulEquiv_apply]
      convert ClassGroup.map_id C.toMul
      exact RingHom.ext fun _ => rfl
    rw [hrefl]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨C, rfl⟩ := clProj_surjective p R a
    rw [mul_apply_eq_comp]
    change clProj p R (Additive.ofMul (ClassGroup.mulEquiv (h.trans g) C.toMul)) =
      clEnd p g (clProj p R (Additive.ofMul (ClassGroup.mulEquiv h C.toMul)))
    have htrans : ClassGroup.mulEquiv (h.trans g) C.toMul =
        ClassGroup.mulEquiv g (ClassGroup.mulEquiv h C.toMul) := by
      rw [ClassGroup.mulEquiv_apply, ClassGroup.mulEquiv_apply, ClassGroup.mulEquiv_apply,
        ClassGroup.map_map]
      rfl
    rw [clEnd_clProj, htrans]

end DedekindAction

section Cyclotomic

variable (K : Type*) [Field K] [NumberField K]

/-- For `p ≠ 0` and a `p`-th cyclotomic number field `K`, `(ZMod p)ˣ` acting on `𝓞 K` by ring
automorphisms through Mathlib's `IsCyclotomicExtension.Rat.galEquivZMod : Gal(K / ℚ) ≃* (ZMod p)ˣ`.
-/
noncomputable def clRingAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* ((𝓞 K) ≃+* (𝓞 K)) :=
  (galRestrictRingAut ℤ ℚ K (𝓞 K)).comp
    (IsCyclotomicExtension.Rat.galEquivZMod p K).symm.toMonoidHom

/-- For `p ≠ 0` and a `p`-th cyclotomic number field `K`, `clRingAction p K d` raises a `p`-th
root of unity of `𝓞 K` to the power `d`. -/
theorem clRingAction_apply_of_pow_eq [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ) {x : 𝓞 K}
    (hx : x ^ p = 1) : clRingAction p K d x = x ^ (d : ZMod p).val := by
  have h := IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq p K
    ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm d) hx
  rw [MulEquiv.apply_symm_apply] at h
  rw [← h]
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  exact algebraMap_galRestrict_apply ℤ _ x

/-- For `p ≠ 0` and a `p`-th cyclotomic number field `K`, `(ZMod p)ˣ` acting on the class group
of `𝓞 K` modulo `p`-th powers. -/
noncomputable def clGalAction [IsCyclotomicExtension {p} ℚ K] :
    (ZMod p)ˣ →* Module.End (ZMod p) (ClGalModule p (𝓞 K)) :=
  (clEndHom p).comp (clRingAction p K)

/-- For `p ≠ 0` and a `p`-th cyclotomic number field `K`, `d` sends the class of a nonzero ideal
`P` in the class group modulo `p`-th powers to the class of its image under
`clRingAction p K d`. -/
theorem clGalAction_clProj_mk0 [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    clGalAction p K d (clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 P))) =
      clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0 ⟨(P : Ideal (𝓞 K)).map (clRingAction p K d),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective (clRingAction p K d).injective).not.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mp P.2)⟩)) :=
  clEnd_clProj_mk0 p (clRingAction p K d) P

end Cyclotomic

end ClassGroupCarrier


end Stickelberger

namespace Stickelberger

open NumberField

variable (p : ℕ) [Fact p.Prime]

section UnitsGalAction

variable (R : Type*) [CommRing R]

/-- For a prime `p`, the endomorphism of `Rˣ` modulo `p`-th powers induced by a ring automorphism
of `R`. -/
noncomputable def unitsEnd (g : R ≃+* R) :
    Module.End (ZMod p) (ModN (Additive Rˣ) p) :=
  modNEnd p (MulEquiv.toAdditive (Units.mapEquiv g.toMulEquiv)).toAddMonoidHom

variable {R} in
@[simp] lemma unitsEnd_proj (g : R ≃+* R) (u : Rˣ) :
    unitsEnd p R g (ModN.mkQ p (Additive.ofMul u)) =
      ModN.mkQ p (Additive.ofMul (Units.mapEquiv g.toMulEquiv u)) :=
  rfl

/-- For a prime `p`, `unitsEnd` as a monoid hom from the ring automorphisms of `R`. -/
noncomputable def unitsEndHom : (R ≃+* R) →* Module.End (ZMod p) (ModN (Additive Rˣ) p) where
  toFun := unitsEnd p R
  map_one' := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨u, rfl⟩ := ModN.mkQ_surjective (G := Additive Rˣ) p a
    exact unitsEnd_proj p (RingEquiv.refl R) u.toMul
  map_mul' g h := by
    refine LinearMap.ext fun a => ?_
    obtain ⟨u, rfl⟩ := ModN.mkQ_surjective (G := Additive Rˣ) p a
    simp only [mul_apply_eq_comp]
    rfl

end UnitsGalAction

set_option backward.isDefEq.respectTransparency false in
/-- `ℚ(ζ_p)` is a `p`-th cyclotomic extension; kept local so importers keep the
Mathlib instance. -/
noncomputable local instance instIsCycExt :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  inferInstance

/-- For a prime `p`, `(ZMod p)ˣ` acting on the units of `𝓞 (ℚ(ζ_p))` modulo `p`-th powers. -/
noncomputable def unitsGalAction :
    (ZMod p)ˣ →* Module.End (ZMod p)
      (ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p) :=
  (unitsEndHom p (𝓞 (CyclotomicField p ℚ))).comp (clRingAction p (CyclotomicField p ℚ))

/-- For a prime `p`, the `ω ^ i` eigenspace of `unitsGalAction p` on the units of `𝓞 (ℚ(ζ_p))`
modulo `p`-th powers. -/
def unitsOmegaEigenspace (i : ℕ) :
    Submodule (ZMod p) (ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p) where
  carrier := {a | IsOmegaEigenvector (unitsGalAction p) i a}
  add_mem' {a b} ha hb d := by
    simp only [Set.mem_ofPred_eq, IsOmegaEigenvector] at *
    rw [map_add, ha d, hb d, smul_add]
  zero_mem' d := by simp
  smul_mem' c a ha d := by
    simp only [Set.mem_ofPred_eq, IsOmegaEigenvector] at *
    rw [map_smul, ha d, smul_comm]

/-- For a prime `p` and an action `ρ` of `(ZMod p)ˣ` on a `ZMod p`-module, the projector
`(p - 1)⁻¹ ∑_d (d ^ i)⁻¹ ρ(d)` onto the `ω ^ i` eigenvectors of `ρ`, with the inverses taken in
`ZMod p`; see `omegaIdempotent_comp_self` and `isOmegaEigenvector_omegaIdempotent`. -/
noncomputable def omegaIdempotent {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) : Module.End (ZMod p) M :=
  (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ • ∑ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d


section OmegaIdempotent

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
  (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M)

/-- For a prime `p`, `omegaIdempotent` applied to a vector. -/
theorem omegaIdempotent_apply (i : ℕ) (a : M) :
    omegaIdempotent p ρ i a =
      (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ •
        ∑ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d a := by
  simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

private lemma isUnit_natCast_card_units_zmod :
    IsUnit ((Nat.card (ZMod p)ˣ : ℕ) : ZMod p) := by
  have hp := (Fact.out : p.Prime)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one, CharP.cast_eq_zero (ZMod p) p, zero_sub]
  exact (IsUnit.neg_iff 1).mpr isUnit_one

/-- For a prime `p`, the projector `omegaIdempotent` fixes every `ω ^ i` eigenvector. -/
theorem omegaIdempotent_apply_of_isOmegaEigenvector {i : ℕ} {a : M}
    (ha : IsOmegaEigenvector ρ i a) : omegaIdempotent p ρ i a = a := by
  rw [omegaIdempotent_apply]
  have hρ : ∀ d : (ZMod p)ˣ, (((d : ZMod p) ^ i)⁻¹) • ρ d a = a := by
    intro d
    rw [ha d, smul_smul, inv_mul_cancel₀ (pow_ne_zero i (Units.ne_zero d)), one_smul]
  simp only [hρ, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul]
  rw [(isUnit_natCast_card_units_zmod p).inv_mul_cancel, one_smul]

/-- For a prime `p`, the image of the projector `omegaIdempotent` consists of `ω ^ i`
eigenvectors. -/
theorem isOmegaEigenvector_omegaIdempotent (i : ℕ) (a : M) :
    IsOmegaEigenvector ρ i (omegaIdempotent p ρ i a) := by
  intro d'
  simp only [omegaIdempotent_apply]
  rw [map_smul, smul_comm]
  congr 1
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_bijective (d' * ·) (Group.mulLeft_bijective d') _ _ fun d => ?_
  simp only [map_mul, mul_apply_eq_comp, map_smul, smul_smul]
  congr 1
  push_cast
  rw [mul_pow, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero i (Units.ne_zero d')), one_mul]

/-- For a prime `p`, the projector `omegaIdempotent` is idempotent. -/
theorem omegaIdempotent_comp_self (i : ℕ) :
    omegaIdempotent p ρ i ∘ₗ omegaIdempotent p ρ i = omegaIdempotent p ρ i :=
  LinearMap.ext fun a =>
    omegaIdempotent_apply_of_isOmegaEigenvector p ρ (isOmegaEigenvector_omegaIdempotent p ρ i a)

end OmegaIdempotent

/-- For a prime `p`, the projector for the unit action lands in `unitsOmegaEigenspace`. -/
theorem omegaIdempotent_mem_unitsOmegaEigenspace (i : ℕ)
    (a : ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p) :
    omegaIdempotent p (unitsGalAction p) i a ∈ unitsOmegaEigenspace p i :=
  isOmegaEigenvector_omegaIdempotent p (unitsGalAction p) i a

/-- For a prime `p`, membership in `unitsOmegaEigenspace` is the eigenvector condition. -/
theorem mem_unitsOmegaEigenspace {i : ℕ} {a : ModN (Additive (𝓞 (CyclotomicField p ℚ))ˣ) p} :
    a ∈ unitsOmegaEigenspace p i ↔
      Stickelberger.IsOmegaEigenvector (unitsGalAction p) i a :=
  Iff.rfl

end Stickelberger
