/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Stickelberger_Basic.lean` and
`Definitions/Def_ClassGroup_ModP.lean`
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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.FreeModule.ModN
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.ExtendedHom
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Stickelberger endomorphism

For a prime `p` and a `ZMod p`-module `A` with an action `ρ` of `(ZMod p)ˣ`, this file
defines the endomorphism `stickelbergerEnd ρ = ∑ ρ (c⁻¹)` of `A`, summed over the exponents `c`
with `0 < c` and `2 * c < p`, and the `ω ^ i` eigenvector condition `IsOmegaEigenvector`. On
Mathlib's quotient `ModN M p = M / pM` of an abelian group it adds the endomorphism `modNEnd`
induced by an endomorphism of `M`, and the endomorphism `clEnd` of the class group modulo
`p`-th powers induced by a ring automorphism of a domain.

## Main results

* `Stickelberger.stickelbergerEnd_apply_of_isOmegaEigenvector`: on an `ω ^ i`
  eigenvector, `stickelbergerEnd ρ` acts as the scalar `∑ c⁻¹ ^ i`.
* `Stickelberger.stickelbergerEnd_apply_of_isOmegaEigenvector_sub_two`: for `i = p - 2`
  this scalar is `eigenvalueScalar p = ∑ c`.

## References

The Stickelberger element of `ℚ(ζ_p)` is `θ = ∑_{a=1}^{p-1} (a / p) σ_a⁻¹`
(L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §6.2).
For odd `p`, a direct computation gives
`(2 - σ_2) θ = ∑_{p/2 < a < p} σ_a⁻¹ = σ_{-1} ∑_{0 < c < p/2} σ_c⁻¹`,
so the sum used here is an element of the Stickelberger ideal.
-/

@[expose] public section

open scoped NumberField nonZeroDivisors

namespace Stickelberger

/-- The Stickelberger exponents `c` with `0 < c` and `2 * c < p`. -/
def exponentSet (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun c => 0 < c ∧ 2 * c < p

@[simp] lemma mem_exponentSet {p c : ℕ} :
    c ∈ exponentSet p ↔ 0 < c ∧ 2 * c < p := by
  simp only [exponentSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

/-- The sum of the Stickelberger exponents `c` with `0 < c` and `2 * c < p`; see
`stickelbergerEnd_apply_of_isOmegaEigenvector_sub_two` for its role as an eigenvalue. -/
def eigenvalueScalar (p : ℕ) : ℕ := ∑ c ∈ exponentSet p, c

variable {p : ℕ}

/-- For prime `p`, every Stickelberger exponent is coprime to `p`. -/
theorem coprime_of_mem_exponentSet (hp : p.Prime) {c : ℕ} (hc : c ∈ exponentSet p) :
    c.Coprime p := by
  rw [mem_exponentSet] at hc
  exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hc.1 (by omega))).symm

/-- For prime `p`, the unit of `ZMod p` represented by a Stickelberger exponent. -/
noncomputable def expUnit [Fact p.Prime] {c : ℕ} (hc : c ∈ exponentSet p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime c (coprime_of_mem_exponentSet Fact.out hc)

@[simp] lemma coe_expUnit [Fact p.Prime] {c : ℕ} (hc : c ∈ exponentSet p) :
    (expUnit hc : ZMod p) = c :=
  ZMod.coe_unitOfCoprime c _

variable {A : Type*} [AddCommGroup A] [Module (ZMod p) A]

/-- For a prime `p` and an action `ρ` of `(ZMod p)ˣ` on a `ZMod p`-module `A`, the Stickelberger
endomorphism `∑ ρ (c⁻¹)` of `A`, summed over the exponents `c` with `0 < c` and `2 * c < p`. -/
noncomputable def stickelbergerEnd [Fact p.Prime] (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) :
    Module.End (ZMod p) A :=
  ∑ c ∈ (exponentSet p).attach, ρ (expUnit c.2)⁻¹

/-- For an action `ρ` of `(ZMod p)ˣ` on a `ZMod p`-module, `a` lies in the `ω ^ i` eigenspace:
each unit `d` acts on it as `d ^ i`. -/
def IsOmegaEigenvector (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) (a : A) : Prop :=
  ∀ d : (ZMod p)ˣ, ρ d a = ((d : ZMod p) ^ i) • a

/-- For a prime `p` and an action `ρ` of `(ZMod p)ˣ` on a `ZMod p`-module, the Stickelberger
endomorphism acts on an `ω ^ i` eigenvector as the scalar `∑ c⁻¹ ^ i` in `ZMod p`, summed over
the exponents `c` with `0 < c` and `2 * c < p`. -/
theorem stickelbergerEnd_apply_of_isOmegaEigenvector [Fact p.Prime]
    {ρ : (ZMod p)ˣ →* Module.End (ZMod p) A} {i : ℕ} {a : A}
    (ha : IsOmegaEigenvector ρ i a) :
    stickelbergerEnd ρ a = (∑ c ∈ exponentSet p, ((c : ZMod p)⁻¹) ^ i) • a := by
  unfold stickelbergerEnd
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [Finset.sum_smul, ← Finset.sum_attach (exponentSet p) (fun c => ((c : ZMod p)⁻¹) ^ i • a)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ha, Units.val_inv_eq_inv_val, coe_expUnit]

/-- For a prime `p` and an action `ρ` of `(ZMod p)ˣ` on a `ZMod p`-module, the Stickelberger
endomorphism acts on an `ω ^ (p - 2)` eigenvector as `eigenvalueScalar p`, since
`c⁻¹ ^ (p - 2) = c` in `ZMod p` by Fermat's little theorem. -/
theorem stickelbergerEnd_apply_of_isOmegaEigenvector_sub_two [Fact p.Prime]
    {ρ : (ZMod p)ˣ →* Module.End (ZMod p) A} {a : A}
    (ha : IsOmegaEigenvector ρ (p - 2) a) :
    stickelbergerEnd ρ a = (eigenvalueScalar p : ZMod p) • a := by
  rw [stickelbergerEnd_apply_of_isOmegaEigenvector ha, eigenvalueScalar, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc0 : (c : ZMod p) ≠ 0 := by
    rw [← coe_expUnit hc]
    exact Units.ne_zero _
  have hpow : (c : ZMod p) ^ (p - 2) * c = 1 := by
    rw [← pow_succ, show p - 2 + 1 = p - 1 by have := (Fact.out : p.Prime).two_le; omega]
    exact ZMod.pow_card_sub_one_eq_one hc0
  rw [inv_pow, inv_eq_of_mul_eq_one_right hpow]

/-- A zero vector is an omega eigenvector for every exponent. -/
theorem isOmegaEigenvector_zero {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] (ρ : (ZMod p)ˣ →* Module.End (ZMod p) A) (i : ℕ) :
    IsOmegaEigenvector ρ i (0 : A) := by
  intro d
  simp

end Stickelberger

namespace ModN

variable {G : Type*} [AddCommGroup G]

lemma mkQ_apply (n : ℕ) (x : G) :
    mkQ n x = Submodule.Quotient.mk (p := LinearMap.range (LinearMap.lsmul ℤ G n)) x :=
  rfl

theorem mkQ_surjective (n : ℕ) : Function.Surjective (mkQ n : G →+ ModN G n) :=
  Submodule.mkQ_surjective _

theorem mkQ_eq_zero_iff (n : ℕ) {x : G} : mkQ n x = 0 ↔ ∃ y, n • y = x := by
  rw [mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  simp only [LinearMap.lsmul_apply, natCast_zsmul]

theorem mkQ_eq_mkQ_iff (n : ℕ) {x y : G} : mkQ n x = mkQ n y ↔ ∃ z, n • z = x - y := by
  rw [← sub_eq_zero, ← map_sub, mkQ_eq_zero_iff]

end ModN

namespace Stickelberger


section ModN

variable (p : ℕ) {M : Type*} [AddCommGroup M]

/-- The endomorphism of `ModN M p = M / pM` induced by an endomorphism of `M`. -/
noncomputable def modNEnd (f : M →+ M) : Module.End (ZMod p) (ModN M p) :=
  ((LinearMap.range (LinearMap.lsmul ℤ M p)).mapQ (LinearMap.range (LinearMap.lsmul ℤ M p))
    f.toIntLinearMap (by
      intro x hx
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
      rw [Submodule.mem_comap]
      exact LinearMap.mem_range.mpr ⟨f y, by simp⟩)).toAddMonoidHom.toZModLinearMap p

@[simp] lemma modNEnd_mkQ (f : M →+ M) (x : M) :
    modNEnd p f (ModN.mkQ p x) = ModN.mkQ p (f x) := rfl

end ModN


section ClassGroupCarrier

variable (p : ℕ)
variable (R : Type*) [CommRing R] [IsDomain R]

/-- The class group of `R` modulo `p`-th powers, as a `ZMod p`-module. -/
abbrev ClGalModule : Type _ := ModN (Additive (ClassGroup R)) p

/-- The projection from the class group to `ClGalModule p R`. -/
noncomputable def clProj : Additive (ClassGroup R) →+ ClGalModule p R :=
  ModN.mkQ p

theorem clProj_surjective : Function.Surjective (clProj p R) :=
  ModN.mkQ_surjective p

variable {R}

/-- The endomorphism of `ClGalModule p R` induced by a ring automorphism of `R`. -/
noncomputable def clEnd (g : R ≃+* R) : Module.End (ZMod p) (ClGalModule p R) :=
  modNEnd p (MonoidHom.toAdditive (ClassGroup.mulEquiv g).toMonoidHom)

@[simp] lemma clEnd_clProj (g : R ≃+* R) (C : ClassGroup R) :
    clEnd p g (clProj p R (Additive.ofMul C)) =
      clProj p R (Additive.ofMul (ClassGroup.mulEquiv g C)) := rfl

end ClassGroupCarrier

end Stickelberger
