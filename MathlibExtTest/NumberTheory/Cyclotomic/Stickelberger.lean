/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.UnitsModPowersEigenspace

@[expose] public section

open scoped NumberField nonZeroDivisors

/-- Source-faithful consumer for the class-group Galois action on an
ideal class, with the original binders. -/
theorem exactSource_clGalAction_clProj_mk0 (p : ℕ) [NeZero p]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    Stickelberger.clGalAction p K d
        (Stickelberger.clProj p (𝓞 K)
          (Additive.ofMul (ClassGroup.mk0 P))) =
      Stickelberger.clProj p (𝓞 K) (Additive.ofMul (ClassGroup.mk0
        ⟨(P : Ideal (𝓞 K)).map (Stickelberger.clRingAction p K d),
          mem_nonZeroDivisors_iff_ne_zero.mpr <|
            (Ideal.map_eq_bot_iff_of_injective
              (Stickelberger.clRingAction p K d).injective).not.mpr
              (mem_nonZeroDivisors_iff_ne_zero.mp P.2)⟩)) :=
  Stickelberger.clGalAction_clProj_mk0 p K d P

open Stickelberger

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### Stickelberger exponents and units -/

example : Stickelberger.exponentSet 5 = {1, 2} := by decide

example : Stickelberger.eigenvalueScalar 5 = 3 := by decide

example : Stickelberger.exponentSet 2 = ∅ := by decide

/-- Boundary: without primality an exponent need not be a unit; `2 ∈ exponentSet 6`
but `2` is not coprime to `6`, which is why `expUnit` requires a prime modulus. -/
example : 2 ∈ exponentSet 6 ∧ ¬ Nat.Coprime 2 6 := by decide

/-- The exponent `2` gives the residue `2` in `ZMod 5`, not the identity unit. -/
example : ((expUnit (p := 5) (c := 2) (by decide) : (ZMod 5)ˣ) : ZMod 5) = 2 := by
  rw [coe_expUnit]
  rfl

example : expUnit (p := 5) (c := 2) (by decide) ≠ 1 := by
  rw [Ne, Units.ext_iff, coe_expUnit, Units.val_one]
  decide

/-! ### The Stickelberger endomorphism on concrete actions -/

/-- `(ZMod p)ˣ` acting on a `ZMod p`-module by scalar multiplication. -/
private noncomputable def scalarAction (p : ℕ) (A : Type*) [AddCommGroup A]
    [Module (ZMod p) A] : (ZMod p)ˣ →* Module.End (ZMod p) A where
  toFun d := (d : ZMod p) • LinearMap.id
  map_one' := by
    ext a
    simp
  map_mul' d e := by
    ext a
    simp [mul_smul]
    exact smul_comm _ _ _

private lemma scalarAction_apply {p : ℕ} {A : Type*} [AddCommGroup A] [Module (ZMod p) A]
    (d : (ZMod p)ˣ) (a : A) : scalarAction p A d a = (d : ZMod p) • a :=
  rfl

private lemma stickelbergerEnd_scalarAction {p : ℕ} [Fact p.Prime] {A : Type*}
    [AddCommGroup A] [Module (ZMod p) A] (a : A) :
    stickelbergerEnd (scalarAction p A) a =
      (∑ c ∈ exponentSet p, ((c : ZMod p))⁻¹) • a := by
  unfold stickelbergerEnd
  simp only [LinearMap.coe_sum, Finset.sum_apply]
  rw [Finset.sum_smul, ← Finset.sum_attach (exponentSet p) (fun c => ((c : ZMod p))⁻¹ • a)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [scalarAction_apply, Units.val_inv_eq_inv_val, coe_expUnit]

/-- For `p = 2` there are no Stickelberger exponents, so the endomorphism is zero. -/
example {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    (ρ : (ZMod 2)ˣ →* Module.End (ZMod 2) A) : stickelbergerEnd ρ = 0 := by
  unfold stickelbergerEnd
  refine Finset.sum_eq_zero fun c _ => absurd c.2 ?_
  rw [mem_exponentSet]
  omega

private lemma sum_inv_exponentSet_five :
    (∑ c ∈ exponentSet 5, ((c : ZMod 5))⁻¹) = -1 := by
  have h2 : ((2 : ℕ) : ZMod 5)⁻¹ = 3 := inv_eq_of_mul_eq_one_right (by decide)
  rw [show exponentSet 5 = {1, 2} by decide, Finset.sum_insert (by decide),
    Finset.sum_singleton, h2, Nat.cast_one, inv_one]
  decide

/-- At `p = 5` the Stickelberger element is `1 + 2⁻¹ = 1 + 3 = -1`, so it acts on the
class of `1` in `ℤ / 5ℤ` as the class of `4`. Replacing the unit `2` by the identity
would give the class of `2` instead. -/
example : stickelbergerEnd (scalarAction 5 (ModN ℤ 5)) (ModN.mkQ 5 (1 : ℤ)) =
    ModN.mkQ 5 (4 : ℤ) := by
  rw [stickelbergerEnd_scalarAction, sum_inv_exponentSet_five, neg_one_smul, ← map_neg,
    ModN.mkQ_eq_mkQ_iff]
  exact ⟨-1, by norm_num⟩

/-- At `p = 3` the scalar action is an `ω ^ (p - 2)` eigenvector condition, so the
Stickelberger endomorphism acts as `eigenvalueScalar 3`. -/
example {A : Type*} [AddCommGroup A] [Module (ZMod 3) A] (a : A) :
    stickelbergerEnd (scalarAction 3 A) a = (eigenvalueScalar 3 : ZMod 3) • a :=
  stickelbergerEnd_apply_of_isOmegaEigenvector_sub_two fun d => by
    rw [scalarAction_apply]
    norm_num

/-! ### The induced endomorphism of `M / pM` -/

/-- The class of `1` in `ℤ / 5ℤ` is nonzero, so the next example is not vacuous. -/
example : ModN.mkQ 5 (1 : ℤ) ≠ 0 := by
  intro h
  obtain ⟨y, hy⟩ := (ModN.mkQ_eq_zero_iff 5).mp h
  rw [nsmul_eq_mul] at hy
  push_cast at hy
  omega

example : ModN.mkQ 5 (5 : ℤ) = 0 :=
  (ModN.mkQ_eq_zero_iff 5).mpr ⟨1, by norm_num⟩

/-- Doubling acts on representatives: it sends the class of `3` to the class of `6`,
which is the class of `1` modulo `5`. -/
example : modNEnd 5 (AddMonoidHom.mulLeft (2 : ℤ)) (ModN.mkQ 5 (3 : ℤ)) =
    ModN.mkQ 5 (1 : ℤ) := by
  rw [modNEnd_mkQ, ModN.mkQ_eq_mkQ_iff]
  exact ⟨1, by norm_num [AddMonoidHom.coe_mulLeft]⟩

/-! ### The unit action on representatives -/

private def negOneOne : (ℤ × ℤ)ˣ :=
  ⟨(-1, 1), (-1, 1), by ext <;> simp, by ext <;> simp⟩

/-- Swapping the factors of `ℤ × ℤ` moves the class of the unit `(-1, 1)` modulo
squares, so the induced unit action is not the identity on `Rˣ / (Rˣ)²`. -/
example : unitsEnd 2 (ℤ × ℤ) RingEquiv.prodComm
      (ModN.mkQ 2 (Additive.ofMul negOneOne)) ≠
    ModN.mkQ 2 (Additive.ofMul negOneOne) := by
  rw [unitsEnd_proj]
  intro h
  obtain ⟨y, hy⟩ := (ModN.mkQ_eq_mkQ_iff 2).mp h
  have h1 := congrArg (fun z : Additive (ℤ × ℤ)ˣ => ((Additive.toMul z : (ℤ × ℤ)ˣ) : ℤ × ℤ).1)
    (eq_sub_iff_add_eq.mp hy)
  simp [negOneOne] at h1
  nlinarith [sq_nonneg ((Additive.toMul y : (ℤ × ℤ)ˣ) : ℤ × ℤ).1]

/-! ### The omega projector -/

section OmegaIdempotent

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
  (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M)

/-- The projector is idempotent, pointwise. -/
example (i : ℕ) (a : M) :
    omegaIdempotent p ρ i (omegaIdempotent p ρ i a) = omegaIdempotent p ρ i a :=
  LinearMap.congr_fun (omegaIdempotent_comp_self p ρ i) a

end OmegaIdempotent

/-- On the units of `𝓞 (ℚ(ζ_5))` modulo fifth powers, the projector lands in the
`ω ^ 2` eigenspace. -/
example (a : ModN (Additive (𝓞 (CyclotomicField 5 ℚ))ˣ) 5) :
    omegaIdempotent 5 (unitsGalAction 5) 2 a ∈ unitsOmegaEigenspace 5 2 :=
  omegaIdempotent_mem_unitsOmegaEigenspace 5 2 a

example : (0 : ModN (Additive (𝓞 (CyclotomicField 5 ℚ))ˣ) 5) ∈
    unitsOmegaEigenspace 5 2 :=
  Submodule.zero_mem _

/-- Every vector is an `ω ^ 1` eigenvector of the scalar action, so the `ω ^ 1`
projector is the identity there. -/
example {A : Type*} [AddCommGroup A] [Module (ZMod 5) A] (a : A) :
    omegaIdempotent 5 (scalarAction 5 A) 1 a = a :=
  omegaIdempotent_apply_of_isOmegaEigenvector 5 (scalarAction 5 A) fun d => by
    rw [scalarAction_apply, pow_one]
