/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Frobenius.TowerRestriction
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Tests for powers and restrictions of arithmetic Frobenius elements

These examples preserve the six power/restriction/inertia helpers and
the original `ZMod 2` checks. They also exercise the actual ring-tower
equality, canonical automorphism inclusion, and the intermediate-field
application with two genuine Frobenius premises. The finite model
`ZMod 2 → GaloisField 2 2` has residue degree two: the base Frobenius
is nonidentity, and its square is the intermediate Frobenius.
-/

@[expose] public section

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]
  {G H : Type*} [Group G] [Group H]
  [MulSemiringAction G B] [SMulCommClass G R B]
  [MulSemiringAction H C] [SMulCommClass H R C]

/-- The power congruence applies generically. -/
example {σ : G} {Q : Ideal B} (h : IsArithFrobAt R σ Q) (f : ℕ) (x : B) :
    (σ ^ f) • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q :=
  h.pow_smul_sub_pow_mem f x

/-- The `AlgHom` power congruence applies generically. -/
example {φ : B →ₐ[R] B} {Q : Ideal B} (h : φ.IsArithFrobAt Q) (f : ℕ)
    (x : B) :
    (φ ^ f) x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q :=
  h.pow_apply_sub_pow_mem f x

/-- The restriction congruence applies generically. -/
example {σ : G} {Q : Ideal B} (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q) :
    IsArithFrobAt R (ρ σ) (Q.comap ι) :=
  h.comap ι ρ hcompat

/-- Two elements satisfying the same powered congruence differ by an
element of inertia. -/
example {σ τ : G} {Q : Ideal B} {r : ℕ}
    (hσ : ∀ x : B, σ • x - x ^ r ∈ Q) (hτ : ∀ x : B, τ • x - x ^ r ∈ Q) :
    σ * τ⁻¹ ∈ Q.inertia G :=
  Ideal.mem_inertia_of_forall_smul_sub_pow_mem hσ hτ

/-- Under trivial inertia, a Frobenius power is the unique element
satisfying the powered congruence. -/
example {σ : G} {Q : Ideal B} {f : ℕ} {τ : G}
    (h : IsArithFrobAt R σ Q)
    (hτ : ∀ x : B, τ • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q)
    (hbot : Q.inertia G = ⊥) : σ ^ f = τ :=
  h.pow_eq_of_forall_smul_sub_pow_mem_of_inertia_eq_bot hτ hbot

/-- Under trivial inertia, a restricted Frobenius is the unique element
satisfying the restricted congruence. -/
example {σ : G} {Q : Ideal B} (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q) {τ : H}
    (hτ : ∀ x : C, τ • x - x ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι)
    (hbot : (Q.comap ι).inertia H = ⊥) : ρ σ = τ :=
  h.eq_comap_of_forall_smul_sub_pow_mem_of_inertia_eq_bot ι ρ hcompat hτ hbot

/-- The residue-field cardinality at `⊥` in `ZMod 2` over itself is `2`. -/
theorem natCard_quotient_under_bot_zmod_two :
    Nat.card ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2)).under (ZMod 2)) = 2 := by
  have hunder : (⊥ : Ideal (ZMod 2)).under (ZMod 2) = ⊥ := by
    rw [Ideal.under]
    exact Ideal.comap_bot_of_injective (algebraMap (ZMod 2) (ZMod 2))
      (fun _ _ h => h)
  rw [hunder]
  rw [Nat.card_congr (RingEquiv.quotientBot (ZMod 2)).toEquiv,
    Nat.card_eq_fintype_card]
  exact ZMod.card 2

/-- The identity map on `ZMod 2` is an arithmetic Frobenius at `⊥`:
this is `x = x ^ 2` in `ZMod 2`. -/
theorem id_isArithFrobAt_bot_zmod_two :
    (AlgHom.id (ZMod 2) (ZMod 2)).IsArithFrobAt (⊥ : Ideal (ZMod 2)) := by
  intro x
  rw [natCard_quotient_under_bot_zmod_two]
  simp only [AlgHom.id_apply]
  rw [Ideal.mem_bot]
  fin_cases x <;> decide

/-- The power congruence for the identity map on `ZMod 2` at exponent `3`:
`x - x ^ 8 = 0` in `ZMod 2`. -/
example (x : ZMod 2) :
    ((AlgHom.id (ZMod 2) (ZMod 2)) ^ 3) x -
      x ^ (Nat.card ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2)).under (ZMod 2))) ^ 3
      ∈ (⊥ : Ideal (ZMod 2)) := by
  have h := id_isArithFrobAt_bot_zmod_two.pow_apply_sub_pow_mem 3 x
  rwa [natCard_quotient_under_bot_zmod_two] at h ⊢

end

@[expose] public section

namespace PR411Model
local notation "F" => GaloisField 2 2

private theorem under_bot (K L : Type*) [Field K] [Field L] [Algebra K L] :
    (⊥ : Ideal L).under K = ⊥ :=
  Ideal.comap_bot_of_injective _ (algebraMap K L).injective

theorem gf4_card : Nat.card F = 4 := by
  simpa using GaloisField.card 2 2 (by decide)

theorem gf4_inertia_degree : (⊥ : Ideal F).inertiaDeg (ZMod 2) = 2 := by
  rw [Ideal.inertiaDeg_bot_eq_finrank]
  exact GaloisField.finrank 2 (by decide)

theorem gf4_base_frobenius :
    IsArithFrobAt (ZMod 2) (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F)
      (⊥ : Ideal F) := by
  intro x
  change (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x -
    x ^ Nat.card ((ZMod 2) ⧸ (⊥ : Ideal F).under (ZMod 2)) ∈ (⊥ : Ideal F)
  rw [under_bot, Nat.card_congr (RingEquiv.quotientBot (ZMod 2)).toEquiv,
    Nat.card_eq_fintype_card, FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
  simpa only [sub_self] using (⊥ : Ideal F).zero_mem

theorem gf4_intermediate_frobenius :
    IsArithFrobAt F (AlgEquiv.refl : F ≃ₐ[F] F) (⊥ : Ideal F) := by
  let : Fintype F := Fintype.ofFinite F
  intro x
  change x - x ^ Nat.card (F ⧸ (⊥ : Ideal F).under F) ∈ (⊥ : Ideal F)
  rw [under_bot, Nat.card_congr (RingEquiv.quotientBot F).toEquiv,
    Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  exact Ideal.zero_mem _

theorem gf4_inertia_bot : (⊥ : Ideal F).inertia (F ≃ₐ[ZMod 2] F) = ⊥ :=
  Ideal.inertia_bot (F ≃ₐ[ZMod 2] F) F

theorem gf4_ambient_frobenius_ne_one :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F ≠ 1 := by
  intro h
  have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) F
  rw [h, orderOf_one, GaloisField.finrank 2 (by decide)] at ho
  norm_num at ho

end PR411Model

namespace PR411Regression

section Tower
variable {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
  [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
  [Module.Finite R T]
  {G H : Type*} [Group G] [Group H] [MulSemiringAction G B]
  [SMulCommClass G R B] [MulSemiringAction H B] [SMulCommClass H T B]
  {σ : G} {τ : H} {Q : Ideal B} [Q.IsPrime]

/-- The degree/cardinality conclusion is derived from two real Frobenius premises. -/
theorem generic_cardinality (hR : IsArithFrobAt R σ Q) (hT : IsArithFrobAt T τ Q) :
    Nat.card (T ⧸ Q.under T) =
      Nat.card (R ⧸ Q.under R) ^ (Q.under T).inertiaDeg R := by
  let : Finite (R ⧸ Q.under R) := hR.finite_quotient
  let : Finite (T ⧸ Q.under T) := hT.finite_quotient
  exact Ideal.natCard_quotient_under_eq_pow_inertiaDeg R T Q

/-- No powered-congruence or cardinality conclusion is assumed by the importing client. -/
theorem generic_tower (ι : H →* G)
    (hcompat : ∀ (h : H) (x : B), (ι h) • x = h • x)
    (hR : IsArithFrobAt R σ Q) (hT : IsArithFrobAt T τ Q)
    (hbot : Q.inertia G = ⊥) : ι τ = σ ^ (Q.under T).inertiaDeg R :=
  hR.tower_eq_of_inertia_eq_bot ι hcompat hT hbot
end Tower

/-- Scalar restriction supplies the canonical inclusion for algebra automorphisms. -/
theorem algebra_automorphism_tower
    {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
    [Module.Finite R T] {σ : B ≃ₐ[R] B} {τ : B ≃ₐ[T] B}
    {Q : Ideal B} [Q.IsPrime]
    (hR : IsArithFrobAt R σ Q) (hT : IsArithFrobAt T τ Q)
    (hbot : Q.inertia (B ≃ₐ[R] B) = ⊥) :
    τ.restrictScalars R = σ ^ (Q.under T).inertiaDeg R :=
  hR.tower_eq_of_inertia_eq_bot_algEquiv hT hbot

/-- In a degree-two residue extension the intermediate Frobenius is the square. -/
theorem gf4_tower_square_one :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) (GaloisField 2 2) ^ 2 = 1 := by
  have h := PR411Model.gf4_base_frobenius.tower_eq_of_inertia_eq_bot_algEquiv
    PR411Model.gf4_intermediate_frobenius PR411Model.gf4_inertia_bot
  rw [PR411Model.under_bot, PR411Model.gf4_inertia_degree] at h
  exact h.symm

/-- The source's intermediate field is bound to its integral closure T. -/
theorem intermediate_field_tower
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R K] [IsFractionRing R K] [Algebra R L] [IsScalarTower R K L]
    (E : IntermediateField K L) [Algebra R E] [IsScalarTower R K E]
    [Algebra R T] [Algebra T E] [IsScalarTower R T E] [IsIntegralClosure T R E]
    [Algebra R B] [Algebra B L] [IsScalarTower R B L] [IsIntegralClosure B R L]
    [Algebra T B] [IsScalarTower R T B] [Algebra T L]
    [IsScalarTower T E L] [IsScalarTower T B L] [Module.Finite R T]
    [MulSemiringAction (L ≃ₐ[K] L) B] [SMulCommClass (L ≃ₐ[K] L) R B]
    [SMulCommClass (↥E.fixingSubgroup) T B]
    {σ : L ≃ₐ[K] L} {τ : E.fixingSubgroup} {Q : Ideal B} [Q.IsPrime]
    (hR : IsArithFrobAt R σ Q) (hT : IsArithFrobAt T τ Q)
    (hbot : Q.inertia (L ≃ₐ[K] L) = ⊥) :
    (τ : L ≃ₐ[K] L) = σ ^ (Q.under T).inertiaDeg R :=
  hR.tower_eq_of_inertia_eq_bot_fixingSubgroup E hT hbot

end PR411Regression
