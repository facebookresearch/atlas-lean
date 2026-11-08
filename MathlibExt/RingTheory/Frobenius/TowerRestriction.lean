/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Arithmetic Frobenius in towers and restrictions

This module proves the tower assertion of ATLAS `NumberTheoryI`, Proposition
7.22, using Mathlib's `IsArithFrobAt`. For a finite ring tower `R → T → B`,
a prime `Q` of `B`, and actual Frobenius elements over `R` and `T`, the
intermediate Frobenius, embedded into the action over `R`, is the
`(Q.under T).inertiaDeg R`-th power of the base Frobenius when inertia is
trivial. The residue-cardinality identity is derived with Mathlib's
`Ideal.cardQuot_pow_inertiaDeg`; it is not an assumed powered congruence.

In the number-field application `K ⊂ E ⊂ L`, take `R`, `T`, and `B` to be
the three rings of integers. Only the subgroup for `L/E` must fix `T`.
The general theorem uses a compatible homomorphism `H →* G`; the two
specializations use canonical scalar restriction of algebra automorphisms
and `E.fixingSubgroup` inclusion. In the latter, `T` and `B` are explicitly
bound to the integral closures of `R` in `E` and `L`, respectively.

## Main results

* `Ideal.natCard_quotient_under_eq_pow_inertiaDeg`: the intermediate
  residue cardinality is the base residue cardinality raised to its inertia degree.
* `IsArithFrobAt.tower_eq_of_inertia_eq_bot`: the actual Frobenius tower equality.
* `IsArithFrobAt.tower_eq_of_inertia_eq_bot_algEquiv`: canonical automorphism inclusion.
* `IsArithFrobAt.tower_eq_of_inertia_eq_bot_fixingSubgroup`: the intermediate-field case.
* The six power, compatible-comap, inertia, and uniqueness helpers remain
  available. The generic powered-congruence uniqueness lemma assumes the
  powered congruence; the actual tower theorem derives it from the
  intermediate Frobenius premise and the residue-cardinality identity.

The abstract power and restriction arguments adapt the corresponding
sections of `v1/Atlas/NumberTheoryI/code/GaloisExtensions.lean`. Its abstract
`q`/`q^f` result alone does not supply the residue-cardinality calculation.
-/
@[expose] public section

namespace Ideal

variable {S : Type*} [CommRing S] {G : Type*} [Group G]
  [MulSemiringAction G S] {Q : Ideal S} {σ τ : G} {r : ℕ}

/-- If `a - b ∈ I`, then `a ^ n - b ^ n ∈ I` for every `n`. -/
private theorem pow_sub_pow_mem (I : Ideal S) {a b : S} (h : a - b ∈ I)
    (n : ℕ) : a ^ n - b ^ n ∈ I := by
  have h0 : Ideal.Quotient.mk I (a ^ n - b ^ n) = 0 := by
    simp only [map_sub, map_pow, Ideal.Quotient.eq.mpr h, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

/-- Two elements satisfying the same powered congruence differ by an
element of the inertia subgroup of `Q`. -/
theorem mem_inertia_of_forall_smul_sub_pow_mem
    (hσ : ∀ x : S, σ • x - x ^ r ∈ Q) (hτ : ∀ x : S, τ • x - x ^ r ∈ Q) :
    σ * τ⁻¹ ∈ Q.inertia G := by
  rw [Ideal.mem_inertia]
  intro x
  have h1 := hσ (τ⁻¹ • x)
  have h2 := hτ (τ⁻¹ • x)
  have hτy : τ • (τ⁻¹ • x) = x := by
    rw [← mul_smul, mul_inv_cancel, one_smul]
  have hgoal : (σ * τ⁻¹) • x - x
      = (σ • (τ⁻¹ • x) - (τ⁻¹ • x) ^ r) -
        (τ • (τ⁻¹ • x) - (τ⁻¹ • x) ^ r) := by
    rw [mul_smul, hτy]
    abel
  rw [hgoal]
  exact Q.sub_mem h1 h2

end Ideal

namespace AlgHom.IsArithFrobAt

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {φ : S →ₐ[R] S} {Q : Ideal S}

/-- Powers of an arithmetic Frobenius map satisfy the powered congruence:
if `φ x - x ^ q ∈ Q` for all `x`, then `(φ ^ f) x - x ^ q ^ f ∈ Q`. -/
theorem pow_apply_sub_pow_mem (h : φ.IsArithFrobAt Q) :
    ∀ (f : ℕ) (x : S),
      (φ ^ f) x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q := by
  intro f
  induction f with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    have e1 : (φ ^ (n + 1)) x = (φ ^ n) (φ x) := by
      rw [pow_succ, AlgHom.mul_apply]
    have e2 : x ^ (Nat.card (R ⧸ Q.under R)) ^ (n + 1)
        = (x ^ Nat.card (R ⧸ Q.under R)) ^ (Nat.card (R ⧸ Q.under R)) ^ n := by
      rw [pow_succ, mul_comm, pow_mul]
    rw [e1, e2]
    have h1 := ih (φ x)
    have h2 := Ideal.pow_sub_pow_mem Q (h x) ((Nat.card (R ⧸ Q.under R)) ^ n)
    have hsum : (φ ^ n) (φ x) - (φ x) ^ (Nat.card (R ⧸ Q.under R)) ^ n +
        ((φ x) ^ (Nat.card (R ⧸ Q.under R)) ^ n -
          (x ^ Nat.card (R ⧸ Q.under R)) ^
            (Nat.card (R ⧸ Q.under R)) ^ n) ∈ Q :=
      Q.add_mem h1 h2
    convert hsum using 1
    abel

end AlgHom.IsArithFrobAt

namespace IsArithFrobAt

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]
  {G H : Type*} [Group G] [Group H]
  [MulSemiringAction G B] [SMulCommClass G R B]
  [MulSemiringAction H C] [SMulCommClass H R C]
  {σ : G} {Q : Ideal B}

/-- Powers of an arithmetic Frobenius element satisfy the powered
congruence: if `σ • x - x ^ q ∈ Q` for all `x`, with
`q = Nat.card (R ⧸ Q.under R)`, then
`(σ ^ f) • x - x ^ q ^ f ∈ Q`. -/
theorem pow_smul_sub_pow_mem (h : IsArithFrobAt R σ Q) :
    ∀ (f : ℕ) (x : B),
      (σ ^ f) • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q := by
  have h' : ∀ x : B,
      σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q := h
  intro f
  induction f with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    have e1 : (σ ^ (n + 1)) • x = (σ ^ n) • (σ • x) := by
      rw [pow_succ, mul_smul]
    have e2 : x ^ (Nat.card (R ⧸ Q.under R)) ^ (n + 1)
        = (x ^ Nat.card (R ⧸ Q.under R)) ^ (Nat.card (R ⧸ Q.under R)) ^ n := by
      rw [pow_succ, mul_comm, pow_mul]
    rw [e1, e2]
    have h1 := ih (σ • x)
    have h2 := Ideal.pow_sub_pow_mem Q (h' x) ((Nat.card (R ⧸ Q.under R)) ^ n)
    have hsum : (σ ^ n) • (σ • x) - (σ • x) ^ (Nat.card (R ⧸ Q.under R)) ^ n +
        ((σ • x) ^ (Nat.card (R ⧸ Q.under R)) ^ n -
          (x ^ Nat.card (R ⧸ Q.under R)) ^
            (Nat.card (R ⧸ Q.under R)) ^ n) ∈ Q :=
      Q.add_mem h1 h2
    convert hsum using 1
    abel

/-- A Frobenius congruence restricts along a compatible pair: if
`ι : C →ₐ[R] B` and `ρ : G →* H` satisfy `ι (ρ g • c) = g • ι c`, and `σ`
is a Frobenius at `Q`, then `ρ σ` is a Frobenius at `Q.comap ι`. -/
theorem comap (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q) : IsArithFrobAt R (ρ σ) (Q.comap ι) := by
  have hunder : (Q.comap ι).under R = Q.under R := by
    rw [Ideal.under, Ideal.under]
    ext x
    simp only [Ideal.mem_comap, ι.commutes]
  intro c
  show (ρ σ) • c - c ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι
  rw [hunder, Ideal.mem_comap]
  have hmap : ι ((ρ σ) • c - c ^ Nat.card (R ⧸ Q.under R))
      = σ • ι c - (ι c) ^ Nat.card (R ⧸ Q.under R) := by
    rw [map_sub, map_pow, hcompat]
  rw [hmap]
  exact h (ι c)

/-- If `σ` is a Frobenius at `Q` and `τ` satisfies the powered congruence
with exponent `q ^ f`, then `σ ^ f = τ` when the inertia subgroup of `Q` is
trivial. This is a uniqueness helper for an already supplied powered
congruence. The actual tower theorem below derives that congruence from the
Frobenius premise over the intermediate ring and its residue cardinality. -/
theorem pow_eq_of_forall_smul_sub_pow_mem_of_inertia_eq_bot
    {f : ℕ} {τ : G}
    (h : IsArithFrobAt R σ Q)
    (hτ : ∀ x : B, τ • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q)
    (hbot : Q.inertia G = ⊥) : σ ^ f = τ := by
  have hpow := h.pow_smul_sub_pow_mem f
  have hmem := Ideal.mem_inertia_of_forall_smul_sub_pow_mem hpow hτ
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

/-- If `σ` is a Frobenius at `Q` and `τ` satisfies the Frobenius congruence
at `Q.comap ι`, then `ρ σ = τ` when the inertia subgroup of `Q.comap ι` is
trivial. This is the equality form of the restriction statement of
Proposition 7.22 under its unramified hypothesis. -/
theorem eq_comap_of_forall_smul_sub_pow_mem_of_inertia_eq_bot
    (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q)
    {τ : H}
    (hτ : ∀ x : C, τ • x - x ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι)
    (hbot : (Q.comap ι).inertia H = ⊥) : ρ σ = τ := by
  have hrest : ∀ x : C,
      (ρ σ) • x - x ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι :=
    h.comap ι ρ hcompat
  have hmem := Ideal.mem_inertia_of_forall_smul_sub_pow_mem hrest hτ
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

end IsArithFrobAt


namespace Ideal

/-- In a finite ring tower `R → T → B`, the intermediate prime residue quotient
has cardinality equal to the base residue cardinality raised to its canonical
inertia degree. The cardinality theorem is Mathlib's `cardQuot_pow_inertiaDeg`. -/
theorem natCard_quotient_under_eq_pow_inertiaDeg
    (R T : Type*) {B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
    [Module.Finite R T] (Q : Ideal B) [Q.IsPrime]
    [Finite (R ⧸ Q.under R)] [Finite (T ⧸ Q.under T)] :
    Nat.card (T ⧸ Q.under T) =
      Nat.card (R ⧸ Q.under R) ^ (Q.under T).inertiaDeg R := by
  have : (Q.under R).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  have : (Q.under T).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  have : (Q.under T).LiesOver (Q.under R) :=
    Ideal.under_liesOver_of_liesOver T Q (Q.under R)
  simpa only [Submodule.cardQuot_apply] using
    (Ideal.cardQuot_pow_inertiaDeg (Q.under R) (Q.under T)).symm

end Ideal


namespace IsArithFrobAt

/-- In a finite ring tower `R → T → B`, the Frobenius over `T`, embedded into
an action over `R`, equals the Frobenius over `R` raised to the intermediate
residue degree when the inertia subgroup is trivial. Only `H` must fix `T`. -/
theorem tower_eq_of_inertia_eq_bot
    {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
    [Module.Finite R T] {G H : Type*} [Group G] [Group H]
    [MulSemiringAction G B] [SMulCommClass G R B]
    [MulSemiringAction H B] [SMulCommClass H T B]
    {σ : G} {τ : H} {Q : Ideal B} [Q.IsPrime]
    (hR : IsArithFrobAt R σ Q) (ι : H →* G)
    (hcompat : ∀ (h : H) (x : B), (ι h) • x = h • x)
    (hT : IsArithFrobAt T τ Q) (hbot : Q.inertia G = ⊥) :
    ι τ = σ ^ (Q.under T).inertiaDeg R := by
  let : Finite (R ⧸ Q.under R) := hR.finite_quotient
  let : Finite (T ⧸ Q.under T) := hT.finite_quotient
  have hcard := Ideal.natCard_quotient_under_eq_pow_inertiaDeg R T Q
  have htransfer (x : B) :
      (ι τ) • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ (Q.under T).inertiaDeg R ∈ Q := by
    rw [hcompat, ← hcard]
    exact hT x
  exact (hR.pow_eq_of_forall_smul_sub_pow_mem_of_inertia_eq_bot htransfer hbot).symm

end IsArithFrobAt


namespace IsArithFrobAt

/-- For algebra automorphisms in a finite ring tower, the inclusion of the
intermediate Frobenius is the canonical `AlgEquiv.restrictScalars`. -/
theorem tower_eq_of_inertia_eq_bot_algEquiv
    {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R T] [Algebra T B] [Algebra R B] [IsScalarTower R T B]
    [Module.Finite R T] {σ : B ≃ₐ[R] B} {τ : B ≃ₐ[T] B}
    {Q : Ideal B} [Q.IsPrime]
    (hR : IsArithFrobAt R σ Q) (hT : IsArithFrobAt T τ Q)
    (hbot : Q.inertia (B ≃ₐ[R] B) = ⊥) :
    τ.restrictScalars R = σ ^ (Q.under T).inertiaDeg R := by
  simpa only [AlgEquiv.restrictScalarsHom_apply] using
    hR.tower_eq_of_inertia_eq_bot (R := R) (T := T) (B := B)
      (AlgEquiv.restrictScalarsHom R : (B ≃ₐ[T] B) →* (B ≃ₐ[R] B))
      (fun _ _ => rfl) hT hbot

end IsArithFrobAt


namespace IsArithFrobAt

/-- The tower equality for the source's intermediate field `E ⊂ L`.
Here `K` is the fraction field of the base ring `R`, `T` is the integral
closure of `R` in `E`, and `B` is its integral closure in `L`. In the
number-field application these are the three rings of integers. The
intermediate action is `E.fixingSubgroup`; the whole `Gal(L/K)` need not fix `T`. -/
theorem tower_eq_of_inertia_eq_bot_fixingSubgroup
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
    (τ : L ≃ₐ[K] L) = σ ^ (Q.under T).inertiaDeg R := by
  exact hR.tower_eq_of_inertia_eq_bot (R := R) (T := T) (B := B)
    E.fixingSubgroup.subtype (fun _ _ => rfl) hT hbot

end IsArithFrobAt
