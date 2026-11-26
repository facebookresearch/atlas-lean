/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer reproduces the theorem type from
`Theorems/Thm_ModularCurve_cayleyHamilton_forall_of_frobeniusQuadratic_of_dense.lean`
in https://github.com/anthropics/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright (c) 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0.
The upstream NOTICE also credits Mathlib and its respective authors under Apache 2.0.
-/

module

public import MathlibExt.NumberTheory.ModularForms.HeckeTorsionCayleyHamilton
import MathlibExt.RingTheory.Valuation.FrobeniusExists

@[expose] public section

open ModularCurve

namespace MathlibExtTest.NumberTheory.ModularForms.HeckeTorsionCayleyHamilton

/-- Source-shaped consumer: the original binders and conclusion. -/
theorem exactSource {J : Type*} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J))) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : J),
      x ∈ heckeTorsion J 𝔪 →
      ∀ (t d : HeckeAlg), Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
        Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0 :=
  cayleyHamilton_forall_of_frobeniusQuadratic_of_dense N p 𝔪 hp ρ hES hS hatt hdense

/-- Higher-universe consumer: the theorem is universe-polymorphic in `J`. -/
theorem exactSourceType1 {J : Type 1} [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg J]
    (N p : ℕ) (𝔪 : Ideal HeckeAlg) (hp : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (hES : FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) N p J)
    {S : Finset ℕ} (hS : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ N * p)
    (hatt : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S →
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ fixingSubgroup
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (heckeTorsion J 𝔪 : Set J))) :
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : J),
      x ∈ heckeTorsion J 𝔪 →
      ∀ (t d : HeckeAlg), Ideal.Quotient.mk 𝔪 t = (ρ σ).trace →
        Ideal.Quotient.mk 𝔪 d = (ρ σ).det →
        σ • σ • x - t • (σ • x) + d • x = 0 :=
  cayleyHamilton_forall_of_frobeniusQuadratic_of_dense N p 𝔪 hp ρ hES hS hatt hdense

/-! ### The density predicate -/

/-- Modulo the whole group, density says exactly that there are a prime `ℓ ∉ S`, a valuation
subring `A` lying over `ℓ` and an element that is Frobenius at `ℓ` for `A`: the power `n = 0`
reaches every `σ`. -/
theorem frobeniusPowerDense_top_iff (S : Finset ℕ) :
    FrobeniusPowerDense S ⊤ ↔
      ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by
  constructor
  · intro h
    obtain ⟨ℓ, A, τ, -, -, hℓ, hS, hA, hτ, -⟩ := h 1
    exact ⟨ℓ, A, τ, hℓ, hS, hA, hτ⟩
  · rintro ⟨ℓ, A, τ, hℓ, hS, hA, hτ⟩ σ
    exact ⟨ℓ, A, τ, 1, 0, hℓ, hS, hA, hτ, Subgroup.mem_top _⟩

/-- Modulo the trivial subgroup, density says that every `σ` equals `g * τ ^ n * g⁻¹` for some
prime `ℓ ∉ S`, valuation subring `A` lying over `ℓ`, element `τ` that is Frobenius at `ℓ` for
`A`, element `g` and exponent `n`. -/
theorem frobeniusPowerDense_bot_iff (S : Finset ℕ) :
    FrobeniusPowerDense S ⊥ ↔
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
          (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
          ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
            g * τ ^ n * g⁻¹ = σ := by
  simp only [FrobeniusPowerDense, Subgroup.mem_bot, mul_inv_eq_one]

/-- Density survives shrinking the exceptional set and enlarging the subgroup. -/
theorem frobeniusPowerDense_mono {S S' : Finset ℕ}
    {H H' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hS : S' ⊆ S) (hH : H ≤ H') (h : FrobeniusPowerDense S H) :
    FrobeniusPowerDense S' H' := by
  intro σ
  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS, hA, hτ, hmem⟩ := h σ
  exact ⟨ℓ, A, τ, g, n, hℓ, fun h' => hℓS (hS h'), hA, hτ, hH hmem⟩

/-- Modulo the whole group, density holds for every finite exceptional set: some prime `ℓ`
lies outside `S`, and `ValuationSubring.exists_isFrobeniusAt_rat` gives a valuation subring
lying over `ℓ` and an element that is Frobenius at `ℓ` for it. -/
theorem frobeniusPowerDense_top (S : Finset ℕ) : FrobeniusPowerDense S ⊤ := by
  obtain ⟨ℓ, hℓ, hℓS⟩ := Nat.infinite_setOfPred_prime.exists_notMem_finset S
  obtain ⟨A, hA, τ, hτ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
  exact (frobeniusPowerDense_top_iff S).mpr ⟨ℓ, A, τ, hℓ, hℓS, hA, hτ⟩

/-- Density is never vacuous: it produces a prime `ℓ ∉ S`, a valuation subring lying over `ℓ`
and an element that is Frobenius at `ℓ` for it. -/
theorem exists_isFrobeniusAt_of_frobeniusPowerDense {S : Finset ℕ}
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (h : FrobeniusPowerDense S H) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ :=
  (frobeniusPowerDense_top_iff S).mp (frobeniusPowerDense_mono subset_rfl le_top h)

/-! ### A concrete Hecke module: the Eisenstein eigensystem modulo `4`

`ZMod 4` is a Hecke module through `T_ℓ ↦ 1 + ℓ`, the eigenvalues of the
weight-two Eisenstein series, with the Galois group acting trivially. Its
torsion for the Eisenstein maximal ideal at `2` is `{0, 2}`. -/

/-- The weight-two Eisenstein eigensystem modulo `n`: `T_ℓ ↦ 1 + ℓ`. -/
noncomputable def eisMod (n : ℕ) : HeckeAlg →+* ZMod n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod n)) fun ℓ => 1 + ((ℓ : ℕ) : ZMod n)

/-- The Eisenstein maximal ideal at `2`. -/
noncomputable abbrev eisIdeal : Ideal HeckeAlg := RingHom.ker (eisMod 2)

/-- `ZMod 4` is a Hecke module through `eisMod 4`. -/
noncomputable local instance : Module HeckeAlg (ZMod 4) :=
  Module.compHom (ZMod 4) (eisMod 4)

/-- The Galois group acts trivially on `ZMod 4`. -/
local instance : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod 4) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

local instance :
    SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (ZMod 4) :=
  ⟨fun _ _ _ => rfl⟩

theorem hecke_smul_eq (t : HeckeAlg) (x : ZMod 4) : t • x = eisMod 4 t * x := rfl

theorem galois_smul_eq (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ZMod 4) :
    σ • x = x := rfl

theorem eisMod_heckeGen (n ℓ : ℕ) (hℓ : ℓ.Prime) :
    eisMod n (heckeGen ⟨ℓ, hℓ⟩) = 1 + (ℓ : ZMod n) :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Reducing `eisMod 4` modulo `2` gives `eisMod 2`. -/
theorem eisMod_two_apply (t : HeckeAlg) :
    eisMod 2 t = ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (eisMod 4 t) := by
  have h : (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).comp (eisMod 4) = eisMod 2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [eisMod]
    · intro ℓ
      simp [eisMod]
  exact (RingHom.congr_fun h t).symm

/-- The `eisIdeal`-torsion of `ZMod 4` is the kernel of multiplication by `2`:
`2 ∈ eisIdeal`, and every element of `eisIdeal` acts by an even residue. -/
theorem mem_heckeTorsion_eisModel_iff (x : ZMod 4) :
    x ∈ heckeTorsion (ZMod 4) eisIdeal ↔ 2 * x = 0 := by
  rw [mem_heckeTorsion_iff]
  constructor
  · intro h
    have h2 : (2 : HeckeAlg) ∈ eisIdeal := by
      rw [RingHom.mem_ker, map_ofNat]
      decide
    simpa only [hecke_smul_eq, map_ofNat] using h 2 h2
  · intro hx t ht
    rw [hecke_smul_eq]
    have h2 : ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2) (eisMod 4 t) = 0 := by
      rw [← eisMod_two_apply]
      exact RingHom.mem_ker.mp ht
    generalize eisMod 4 t = a at h2 ⊢
    revert a x
    decide

theorem two_mem_heckeTorsion : (2 : ZMod 4) ∈ heckeTorsion (ZMod 4) eisIdeal :=
  (mem_heckeTorsion_eisModel_iff 2).mpr (by decide)

theorem one_not_mem_heckeTorsion : (1 : ZMod 4) ∉ heckeTorsion (ZMod 4) eisIdeal :=
  fun h => absurd ((mem_heckeTorsion_eisModel_iff 1).mp h) (by decide)

/-- Units of `ZMod 4` act by multiplication, compatibly with the Hecke action. -/
local instance : SMulCommClass (ZMod 4)ˣ HeckeAlg (ZMod 4) :=
  ⟨fun u t x => by simp only [hecke_smul_eq, Units.smul_def, smul_eq_mul]; ring⟩

/-- A compatible group action preserves torsion: `-1` keeps the torsion
element `2`. -/
example : ((-1 : (ZMod 4)ˣ) • (2 : ZMod 4)) ∈ heckeTorsion (ZMod 4) eisIdeal :=
  smul_mem_heckeTorsion (ZMod 4) (-1) two_mem_heckeTorsion

example : ((-1 : (ZMod 4)ˣ) • (2 : ZMod 4)) = 2 := by
  decide

/-- On torsion, Hecke operators act through `HeckeAlg ⧸ eisIdeal`: `T₅ ∈ eisIdeal`
kills the torsion element `2`, but sends the non-torsion element `1` to `2`. -/
example : heckeGen ⟨5, Nat.prime_five⟩ ∈ eisIdeal := by
  rw [RingHom.mem_ker, eisMod_heckeGen]
  decide

example : heckeGen ⟨5, Nat.prime_five⟩ • (2 : ZMod 4) = 0 := by
  rw [hecke_smul_eq, eisMod_heckeGen]
  decide

example : heckeGen ⟨5, Nat.prime_five⟩ • (1 : ZMod 4) = 2 := by
  rw [hecke_smul_eq, eisMod_heckeGen]
  decide

/-- The quotient `HeckeAlg ⧸ eisIdeal` acts on the torsion submodule: `T₂ ≡ 1`
fixes the torsion element `2`, although `T₂` sends `1` to `3`. -/
example : (Ideal.Quotient.mk eisIdeal (heckeGen ⟨2, Nat.prime_two⟩) •
      (⟨2, two_mem_heckeTorsion⟩ : heckeTorsion (ZMod 4) eisIdeal)) =
    ⟨2, two_mem_heckeTorsion⟩ := by
  rw [Submodule.torsionBySet.mk_smul]
  ext
  rw [Submodule.coe_smul, hecke_smul_eq, eisMod_heckeGen]
  decide

example : heckeGen ⟨2, Nat.prime_two⟩ • (1 : ZMod 4) = 3 := by
  rw [hecke_smul_eq, eisMod_heckeGen]
  decide

/-! ### The theorem on the model -/

/-- The trivial two-dimensional representation over `HeckeAlg ⧸ eisIdeal`. -/
noncomputable abbrev trivRep :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ eisIdeal) := 1

theorem trace_trivRep (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (trivRep σ).trace = 2 := by
  simp [trivRep, Matrix.trace_one]

theorem det_trivRep (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (trivRep σ).det = 1 := by
  simp [trivRep]

theorem mk_natCast_of_odd {ℓ : ℕ} (hℓ : Odd ℓ) :
    Ideal.Quotient.mk eisIdeal (ℓ : HeckeAlg) = 1 := by
  rw [← map_one (Ideal.Quotient.mk eisIdeal), Ideal.Quotient.eq, RingHom.mem_ker, map_sub,
    map_natCast, map_one, ZMod.natCast_eq_one_iff_odd.mpr hℓ, sub_self]

theorem mk_heckeGen_of_odd {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ) :
    Ideal.Quotient.mk eisIdeal (heckeGen ⟨ℓ, hℓ⟩) = 2 := by
  rw [← map_ofNat (Ideal.Quotient.mk eisIdeal) 2, Ideal.Quotient.eq, RingHom.mem_ker, map_sub,
    eisMod_heckeGen, map_ofNat, ZMod.natCast_eq_one_iff_odd.mpr hodd]
  decide

/-- The quadratic Frobenius relation holds on the model with `N = 1`, `p = 2`. -/
theorem frobeniusQuadratic_eisModel :
    FrobeniusQuadratic (K := ℚ) (L := AlgebraicClosure ℚ) 1 2 (ZMod 4) := by
  intro ℓ hℓ _ A _ σ _ x _
  rw [galois_smul_eq, galois_smul_eq, hecke_smul_eq, eisMod_heckeGen, nsmul_eq_mul]
  ring

/-- On the model the density hypothesis says exactly that there are an odd prime `ℓ`, a
valuation subring lying over `ℓ` and an element that is Frobenius at `ℓ` for it. Every other
hypothesis is checked below without using any Frobenius element, so density is the only one
that asks for one. -/
theorem frobeniusPowerDense_eisModel_iff :
    FrobeniusPowerDense {2} (trivRep.ker ⊓ fixingSubgroup
      (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (heckeTorsion (ZMod 4) eisIdeal : Set (ZMod 4))) ↔
      ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
        (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        ℓ.Prime ∧ ℓ ∉ ({2} : Finset ℕ) ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by
  have htop : trivRep.ker ⊓ fixingSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (heckeTorsion (ZMod 4) eisIdeal : Set (ZMod 4)) = ⊤ := by
    rw [MonoidHom.ker_one, top_inf_eq, eq_top_iff]
    intro σ _
    rw [mem_fixingSubgroup_iff]
    intro y _
    rfl
  rw [htop, frobeniusPowerDense_top_iff]

/-- The theorem applied to the model: `N = 1`, `p = 2`, `S = {2}` and the trivial
representation, with every hypothesis checked, density included. -/
theorem eisModel_cayleyHamilton
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ZMod 4)
    (hx : x ∈ heckeTorsion (ZMod 4) eisIdeal) (t d : HeckeAlg)
    (ht : Ideal.Quotient.mk eisIdeal t = 2) (hd : Ideal.Quotient.mk eisIdeal d = 1) :
    σ • σ • x - t • (σ • x) + d • x = 0 := by
  refine cayleyHamilton_forall_of_frobeniusQuadratic_of_dense 1 2 eisIdeal ?_ trivRep
    frobeniusQuadratic_eisModel (S := {2}) ?_ ?_
    (frobeniusPowerDense_eisModel_iff.mpr ((frobeniusPowerDense_top_iff _).mp
      (frobeniusPowerDense_top _)))
    σ x hx t d (by rw [ht, trace_trivRep]) (by rw [hd, det_trivRep])
  · rw [RingHom.mem_ker, map_natCast]
    decide
  · intro ℓ hℓ hℓS hdvd
    rw [one_mul] at hdvd
    exact hℓS (Finset.mem_singleton.mpr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp hdvd))
  · intro ℓ hℓ hℓS A _ τ _
    have hodd : Odd ℓ := hℓ.odd_of_ne_two fun h => hℓS (Finset.mem_singleton.mpr h)
    exact ⟨by rw [mk_heckeGen_of_odd hℓ hodd, trace_trivRep],
      by rw [mk_natCast_of_odd hodd, det_trivRep]⟩

/-- Values: on the torsion element `2`, with the lifts `t = 2 + T₃` of the trace
and `d = 3` of the determinant, the relation reads `2 - 6 * 2 + 3 * 2 = 0`. -/
example (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ • σ • (2 : ZMod 4) - (2 + heckeGen ⟨3, Nat.prime_three⟩) • (σ • (2 : ZMod 4)) +
      (3 : HeckeAlg) • (2 : ZMod 4) = 0 := by
  refine eisModel_cayleyHamilton σ 2 two_mem_heckeTorsion _ _ ?_ ?_
  · rw [← map_ofNat (Ideal.Quotient.mk eisIdeal) 2, Ideal.Quotient.eq, RingHom.mem_ker,
      add_sub_cancel_left, eisMod_heckeGen]
    decide
  · rw [← map_one (Ideal.Quotient.mk eisIdeal), Ideal.Quotient.eq, RingHom.mem_ker, map_sub,
      map_ofNat, map_one]
    decide

/-- The torsion hypothesis matters: at the non-torsion element `1` the same lifts
give `1 - 6 + 3 = 2 ≠ 0`. -/
example (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ • σ • (1 : ZMod 4) - (2 + heckeGen ⟨3, Nat.prime_three⟩) • (σ • (1 : ZMod 4)) +
      (3 : HeckeAlg) • (1 : ZMod 4) ≠ 0 := by
  rw [galois_smul_eq, galois_smul_eq, hecke_smul_eq, hecke_smul_eq, map_add, map_ofNat,
    map_ofNat, eisMod_heckeGen]
  decide

end MathlibExtTest.NumberTheory.ModularForms.HeckeTorsionCayleyHamilton
