/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GroupCohomology_Kummer.lean`,
`Theorems/Thm_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient.lean`
and
`P2M/Sol/S_KummerTheory_natCard_algEquiv_eq_natCard_powerSubgroup_quotient.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

namespace groupCohomology

namespace Kummer

variable {K : Type} {L : Type} [Field K] [Field L] [Algebra K L]

@[simp]
lemma val_smul_units (σ : L ≃ₐ[K] L) (α : Lˣ) :
    ((σ • α : Lˣ) : L) = σ (α : L) :=
  rfl

lemma smul_units_div (σ : L ≃ₐ[K] L) (x y : Lˣ) :
    σ • (x / y) = σ • x / σ • y := by
  ext
  simp only [val_smul_units, Units.val_div_eq_div_val, map_div₀]

lemma smul_units_pow (σ : L ≃ₐ[K] L) (x : Lˣ) (n : ℕ) :
    σ • (x ^ n) = (σ • x) ^ n := by
  ext
  simp only [val_smul_units, Units.val_pow_eq_pow_val, map_pow]

lemma smul_units_eq_self_of_mem_range (σ : L ≃ₐ[K] L) {α : Lˣ}
    (hα : (α : L) ∈ Set.range (algebraMap K L)) : σ • α = α := by
  obtain ⟨b, hb⟩ := hα
  ext
  rw [val_smul_units, ← hb, AlgEquiv.commutes]

/-- The Kummer cocycle attached to a unit `α`: `σ ↦ (σ • α) / α`. -/
def kummerCocycle (α : Lˣ) (σ : L ≃ₐ[K] L) : Lˣ :=
  σ • α / α

lemma kummerCocycle_apply (α : Lˣ) (σ : L ≃ₐ[K] L) :
    kummerCocycle α σ = σ • α / α :=
  rfl

lemma isMulCoboundary₁_kummerCocycle (α : Lˣ) :
    IsMulCoboundary₁ (kummerCocycle (K := K) α) :=
  ⟨α, fun _ => rfl⟩

theorem isMulCocycle₁_kummerCocycle (α : Lˣ) :
    IsMulCocycle₁ (kummerCocycle (K := K) α) := by
  intro σ τ
  show (σ * τ) • α / α = σ • (τ • α / α) * (σ • α / α)
  rw [mul_smul, smul_units_div, div_mul_div_cancel]

theorem kummerCocycle_mul (α β : Lˣ) (σ : L ≃ₐ[K] L) :
    kummerCocycle (α * β) σ = kummerCocycle α σ * kummerCocycle β σ := by
  show σ • (α * β) / (α * β) = (σ • α / α) * (σ • β / β)
  rw [smul_mul', mul_div_mul_comm]

theorem kummerCocycle_pow_eq_one {p : ℕ} {a : K} {α : Lˣ}
    (hα : algebraMap K L a = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    kummerCocycle α σ ^ p = 1 := by
  have hmem : ((α ^ p : Lˣ) : L) ∈ Set.range (algebraMap K L) :=
    ⟨a, by rw [hα, Units.val_pow_eq_pow_val]⟩
  rw [kummerCocycle_apply, div_pow, ← smul_units_pow,
    smul_units_eq_self_of_mem_range σ hmem, div_self']

theorem kummerCocycle_div_kummerCocycle_of_pow_eq {p : ℕ} {a : K}
    {α β : Lˣ} (hα : algebraMap K L a = (α : L) ^ p)
    (hβ : algebraMap K L a = (β : L) ^ p) :
    (α / β) ^ p = 1 ∧
      ∀ σ : L ≃ₐ[K] L,
        kummerCocycle α σ / kummerCocycle β σ = σ • (α / β) / (α / β) := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [div_pow, div_eq_one]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hα, ← hβ]
  · rw [kummerCocycle_apply, kummerCocycle_apply, smul_units_div,
      div_div_div_comm]

lemma smul_mem_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L) {ζ : Lˣ}
    (hζ : ζ ∈ rootsOfUnity p L) : σ • ζ ∈ rootsOfUnity p L := by
  rw [mem_rootsOfUnity] at hζ ⊢
  rw [← smul_units_pow, hζ, smul_one]

instance instMulDistribMulActionRootsOfUnity (p : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L) where
  smul σ ζ := ⟨σ • (ζ : Lˣ), smul_mem_rootsOfUnity σ ζ.2⟩
  one_smul ζ := Subtype.ext (one_smul _ (ζ : Lˣ))
  mul_smul σ τ ζ := Subtype.ext (mul_smul σ τ (ζ : Lˣ))
  smul_mul σ ζ η := Subtype.ext (smul_mul' σ (ζ : Lˣ) (η : Lˣ))
  smul_one σ := Subtype.ext (smul_one σ)

@[simp]
lemma coe_smul_rootsOfUnity {p : ℕ} (σ : L ≃ₐ[K] L)
    (ζ : rootsOfUnity p L) :
    ((σ • ζ : rootsOfUnity p L) : Lˣ) = σ • (ζ : Lˣ) :=
  rfl

/-- The representation of the Galois group on the `p`-th roots of unity,
used as the coefficient module for the Kummer class. -/
noncomputable abbrev kummerRep (K L : Type) [Field K] [Field L]
    [Algebra K L] (p : ℕ) : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L)

variable {p : ℕ} {a : Kˣ} {α : Lˣ}

def kummerCocycleRoots
    (hα : algebraMap K L (a : K) = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    rootsOfUnity p L :=
  ⟨kummerCocycle α σ, kummerCocycle_pow_eq_one hα σ⟩

@[simp]
lemma coe_kummerCocycleRoots
    (hα : algebraMap K L (a : K) = (α : L) ^ p) (σ : L ≃ₐ[K] L) :
    (kummerCocycleRoots hα σ : Lˣ) = kummerCocycle α σ :=
  rfl

theorem isMulCocycle₁_kummerCocycleRoots
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    IsMulCocycle₁ (kummerCocycleRoots hα) :=
  fun σ τ => Subtype.ext (isMulCocycle₁_kummerCocycle α σ τ)

noncomputable def kummerCocycles
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    cocycles₁ (kummerRep K L p) :=
  cocyclesOfIsMulCocycle₁ (isMulCocycle₁_kummerCocycleRoots hα)

lemma coe_kummerCocycles
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    ⇑(kummerCocycles hα) = Additive.ofMul ∘ kummerCocycleRoots hα :=
  rfl

/-- The Kummer class in `H¹` attached to an element of `K` that becomes a
`p`-th power in `L`, for a chosen `p`-th root. -/
noncomputable def kummerClass
    (hα : algebraMap K L (a : K) = (α : L) ^ p) : H1 (kummerRep K L p) :=
  H1π (kummerRep K L p) (kummerCocycles hα)

theorem kummerClass_eq_of_pow_eq {β : Lˣ}
    (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (a : K) = (β : L) ^ p) :
    kummerClass hα = kummerClass hβ := by
  obtain ⟨hpow, hcob⟩ := kummerCocycle_div_kummerCocycle_of_pow_eq hα hβ
  rw [kummerClass, kummerClass, H1π_eq_iff]
  exact (coboundariesOfIsMulCoboundary₁
    (f := fun σ => kummerCocycleRoots hα σ / kummerCocycleRoots hβ σ)
    ⟨⟨α / β, hpow⟩, fun σ => Subtype.ext (hcob σ).symm⟩).2

theorem mul_pow_eq {b : Kˣ} {β : Lˣ}
    (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (b : K) = (β : L) ^ p) :
    algebraMap K L ((a * b : Kˣ) : K) = ((α * β : Lˣ) : L) ^ p := by
  rw [Units.val_mul, map_mul, hα, hβ, Units.val_mul, mul_pow]

theorem kummerClass_mul {b : Kˣ} {β : Lˣ}
    (hα : algebraMap K L (a : K) = (α : L) ^ p)
    (hβ : algebraMap K L (b : K) = (β : L) ^ p) :
    kummerClass (mul_pow_eq hα hβ) = kummerClass hα + kummerClass hβ := by
  rw [kummerClass, kummerClass, kummerClass, ← map_add]
  congr 1
  ext σ
  exact congrArg Additive.ofMul (Subtype.ext (kummerCocycle_mul α β σ))

theorem inv_pow_eq {a : Kˣ} {α : Lˣ}
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    algebraMap K L ((a⁻¹ : Kˣ) : K) = ((α⁻¹ : Lˣ) : L) ^ p := by
  rw [Units.val_inv_eq_inv_val, map_inv₀, hα, Units.val_inv_eq_inv_val,
    inv_pow]

/-- The subgroup of `Kˣ` of elements that become `p`-th powers in `L`. -/
def powerSubgroup (K L : Type) [Field K] [Field L] [Algebra K L]
    (p : ℕ) : Subgroup Kˣ where
  carrier := {a : Kˣ | ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := fun ⟨α, hα⟩ ⟨β, hβ⟩ => ⟨α * β, mul_pow_eq hα hβ⟩
  inv_mem' := fun ⟨α, hα⟩ => ⟨α⁻¹, inv_pow_eq hα⟩

/-- An element of `Kˣ` lies in `powerSubgroup K L p` exactly when it
becomes a `p`-th power in `L`. -/
@[simp]
theorem mem_powerSubgroup_iff {a : Kˣ} :
    a ∈ powerSubgroup K L p ↔
      ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p :=
  Iff.rfl

theorem range_powMonoidHom_le_powerSubgroup :
    (powMonoidHom p : Kˣ →* Kˣ).range ≤ powerSubgroup K L p := by
  rintro _ ⟨b, rfl⟩
  refine ⟨Units.map (algebraMap K L).toMonoidHom b, ?_⟩
  show algebraMap K L (((b ^ p : Kˣ) : K)) = (algebraMap K L (b : K)) ^ p
  rw [Units.val_pow_eq_pow_val, map_pow]

noncomputable def chosenRoot (a : powerSubgroup K L p) : Lˣ :=
  (mem_powerSubgroup_iff.mp a.2).choose

theorem chosenRoot_spec (a : powerSubgroup K L p) :
    algebraMap K L ((a : Kˣ) : K) = ((chosenRoot a : Lˣ) : L) ^ p :=
  (mem_powerSubgroup_iff.mp a.2).choose_spec

/-- The Kummer homomorphism from `powerSubgroup K L p` to `H¹` of the
roots-of-unity representation. -/
noncomputable def kummerHom (K L : Type) [Field K] [Field L]
    [Algebra K L] (p : ℕ) :
    powerSubgroup K L p →* Multiplicative (H1 (kummerRep K L p)) :=
  MonoidHom.mk' (fun a =>
    Multiplicative.ofAdd (kummerClass (chosenRoot_spec a))) fun a b => by
    have h : kummerClass (chosenRoot_spec (a * b))
        = kummerClass (chosenRoot_spec a)
          + kummerClass (chosenRoot_spec b) := by
      rw [kummerClass_eq_of_pow_eq (chosenRoot_spec (a * b))
        (mul_pow_eq (chosenRoot_spec a) (chosenRoot_spec b))]
      exact kummerClass_mul _ _
    show Multiplicative.ofAdd (kummerClass (chosenRoot_spec (a * b)))
        = Multiplicative.ofAdd (kummerClass (chosenRoot_spec a))
          * Multiplicative.ofAdd (kummerClass (chosenRoot_spec b))
    rw [← ofAdd_add, h]

@[simp]
theorem kummerHom_apply (a : powerSubgroup K L p) :
    kummerHom K L p a
      = Multiplicative.ofAdd (kummerClass (chosenRoot_spec a)) :=
  rfl

theorem kummerHom_apply_mk (a : Kˣ) (α : Lˣ)
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerHom K L p ⟨a, α, hα⟩
      = Multiplicative.ofAdd (kummerClass hα) := by
  show Multiplicative.ofAdd (kummerClass (chosenRoot_spec ⟨a, α, hα⟩)) = _
  rw [kummerClass_eq_of_pow_eq (chosenRoot_spec ⟨a, α, hα⟩) hα]

variable [FiniteDimensional K L] [IsGalois K L]

theorem exists_kummerCocycle_eq_of_isMulCocycle1
    {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f)
    (hfp : ∀ σ : L ≃ₐ[K] L, f σ ^ p = 1) :
    ∃ (a : Kˣ) (α : Lˣ),
      algebraMap K L (a : K) = (α : L) ^ p
        ∧ ∀ σ : L ≃ₐ[K] L, f σ = kummerCocycle α σ := by
  obtain ⟨α, hα⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  have hfix : ∀ σ : L ≃ₐ[K] L, σ ((α ^ p : Lˣ) : L) = ((α ^ p : Lˣ) : L) := by
    intro σ
    rw [← val_smul_units, smul_units_pow]
    have h1 : (σ • α) ^ p = α ^ p * (f σ) ^ p := by
      rw [← hα σ, div_pow, mul_div_assoc']
      rw [mul_comm, mul_div_assoc, div_self', mul_one]
    rw [h1, hfp σ, mul_one]
  obtain ⟨c, hc⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed ((α ^ p : Lˣ) : L)).mpr hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (α ^ p).ne_zero (by rw [← hc, map_zero])
  exact ⟨Units.mk0 c hc0, α,
    by rw [Units.val_mk0, hc, Units.val_pow_eq_pow_val],
    fun σ => (hα σ).symm⟩

theorem exists_kummerClass_eq (x : H1 (kummerRep K L p)) :
    ∃ (a : Kˣ) (α : Lˣ) (hα : algebraMap K L (a : K) = (α : L) ^ p),
      x = kummerClass hα := by
  induction x using H1_induction_on with
  | h y =>
    have hy : IsMulCocycle₁ (M := rootsOfUnity p L) (Additive.toMul ∘ ⇑y) :=
      isMulCocycle₁_of_mem_cocycles₁ _ y.2
    set f : (L ≃ₐ[K] L) → Lˣ :=
      fun σ => ((Additive.toMul (y.1 σ) : rootsOfUnity p L) : Lˣ) with hf_def
    have hf : IsMulCocycle₁ f :=
      fun σ τ => congrArg Subtype.val (hy σ τ)
    have hfp : ∀ σ : L ≃ₐ[K] L, f σ ^ p = 1 := fun σ =>
      (mem_rootsOfUnity p _).1 (Additive.toMul (y.1 σ) : rootsOfUnity p L).2
    obtain ⟨a, α, hα, hfeq⟩ := exists_kummerCocycle_eq_of_isMulCocycle1 hf hfp
    refine ⟨a, α, hα, ?_⟩
    have hy_eq : y = kummerCocycles hα := by
      ext σ
      exact congrArg Additive.ofMul (Subtype.ext (hfeq σ))
    rw [kummerClass, hy_eq]

theorem exists_pow_eq_iff_exists_rootOfUnity_coboundary
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Lˣ, ζ ^ p = 1
        ∧ ∀ σ : L ≃ₐ[K] L, σ • ζ / ζ = kummerCocycle α σ := by
  constructor
  · rintro ⟨b, rfl⟩
    set β : Lˣ := Units.map (algebraMap K L : K →* L) b with hβ_def
    have hβval : (β : L) = algebraMap K L (b : K) := rfl
    have hβrange : (β : L) ∈ Set.range (algebraMap K L) := ⟨b, hβval.symm⟩
    have hβp : β ^ p = α ^ p := by
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hβval,
        ← map_pow, ← hα, Units.val_pow_eq_pow_val]
    refine ⟨α / β, ?_, fun σ => ?_⟩
    · rw [div_pow, hβp, div_self']
    · rw [smul_units_div, smul_units_eq_self_of_mem_range σ hβrange,
        kummerCocycle_apply, div_div_div_comm, div_self', div_one]
  · rintro ⟨ζ, hζp, hζ⟩
    have hfix : ∀ σ : L ≃ₐ[K] L,
        σ ((α / ζ : Lˣ) : L) = ((α / ζ : Lˣ) : L) := by
      intro σ
      rw [← val_smul_units, smul_units_div]
      congr 1
      rw [div_eq_div_iff_mul_eq_mul]
      have h1 : σ • ζ * α = σ • α * ζ :=
        div_eq_div_iff_mul_eq_mul.mp (hζ σ)
      rw [mul_comm (α : Lˣ) (σ • ζ)]
      exact h1.symm
    obtain ⟨c, hc⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed ((α / ζ : Lˣ) : L)).mpr hfix
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (α / ζ).ne_zero (by rw [← hc, map_zero])
    refine ⟨Units.mk0 c hc0, ?_⟩
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    apply (algebraMap K L).injective
    rw [map_pow, hc, hα, Units.val_div_eq_div_val, div_pow,
      ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hζp,
      Units.val_one, div_one]

theorem kummerClass_eq_zero_iff
    (hα : algebraMap K L (a : K) = (α : L) ^ p) :
    kummerClass hα = 0 ↔ ∃ b : Kˣ, b ^ p = a := by
  rw [kummerClass, H1π_eq_zero_iff]
  constructor
  · intro h
    have h2 : IsMulCoboundary₁ (M := rootsOfUnity p L)
        (kummerCocycleRoots hα) :=
      isMulCoboundary₁_of_mem_coboundaries₁ _ h
    obtain ⟨ζ, hζ⟩ := h2
    refine (exists_pow_eq_iff_exists_rootOfUnity_coboundary hα).2
      ⟨(ζ : Lˣ), (mem_rootsOfUnity p (ζ : Lˣ)).1 ζ.2, fun σ => ?_⟩
    exact congrArg (Subtype.val) (hζ σ)
  · intro h
    obtain ⟨ζ, hζp, hζ⟩ :=
      (exists_pow_eq_iff_exists_rootOfUnity_coboundary hα).1 h
    exact (coboundariesOfIsMulCoboundary₁
      (f := kummerCocycleRoots hα)
      ⟨⟨ζ, hζp⟩, fun σ => Subtype.ext (hζ σ)⟩).2

theorem ker_kummerHom (p : ℕ) :
    (kummerHom K L p).ker
      = ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf
          (powerSubgroup K L p) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, kummerHom_apply,
    ofAdd_eq_one, kummerClass_eq_zero_iff]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb⟩, fun ⟨b, hb⟩ => ⟨b, hb⟩⟩

theorem kummerHom_surjective (p : ℕ) :
    Function.Surjective (kummerHom K L p) := by
  intro x
  obtain ⟨a, α, hα, hx⟩ := exists_kummerClass_eq (Multiplicative.toAdd x)
  refine ⟨⟨a, α, hα⟩, ?_⟩
  rw [kummerHom_apply_mk a α hα, ← hx]
  exact ofAdd_toAdd x

/-- The first cohomology of the roots-of-unity representation has the
same cardinal as the Kummer quotient `Δ / Kˣⁿ`. -/
theorem natCard_H1_eq_natCard_quotient (p : ℕ) :
    Nat.card (H1 (kummerRep K L p))
      = Nat.card (powerSubgroup K L p ⧸
          ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf
            (powerSubgroup K L p)) := by
  let e : (powerSubgroup K L p ⧸
        ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf
          (powerSubgroup K L p))
      ≃* Multiplicative (H1 (kummerRep K L p)) :=
    (QuotientGroup.quotientMulEquivOfEq (ker_kummerHom (K := K) (L := L) p).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (kummerHom_surjective p))
  exact ((Nat.card_congr e.toEquiv).trans
    (Nat.card_congr Multiplicative.toAdd)).symm

/-- Kummer theory: for a finite Galois extension `L/K` with abelian
Galois group of exponent dividing `n`, with `K` containing a primitive
`n`-th root of unity, the cardinal of the Galois group equals the
cardinal of the Kummer quotient `Δ / Kˣⁿ`, where `Δ` is the subgroup of
`Kˣ` of elements that become `n`-th powers in `L`. -/
theorem natCard_algEquiv_eq_natCard_powerSubgroup_quotient {n : ℕ}
    (hμ : (primitiveRoots n K).Nonempty)
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ)
    (hexp : ∀ σ : L ≃ₐ[K] L, σ ^ n = 1) :
    Nat.card (L ≃ₐ[K] L)
      = Nat.card (powerSubgroup K L n ⧸
          ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf
            (powerSubgroup K L n)) := by
  classical
  rw [← natCard_H1_eq_natCard_quotient (K := K) (L := L) n]
  obtain ⟨ζ, hζmem⟩ := hμ
  have hnpos : 0 < n :=
    Nat.pos_of_ne_zero (by rintro rfl; simp at hζmem)
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots hnpos).1 hζmem
  haveI : NeZero n := ⟨hnpos.ne'⟩
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) n :=
    hζ.map_of_injective (algebraMap K L).injective
  haveI htriv : (kummerRep K L n).IsTrivial := by
    refine ⟨fun σ => ?_⟩
    apply LinearMap.ext
    intro x
    have hξ : (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) ^ n = 1 := by
      have h := (Additive.toMul x).2
      rw [mem_rootsOfUnity] at h
      have h__af := congrArg Units.val h
      simp at h__af
      exact h__af
    obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one hξ
    have hfix : σ • (Additive.toMul x : rootsOfUnity n L)
        = Additive.toMul x :=
      Subtype.ext (Units.ext (by
        show σ (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L)
          = ((Additive.toMul x : rootsOfUnity n L) : Lˣ)
        rw [← hi, map_pow, AlgEquiv.commutes]))
    rw [LinearMap.id_apply]
    change Additive.ofMul
      (σ • (Additive.toMul x : rootsOfUnity n L) : rootsOfUnity n L) = x
    rw [hfix]
    rfl
  have h1 : Nat.card (H1 (kummerRep K L n))
      = Nat.card (Additive (L ≃ₐ[K] L) →+ Additive (rootsOfUnity n L)) :=
    Nat.card_congr (H1IsoOfIsTrivial
      (kummerRep K L n)).toLinearEquiv.toEquiv
  have h2 : Nat.card (Additive (L ≃ₐ[K] L) →+ Additive (rootsOfUnity n L))
      = Nat.card ((L ≃ₐ[K] L) →* rootsOfUnity n L) :=
    (Nat.card_congr (MonoidHom.toAdditive
      (α := L ≃ₐ[K] L) (β := rootsOfUnity n L))).symm
  have h3 : Nat.card ((L ≃ₐ[K] L) →* rootsOfUnity n L)
      = Nat.card ((L ≃ₐ[K] L) →* Lˣ) := by
    refine Nat.card_congr ⟨fun f => (rootsOfUnity n L).subtype.comp f,
      fun f => f.codRestrict (rootsOfUnity n L)
        (fun σ => by rw [mem_rootsOfUnity, ← map_pow, hexp, map_one]),
      fun f => by ext; rfl, fun f => by ext; rfl⟩
  have h4 : Nat.card ((L ≃ₐ[K] L) →* Lˣ) = Nat.card (L ≃ₐ[K] L) := by
    letI : CommGroup (L ≃ₐ[K] L) :=
      { toGroup := inferInstance, mul_comm := hcomm }
    have hexp' : Monoid.exponent (L ≃ₐ[K] L) ∣ n :=
      Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    haveI : NeZero (Monoid.exponent (L ≃ₐ[K] L)) :=
      ⟨Monoid.exponent_ne_zero_of_finite⟩
    haveI : HasEnoughRootsOfUnity L (Monoid.exponent (L ≃ₐ[K] L)) := by
      obtain ⟨d, hd⟩ := hexp'
      exact ⟨⟨algebraMap K L ζ ^ d,
        hζL.pow hnpos (by rw [hd, mul_comm])⟩, inferInstance⟩
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity
      (L ≃ₐ[K] L) L
  exact (h1.trans (h2.trans (h3.trans h4))).symm

end Kummer

end groupCohomology
