/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_CommRing_Pic_exists_boundaryHom_conductorSquare_exact.lean`
and
`P2M/Sol/S_CommRing_Pic_exists_boundaryHom_conductorSquare_exact.lean`
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

public import Mathlib.RingTheory.PicardGroup
import Mathlib.LinearAlgebra.TensorProduct.Quotient

@[expose] public section

open TensorProduct

universe u v

namespace ConductorSquarePic


variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private def glueSubmodule (𝔠 : Ideal B) (u : B ⧸ 𝔠) : Submodule A B where
  carrier := {x | ∃ a : A, u * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add, mul_add, ha, ha', map_add, map_add]⟩
  smul_mem' := by
    rintro r x ⟨a, ha⟩
    refine ⟨r * a, ?_⟩
    rw [Algebra.smul_def, map_mul, mul_left_comm, ha, ← map_mul, ← map_mul]

variable (𝔠 : Ideal B)

private theorem mem_glueSubmodule {u : B ⧸ 𝔠} {x : B} :
    x ∈ glueSubmodule (A := A) 𝔠 u ↔
      ∃ a : A, u * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a) :=
  Iff.rfl

private theorem mem_glueSubmodule_of_mem {u : B ⧸ 𝔠} {x : B} (hx : x ∈ 𝔠) :
    x ∈ glueSubmodule (A := A) 𝔠 u :=
  ⟨0, by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, mul_zero, map_zero, map_zero]⟩

private theorem glueSubmodule_mul_le (u v : B ⧸ 𝔠) :
    glueSubmodule (A := A) 𝔠 u * glueSubmodule 𝔠 v ≤ glueSubmodule 𝔠 (u * v) := by
  rw [Submodule.mul_le]
  rintro x ⟨a, ha⟩ y ⟨b, hb⟩
  refine ⟨a * b, ?_⟩
  rw [map_mul, mul_mul_mul_comm, ha, hb, ← map_mul, ← map_mul]

section conductor

variable {𝔠}
variable (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B))
include h𝔠

private theorem exists_eq_of_mk_eq {x : B} {a : A}
    (h : Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) :
    ∃ a' : A, algebraMap A B a' = x := by
  rw [Ideal.Quotient.eq] at h
  obtain ⟨c, hc⟩ := h𝔠 _ h
  exact ⟨a + c, by rw [map_add, hc, add_sub_cancel]⟩

private theorem glueSubmodule_one : glueSubmodule (A := A) 𝔠 1 = 1 := by
  ext x
  rw [mem_glueSubmodule, Submodule.mem_one]
  constructor
  · rintro ⟨a, ha⟩
    rw [one_mul] at ha
    exact exists_eq_of_mk_eq h𝔠 ha
  · rintro ⟨a, rfl⟩
    exact ⟨a, by rw [one_mul]⟩

variable [FaithfulSMul A B]

omit [FaithfulSMul A B] in

private theorem le_glueSubmodule_mul (u : (B ⧸ 𝔠)ˣ) :
    (𝔠.restrictScalars A : Submodule A B) ≤
      glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) := by
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ 𝔠)
  have hxmem : x ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
    ⟨1, by rw [hx, Units.mul_inv, map_one, map_one]⟩
  have hymem : y ∈ glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
    ⟨1, by rw [hy, Units.inv_mul, map_one, map_one]⟩

  have hc : x * y - 1 ∈ 𝔠 := by
    rw [← Ideal.Quotient.eq, map_mul, hx, hy, Units.inv_mul, map_one]
  intro z hz
  change z ∈ 𝔠 at hz
  have hz1 : z * x * y ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
    Submodule.mul_mem_mul (mem_glueSubmodule_of_mem 𝔠 (𝔠.mul_mem_right _ hz)) hymem
  have hz2 : z * (x * y - 1) ∈
      glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
    Submodule.mul_mem_mul (mem_glueSubmodule_of_mem 𝔠 hz) (mem_glueSubmodule_of_mem 𝔠 hc)
  have : z = z * x * y - z * (x * y - 1) := by ring
  rw [this]
  exact sub_mem hz1 hz2

private theorem glueSubmodule_mul_inv (u : (B ⧸ 𝔠)ˣ) :
    glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) = 1 := by
  apply le_antisymm
  · calc _ ≤ glueSubmodule (A := A) 𝔠 ((u : B ⧸ 𝔠) * ↑u⁻¹) := glueSubmodule_mul_le 𝔠 _ _
      _ = 1 := by rw [Units.mul_inv, glueSubmodule_one h𝔠]
  ·
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ 𝔠)
    have hxmem : x ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
      ⟨1, by rw [hx, Units.mul_inv, map_one, map_one]⟩
    have hymem : y ∈ glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
      ⟨1, by rw [hy, Units.inv_mul, map_one, map_one]⟩
    have hc : x * y - 1 ∈ 𝔠 := by
      rw [← Ideal.Quotient.eq, map_mul, hx, hy, Units.inv_mul, map_one]
    have h1 : (1 : B) ∈
        glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠) := by
      have : (1 : B) = x * y - (x * y - 1) := by ring
      rw [this]
      exact sub_mem (Submodule.mul_mem_mul hxmem hymem) (le_glueSubmodule_mul h𝔠 u hc)
    rw [Submodule.one_le]
    exact h1

private noncomputable def glueUnits : (B ⧸ 𝔠)ˣ →* (Submodule A B)ˣ where
  toFun u :=
    { val := glueSubmodule 𝔠 (u : B ⧸ 𝔠)
      inv := glueSubmodule 𝔠 (↑u⁻¹ : B ⧸ 𝔠)
      val_inv := glueSubmodule_mul_inv h𝔠 u
      inv_val := by rw [mul_comm]; exact glueSubmodule_mul_inv h𝔠 u }
  map_one' := Units.ext (by simp only [Units.val_one]; exact glueSubmodule_one h𝔠)
  map_mul' u v := by
    apply Units.ext
    simp only [Units.val_mul]
    apply le_antisymm
    ·
      have h1 : glueSubmodule (A := A) 𝔠 (↑v⁻¹ : B ⧸ 𝔠) * glueSubmodule 𝔠 (v : B ⧸ 𝔠) = 1 := by
        rw [mul_comm]; exact glueSubmodule_mul_inv h𝔠 v
      calc glueSubmodule (A := A) 𝔠 ((u : B ⧸ 𝔠) * v)
          = glueSubmodule 𝔠 ((u : B ⧸ 𝔠) * v) *
              (glueSubmodule 𝔠 (↑v⁻¹ : B ⧸ 𝔠) * glueSubmodule 𝔠 (v : B ⧸ 𝔠)) := by
            rw [h1, mul_one]
        _ = glueSubmodule 𝔠 ((u : B ⧸ 𝔠) * v) * glueSubmodule 𝔠 (↑v⁻¹ : B ⧸ 𝔠) *
              glueSubmodule 𝔠 (v : B ⧸ 𝔠) := by rw [mul_assoc]
        _ ≤ glueSubmodule 𝔠 ((u : B ⧸ 𝔠) * v * ↑v⁻¹) * glueSubmodule 𝔠 (v : B ⧸ 𝔠) :=
            Submodule.mul_le.mpr fun m hm n hn =>
              Submodule.mul_mem_mul (glueSubmodule_mul_le 𝔠 _ _ hm) hn
        _ = glueSubmodule 𝔠 (u : B ⧸ 𝔠) * glueSubmodule 𝔠 (v : B ⧸ 𝔠) := by
            rw [Units.mul_inv_cancel_right]
    · exact glueSubmodule_mul_le 𝔠 _ _

@[scoped simp] private theorem val_glueUnits (u : (B ⧸ 𝔠)ˣ) :
    (glueUnits h𝔠 u : Submodule A B) = glueSubmodule 𝔠 (u : B ⧸ 𝔠) := rfl

private noncomputable def boundary : (B ⧸ 𝔠)ˣ →* CommRing.Pic A :=
  (Submodule.unitsToPic A B).comp (glueUnits h𝔠)

private theorem boundary_apply (u : (B ⧸ 𝔠)ˣ) :
    boundary h𝔠 u = Submodule.unitsToPic A B (glueUnits h𝔠 u) := rfl

private noncomputable def boundaryEquiv (u : (B ⧸ 𝔠)ˣ) :
    (boundary h𝔠 u : CommRing.Pic A) ≃ₗ[A] ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) :=
  Submodule.unitsToPicEquiv (glueUnits h𝔠 u)

local notation "𝔠A" => Ideal.comap (algebraMap A B) 𝔠

private theorem glueSubmodule_eq_span_of_eq (u : B ⧸ 𝔠) (s : Bˣ) (a : (A ⧸ 𝔠A)ˣ)
    (hu : u = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠A) *
      Ideal.Quotient.mk 𝔠 (s : B)) :
    glueSubmodule (A := A) 𝔠 u = Submodule.span A {((s⁻¹ : Bˣ) : B)} := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (a : A ⧸ 𝔠A)
  obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (↑a⁻¹ : A ⧸ 𝔠A)
  have h01 : Ideal.Quotient.mk 𝔠 (algebraMap A B a₁) *
      Ideal.Quotient.mk 𝔠 (algebraMap A B a₀) = 1 := by
    rw [← Ideal.quotientMap_mk (I := 𝔠) (f := algebraMap A B) (H := le_rfl),
      ← Ideal.quotientMap_mk (I := 𝔠) (f := algebraMap A B) (H := le_rfl), ha₀, ha₁, ← map_mul,
      Units.inv_mul, map_one]
  ext x
  rw [mem_glueSubmodule, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    rw [hu, ← ha₀, Ideal.quotientMap_mk] at hc

    have hc' : Ideal.Quotient.mk 𝔠 ((s : B) * x) =
        Ideal.Quotient.mk 𝔠 (algebraMap A B (a₁ * c)) := by
      have := congrArg (fun z => Ideal.Quotient.mk 𝔠 (algebraMap A B a₁) * z) hc
      rw [← mul_assoc, ← mul_assoc, h01, one_mul, ← map_mul, ← map_mul, ← map_mul] at this
      exact this
    obtain ⟨a', ha'⟩ := exists_eq_of_mk_eq h𝔠 hc'
    refine ⟨a', ?_⟩
    rw [Algebra.smul_def, ha', mul_comm, Units.inv_mul_cancel_left]
  · rintro ⟨c, rfl⟩
    refine ⟨a₀ * c, ?_⟩
    rw [hu, ← ha₀, Ideal.quotientMap_mk, Algebra.smul_def, ← map_mul, ← map_mul,
      mul_mul_mul_comm, Units.mul_inv, mul_one, ← map_mul]

private theorem boundary_eq_one_iff (u : (B ⧸ 𝔠)ˣ) :
    boundary h𝔠 u = 1 ↔
      ∃ (t : Bˣ) (a : (A ⧸ 𝔠A)ˣ),
        (u : B ⧸ 𝔠) = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠A) *
          Ideal.Quotient.mk 𝔠 (t : B) := by
  have hker : boundary h𝔠 u = 1 ↔
      glueUnits h𝔠 u ∈ (Units.map (Submodule.spanSingleton A).toMonoidHom).range := by
    rw [← Submodule.ker_unitsToPic A B, MonoidHom.mem_ker]; rfl
  rw [hker]
  constructor
  · rintro ⟨t, ht⟩
    have hval : Submodule.span A {(t : B)} = glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) := by
      simpa using congrArg (fun w : (Submodule A B)ˣ => (w : Submodule A B)) ht
    have hinv : Submodule.span A {((t⁻¹ : Bˣ) : B)} =
        glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) := by
      have h__af := (congrArg (fun w : (Submodule A B)ˣ => (w : Submodule A B)) (congrArg (·⁻¹) ht))
      simp at h__af
      exact h__af
    have ht_mem : (t : B) ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
      hval ▸ Submodule.mem_span_singleton_self _
    have hti_mem : ((t⁻¹ : Bˣ) : B) ∈ glueSubmodule (A := A) 𝔠 (↑u⁻¹ : B ⧸ 𝔠) :=
      hinv ▸ Submodule.mem_span_singleton_self _
    obtain ⟨a₀, ha₀⟩ := ht_mem
    obtain ⟨a₁, ha₁⟩ := hti_mem
    have hprod : Ideal.Quotient.mk (𝔠A) a₀ * Ideal.Quotient.mk (𝔠A) a₁ = 1 := by
      apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
      rw [map_mul, map_one, Ideal.quotientMap_mk, Ideal.quotientMap_mk, ← ha₀, ← ha₁,
        mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, Units.mul_inv, map_one]
    refine ⟨t⁻¹, ⟨Ideal.Quotient.mk (𝔠A) a₀, Ideal.Quotient.mk (𝔠A) a₁, hprod,
      by rw [mul_comm]; exact hprod⟩, ?_⟩
    change (u : B ⧸ 𝔠) = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (Ideal.Quotient.mk (𝔠A) a₀) *
      Ideal.Quotient.mk 𝔠 ((t⁻¹ : Bˣ) : B)
    rw [Ideal.quotientMap_mk, ← ha₀, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
  · rintro ⟨s, a, hu⟩
    refine ⟨s⁻¹, Units.ext ?_⟩
    change Submodule.span A {((s⁻¹ : Bˣ) : B)} = glueSubmodule 𝔠 (u : B ⧸ 𝔠)
    rw [glueSubmodule_eq_span_of_eq h𝔠 (u : B ⧸ 𝔠) s a hu]

omit [FaithfulSMul A B] in
private theorem exists_unit_eq (hinj : Function.Injective (algebraMap A B)) (t : Bˣ) (a : (A ⧸ 𝔠A)ˣ)
    (h : Ideal.Quotient.mk 𝔠 (t : B) =
      Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠A)) :
    ∃ s : Aˣ, algebraMap A B s = t := by
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective (a : A ⧸ 𝔠A)
  obtain ⟨a₁, ha₁⟩ := Ideal.Quotient.mk_surjective (↑a⁻¹ : A ⧸ 𝔠A)
  have h1 : Ideal.Quotient.mk 𝔠 (t : B) *
      Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ 𝔠A) = 1 := by
    rw [h, ← map_mul, Units.mul_inv, map_one]
  have h' : Ideal.Quotient.mk 𝔠 ((t⁻¹ : Bˣ) : B) =
      Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ 𝔠A) := by
    calc Ideal.Quotient.mk 𝔠 ((t⁻¹ : Bˣ) : B)
        = Ideal.Quotient.mk 𝔠 ((t⁻¹ : Bˣ) : B) * (Ideal.Quotient.mk 𝔠 (t : B) *
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ 𝔠A)) := by
          rw [h1, mul_one]
      _ = Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (↑a⁻¹ : A ⧸ 𝔠A) := by
          rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [← ha₀, Ideal.quotientMap_mk] at h
  rw [← ha₁, Ideal.quotientMap_mk] at h'
  obtain ⟨s₀, hs₀⟩ := exists_eq_of_mk_eq h𝔠 h
  obtain ⟨s₁, hs₁⟩ := exists_eq_of_mk_eq h𝔠 h'
  have hmul : s₀ * s₁ = 1 := hinj (by rw [map_mul, hs₀, hs₁, Units.mul_inv, map_one])
  exact ⟨⟨s₀, s₁, hmul, by rw [mul_comm]; exact hmul⟩, hs₀⟩

private theorem mapAlgebra_boundary (u : (B ⧸ 𝔠)ˣ) :
    CommRing.Pic.mapAlgebra A B (boundary h𝔠 u) = 1 := by
  have : boundary h𝔠 u ∈ (Submodule.unitsToPic A B).range := ⟨glueUnits h𝔠 u, rfl⟩
  rw [Submodule.range_unitsToPic] at this
  exact this

omit [FaithfulSMul A B] h𝔠 in
private theorem exists_of_coe_glueSubmodule (u : B ⧸ 𝔠) (x : ↥(glueSubmodule (A := A) 𝔠 u)) :
    ∃ a : A, u * Ideal.Quotient.mk 𝔠 (x : B) = Ideal.Quotient.mk 𝔠 (algebraMap A B a) :=
  x.2

omit [FaithfulSMul A B] h𝔠 in
private noncomputable def glueValueFun (u : B ⧸ 𝔠) (x : ↥(glueSubmodule (A := A) 𝔠 u)) : A ⧸ 𝔠A :=
  Ideal.Quotient.mk (𝔠A) (Classical.choose (exists_of_coe_glueSubmodule u x))

omit [FaithfulSMul A B] h𝔠 in
private theorem quotientMap_glueValueFun (u : B ⧸ 𝔠) (x : ↥(glueSubmodule (A := A) 𝔠 u)) :
    Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (glueValueFun u x) =
      u * Ideal.Quotient.mk 𝔠 (x : B) := by
  rw [glueValueFun, Ideal.quotientMap_mk]
  exact (Classical.choose_spec (exists_of_coe_glueSubmodule u x)).symm

omit [FaithfulSMul A B] h𝔠 in
private noncomputable def glueValue (u : (B ⧸ 𝔠)ˣ) :
    ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) →ₗ[A] (A ⧸ 𝔠A) where
  toFun := glueValueFun (u : B ⧸ 𝔠)
  map_add' x y := by
    apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
    rw [map_add, quotientMap_glueValueFun, quotientMap_glueValueFun, quotientMap_glueValueFun,
      Submodule.coe_add, map_add, mul_add]
  map_smul' r x := by
    apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
    rw [RingHom.id_apply, quotientMap_glueValueFun, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      map_mul, Ideal.quotientMap_mk, quotientMap_glueValueFun, Submodule.coe_smul, Algebra.smul_def,
      map_mul, mul_left_comm]

omit [FaithfulSMul A B] h𝔠 in
private theorem quotientMap_glueValue (u : (B ⧸ 𝔠)ˣ) (x : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))) :
    Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (glueValue (A := A) u x) =
      (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 (x : B) :=
  quotientMap_glueValueFun _ x

omit [FaithfulSMul A B] in
private theorem mem_smul_top_of_mem (u : (B ⧸ 𝔠)ˣ) (x : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)))
    (hx : (x : B) ∈ 𝔠) :
    x ∈ (𝔠A) • (⊤ : Submodule A ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))) := by
  obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
  obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ 𝔠)
  have hx₀mem : x₀ ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
    ⟨1, by rw [hx₀, Units.mul_inv, map_one, map_one]⟩
  have hc : x₀ * y₀ - 1 ∈ 𝔠 := by
    rw [← Ideal.Quotient.eq, map_mul, hx₀, hy₀, Units.inv_mul, map_one]
  obtain ⟨c₁, hc₁⟩ := h𝔠 _ (𝔠.mul_mem_right y₀ hx)
  obtain ⟨c₂, hc₂⟩ := h𝔠 _ hx
  have hc₁mem : c₁ ∈ 𝔠A := by
    rw [Ideal.mem_comap, hc₁]; exact 𝔠.mul_mem_right y₀ hx
  have hc₂mem : c₂ ∈ 𝔠A := by rw [Ideal.mem_comap, hc₂]; exact hx
  set X₀ : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) := ⟨x₀, hx₀mem⟩
  set C : ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠)) := ⟨x₀ * y₀ - 1, mem_glueSubmodule_of_mem 𝔠 hc⟩
  have hdecomp : x = c₁ • X₀ - c₂ • C := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def,
      Algebra.smul_def, hc₁, hc₂]
    change (x : B) = _ * x₀ - _ * (x₀ * y₀ - 1)
    ring
  rw [hdecomp]
  exact sub_mem (Submodule.smul_mem_smul hc₁mem Submodule.mem_top)
    (Submodule.smul_mem_smul hc₂mem Submodule.mem_top)

private theorem bijective_liftBaseChange_glueValue (u : (B ⧸ 𝔠)ˣ) :
    Function.Bijective ((glueValue (A := A) u).liftBaseChange (A ⧸ 𝔠A)) := by
  set M := ↥(glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠))
  set Φ := (glueValue (A := A) u).liftBaseChange (A ⧸ 𝔠A)
  have hsurj1 : ∀ z : (A ⧸ 𝔠A) ⊗[A] M, ∃ x : M, z = 1 ⊗ₜ x := fun z => by
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _
      (TensorProduct.quotTensorEquivQuotSMul M (𝔠A) z)
    refine ⟨x, ?_⟩
    apply (TensorProduct.quotTensorEquivQuotSMul M (𝔠A)).injective
    rw [← hx, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := hsurj1 z
    rw [LinearMap.liftBaseChange_tmul, one_smul] at hz
    have hx : (x : B) ∈ 𝔠 := by
      have := quotientMap_glueValue (A := A) u x
      rw [hz, map_zero, eq_comm, Units.mul_right_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at this
      exact this
    have hmem := mem_smul_top_of_mem h𝔠 u x hx
    apply (TensorProduct.quotTensorEquivQuotSMul M (𝔠A)).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero]
    exact hmem
  · obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ 𝔠)
    have hx₀mem : x₀ ∈ glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) :=
      ⟨1, by rw [hx₀, Units.mul_inv, map_one, map_one]⟩
    have hval : glueValue (A := A) u ⟨x₀, hx₀mem⟩ = 1 := by
      apply Ideal.quotientMap_injective (I := 𝔠) (f := algebraMap A B)
      rw [quotientMap_glueValue, map_one]
      change (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x₀ = 1
      rw [hx₀, Units.mul_inv]
    intro a
    refine ⟨a ⊗ₜ ⟨x₀, hx₀mem⟩, ?_⟩
    rw [LinearMap.liftBaseChange_tmul, hval, smul_eq_mul, mul_one]

private theorem mapAlgebra_quotient_boundary (u : (B ⧸ 𝔠)ˣ) :
    CommRing.Pic.mapAlgebra A (A ⧸ 𝔠A) (boundary h𝔠 u) = 1 := by
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff]
  exact ⟨(LinearEquiv.baseChange A (A ⧸ 𝔠A) _ _ (boundaryEquiv h𝔠 u)) ≪≫ₗ
    LinearEquiv.ofBijective _ (bijective_liftBaseChange_glueValue h𝔠 u)⟩

omit [FaithfulSMul A B] in
private theorem exists_glueSubmodule_eq (J : Submodule A B) (hJB : ⊤ * J = ⊤)
    (hfree : Nonempty ((A ⧸ 𝔠A) ⊗[A] ↥J ≃ₗ[A ⧸ 𝔠A] (A ⧸ 𝔠A))) :
    ∃ u : (B ⧸ 𝔠)ˣ, glueSubmodule (A := A) 𝔠 (u : B ⧸ 𝔠) = J := by
  obtain ⟨e'⟩ := hfree
  set q := TensorProduct.quotTensorEquivQuotSMul (↥J) (𝔠A)

  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (q (e'.symm 1))
  have hg' : e'.symm 1 = 1 ⊗ₜ g := by
    apply q.injective; rw [← hg, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]

  have hsmul : ∀ y : ↥J, y ∈ (𝔠A) • (⊤ : Submodule A ↥J) → (y : B) ∈ 𝔠 := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun c hc j _ => ?_) (fun y z hy hz => ?_)
    · rw [Submodule.coe_smul, Algebra.smul_def]
      exact 𝔠.mul_mem_right _ (Ideal.mem_comap.mp hc)
    · rw [Submodule.coe_add]; exact add_mem hy hz

  have star : ∀ x : ↥J, ∃ a : A, (x : B) - algebraMap A B a * g ∈ 𝔠 := by
    intro x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e' (1 ⊗ₜ x))
    refine ⟨a, ?_⟩
    have h1 : (1 : A ⧸ 𝔠A) ⊗ₜ[A] x = Ideal.Quotient.mk (𝔠A) a ⊗ₜ[A] g := by
      calc (1 : A ⧸ 𝔠A) ⊗ₜ[A] x = e'.symm (e' (1 ⊗ₜ x)) := (e'.symm_apply_apply _).symm
        _ = e'.symm (Ideal.Quotient.mk (𝔠A) a • 1) := by rw [← ha, smul_eq_mul, mul_one]
        _ = Ideal.Quotient.mk (𝔠A) a • (1 ⊗ₜ g) := by rw [map_smul, hg']
        _ = Ideal.Quotient.mk (𝔠A) a ⊗ₜ[A] g := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : Submodule.Quotient.mk (p := (𝔠A) • (⊤ : Submodule A ↥J)) x =
        Submodule.Quotient.mk (a • g) := by
      rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, h1,
        TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    rw [Submodule.Quotient.eq] at h2
    have := hsmul _ h2
    rwa [Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def] at this

  have hone : (1 : B) ∈ ⊤ * J := by rw [hJB]; exact Submodule.mem_top
  have hunit : IsUnit (Ideal.Quotient.mk 𝔠 (g : B)) := by
    have key : ∀ r ∈ ⊤ * J, ∃ y : B ⧸ 𝔠,
        Ideal.Quotient.mk 𝔠 r = y * Ideal.Quotient.mk 𝔠 (g : B) := by
      intro r hr
      refine Submodule.mul_induction_on hr (fun m _ n hn => ?_) (fun x y hx hy => ?_)
      · obtain ⟨a, ha⟩ := star ⟨n, hn⟩
        refine ⟨Ideal.Quotient.mk 𝔠 m * Ideal.Quotient.mk 𝔠 (algebraMap A B a), ?_⟩
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
        change Ideal.Quotient.mk 𝔠 n = _ at ha
        rw [map_mul (Ideal.Quotient.mk 𝔠) m n, ha, map_mul (Ideal.Quotient.mk 𝔠) _ (g : B),
          mul_assoc]
      · obtain ⟨y₁, h₁⟩ := hx
        obtain ⟨y₂, h₂⟩ := hy
        exact ⟨y₁ + y₂, by rw [map_add, h₁, h₂, add_mul]⟩
    obtain ⟨y, hy⟩ := key 1 hone
    rw [map_one] at hy
    exact IsUnit.of_mul_eq_one_right _ hy.symm

  have hcJ : ∀ c ∈ 𝔠, c ∈ J := by
    intro c hc
    have key : ∀ r ∈ ⊤ * J, c * r ∈ J := by
      intro r hr
      refine Submodule.mul_induction_on hr (fun m _ n hn => ?_) (fun x y hx hy => ?_)
      · obtain ⟨c', hc'⟩ := h𝔠 _ (𝔠.mul_mem_right m hc)
        rw [← mul_assoc, ← hc', ← Algebra.smul_def]
        exact J.smul_mem c' hn
      · rw [mul_add]; exact add_mem hx hy
    simpa using key 1 hone
  refine ⟨hunit.unit⁻¹, ?_⟩
  ext x
  rw [mem_glueSubmodule]
  constructor
  · rintro ⟨a, ha⟩
    rw [Units.inv_mul_eq_iff_eq_mul, IsUnit.unit_spec, ← map_mul, mul_comm,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha
    have : x = (x - algebraMap A B a * g) + a • (g : B) := by rw [Algebra.smul_def]; ring
    rw [this]
    exact add_mem (hcJ _ ha) (J.smul_mem a g.2)
  · intro hx
    obtain ⟨a, ha⟩ := star ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [Units.inv_mul_eq_iff_eq_mul, IsUnit.unit_spec, ← map_mul, mul_comm,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact ha

private theorem exists_boundary_eq (P : CommRing.Pic A) (hB : CommRing.Pic.mapAlgebra A B P = 1)
    (hA : CommRing.Pic.mapAlgebra A (A ⧸ 𝔠A) P = 1) : ∃ u, boundary h𝔠 u = P := by
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff] at hB hA
  obtain ⟨e⟩ := hB
  set J := Module.Flat.submoduleAlgebra e
  have eJ : ↥J ≃ₗ[A] ↥P := Module.Flat.submoduleAlgebraEquiv e
  have hJB : ⊤ * J = ⊤ := Module.Flat.top_mul_submoduleAlgebra e
  have hfree : Nonempty ((A ⧸ 𝔠A) ⊗[A] ↥J ≃ₗ[A ⧸ 𝔠A] (A ⧸ 𝔠A)) :=
    ⟨LinearEquiv.baseChange A (A ⧸ 𝔠A) _ _ eJ ≪≫ₗ hA.some⟩
  obtain ⟨u, hu⟩ := exists_glueSubmodule_eq h𝔠 J hJB hfree
  refine ⟨u, ?_⟩
  rw [boundary_apply, Submodule.unitsToPic_apply, CommRing.Pic.mk_eq_iff]
  exact ⟨LinearEquiv.ofEq _ _ hu ≪≫ₗ eJ⟩

end conductor


end ConductorSquarePic

/-- Construct the conductor-square boundary map from units of `B ⧸ 𝔠` to
`Pic A`, where `A → B` is faithful and every element of `𝔠` comes from `A`.
The image of a unit is represented by the explicit gluing submodule of `B`
cut out by that unit. The kernel consists exactly of the products of a unit
from `A ⧸ 𝔠.comap (algebraMap A B)` and the image of a unit of `B`, and the
image consists exactly of the classes in `Pic A` that become trivial after
base change to both `B` and `A ⧸ 𝔠.comap (algebraMap A B)`. The last
component records that a unit of `B` whose reduction agrees with a unit
coming from `A ⧸ 𝔠.comap (algebraMap A B)` itself comes from a unit of `A`. -/
public theorem CommRing.Pic.exists_boundaryHom_conductorSquare_exact
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔠 : Ideal B) (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B)) :
    ∃ δ : (B ⧸ 𝔠)ˣ →* CommRing.Pic A,
      (∀ u : (B ⧸ 𝔠)ˣ, ∃ I : Submodule A B,
        (∀ x : B, x ∈ I ↔ ∃ a : A,
          (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) ∧
        Nonempty ((δ u : CommRing.Pic A) ≃ₗ[A] ↥I)) ∧
      (∀ u : (B ⧸ 𝔠)ˣ, δ u = 1 ↔
        ∃ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
          (u : B ⧸ 𝔠) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) *
              Ideal.Quotient.mk 𝔠 (t : B)) ∧
      (∀ P : CommRing.Pic A, (∃ u, δ u = P) ↔
        CommRing.Pic.mapAlgebra A B P = 1 ∧
          CommRing.Pic.mapAlgebra A (A ⧸ 𝔠.comap (algebraMap A B)) P = 1) ∧
      (∀ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
        Ideal.Quotient.mk 𝔠 (t : B) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) →
          ∃ s : Aˣ, algebraMap A B s = t) := by
  refine ⟨ConductorSquarePic.boundary h𝔠,
    fun u => ⟨_, fun x => Iff.rfl, ⟨ConductorSquarePic.boundaryEquiv h𝔠 u⟩⟩,
    ConductorSquarePic.boundary_eq_one_iff h𝔠, fun P => ?_,
    fun t a h => ConductorSquarePic.exists_unit_eq h𝔠
      (FaithfulSMul.algebraMap_injective A B) t a h⟩
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨ConductorSquarePic.mapAlgebra_boundary h𝔠 u,
      ConductorSquarePic.mapAlgebra_quotient_boundary h𝔠 u⟩
  · rintro ⟨hB, hA⟩
    exact ConductorSquarePic.exists_boundary_eq h𝔠 P hB hA
