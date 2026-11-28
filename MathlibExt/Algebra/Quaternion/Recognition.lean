/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four.lean`
and
`P2M/Sol/S_exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Central.Basic
import Mathlib.Tactic
import Mathlib.Algebra.QuaternionBasis

/-!
# Recognition of quaternion algebras over `ℚ`
-/
@[expose] public section

set_option autoImplicit false

open scoped Quaternion

namespace QuaternionRecog

variable {D : Type*} [Ring D] [Algebra ℚ D]

private theorem mul_eq_zero_iff_of_units (hdiv : ∀ x : D, x ≠ 0 → IsUnit x) {x y : D} : x * y = 0
  ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨u, rfl⟩ := hdiv x hne.1
    exact hne.2 (by simpa using congrArg (fun z => (↑u⁻¹ : D) * z) h)
  · rintro (rfl | rfl) <;> simp

private theorem eq_zero_of_smul_add_smul_one [Nontrivial D] {i : D} (hi : i ∉ Set.range
  (algebraMap ℚ D)) {c d : ℚ}
    (h : c • i + d • (1 : D) = 0) : c = 0 ∧ d = 0 := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_smul, zero_add, smul_eq_zero, one_ne_zero, or_false] at h
    exact ⟨rfl, h⟩
  · exfalso
    apply hi
    refine ⟨-d / c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    have : i = c⁻¹ • (-(d • (1 : D))) := by
      rw [← eq_neg_iff_add_eq_zero] at h
      rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this, smul_neg, smul_smul, neg_div, neg_smul, div_eq_inv_mul]

private theorem exists_mul_self_eq_smul_add_smul (hdim : Module.finrank ℚ D = 4)
    (hdiv : ∀ x : D, x ≠ 0 → IsUnit x)
    (hcen : ∀ z : D, (∀ x : D, z * x = x * z) → z ∈ Set.range (algebraMap ℚ D))
    {i : D} (hi : i ∉ Set.range (algebraMap ℚ D)) :
    ∃ β γ : ℚ, i * i = β • i + γ • (1 : D) := by
  have hpos : 0 < Module.finrank ℚ D := by omega
  haveI : Nontrivial D := Module.nontrivial_of_finrank_pos hpos
  haveI : Module.Finite ℚ D := Module.finite_of_finrank_pos hpos
  haveI : NoZeroDivisors D := ⟨fun h => (mul_eq_zero_iff_of_units hdiv).mp h⟩
  haveI : IsDomain D := NoZeroDivisors.to_isDomain D
  let S : Subalgebra ℚ D := Algebra.adjoin ℚ {i}
  have hiS : i ∈ S := Algebra.subset_adjoin rfl
  haveI : Algebra.IsIntegral ℚ S := Algebra.IsIntegral.of_finite ℚ S
  have hSf : IsField S := isField_of_isIntegral_of_isField' (Field.toIsField ℚ)
  letI : Field S := hSf.toField

  have htower : Module.finrank ℚ S * Module.finrank S D = 4 := by
    rw [Module.finrank_mul_finrank ℚ S D, hdim]

  have hS4 : Module.finrank ℚ S ≠ 4 := by
    intro h4
    have htop : Subalgebra.toSubmodule S = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h4, hdim])
    apply hi
    apply hcen
    intro x
    have hx : x ∈ S := by
      have : x ∈ Subalgebra.toSubmodule S := by rw [htop]; trivial
      exact this
    have := mul_comm (⟨i, hiS⟩ : S) ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hS1 : Module.finrank ℚ S ≠ 1 := by
    intro h1
    have hone : (1 : S) ≠ 0 := one_ne_zero
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' (1 : S) hone).mp h1 ⟨i, hiS⟩
    apply hi
    refine ⟨c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact congrArg Subtype.val hc
  have hS0 : Module.finrank ℚ S ≠ 0 := Module.finrank_pos.ne'
  have hS2 : Module.finrank ℚ S = 2 := by
    have hdvd : Module.finrank ℚ S ∣ 4 := Dvd.intro _ htower
    have hle : Module.finrank ℚ S ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Module.finrank ℚ S
    · exact absurd rfl hS0
    · exact absurd rfl hS1
    · rfl
    · omega
    · exact absurd rfl hS4

  let f : Fin 3 → S := ![1, ⟨i, hiS⟩, ⟨i * i, S.mul_mem hiS hiS⟩]
  have hdep : ¬ LinearIndependent ℚ f := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, hS2] at this
    omega
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hgD : g 0 • (1 : D) + g 1 • i + g 2 • (i * i) = 0 := by
    have := congrArg Subtype.val hg
    simpa [f, Fin.sum_univ_three] using this
  have hg2 : g 2 ≠ 0 := by
    intro h2
    rw [h2, zero_smul, add_zero, add_comm] at hgD
    obtain ⟨h1, h0⟩ := eq_zero_of_smul_add_smul_one hi hgD
    fin_cases k <;> simp_all
  refine ⟨-(g 1) / g 2, -(g 0) / g 2, ?_⟩
  have : i * i = (g 2)⁻¹ • (-(g 0 • (1 : D) + g 1 • i)) := by
    have h' : g 2 • (i * i) = -(g 0 • (1 : D) + g 1 • i) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hgD
    rw [← h', smul_smul, inv_mul_cancel₀ hg2, one_smul]
  rw [this, neg_add, smul_add, smul_neg, smul_neg, smul_smul, smul_smul]
  module

end QuaternionRecog

open QuaternionRecog in
/-- **Recognition of quaternion algebras over `ℚ`.** A four-dimensional
central division algebra over `ℚ` is a quaternion algebra: there are nonzero
`a, b : ℚ` with `D ≃ₐ[ℚ] ℍ[ℚ, a, b]`. Here `hdiv` and `hcen` say that `D` is a division ring
with centre `ℚ`. The same result, stated with the classes `DivisionRing D` and
`Algebra.IsCentral ℚ D`, is
`Algebra.IsCentral.exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four`. -/
public theorem exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
    (D : Type*) [Ring D] [Algebra ℚ D] (hdim : Module.finrank ℚ D = 4)
    (hdiv : ∀ x : D, x ≠ 0 → IsUnit x)
    (hcen : ∀ z : D, (∀ x : D, z * x = x * z) → z ∈ Set.range (algebraMap ℚ D)) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) := by
  have hpos : 0 < Module.finrank ℚ D := by omega
  haveI : Nontrivial D := Module.nontrivial_of_finrank_pos hpos
  haveI : Module.Finite ℚ D := Module.finite_of_finrank_pos hpos
  have hzd : ∀ {x y : D}, x * y = 0 → x = 0 ∨ y = 0 := fun h => (mul_eq_zero_iff_of_units hdiv).mp h

  have hrange : ∀ x : D, x ∈ Set.range (algebraMap ℚ D) ↔ ∃ c : ℚ, x = c • 1 := fun x => by
    constructor
    · rintro ⟨c, rfl⟩; exact ⟨c, Algebra.algebraMap_eq_smul_one c⟩
    · rintro ⟨c, rfl⟩; exact ⟨c, Algebra.algebraMap_eq_smul_one c⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : D, i₀ ∉ Set.range (algebraMap ℚ D) := by
    by_contra hall
    push Not at hall
    have hsurj : Function.Surjective (Algebra.linearMap ℚ D) := fun x => hall x
    have h1 : Module.finrank ℚ D ≤ Module.finrank ℚ ℚ := by
      have := LinearMap.finrank_range_le (Algebra.linearMap ℚ D)
      rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at this
    rw [Module.finrank_self] at h1
    omega

  obtain ⟨β, γ, hq⟩ := exists_mul_self_eq_smul_add_smul hdim hdiv hcen hi₀
  let i : D := (2 : ℚ) • i₀ - β • (1 : D)
  let a : ℚ := 4 * γ + β ^ 2
  have hii : i * i = a • (1 : D) := by
    simp only [i, a, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, hq,
      smul_add, smul_smul]
    module
  have hi : i ∉ Set.range (algebraMap ℚ D) := by
    rintro ⟨c, hc⟩
    apply hi₀
    refine ⟨(c + β) / 2, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one] at hc ⊢
    have h2 : (2 : ℚ) • i₀ = c • (1 : D) + β • 1 := sub_eq_iff_eq_add.mp (by simpa [i] using
      hc.symm)
    calc ((c + β) / 2) • (1 : D) = (2 : ℚ)⁻¹ • (c • (1 : D) + β • 1) := by module
      _ = (2 : ℚ)⁻¹ • ((2 : ℚ) • i₀) := by rw [h2]
      _ = i₀ := by rw [smul_smul]; norm_num
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at hii
    rcases hzd hii with h | h <;> exact hi (h ▸ ⟨0, by simp⟩)

  obtain ⟨y, hy⟩ : ∃ y : D, i * y ≠ y * i := by
    by_contra hall
    push Not at hall
    exact hi (hcen i hall)
  let j : D := i * y - y * i
  have hj0 : j ≠ 0 := fun h => hy (sub_eq_zero.mp h)
  have hji : j * i = -(i * j) := by
    have h1 : i * (i * y) = a • y := by rw [← mul_assoc, hii, smul_mul_assoc, one_mul]
    have h2 : y * i * i = a • y := by rw [mul_assoc, hii, mul_smul_comm, mul_one]
    simp only [j, sub_mul, mul_sub, h2, mul_assoc]
    rw [← mul_assoc i i y, hii, smul_mul_assoc, one_mul]
    abel

  have hij_i : i * j * i = -(a • j) := by
    rw [mul_assoc, hji, mul_neg, ← mul_assoc, hii, smul_mul_assoc, one_mul]
  have hlin : ∀ α β' γ' δ : ℚ, α • (1 : D) + β' • i + γ' • j + δ • (i * j) = 0 → α = 0 ∧ β' = 0 ∧
    γ' = 0 ∧ δ = 0 := by
    intro α β' γ' δ hR

    have hL : i * (α • (1 : D) + β' • i + γ' • j + δ • (i * j)) = α • i + (β' * a) • (1 : D) + γ'
      • (i * j) + (δ * a) • j := by
      simp only [mul_add, mul_smul_comm, mul_one, hii, ← mul_assoc, smul_mul_assoc, one_mul,
        smul_smul, mul_comm β' a, mul_comm δ a]
    have hRt : (α • (1 : D) + β' • i + γ' • j + δ • (i * j)) * i = α • i + (β' * a) • (1 : D) -
      γ' • (i * j) - (δ * a) • j := by
      simp only [add_mul, smul_mul_assoc, one_mul, hii, hji, hij_i, smul_neg, smul_smul, mul_comm
        β' a, mul_comm δ a]
      abel
    have hdiff : ((2 * γ') • i + (2 * δ * a) • (1 : D)) * j = 0 := by
      have e1 := congrArg (i * ·) hR
      have e2 := congrArg (· * i) hR
      simp only [mul_zero, zero_mul] at e1 e2
      rw [hL] at e1
      rw [hRt] at e2
      have e3 : (α • i + (β' * a) • (1 : D) + γ' • (i * j) + (δ * a) • j) - (α • i + (β' * a) •
        (1 : D) - γ' • (i * j) - (δ * a) • j) = 0 := by
        rw [e1, e2, sub_zero]
      have e4 : (2 * γ') • (i * j) + (2 * δ * a) • j = 0 := by
        rw [← e3]; module
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
      exact e4
    rcases hzd hdiff with h | h
    · obtain ⟨hγ, hδ⟩ := eq_zero_of_smul_add_smul_one hi h
      have hγ0 : γ' = 0 := by linarith
      have hδ0 : δ = 0 := by
        rcases mul_eq_zero.mp hδ with h' | h'
        · linarith
        · exact absurd h' ha
      rw [hγ0, hδ0, zero_smul, zero_smul, add_zero, add_zero, add_comm] at hR
      obtain ⟨hβ, hα⟩ := eq_zero_of_smul_add_smul_one hi hR
      exact ⟨hα, hβ, hγ0, hδ0⟩
    · exact absurd h hj0
  let v : Fin 4 → D := ![1, i, j, i * j]
  have hvli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have hsum : g 0 • (1 : D) + g 1 • i + g 2 • j + g 3 • (i * j) = 0 := by
      simpa [v, Fin.sum_univ_four] using hg
    obtain ⟨h0, h1, h2, h3⟩ := hlin _ _ _ _ hsum
    fin_cases k <;> assumption
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hdim])

  have hjj_comm : ∀ x : D, (j * j) * x = x * (j * j) := by
    have hgen : ∀ x ∈ Set.range v, (j * j) * x = x * (j * j) := by
      rintro x ⟨k, rfl⟩
      fin_cases k
      · simp [v]
      · show j * j * i = i * (j * j)
        rw [mul_assoc, hji, mul_neg, ← mul_assoc, hji, neg_mul, neg_neg, mul_assoc]
      · show j * j * j = j * (j * j)
        rw [mul_assoc]
      · show j * j * (i * j) = i * j * (j * j)
        rw [← mul_assoc (j * j) i j, mul_assoc j j i, hji, mul_neg, ← mul_assoc j i j, hji]
        simp only [neg_mul, neg_neg]
        rw [mul_assoc (i * j) j j]
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul, hx, hy]
    | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, hx]
  obtain ⟨b, hb⟩ := hcen (j * j) hjj_comm
  have hjj : j * j = b • (1 : D) := by rw [← hb, Algebra.algebraMap_eq_smul_one]
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hjj
    rcases hzd hjj with h | h <;> exact hj0 h

  let B : QuaternionAlgebra.Basis D a 0 b :=
    { i := i, j := j, k := i * j,
      i_mul_i := by rw [hii, zero_smul, add_zero]
      j_mul_j := hjj
      i_mul_j := rfl
      j_mul_i := by rw [hji, zero_smul, zero_sub] }
  let f : ℍ[ℚ, a, b] →ₐ[ℚ] D := B.liftHom
  have hf : ∀ q : ℍ[ℚ, a, b], f q = q.re • (1 : D) + q.imI • i + q.imJ • j + q.imK • (i * j) :=
    fun q => by
    show B.lift q = _
    rw [QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one]
  have hsurj : Function.Surjective f := by
    have hrange : Set.range v ⊆ (LinearMap.range f.toLinearMap : Set D) := by
      rintro x ⟨k, rfl⟩
      fin_cases k
      · exact ⟨1, by simp [v]⟩
      · exact ⟨⟨0, 1, 0, 0⟩, by simp [hf, v]⟩
      · exact ⟨⟨0, 0, 1, 0⟩, by simp [hf, v]⟩
      · exact ⟨⟨0, 0, 0, 1⟩, by simp [hf, v]⟩
    have htop : LinearMap.range f.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan]
      exact Submodule.span_le.mpr hrange
    exact LinearMap.range_eq_top.mp htop
  have hbij : Function.Bijective f := by
    refine ⟨?_, hsurj⟩
    have hfin : Module.finrank ℚ ℍ[ℚ, a, b] = Module.finrank ℚ D := by
      rw [QuaternionAlgebra.finrank_eq_four, hdim]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f :=
      f.toLinearMap)).mpr hsurj
  exact ⟨a, b, ha, hb0, ⟨(AlgEquiv.ofBijective f hbij).symm⟩⟩

-- `exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four` with the classes
-- `DivisionRing D` and `Algebra.IsCentral ℚ D` in place of `hdiv` and `hcen`. It has no docstring
-- of its own, so that the result keeps one page, documented by the theorem above.
public theorem Algebra.IsCentral.exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four
    (D : Type*) [DivisionRing D] [Algebra ℚ D] [Algebra.IsCentral ℚ D]
    (hdim : Module.finrank ℚ D = 4) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) := by
  refine _root_.exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four D hdim
    (fun _ hx ↦ hx.isUnit) fun z hz ↦ ?_
  obtain ⟨c, rfl⟩ := (Algebra.IsCentral.mem_center_iff ℚ).mp
    (Subalgebra.mem_center_iff.mpr fun x ↦ (hz x).symm)
  exact ⟨c, rfl⟩
