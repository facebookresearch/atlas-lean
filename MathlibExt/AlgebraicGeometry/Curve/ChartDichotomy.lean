/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_CharPModel_chart_dichotomy_jBar.lean`
and
`P2M/Sol/S_ModularCurve_CharPModel_chart_dichotomy_jBar.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import MathlibExt.AlgebraicGeometry.Curve.Place

@[expose] public section

open IsLocalRing

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

/-- The residue field of a place. -/
noncomputable abbrev ResidueField (v : Place K F) : Type _ :=
  IsLocalRing.ResidueField v.toValuationSubring

variable (v : Place K F)

theorem algebraMap_mem (a : K) : algebraMap K F a ∈ v.toValuationSubring :=
  v.algebraMap_mem' a

theorem algebraMap_mem_nonunits_iff (a : K) :
    algebraMap K F a ∈ v.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using v.algebraMap_mem a⁻¹) hinv
  · rintro rfl
    simp

theorem mul_mem_nonunits {x y : F} (hx : x ∈ v.toValuationSubring.nonunits)
    (hy : y ∈ v.toValuationSubring) : x * y ∈ v.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc v.toValuationSubring.valuation (x * y)
      = v.toValuationSubring.valuation x * v.toValuationSubring.valuation y :=
        map_mul _ _ _
    _ ≤ v.toValuationSubring.valuation x * 1 := by gcongr
    _ = v.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

/-- A place has a value at `a` when `f - a` lies in the nonunits. -/
def HasValueAt (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ v.toValuationSubring.nonunits

theorem mem_of_hasValueAt {f : F} {a : K} (h : v.HasValueAt f a) :
    f ∈ v.toValuationSubring :=
  by simpa using add_mem (v.toValuationSubring.nonunits_subset h) (v.algebraMap_mem a)

theorem hasValueAt_unique {f : F} {a b : K} (ha : v.HasValueAt f a)
    (hb : v.HasValueAt f b) : a = b := by
  have h : algebraMap K F (a - b) ∈ v.toValuationSubring.nonunits := by
    have hsub := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at hsub
  exact sub_eq_zero.mp ((v.algebraMap_mem_nonunits_iff _).mp h)

theorem hasValueAt_add {f g : F} {a b : K} (hf : v.HasValueAt f a)
    (hg : v.HasValueAt g b) : v.HasValueAt (f + g) (a + b) := by
  have h := add_mem hf hg
  rw [HasValueAt, map_add]
  convert h using 1
  ring

theorem hasValueAt_neg {f : F} {a : K} (hf : v.HasValueAt f a) :
    v.HasValueAt (-f) (-a) := by
  have h := neg_mem hf
  rw [HasValueAt, map_neg]
  convert h using 1
  ring

theorem hasValueAt_mul {f g : F} {a b : K} (hf : v.HasValueAt f a)
    (hg : v.HasValueAt g b) : v.HasValueAt (f * g) (a * b) := by
  have h1 : (f - algebraMap K F a) * g ∈ v.toValuationSubring.nonunits :=
    v.mul_mem_nonunits hf (v.mem_of_hasValueAt hg)
  have h2 : (g - algebraMap K F b) * algebraMap K F a ∈
      v.toValuationSubring.nonunits :=
    v.mul_mem_nonunits hg (v.algebraMap_mem a)
  have h := add_mem h1 h2
  rw [HasValueAt, map_mul]
  convert h using 1
  ring

theorem hasValueAt_inv {f : F} {a : K} (hf : v.HasValueAt f a) (ha : a ≠ 0) :
    v.HasValueAt f⁻¹ a⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h0 : v.HasValueAt (0 : F) 0 := by
      change (0 : F) - algebraMap K F 0 ∈ v.toValuationSubring.nonunits
      simp
    exact ha (v.hasValueAt_unique hf h0)
  have hfu : f ∉ v.toValuationSubring.nonunits := fun hfn =>
    ha (v.hasValueAt_unique hf (by
      show v.HasValueAt f 0
      rwa [HasValueAt, map_zero, sub_zero]))
  have hfinv : f⁻¹ ∈ v.toValuationSubring := by
    by_contra hne
    exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
  have hprod : (f - algebraMap K F a) * (f⁻¹ * algebraMap K F a⁻¹)
      ∈ v.toValuationSubring.nonunits :=
    v.mul_mem_nonunits hf (mul_mem hfinv (v.algebraMap_mem _))
  have h := neg_mem hprod
  change f⁻¹ - algebraMap K F a⁻¹ ∈ v.toValuationSubring.nonunits
  convert h using 1
  have haF : algebraMap K F a ≠ 0 := by simpa using ha
  rw [map_inv₀]
  field_simp
  ring

theorem hasValueAt_iff_residue {f : F} (hf : f ∈ v.toValuationSubring) (a : K) :
    v.HasValueAt f a ↔
      residue v.toValuationSubring ⟨f, hf⟩ = algebraMap K v.ResidueField a := by
  have e : algebraMap K v.ResidueField a =
      residue v.toValuationSubring (algebraMap K v.toValuationSubring a) := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

theorem exists_hasValueAt (hw : Function.Surjective (algebraMap K v.ResidueField))
    {f : F} (hf : f ∈ v.toValuationSubring) : ∃ a : K, v.HasValueAt f a := by
  obtain ⟨a, ha⟩ := hw (residue v.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (v.hasValueAt_iff_residue hf a).mpr ha.symm⟩

theorem surjective_algebraMap_residueField_of_isAlgClosed [IsAlgClosed K]
    [Module.Finite K v.ResidueField] :
    Function.Surjective (algebraMap K v.ResidueField) :=
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end Place

namespace Place

variable (v : Place K F)

/-- Chart dichotomy at a place: for a valuation subring `A` of the base field
and any element `j` of the function field, either `j` or its inverse takes a
value in `A` at the place. For the modular function field with its
`j`-invariant this is the statement that a place lies on the `j` chart or on
the inverse-`j` chart; the finite-residue hypothesis is what the modular
polynomial relations supply for that field. -/
public theorem chart_dichotomy [IsAlgClosed K] [Module.Finite K v.ResidueField]
    (A : ValuationSubring K) (j : F) :
    (∃ a : A, (j - algebraMap K F (a : K)) ∈ v.toValuationSubring.nonunits) ∨
      (∃ a : A, (j⁻¹ - algebraMap K F (a : K)) ∈ v.toValuationSubring.nonunits) := by
  classical
  have hsurj := v.surjective_algebraMap_residueField_of_isAlgClosed
  by_cases hmem : j ∈ v.toValuationSubring
  · obtain ⟨c, hc⟩ := v.exists_hasValueAt hsurj hmem
    rcases eq_or_ne c 0 with rfl | hc0
    · exact Or.inl ⟨⟨0, A.zero_mem⟩, hc⟩
    · rcases A.mem_or_inv_mem c with hcA | hcA
      · exact Or.inl ⟨⟨c, hcA⟩, hc⟩
      · exact Or.inr ⟨⟨c⁻¹, hcA⟩, v.hasValueAt_inv hc hc0⟩
  · refine Or.inr ⟨0, ?_⟩
    have hj0 : j ≠ 0 := fun h => hmem (h.symm ▸ zero_mem _)
    have hnu : j⁻¹ ∈ v.toValuationSubring.nonunits :=
      (ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hmem))
    simpa using hnu

end Place

end AlgebraicCurve
