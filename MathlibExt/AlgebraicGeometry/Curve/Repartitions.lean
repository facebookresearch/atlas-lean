/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_Repartitions.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup

/-!
# Repartitions and Riemann-Roch spaces

This file defines the repartitions (adèles) of `F`, the subspaces of repartitions bounded by a
divisor, and the Riemann-Roch spaces `L(D)`.
-/

@[expose] public section

noncomputable section

open WithZero

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adicValuation_le_one_of_mem {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_algebraMap_le_one (a : K) :
    v.adicValuation (algebraMap K F a) ≤ 1 :=
  v.adicValuation_le_one_of_mem (v.algebraMap_mem' a)

theorem adicValuation_eq_exp_neg_ord {f : F} (hf : f ≠ 0) :
    v.adicValuation f = exp (-v.ord f) := by
  unfold ord
  rw [neg_neg, exp_log (v.adicValuation_ne_zero hf)]

theorem adicValuation_le_exp_iff {f : F} {n : ℤ} :
    v.adicValuation f ≤ exp n ↔ f = 0 ∨ -n ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [v.adicValuation_eq_exp_neg_ord hf, exp_le_exp, neg_le, or_iff_right hf]

theorem adicValuation_le_one_iff {f : F} :
    v.adicValuation f ≤ 1 ↔ f = 0 ∨ 0 ≤ v.ord f := by
  simpa using v.adicValuation_le_exp_iff (n := 0)

theorem not_adicValuation_le_one_iff {f : F} :
    ¬v.adicValuation f ≤ 1 ↔ v.ord f < 0 := by
  rw [v.adicValuation_le_one_iff, not_or, not_le]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fun h0 => by simp [h0] at h, h⟩

end Place

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def repartitions : Subalgebra F (Place K F → F) :=
  Algebra.adjoin F
    {α : Place K F → F | {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite}

variable {K F}

theorem mem_repartitions_of_finite {α : Place K F → F}
    (hα : {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite) :
    α ∈ repartitions K F :=
  Algebra.subset_adjoin hα

theorem mem_repartitions_of_finite_ord {α : Place K F → F}
    (hα : {v : Place K F | v.ord (α v) < 0}.Finite) :
    α ∈ repartitions K F :=
  mem_repartitions_of_finite <| by
    rwa [show {v : Place K F | ¬v.adicValuation (α v) ≤ 1}
        = {v : Place K F | v.ord (α v) < 0} from
      Set.ext fun v => v.not_adicValuation_le_one_iff]

theorem mem_repartitions_of_forall_le_exp (D : Divisor K F) (α : Place K F → F)
    (h : ∀ v : Place K F, v.adicValuation (α v) ≤ exp (D v)) :
    α ∈ repartitions K F :=
  mem_repartitions_of_finite <| D.support.finite_toSet.subset fun v hv => by
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hD0
    exact hv ((h v).trans (by rw [hD0]; simp))

def repartitionsOf (D : Divisor K F) : Submodule K ↥(repartitions K F) where
  carrier :=
    {α | ∀ v : Place K F, v.adicValuation ((α : Place K F → F) v) ≤ exp (D v)}
  zero_mem' := by
    intro v
    change v.adicValuation (0 : F) ≤ exp (D v)
    simp
  add_mem' := by
    intro α β hα hβ v
    exact (Valuation.map_add _ _ _).trans (max_le (hα v) (hβ v))
  smul_mem' := by
    intro c α hα v
    change v.adicValuation (c • (α : Place K F → F) v) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hα v)

theorem mem_repartitionsOf_iff {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔
      ∀ v : Place K F,
        (α : Place K F → F) v = 0 ∨ -D v ≤ v.ord ((α : Place K F → F) v) := by
  change (∀ v : Place K F, v.adicValuation ((α : Place K F → F) v) ≤ exp (D v)) ↔ _
  exact forall_congr' fun v => v.adicValuation_le_exp_iff

theorem repartitionsOf_mono {D D' : Divisor K F} (h : D ≤ D') :
    repartitionsOf D ≤ repartitionsOf D' := fun _ hα v =>
  (hα v).trans (exp_le_exp.mpr (Finsupp.le_def.mp h v))

def riemannRochSpace (D : Divisor K F) : Submodule K F where
  carrier := {f | ∀ v : Place K F, v.adicValuation f ≤ exp (D v)}
  zero_mem' := by
    intro v
    simp
  add_mem' := by
    intro f g hf hg v
    exact (Valuation.map_add _ _ _).trans (max_le (hf v) (hg v))
  smul_mem' := by
    intro c f hf v
    change v.adicValuation (c • f) ≤ exp (D v)
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hf v)

theorem mem_riemannRochSpace_iff {D : Divisor K F} {f : F} :
    f ∈ riemannRochSpace D ↔ ∀ v : Place K F, f = 0 ∨ -D v ≤ v.ord f := by
  change (∀ v : Place K F, v.adicValuation f ≤ exp (D v)) ↔ _
  exact forall_congr' fun v => v.adicValuation_le_exp_iff

variable (K F) in
def principalRepartitions : Submodule K ↥(repartitions K F) :=
  (LinearMap.range (Algebra.linearMap F ↥(repartitions K F))).restrictScalars K

theorem mem_principalRepartitions_iff {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔
      ∃ f : F, (α : Place K F → F) = fun _ => f := by
  simp only [principalRepartitions, Submodule.restrictScalars_mem, LinearMap.mem_range,
    Algebra.linearMap_apply]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, Subtype.ext hf.symm⟩

abbrev H1 (D : Divisor K F) : Type _ :=
  ↥(repartitions K F) ⧸ (repartitionsOf D ⊔ principalRepartitions K F)

variable (K F) in
def genusFF : ℕ := Module.finrank K (H1 (0 : Divisor K F))

end AlgebraicCurve

end
