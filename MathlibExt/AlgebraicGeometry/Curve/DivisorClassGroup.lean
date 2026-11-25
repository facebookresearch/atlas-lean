/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
and
`Definitions/Def_ModularCurve_CuspidalClass.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy
public import MathlibExt.AlgebraicGeometry.Curve.Divisor
public import MathlibExt.AlgebraicGeometry.Curve.Place

/-!
# Degree-zero divisor classes of a function field

This file defines the divisor `P - Q` of two points on any type of points. For a field extension
`F/K`, it defines the divisors of `F` over `K`, as finitely supported integer combinations of the
places of `F` over `K`, and the subgroup of principal divisors (the divisors of nonzero elements
of `F`). When the residue field of every place is finite-dimensional over `K`, as for the function
field of a curve over `K`, it defines the degree of a place and of a divisor, and the group
`Pic0 K F` of divisors of degree zero modulo the principal divisors of degree zero.
-/

@[expose] public section

namespace CurveDivisor

variable {C : Type*}

/-- The divisor `P - Q` of two points `P` and `Q`: the difference of the two single-point
divisors. -/
noncomputable def pointDiff (P Q : C) : CurveDivisor C :=
  Finsupp.single P 1 - Finsupp.single Q 1

theorem pointDiff_def (P Q : C) : pointDiff P Q = Finsupp.single P 1 - Finsupp.single Q 1 :=
  rfl

theorem pointDiff_self (P : C) : pointDiff P P = 0 := by
  simp [pointDiff_def]

/-- For distinct points `P` and `Q`, the divisor `P - Q` has coefficient `1` at `P`. -/
theorem coeff_pointDiff_left (P Q : C) (h : P ≠ Q) : coeff (pointDiff P Q) P = 1 := by
  classical
  simp [pointDiff_def, coeff, h]

theorem pointDiff_ne_zero (P Q : C) (h : P ≠ Q) : pointDiff P Q ≠ 0 := by
  intro h0
  have := coeff_pointDiff_left P Q h
  rw [h0] at this
  simp [coeff] at this

end CurveDivisor

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F} (v : Place K F)

/-- The degree of a place whose residue field is finite-dimensional over `K`: the dimension of
the residue field over `K`. -/
noncomputable def deg [FiniteDimensional K v.ResidueField] : ℕ :=
  Module.finrank K v.ResidueField

/-- The degree of a place is positive. -/
theorem deg_pos [FiniteDimensional K v.ResidueField] : 0 < v.deg :=
  Module.finrank_pos

end Place

/-- The divisors of `F` over `K`: finitely supported integer combinations of the places of `F`
over `K`. -/
abbrev Divisor : Type _ := CurveDivisor (Place K F)

namespace Divisor

variable {K F}

/-- A divisor is principal if it is the divisor of a nonzero element `f` of `F`: its
coefficient at every place is the order of `f` there. -/
def IsPrincipal (D : Divisor K F) : Prop :=
  ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

/-- The subgroup of principal divisors. -/
def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

theorem mem_principal {D : Divisor K F} :
    D ∈ principal (K := K) (F := F) ↔ IsPrincipal D :=
  Iff.rfl

variable [∀ v : Place K F, FiniteDimensional K v.ResidueField]

/-- The degree of a divisor: the sum of its coefficients, each weighted by the degree of its
place. -/
noncomputable def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (v.deg : ℤ)

@[simp]
theorem degree_single (v : Place K F) (n : ℤ) :
    degree (Finsupp.single v n) = n * v.deg := by
  simp [degree]

/-- The subgroup of divisors of degree zero. -/
noncomputable def degZero : AddSubgroup (Divisor K F) := degree.ker

theorem mem_degZero {D : Divisor K F} : D ∈ degZero (K := K) (F := F) ↔ degree D = 0 :=
  Iff.rfl

/-- The degree of the divisor `P - Q` of two places is the difference of their degrees. -/
theorem degree_pointDiff (P Q : Place K F) :
    degree (CurveDivisor.pointDiff P Q) = (P.deg : ℤ) - Q.deg := by
  rw [CurveDivisor.pointDiff_def, map_sub, degree_single, degree_single, one_mul, one_mul]

/-- The divisor `P - Q` of two places has degree zero exactly when the two places have the same
degree. -/
theorem pointDiff_mem_degZero_iff (P Q : Place K F) :
    CurveDivisor.pointDiff P Q ∈ degZero (K := K) (F := F) ↔ P.deg = Q.deg := by
  rw [mem_degZero, degree_pointDiff, sub_eq_zero, Nat.cast_inj]

end Divisor

/-- The group of degree-zero divisor classes of `F` over `K`: the divisors of degree zero modulo
the principal divisors of degree zero. -/
abbrev Pic0 [∀ v : Place K F, FiniteDimensional K v.ResidueField] : Type _ :=
  Divisor.degZero (K := K) (F := F) ⧸
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))

namespace Pic0

variable {K F} [∀ v : Place K F, FiniteDimensional K v.ResidueField]

/-- The class of a divisor of degree zero. -/
noncomputable def mk (D : Divisor.degZero (K := K) (F := F)) : Pic0 K F :=
  QuotientAddGroup.mk D

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

@[simp]
theorem mk_add (D E : Divisor.degZero (K := K) (F := F)) : mk (D + E) = mk D + mk E :=
  rfl

@[simp]
theorem mk_zero : mk (0 : Divisor.degZero (K := K) (F := F)) = 0 :=
  rfl

/-- The class of a divisor of degree zero vanishes exactly when the divisor is principal. -/
theorem mk_eq_zero_iff (D : Divisor.degZero (K := K) (F := F)) :
    mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]

end Pic0

end AlgebraicCurve
