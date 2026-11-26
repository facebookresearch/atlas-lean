/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.Length.FiniteColengthAlgebra
public import MathlibExt.RingTheory.Length.AnnihilatorQuotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Actual finite colength inside a common fraction field

Every subalgebra of the genuine fraction field has torsion quotient by
the base ring. For a finite subalgebra, one nonzero scalar annihilates this
actual quotient. Over a Noetherian domain of dimension at most one, the
principal annihilating quotient has finite length, so the original scalar
cokernel has finite length as well.

Consequently the principal quotient-length comparison applies to actual
finite birational inclusions in a prescribed fraction field. No finite-
colength identity is supplied by the caller. The base ring and common
fraction field retain independent universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v

namespace Subalgebra

variable {R : Type u} [CommRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Let `R` be a commutative ring, `K` an `R`-algebra field that is a fraction
ring of `R`, and `A ⊆ K` an `R`-subalgebra. The `R`-module quotient of `A` by the
image of the algebra map from `R` is torsion: each class is annihilated by a
non-zero-divisor of `R`. The ring and field universes are independent. -/
theorem isTorsion_quotient_range (A : Subalgebra R K) :
    Module.IsTorsion R (A ⧸ (Algebra.linearMap R A).range) := by
  let N : Submodule R A := (Algebra.linearMap R A).range
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
  obtain ⟨c, r, hr⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) (x : K)
  refine ⟨c, ?_⟩
  change (c : R) • N.mkQ x = 0
  rw [← N.mkQ.map_smul]
  apply (Submodule.Quotient.mk_eq_zero N).mpr
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change algebraMap R K r = (c : R) • (x : K)
  exact hr

variable [IsDomain R]

/-- Let `R` be a domain, `K` a chosen fraction field, and `A ⊆ K` a finite
`R`-subalgebra. There exists one nonzero `c ∈ R` that annihilates every class of
the `R`-module quotient of `A` by the image of `R`. -/
theorem exists_nonzero_annihilator_quotient_range (A : Subalgebra R K)
    [Module.Finite R A] :
    ∃ c : R, c ≠ 0 ∧ ∀ z : A ⧸ (Algebra.linearMap R A).range, c • z = 0 := by
  obtain ⟨c, hc, hc0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (isTorsion_quotient_range A)
  exact ⟨c, mem_nonZeroDivisors_iff_ne_zero.mp hc0,
    fun z ↦ Submodule.mem_annihilator.mp hc z Submodule.mem_top⟩

/-- Let `R` be a Noetherian domain of Krull dimension at most one, `K` its
chosen fraction field, and `A ⊆ K` a finite `R`-subalgebra. The quotient of `A`
by the scalar image of `R` has finite composition length over `R`. -/
theorem isFiniteLength_quotient_range (A : Subalgebra R K)
    [Module.Finite R A] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] :
    IsFiniteLength R (A ⧸ (Algebra.linearMap R A).range) := by
  obtain ⟨c, hc, hann⟩ := exists_nonzero_annihilator_quotient_range A
  have hI : Ideal.span {c} ≤ Module.annihilator R (A ⧸ (Algebra.linearMap R A).range) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Module.mem_annihilator.mpr hann))
  have hquot : Module.length R (R ⧸ Ideal.span {c}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr hc))
  exact Module.length_ne_top_iff.mp
    (Module.length_ne_top_of_finite_of_ideal_le_annihilator R
      (A ⧸ (Algebra.linearMap R A).range) (Ideal.span {c}) hI hquot)

/-- Let `R` be a Noetherian domain of Krull dimension at most one, `K` its
chosen fraction field, and `A ⊆ K` a finite `R`-subalgebra. For every nonzero
`a ∈ R`, the principal quotients have equal base-ring lengths:
`length_R(R/(a)) = length_R(A/(aA))`. -/
theorem length_quotient_span_eq_of_finite (A : Subalgebra R K)
    [Module.Finite R A] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {a : R} (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) =
      Module.length R (A ⧸ Ideal.span {algebraMap R A a}) := by
  apply Algebra.length_quotient_span_eq_of_finite_colength
    (S := A) ?_ (isFiniteLength_quotient_range A) a ha
  intro x y h
  apply IsFractionRing.injective R K
  exact congrArg Subtype.val h

end Subalgebra
