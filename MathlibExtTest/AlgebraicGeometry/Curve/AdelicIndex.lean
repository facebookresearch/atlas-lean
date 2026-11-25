/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.AdelicIndex

/-! # Tests for the adèle space, the index of specialty and the repartition bridge -/

@[expose] public section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

-- The adèle space is the restricted product: integral at all but finitely many places.
example {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ {v : Place K F | ¬v.adicValuation (α v) ≤ 1}.Finite :=
  mem_adeleSpace_iff_finite

example {α : Place K F → F} : α ∈ adeleSpace K F ↔ ∃ D : Divisor K F, α ∈ adeleBdd D :=
  mem_adeleSpace_iff

-- Boundary: a constant is an adèle exactly when it has finitely many poles, with no hypothesis
-- on `F`; the repartition algebra contains every constant.
example (f : F) :
    diagonalHom K F f ∈ adeleSpace K F ↔ {v : Place K F | v.ord f < 0}.Finite := by
  rw [mem_adeleSpace_iff_finite]
  simp only [diagonalHom_apply, Place.not_adicValuation_le_one_iff]

example (f : F) : algebraMap F (Place K F → F) f ∈ repartitions K F :=
  (repartitions K F).algebraMap_mem f

-- Every adèle is a repartition.
example {α : Place K F → F} (hα : α ∈ adeleSpace K F) : α ∈ repartitions K F :=
  mem_repartitions_of_mem_adeleSpace hα

-- Boundary: the zero function and a function bounded by a divisor are adèles.
example : (0 : Place K F → F) ∈ adeleSpace K F := (adeleSpace K F).zero_mem

example (D : Divisor K F) {α : Place K F → F} (hα : α ∈ adeleBdd D) : α ∈ adeleSpace K F :=
  adeleBdd_le_adeleSpace hα

section PrincipalDivisors

variable [HasPrincipalDivisors K F]

-- With principal divisors, every constant is an adèle and the adèles are the repartitions.
example (f : F) : diagonalHom K F f ∈ adeleSpace K F := diagonal_mem_adeleSpace f

example {α : Place K F → F} : α ∈ adeleSpace K F ↔ α ∈ repartitions K F :=
  mem_adeleSpace_iff_mem_repartitions

example (α : repartitions K F) :
    (repartitionsEquivAdeleSpace K F α : Place K F → F) = α :=
  coe_repartitionsEquivAdeleSpace α

-- Bounded and principal repartitions are `adeleBdd D` and `globalSub K F`.
example (D : Divisor K F) :
    (repartitionsOf K F D).map (repartitionsEquivAdeleSpace K F).toLinearMap =
      (adeleBdd D).comap (adeleSpace K F).subtype :=
  map_repartitionsOf_repartitionsEquivAdeleSpace D

example :
    (principalRepartitions K F).map (repartitionsEquivAdeleSpace K F).toLinearMap =
      (globalSub K F).comap (adeleSpace K F).subtype :=
  map_principalRepartitions_repartitionsEquivAdeleSpace

-- A repartition bounded by `D` is an adèle in `adeleBdd D`, as a function on places.
example (D : Divisor K F) {α : repartitions K F} (hα : α ∈ repartitionsOf K F D) :
    (α : Place K F → F) ∈ adeleBdd D := by
  have h : repartitionsEquivAdeleSpace K F α ∈
      (repartitionsOf K F D).map (repartitionsEquivAdeleSpace K F).toLinearMap :=
    Submodule.mem_map_of_mem hα
  rw [map_repartitionsOf_repartitionsEquivAdeleSpace] at h
  exact h

-- The quotient bridge: `H¹(D)` is the quotient defining `indexOfSpecialty D`.
example (D : Divisor K F) : Module.finrank K (H1 K F D) = indexOfSpecialty D :=
  finrank_h1_eq_indexOfSpecialty D

example (D : Divisor K F) (α : repartitions K F) :
    h1EquivAdeleQuotient D (Submodule.Quotient.mk α) =
      Submodule.Quotient.mk (repartitionsEquivAdeleSpace K F α) :=
  h1EquivAdeleQuotient_mk D α

-- The genus bridge at the zero divisor.
example : genusFF K F = indexOfSpecialty (0 : Divisor K F) :=
  genusFF_eq_indexOfSpecialty K F

example : IndexOfSpecialtyFinite K F ↔ ∃ D₀ : Divisor K F, Module.Finite K (H1 K F D₀) :=
  indexOfSpecialtyFinite_iff_exists_finite_h1

-- Boundary: the class of a constant repartition is zero in `H¹(D)`, and so is its image.
example (D : Divisor K F) (f : F) :
    (Submodule.Quotient.mk (algebraMap F (repartitions K F) f) : H1 K F D) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_sup_right (mem_principalRepartitions_iff.mpr ⟨f, rfl⟩)

example (D : Divisor K F) (f : F) :
    h1EquivAdeleQuotient D (Submodule.Quotient.mk (algebraMap F (repartitions K F) f)) = 0 := by
  rw [h1EquivAdeleQuotient_mk, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_sup_right (diagonal_mem_globalSub (K := K) f)

end PrincipalDivisors

-- Boundary: constants lie in `L(0)`, and `ℓ(0) = 1` when the constants are `K`.
example (c : K) : algebraMap K F c ∈ LSpace (0 : Divisor K F) :=
  algebraMap_mem_lSpace_zero c

example (h : ConstantsAreBase K F) : ell (0 : Divisor K F) = 1 :=
  ell_zero_eq_one_of_constantsAreBase h

example (D : Divisor K F) : (0 : F) ∈ LSpace D := (LSpace D).zero_mem

-- Universe check: the base field and the function field may live in different universes.
universe u v in
example {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] :
    genusFF K F = indexOfSpecialty (0 : Divisor K F) :=
  genusFF_eq_indexOfSpecialty K F

end AlgebraicCurve
