/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.K0.FiniteFreeCofinality
public import MathlibExt.KTheory.Ring.K0.Rank

/-!
# K₀ of a field

For a field `F`, rank identifies the Grothendieck ring `RingK0 F` of finitely
generated projective `F`-modules with `ℤ`. The inverse is integer cast, and
the class of a finite projective module is its dimension.

`fieldRank F` evaluates the integer-valued rank function on `PrimeSpectrum F`
at its unique prime. Extension of scalars between fields in the same universe
preserves this integer.

## Main results

* `fieldRankEquiv`: the rank isomorphism `RingK0 F ≃+* ℤ`.
* `fieldRank_naturality`: compatibility with extension of scalars.
* `mapRingHom_eq_fieldRank`: the scalar-extension map expressed through
  the rank isomorphisms.

## References

* Weibel, *The K-book*, Chapter II, §2, p.68: projective-module K₀, the field
  computation and scalar-extension ring functoriality.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicKTheory.RingK0

variable (F : Type u) [Field F]

/-- The K₀ class of a finite projective module over a field is its dimension. -/
theorem mk_eq_finrank_natCast (P : FGProjectiveCat.{u} F) :
    (K0.mk P : RingK0 F) = (Module.finrank F P : RingK0 F) := by
  let e : P ≅ standardFreeProjective F (Module.finrank F P) :=
    FGProjectiveCat.isoOfLinearEquiv (Module.finBasis F P).equivFun
  have hOne : regularClass F = (1 : RingK0 F) := K0.one_eq (FGProjectiveCat.{u} F)
  calc
    K0.mk P = K0.mk (standardFreeProjective F (Module.finrank F P)) :=
      K0.mk_congr_of_iso e
    _ = Module.finrank F P • regularClass F := mk_standardFreeProjective F _
    _ = (Module.finrank F P : RingK0 F) := by
      rw [hOne, nsmul_eq_mul, mul_one]

/-- Integer-valued rank, evaluated at the unique prime of the field. -/
def fieldRank : RingK0 F →+* ℤ :=
  (LocallyConstant.evalRingHom (default : PrimeSpectrum F)).comp (rank F)

/-- Field rank evaluates the integer-valued rank function at the unique prime. -/
theorem fieldRank_apply (x : RingK0 F) :
    fieldRank F x = rank F x (default : PrimeSpectrum F) :=
  rfl

/-- The rank of a finite projective module is its dimension. -/
@[simp]
theorem fieldRank_mk (P : FGProjectiveCat.{u} F) :
    fieldRank F (K0.mk P) = (Module.finrank F P : ℤ) := by
  rw [fieldRank_apply, rank_mk, FGProjectiveCat.rankInt_apply]
  simp only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]

/-- Integer cast recovers a K₀ class from its rank. -/
@[simp]
theorem intCast_fieldRank (x : RingK0 F) :
    (fieldRank F x : RingK0 F) = x := by
  obtain ⟨P, Q, rfl⟩ := exists_eq_mk_sub_mk F x
  rw [map_sub, fieldRank_mk, fieldRank_mk, Int.cast_sub]
  simp only [Int.cast_natCast, mk_eq_finrank_natCast]

/-- The rank isomorphism `RingK0 F ≃+* ℤ`. -/
def fieldRankEquiv : RingK0 F ≃+* ℤ where
  toFun := fieldRank F
  invFun z := (z : RingK0 F)
  left_inv := intCast_fieldRank F
  right_inv z := map_intCast (fieldRank F) z
  map_mul' := (fieldRank F).map_mul
  map_add' := (fieldRank F).map_add

/-- The rank equivalence has forward map `fieldRank F`. -/
@[simp]
theorem fieldRankEquiv_apply (x : RingK0 F) :
    fieldRankEquiv F x = fieldRank F x :=
  rfl

/-- The inverse of the rank equivalence is integer cast. -/
@[simp]
theorem fieldRankEquiv_symm_apply (z : ℤ) :
    (fieldRankEquiv F).symm z = (z : RingK0 F) :=
  rfl

/-- The rank equivalence sends a finite projective module to its dimension. -/
theorem fieldRankEquiv_mk (P : FGProjectiveCat.{u} F) :
    fieldRankEquiv F (K0.mk P) = (Module.finrank F P : ℤ) :=
  fieldRank_mk F P

/-- The rank function `rank F x` on `PrimeSpectrum F` is constant, with value
`fieldRank F x`. -/
theorem rank_eq_const_fieldRank (x : RingK0 F) :
    rank F x = LocallyConstant.const (PrimeSpectrum F) (fieldRank F x) := by
  ext p
  change rank F x p = rank F x (default : PrimeSpectrum F)
  exact congrArg (rank F x) (Subsingleton.elim p default)

/-- Rank is injective on K₀ of a field. -/
theorem rank_injective_of_field : Function.Injective (rank F) := by
  intro x y h
  apply (fieldRankEquiv F).injective
  exact congrArg (LocallyConstant.evalRingHom (default : PrimeSpectrum F)) h

/-- The reduced K₀ ideal of a field is zero. -/
theorem reducedIdeal_field_eq_bot : reducedIdeal F = ⊥ := by
  ext x
  simp only [mem_reducedIdeal_iff, Ideal.mem_bot]
  constructor
  · intro h
    exact rank_injective_of_field F (h.trans (map_zero (rank F)).symm)
  · rintro rfl
    exact map_zero (rank F)

variable {F} {G : Type u} [Field G]

/-- Extension of scalars between fields preserves rank. -/
theorem fieldRank_naturality (f : F →+* G) :
    (fieldRank G).comp (mapRingHom f) = fieldRank F := by
  ext x
  change fieldRank G (mapRingHom f x) = fieldRank F x
  calc
    fieldRank G (mapRingHom f x) =
        fieldRank G (mapRingHom f (fieldRank F x : RingK0 F)) :=
      congrArg (fun y => fieldRank G (mapRingHom f y)) (intCast_fieldRank F x).symm
    _ = fieldRank F x := by simp only [map_intCast, Int.cast_id]

/-- Extension of scalars is determined by the rank equivalences. -/
theorem mapRingHom_eq_fieldRank (f : F →+* G) :
    mapRingHom f =
      (fieldRankEquiv G).symm.toRingHom.comp (fieldRankEquiv F).toRingHom := by
  ext x
  change mapRingHom f x = (fieldRank F x : RingK0 G)
  calc
    mapRingHom f x = mapRingHom f (fieldRank F x : RingK0 F) :=
      congrArg (mapRingHom f) (intCast_fieldRank F x).symm
    _ = (fieldRank F x : RingK0 G) := map_intCast (mapRingHom f) _

/-- Any two homomorphisms between fixed fields induce the same map on K₀. -/
theorem mapRingHom_eq_of_field (f g : F →+* G) :
    mapRingHom f = mapRingHom g :=
  (mapRingHom_eq_fieldRank f).trans (mapRingHom_eq_fieldRank g).symm

end AlgebraicKTheory.RingK0
