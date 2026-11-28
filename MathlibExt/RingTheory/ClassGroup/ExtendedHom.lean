/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup.ExtendedHom

/-!
# The class group map on representatives over arbitrary fraction fields

Mathlib's `ClassGroup.map f hf : ClassGroup A →* ClassGroup B`, for an injective ring
homomorphism `f : A →+* B` of domains, extends fractional ideals along `f`; its computation rule
`ClassGroup.map_quotientMk` is stated for fractional ideals over `FractionRing A` and
`FractionRing B`. This file states it for fractional ideals over any fraction fields `K` of `A`
and `L` of `B` (`ClassGroup.map_mk`).
-/

@[expose] public section

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] {S : Submonoid R} (P P' : Type*) [CommRing P] [Algebra R P]
  [IsLocalization S P] [CommRing P'] [Algebra R P'] [IsLocalization S P']

/-- The canonical isomorphism between the fractional ideals of two localizations `P` and `P'` of
`R` at `S` is extension along the identity of `R`. -/
theorem canonicalEquiv_eq_extended (I : FractionalIdeal S P) :
    canonicalEquiv S P P' I = I.extended P' (f := RingHom.id R) (M := S) (N := S)
      (show S ≤ S.comap (RingHom.id R) from fun _ hy => hy) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_canonicalEquiv_apply S P P').mp hx
    exact (mem_extended_iff _ _ _ _).mpr (Submodule.subset_span ⟨y, hy, rfl⟩)
  · intro hx
    refine (mem_canonicalEquiv_apply S P P').mpr ?_
    have hx' := (mem_extended_iff _ _ _ _).mp hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem z hz => exact hz
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', Submodule.add_mem _ hy hy', map_add _ _ _⟩
    | smul r z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨r • y, Submodule.smul_mem _ r hy, IsLocalization.map_smul _ _ _⟩

end FractionalIdeal

namespace ClassGroup

variable {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  (K L : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra B L]
  [IsFractionRing B L]

/-- **The class group map on representatives.** Let $f : A \to B$ be an injective homomorphism
of integral domains, and let $K$ and $L$ be fraction fields of $A$ and $B$. For an invertible
fractional ideal $I$ of $A$ in $K$, the map of class groups induced by $f$
(`ClassGroup.map`) sends the class of $I$ to the class of the extended fractional ideal of $B$
in $L$ spanned by the image of $I$ under the map $K \to L$ induced by $f$
(`FractionalIdeal.extendedHom'`). -/
theorem map_mk (f : A →+* B) (hf : Function.Injective f) (I : (FractionalIdeal A⁰ K)ˣ) :
    map f hf (ClassGroup.mk K I) = ClassGroup.mk L
      (Units.map (FractionalIdeal.extendedHom' L
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf)).toMonoidHom I) := by
  rw [ClassGroup.mk_def, ClassGroup.mk_def, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    map_quotientMk]
  congr 1
  ext1
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    FractionalIdeal.extendedHom'_apply]
  rw [FractionalIdeal.canonicalEquiv_eq_extended, FractionalIdeal.canonicalEquiv_eq_extended,
    FractionalIdeal.extended_extended, FractionalIdeal.extended_extended]

end ClassGroup
