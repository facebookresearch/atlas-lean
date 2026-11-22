/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of the integral-closure setup and field-element adapter are adapted
from `P2M/Sol/S_flt_regular.lean`, lines 2519–2580, in
`anthropics/fermats-last-theorem` at
`6e837e75355538c7f80bab5b956861e86c4eacc2`:
Copyright 2026 Anthropic, PBC.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).

That portion is a port of
`FltRegular/NumberTheory/Unramified.lean` from
`leanprover-community/flt-regular`:
Copyright (c) the flt-regular authors.
Authors (project attribution): Alex J. Best, Christopher Birkbeck,
Riccardo Brasca, Eric Rodriguez Boidi, Ruben Van de Velde, Andrew Yang.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).

These credits follow the frozen source repository's `NOTICE` (item 2) and
`ATTRIBUTION.md` (§3). That snapshot records the flt-regular project authors;
it does not reproduce that project's per-file headers.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Local unramifiedness from a reduced minimal polynomial

For an integral closure in a finite separable extension of fraction fields,
a primitive field generator with separable reduced minimal polynomial proves
local unramifiedness. The generator need not generate the integral ring.

The integral-closure setup and field-element adapter are adapted from
`P2M/Sol/S_flt_regular.lean`, lines 2519–2580, in
`anthropics/fermats-last-theorem` at
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Apache 2.0).
The proof composes Mathlib's derivative nonvanishing and different-ideal APIs.
-/

@[expose] public section

open Polynomial

private lemma derivative_notMem_of_separable_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] (x : S) (f : R[X])
    (hf : aeval x f = 0)
    (hsep : (f.map (Ideal.Quotient.mk (P.under R))).Separable) :
    aeval x f.derivative ∉ P := by
  let j := Ideal.quotientMap P (algebraMap R S) le_rfl
  have eval_transport (g : R[X]) :
      (g.map (Ideal.Quotient.mk (P.under R))).eval₂ j
        (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (aeval x g) := by
    rw [eval₂_map, Ideal.quotientMap_comp_mk]
    exact (hom_eval₂ g (algebraMap R S) (Ideal.Quotient.mk P) x).symm
  have hroot := eval_transport f
  rw [hf, map_zero] at hroot
  have hne := hsep.eval₂_derivative_ne_zero j hroot
  rw [derivative_map, eval_transport] at hne
  exact fun hx => hne ((Ideal.Quotient.eq_zero_iff_mem).mpr hx)

namespace Algebra

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {R S : Type*} (K L : Type*)
  [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
  [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsIntegralClosure S R L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- A primitive field generator in the integral closure with separable
reduced minimal polynomial proves local unramifiedness. This retains the
nonzero-prime hypothesis of the source; integral-ring generation is not
required. -/
theorem isUnramifiedAt_of_separable_minpoly
    (P : Ideal S) [P.IsPrime] (_hP : P ≠ ⊥) (x : S)
    (hx : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (hsep : ((minpoly R x).map (Ideal.Quotient.mk (P.under R))).Separable) :
    IsUnramifiedAt R P := by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain _
  have hinj : Function.Injective (algebraMap R S) := by
    apply Function.Injective.of_comp (f := algebraMap S L)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have := IsIntegralClosure.isDedekindDomain R K L S
  have := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  have : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R L
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have hcomm : (algebraMap (FractionRing R) (FractionRing S)).comp
      (FractionRing.algEquiv R K).symm.toRingEquiv.toRingHom =
      (FractionRing.algEquiv S L).symm.toRingEquiv.toRingHom.comp
        (algebraMap K L) := by
    ext z
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv R K).symm (FractionRing.algEquiv S L).symm z
  have : Algebra.IsSeparable (FractionRing R) (FractionRing S) :=
    Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv R K).symm.toRingEquiv
      (FractionRing.algEquiv S L).symm.toRingEquiv hcomm
  apply (not_dvd_differentIdeal_iff (A := R) (B := S) (P := P)).mp
  intro hdiv
  exact derivative_notMem_of_separable_map P x (minpoly R x)
    (minpoly.aeval R x) hsep
    (Ideal.dvd_iff_le.mp hdiv (aeval_derivative_mem_differentIdeal R K L x hx))

/-- The integral field-element form of
`Algebra.isUnramifiedAt_of_separable_minpoly`. The supplied integral closure
need not be a canonical representation of the integral elements. -/
theorem isUnramifiedAt_of_separable_minpoly_of_isIntegral
    (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥) (x : L)
    (hx : IsIntegral R x) (hgen : Algebra.adjoin K {x} = ⊤)
    (hsep : ((minpoly R x).map (Ideal.Quotient.mk (P.under R))).Separable) :
    IsUnramifiedAt R P := by
  apply isUnramifiedAt_of_separable_minpoly K L P hP
    (IsIntegralClosure.mk' S x hx)
  · simpa only [IsIntegralClosure.algebraMap_mk'] using hgen
  · rwa [← IsIntegralClosure.algebraMap_mk' S x hx,
      minpoly.algebraMap_eq
        (IsIntegralClosure.algebraMap_injective S R L)] at hsep

end Algebra
