/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.RayClassToClassGroup
import MathlibExt.RingTheory.ClassGroup.CoprimeRepresentative

/-!
# Six-term ray class exact sequence, projection surjectivity (N406 E5)

Final exactness stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the `mk0` membership/count bridge, surjectivity of the coprime ideal-class map
and of the ray-class-to-class-group projection, and the two six-term
aggregations (raw quotient and residue-sign forms). ATLAS has no single
wrapper declaration.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E5 lines 1431--1480
(`mk0` bridge through ray-class projection surjectivity).

Source-to-API map:
- Lemma 21.7 at lines 958--1010 is reused via Mathlib's stronger
  `ClassGroup.exists_mk0_eq_and_isCoprime`, which subsumes
  it: every ideal class has an integral representative coprime to any
  prescribed nonzero ideal;
- ATLAS lines 1431--1465 to `fractionalIdealMk0_mem_coprimeFractionalIdeals`
  (the `mk0` membership/count bridge);
- ATLAS lines 1466--1476 to `coprimeIdealClassMap_surjective` (coprime
  ideal-class map surjectivity);
- ATLAS lines 1478--1480 to `rayClassToClassGroup_surjective`
  (ray-class projection surjectivity: coprime-ideal preimage under
  `coprimeIdealClassMap_surjective` pushed through `rayClassMap` via
  `rayClassToClassGroup_rayClassMap`);
- `rayClass_six_term_exact` aggregates the separately source-backed
  map/exactness/surjectivity declarations from lines 1012--1480; it is not a
  direct declaration port. It combines only source-backed components: E1
  injectivity/exactness at units, E2--E3 quotient exactness, E4 exactness at
  the ray class group, and the new E5 surjectivity. No component is re-proved
  here;
- `rayClass_residueSign_six_term_exact` additionally transports through the
  quotient equivalence backed by lines 2607--2647.

E5 stage boundary: this module proves no finiteness statement and no part of
Corollary 21.9; those are explicitly excluded.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Integral ideals coprime to the finite part land in coprime fractional
ideals via `FractionalIdeal.mk0` (E5 `mk0` membership/count bridge for lines
1431--1465). -/
theorem fractionalIdealMk0_mem_coprimeFractionalIdeals
    (m : Modulus K) (I : nonZeroDivisors (Ideal (𝓞 K)))
    (hI : IsCoprime (I : Ideal (𝓞 K))
      (m.finitePart : Ideal (𝓞 K))) :
    FractionalIdeal.mk0 K I ∈ coprimeFractionalIdeals m := by
  rw [mem_coprimeFractionalIdeals_iff]
  intro v hv
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hsup := hI.sup_eq
  have hv' : (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal := hv
  have hndvd : ¬ v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    intro hdvd
    have hle : (I : Ideal (𝓞 K)) ⊔ (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal :=
      sup_le (Ideal.dvd_iff_le.mp hdvd) hv'
    rw [hsup] at hle
    exact v.isPrime.ne_top (top_le_iff.mp hle)
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coeIdeal K v hI0]
  have hcount : (Associates.mk v.asIdeal).count
      (Associates.mk (I : Ideal (𝓞 K))).factors = 0 := by
    by_contra hne
    exact hndvd
      ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne)
  exact Nat.cast_eq_zero.mpr hcount

/-- Surjectivity of the ideal-class map on coprime fractional ideals
(ATLAS lines 1466--1476; Lemma 21.7 at lines 958--1010 reused via the stronger
`ClassGroup.exists_mk0_eq_and_isCoprime`). -/
theorem coprimeIdealClassMap_surjective (m : Modulus K) :
    Function.Surjective (coprimeIdealClassMap m) := by
  intro c
  obtain ⟨⟨J, hJmem⟩, hJclass, hJcop⟩ :=
    ClassGroup.exists_mk0_eq_and_isCoprime c (J := (m.finitePart : Ideal (𝓞 K)))
      (mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property)
  have hJne : J ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hJmem
  have hJne0 : J ≠ 0 := by simpa using hJne
  let I : nonZeroDivisors (Ideal (𝓞 K)) :=
    ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJne0⟩
  have hJcop' : IsCoprime (I : Ideal (𝓞 K))
      (m.finitePart : Ideal (𝓞 K)) := hJcop
  have hmem := fractionalIdealMk0_mem_coprimeFractionalIdeals m I hJcop'
  refine ⟨⟨FractionalIdeal.mk0 K I, hmem⟩, ?_⟩
  have hsub : (coprimeFractionalIdeals m).subtype
      (⟨FractionalIdeal.mk0 K I, hmem⟩ : coprimeFractionalIdeals m) =
      FractionalIdeal.mk0 K I := rfl
  rw [coprimeIdealClassMap_apply, hsub, ClassGroup.mk_mk0]
  exact hJclass

/-- Surjectivity of the ray-class-to-class-group projection
(ATLAS lines 1478--1480). -/
theorem rayClassToClassGroup_surjective (m : Modulus K) :
    Function.Surjective (rayClassToClassGroup m) := by
  intro c
  obtain ⟨I, hI⟩ := coprimeIdealClassMap_surjective m c
  exact ⟨rayClassMap m I, (rayClassToClassGroup_rayClassMap m I).trans hI⟩

/-- Six-term exact sequence, raw quotient form: aggregation of the separately
source-backed map/exactness/surjectivity declarations from ATLAS lines
1012--1480 (not a direct declaration port). -/
theorem rayClass_six_term_exact (m : Modulus K) :
    Function.Injective (integralRayOneUnitsInclusion m) ∧
    Function.MulExact (integralRayOneUnitsInclusion m)
      (integralUnitsToRayQuotient m) ∧
    Function.MulExact (integralUnitsToRayQuotient m)
      (rayQuotientToRayClassGroup m) ∧
    Function.MulExact (rayQuotientToRayClassGroup m)
      (rayClassToClassGroup m) ∧
    Function.Surjective (rayClassToClassGroup m) :=
  ⟨integralRayOneUnitsInclusion_injective m,
    integralUnits_mulExact_quotient m,
    integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup m,
    rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup m,
    rayClassToClassGroup_surjective m⟩

/-- Six-term exact sequence, residue-sign form: aggregation of the separately
source-backed map/exactness/surjectivity declarations from ATLAS lines
1012--1480 (not a direct declaration port), additionally transported through
the quotient equivalence backed by lines 2607--2647. -/
theorem rayClass_residueSign_six_term_exact (m : Modulus K) :
    Function.Injective (integralRayOneUnitsInclusion m) ∧
    Function.MulExact (integralRayOneUnitsInclusion m)
      (integralUnitsToResidueSign m) ∧
    Function.MulExact (integralUnitsToResidueSign m)
      (residueSignToRayClassGroup m) ∧
    Function.MulExact (residueSignToRayClassGroup m)
      (rayClassToClassGroup m) ∧
    Function.Surjective (rayClassToClassGroup m) :=
  ⟨integralRayOneUnitsInclusion_injective m,
    integralUnits_mulExact_residueSign m,
    integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup m,
    residueSignToRayClassGroup_mulExact_rayClassToClassGroup m,
    rayClassToClassGroup_surjective m⟩

end Modulus
end NumberField
