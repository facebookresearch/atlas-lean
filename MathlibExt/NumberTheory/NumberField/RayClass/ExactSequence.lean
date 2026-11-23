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
- Lemma 21.7 at lines 958--1010 is reused via the stronger existing
  formal-math theorem `ClassGroup.exists_mk0_eq_and_isCoprime`, which subsumes
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

/-- **Nonzero integral ideals coprime to the modulus are coprime fractional ideals.** Let $K$
be a number field with ring of integers $\mathcal O_K$, let $\mathfrak m$ be a modulus of $K$
with finite part $\mathfrak m_0$, and let $I$ be a nonzero ideal of $\mathcal O_K$ with
$I + \mathfrak m_0 = \mathcal O_K$. Then $I$, viewed as an invertible fractional ideal of $K$,
belongs to the group of fractional ideals coprime to $\mathfrak m_0$: its exponent at every prime
dividing $\mathfrak m_0$ is $0$.

Source: E5 `mk0` membership/count bridge for ATLAS lines 1431--1465. -/
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
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe K v hI0]
  have hcount : (Associates.mk v.asIdeal).count
      (Associates.mk (I : Ideal (𝓞 K))).factors = 0 := by
    by_contra hne
    exact hndvd
      ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hne)
  exact Nat.cast_eq_zero.mpr hcount

/-- **Every ideal class contains a fractional ideal coprime to the modulus.** Let $K$ be a
number field and $\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$. The homomorphism
from the group of fractional ideals of $K$ coprime to $\mathfrak m_0$ (those whose exponent at
every prime dividing $\mathfrak m_0$ is $0$) to the class group of $\mathcal O_K$, sending each
such fractional ideal to its ideal class, is surjective.

Source: ATLAS lines 1466--1476; Lemma 21.7 at lines 958--1010 is reused via the stronger
`ClassGroup.exists_mk0_eq_and_isCoprime`. -/
theorem coprimeIdealClassMap_surjective (m : Modulus K) :
    Function.Surjective (coprimeIdealClassMap m) := by
  intro c
  obtain ⟨J, hJne, hJclass, hJcop⟩ :=
    ClassGroup.exists_mk0_eq_and_isCoprime c
      (m.finitePart : Ideal (𝓞 K))
      (mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property)
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

/-- **The ray class group surjects onto the class group.** Let $K$ be a number field and
$\mathfrak m$ a modulus of $K$. The homomorphism from the ray class group of $\mathfrak m$ to the
class group of $\mathcal O_K$, sending the ray class of a fractional ideal coprime to the finite
part of $\mathfrak m$ to its ideal class, is surjective.

Source: ATLAS lines 1478--1480. -/
theorem rayClassToClassGroup_surjective (m : Modulus K) :
    Function.Surjective (rayClassToClassGroup m) := by
  intro c
  obtain ⟨I, hI⟩ := coprimeIdealClassMap_surjective m c
  exact ⟨rayClassMap m I, (rayClassToClassGroup_rayClassMap m I).trans hI⟩

/-- **The ray class exact sequence.** Let $K$ be a number field with ring of
integers $\mathcal O_K$, and let $\mathfrak m$ be a modulus of $K$ with finite part
$\mathfrak m_0$ (a nonzero ideal of $\mathcal O_K$) and infinite part $\mathfrak m_\infty$ (a
finite set of real places). Let $K_{\mathfrak m}$ be the group of $x \in K^\times$ whose
principal fractional ideal is coprime to $\mathfrak m_0$, and let
$K_{\mathfrak m,1} \subseteq K_{\mathfrak m}$ be the subgroup of those $x$ that are positive at
every real place in $\mathfrak m_\infty$ and satisfy, for every prime
$\mathfrak p \mid \mathfrak m_0$, either $x = 1$ or
$v_{\mathfrak p}(x - 1) \ge v_{\mathfrak p}(\mathfrak m_0)$, where $v_{\mathfrak p}$ of an
element of $K^\times$ or of a nonzero ideal is the exponent of $\mathfrak p$ in its fractional
ideal. Let $U_{\mathfrak m,1}$ be the group
of units of $\mathcal O_K$ lying in $K_{\mathfrak m,1}$, let $\mathrm{Cl}_{\mathfrak m}$ be the
ray class group (fractional ideals coprime to $\mathfrak m_0$ modulo the subgroup generated by
the principal ideals $(x)$ with $x \in K_{\mathfrak m,1}$), and let $\mathrm{Cl}(\mathcal O_K)$
be the class group. Then the sequence
$$
1 \to U_{\mathfrak m,1} \to \mathcal O_K^\times \to K_{\mathfrak m}/K_{\mathfrak m,1}
\to \mathrm{Cl}_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K) \to 1
$$
is exact, where the maps are the inclusion, the map sending a unit to its class modulo
$K_{\mathfrak m,1}$, the map sending the class of $x$ to the ray class of $(x)$, and the map
sending the ray class of a fractional ideal to its ideal class.

Source: ATLAS lines 1012--1480; this theorem aggregates the separately source-backed map,
exactness and surjectivity declarations and is not a direct declaration port. -/
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

/-- **The ray class exact sequence, sign and residue form.** Let $K$ be a number field with ring of
integers $\mathcal O_K$, and let $\mathfrak m$ be a modulus of $K$ with finite part
$\mathfrak m_0$ (a nonzero ideal of $\mathcal O_K$) and infinite part $\mathfrak m_\infty$ (a
finite set of real places). Let $K_{\mathfrak m}$ be the group of $x \in K^\times$ whose
principal fractional ideal is coprime to $\mathfrak m_0$, and let
$K_{\mathfrak m,1} \subseteq K_{\mathfrak m}$ be the subgroup of those $x$ that are positive at
every real place in $\mathfrak m_\infty$ and satisfy, for every prime
$\mathfrak p \mid \mathfrak m_0$, either $x = 1$ or
$v_{\mathfrak p}(x - 1) \ge v_{\mathfrak p}(\mathfrak m_0)$, where $v_{\mathfrak p}$ of an
element of $K^\times$ or of a nonzero ideal is the exponent of $\mathfrak p$ in its fractional
ideal. Let $U_{\mathfrak m,1}$ be the group
of units of $\mathcal O_K$ lying in $K_{\mathfrak m,1}$, let $\mathrm{Cl}_{\mathfrak m}$ be the
ray class group (fractional ideals coprime to $\mathfrak m_0$ modulo the subgroup generated by
the principal ideals $(x)$ with $x \in K_{\mathfrak m,1}$), and let $\mathrm{Cl}(\mathcal O_K)$
be the class group. For
$x \in K_{\mathfrak m}$, let $\rho(x) \in \{\pm 1\}^{\mathfrak m_\infty} \times
(\mathcal O_K/\mathfrak m_0)^\times$ record the sign of $x$ at each real place in
$\mathfrak m_\infty$ and the residue class of $x$ modulo $\mathfrak m_0$ (the class of $a b^{-1}$
when $x = a/b$ with $a, b \in \mathcal O_K$ prime to $\mathfrak m_0$); $\rho$ is surjective with
kernel $K_{\mathfrak m,1}$. Then the sequence
$$
1 \to U_{\mathfrak m,1} \to \mathcal O_K^\times \to
\{\pm 1\}^{\mathfrak m_\infty} \times (\mathcal O_K/\mathfrak m_0)^\times
\to \mathrm{Cl}_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K) \to 1
$$
is exact, where the maps are the inclusion, the restriction of $\rho$ to units, the map sending
$\rho(x)$ to the ray class of $(x)$, and the map sending the ray class of a fractional ideal to
its ideal class.

Source: ATLAS lines 1012--1480, aggregated from the separately source-backed map, exactness and
surjectivity declarations (not a direct declaration port), and transported through the quotient
equivalence backed by lines 2607--2647. -/
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
