/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.ResidueSign
import Mathlib.Algebra.Exact.Basic

/-!
# Integral units into ray elements and exactness at units (N406 E1)

Left endpoint of the six-term exact sequence in ATLAS NumberTheoryI N406,
Theorem 21.8, Section 21.3: the integral-unit embedding, the ray-one unit
subgroup, the quotient and residue-sign endpoint maps, and exactness at units.

Source: `v1/Atlas/NumberTheoryI/code/RayClassFields.lean`,
declarations `exactSeq_map1`, `okUnitsToKUnits`, `valuation_algebraMap_unit_eq_one`,
`okUnitsInUnitsCoprime`, `okUnitsToUnitsCoprime`, `exactSeq_map2` (source lines
1012--1052) and `exactSeq_exact_at_units` (source lines 1134--1158).

Source-to-API map:
- ATLAS `UnitsCoprime` is `rayElements m`; ATLAS `UnitsCongruent_in_UnitsCoprime`
  is `rayOneElements m`; ATLAS `QuotientUnits` is the direct quotient
  `rayElements m ⧸ rayOneElements m`; ATLAS `SignsTimesUnits` is
  `ResidueSignTarget m` via `rayElementsQuotientEquivResidueSign` (PR #1367).
- ATLAS `exactSeq_map1` is `integralRayOneUnitsInclusion m`;
  `okUnitsToKUnits` is `integralUnitsToFieldUnits`;
  `valuation_algebraMap_unit_eq_one` is discharged inline in
  `integralUnitsToRayElements m` by Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem`;
  `okUnitsToUnitsCoprime` is `integralUnitsToRayElements m`;
  `exactSeq_map2` is `integralUnitsToRayQuotient m`.
- ATLAS `exactSeq_exact_at_units` is `integralUnits_mulExact_quotient`;
  `integralUnits_mulExact_residueSign` is the transported residue-sign form used
  by the concrete six-term sequence.

E1 partial-stage boundary: this module stops before the principal-ideal material
at source line 1054 and before the integral-unit/principal-ideal bridge at line
1160. It does not add the map to the ray class group or later exactness stages.
-/

@[expose] public noncomputable section

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Embedding of integral units into field units.** Let $K$ be a field and $\mathcal{O}_K$ its
ring of integers, the integral closure of $\mathbb{Z}$ in $K$. This is the group homomorphism
$\mathcal{O}_K^\times \to K^\times$ induced by the inclusion $\mathcal{O}_K \subseteq K$: it sends
a unit of $\mathcal{O}_K$ to the same element regarded as a unit of $K$.

Source: ATLAS `okUnitsToKUnits`. -/
def integralUnitsToFieldUnits : (𝓞 K)ˣ →* Kˣ :=
  Units.map (algebraMap (𝓞 K) K).toMonoidHom

omit [NumberField K] in
/-- **Integral units embed injectively into field units.** Let $K$ be a field and $\mathcal{O}_K$
its ring of integers, the integral closure of $\mathbb{Z}$ in $K$. The group homomorphism
$\mathcal{O}_K^\times \to K^\times$ induced by the inclusion $\mathcal{O}_K \subseteq K$ is
injective. -/
theorem integralUnitsToFieldUnits_injective :
    Function.Injective (integralUnitsToFieldUnits (K := K)) :=
  Units.map_injective (NumberField.RingOfIntegers.coe_injective (K := K))

/-- **Integral units as ray elements.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$, let $\mathfrak{m}$ be a modulus of $K$, and let
$K_{\mathfrak{m}} \subseteq K^\times$ be the group of ray elements for $\mathfrak{m}$. Every unit
of $\mathcal{O}_K$ has $\mathfrak{p}$-adic valuation $0$ at every prime $\mathfrak{p}$ of
$\mathcal{O}_K$, so it lies in $K_{\mathfrak{m}}$. This is the group homomorphism
$\mathcal{O}_K^\times \to K_{\mathfrak{m}}$ sending a unit $u$ to its image in $K^\times$.

Source: ATLAS `okUnitsToUnitsCoprime`; ATLAS `valuation_algebraMap_unit_eq_one` is discharged
inline in the definition. -/
def integralUnitsToRayElements (m : Modulus K) :
    (𝓞 K)ˣ →* rayElements m :=
  MonoidHom.codRestrict integralUnitsToFieldUnits (rayElements m)
    (fun u => mem_rayElements_of_valuation_eq_one m
      (integralUnitsToFieldUnits u) (fun v _ =>
        (v.valuation_eq_one_iff_notMem).2 (v.asIdeal.notMem_of_isUnit u.isUnit)))

/-- **Ray-element image of an integral unit as a field unit.** Let $K$ be a number field with
ring of integers $\mathcal{O}_K$, let $\mathfrak{m}$ be a modulus of $K$, and let
$u \in \mathcal{O}_K^\times$. The image of $u$ in the group of ray elements for $\mathfrak{m}$,
regarded as an element of $K^\times$, equals the image of $u$ under the embedding
$\mathcal{O}_K^\times \to K^\times$. -/
@[simp] theorem integralUnitsToRayElements_coe (m : Modulus K) (u : (𝓞 K)ˣ) :
    ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
      integralUnitsToFieldUnits u :=
  rfl

/-- **Integral units embed injectively into the ray elements.** Let $K$ be a number field with
ring of integers $\mathcal{O}_K$ and let $\mathfrak{m}$ be a modulus of $K$. The homomorphism
from $\mathcal{O}_K^\times$ to the group of ray elements for $\mathfrak{m}$ that sends a unit to
its image in $K^\times$ is injective. -/
theorem integralUnitsToRayElements_injective (m : Modulus K) :
    Function.Injective (integralUnitsToRayElements m) :=
  (MonoidHom.injective_codRestrict _ _ _).mpr
    integralUnitsToFieldUnits_injective

/-- **Ray-one integral units.** Let $K$ be a number field with ring of integers $\mathcal{O}_K$,
let $\mathfrak{m}$ be a modulus of $K$ with finite part $\mathfrak{m}_0$, and send each unit of
$\mathcal{O}_K$ to its image in the group of ray elements for $\mathfrak{m}$. For a nonzero prime
$\mathfrak{p}$ of $\mathcal{O}_K$, write $v_{\mathfrak{p}}$ for the $\mathfrak{p}$-adic valuation
of nonzero elements and nonzero ideals. The ray-one integral units for $\mathfrak{m}$ form the
subgroup of $\mathcal{O}_K^\times$ of those units $u$ whose image lies in the ray-one subgroup,
that is: for every prime $\mathfrak{p}$ dividing $\mathfrak{m}_0$, either $u = 1$ or
$v_{\mathfrak{p}}(u - 1) \ge v_{\mathfrak{p}}(\mathfrak{m}_0)$, and $u$ is positive under the
real embedding of every real place in the infinite part of $\mathfrak{m}$.

Source: ATLAS `UnitsInCongruenceSubgroup`. -/
def integralRayOneUnits (m : Modulus K) : Subgroup (𝓞 K)ˣ :=
  (rayOneElements m).comap (integralUnitsToRayElements m)

/-- **Membership in the ray-one integral units.** Let $\mathfrak m$ be a modulus of a number field
$K$ with finite part $\mathfrak m_0$ and set of real places $\mathfrak m_\infty$, and for a nonzero
prime $\mathfrak p$ of the ring of integers $\mathcal O_K$ write $v_{\mathfrak p}$ for the exponent
of $\mathfrak p$ in a fractional ideal of $K$, applied to an element through its principal
fractional ideal. A unit $u$ of $\mathcal O_K$ lies in the subgroup of ray-one integral units if
and only if $u$, viewed as an element of $K^\times$, is a ray element congruent to $1$ modulo
$\mathfrak m$: its principal fractional ideal is coprime to $\mathfrak m_0$, for every nonzero
prime $\mathfrak p$ dividing $\mathfrak m_0$ either $u = 1$ or
$v_{\mathfrak p}(u - 1) \ge v_{\mathfrak p}(\mathfrak m_0)$, and $u$ is positive under the real
embedding of every place in $\mathfrak m_\infty$. -/
@[simp] theorem mem_integralRayOneUnits_iff (m : Modulus K) (u : (𝓞 K)ˣ) :
    u ∈ integralRayOneUnits m ↔
      IsRayElementOne m
        ((integralUnitsToRayElements m u : rayElements m) : Kˣ) := by
  unfold integralRayOneUnits
  rw [Subgroup.mem_comap, mem_rayOneElements_iff]
  constructor
  · rintro ⟨hfin, hpos⟩
    exact ⟨(integralUnitsToRayElements m u).property, hfin, hpos⟩
  · rintro ⟨_, hfin, hpos⟩
    exact ⟨hfin, hpos⟩

/-- **Inclusion of the ray-one integral units.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$ and let $\mathfrak{m}$ be a modulus of $K$. The inclusion of the ray-one integral
units for $\mathfrak{m}$ is the group homomorphism from the subgroup of ray-one integral units for
$\mathfrak{m}$ to $\mathcal{O}_K^\times$ that sends each such unit to itself.

Source: ATLAS `exactSeq_map1`. -/
def integralRayOneUnitsInclusion (m : Modulus K) :
    integralRayOneUnits m →* (𝓞 K)ˣ :=
  (integralRayOneUnits m).subtype

/-- **Map from integral units to the ray quotient.** Let $\mathfrak m$ be a modulus of a number
field $K$, let $K_{\mathfrak m} \le K^\times$ be the group of ray elements (elements whose principal
fractional ideal is coprime to the finite part of $\mathfrak m$) and let
$K_{\mathfrak m,1} \le K_{\mathfrak m}$ be the ray-one subgroup. This is the group homomorphism
$\mathcal O_K^\times \to K_{\mathfrak m}/K_{\mathfrak m,1}$ sending a unit $u$ of the ring of
integers $\mathcal O_K$ to the coset of $u$, viewed as an element of $K_{\mathfrak m}$.

Source: ATLAS `exactSeq_map2`. -/
def integralUnitsToRayQuotient (m : Modulus K) :
    (𝓞 K)ˣ →* rayElements m ⧸ rayOneElements m :=
  (QuotientGroup.mk' (rayOneElements m)).comp (integralUnitsToRayElements m)

/-- **Value of the ray-quotient map on integral units.** Let $\mathfrak m$ be a modulus of a
number field $K$, let $K_{\mathfrak m} \le K^\times$ be the group of ray elements (elements whose
principal fractional ideal is coprime to the finite part of $\mathfrak m$) and let
$K_{\mathfrak m,1} \le K_{\mathfrak m}$ be the ray-one subgroup. For every unit $u$ of the ring of
integers $\mathcal O_K$, the map $\mathcal O_K^\times \to K_{\mathfrak m}/K_{\mathfrak m,1}$ sends
$u$ to the coset of $u$, viewed as an element of $K_{\mathfrak m}$. -/
@[simp] theorem integralUnitsToRayQuotient_apply (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToRayQuotient m u =
      QuotientGroup.mk (integralUnitsToRayElements m u) := by
  simp [integralUnitsToRayQuotient]

/-- **Residue-sign map on integral units.** Let $\mathfrak m$ be a modulus of a number field $K$
with finite part $\mathfrak m_0$ and set of real places $\mathfrak m_\infty$, let
$K_{\mathfrak m} \le K^\times$ be the group of ray elements and let
$K_{\mathfrak m,1} \le K_{\mathfrak m}$ be the ray-one subgroup. The residue-sign map on integral
units is the group homomorphism from $\mathcal O_K^\times$ to
$(\mathbb Z/2\mathbb Z)^{\mathfrak m_\infty} \times (\mathcal O_K/\mathfrak m_0)^\times$, with
$\mathbb Z/2\mathbb Z$ written multiplicatively, obtained by composing the map
$\mathcal O_K^\times \to K_{\mathfrak m}/K_{\mathfrak m,1}$ sending a unit to its coset with the
isomorphism from $K_{\mathfrak m}/K_{\mathfrak m,1}$ onto this group induced by the residue-sign
homomorphism on $K_{\mathfrak m}$. -/
noncomputable def integralUnitsToResidueSign (m : Modulus K) :
    (𝓞 K)ˣ →* ResidueSignTarget m :=
  (rayElementsQuotientEquivResidueSign m).toMonoidHom.comp
    (integralUnitsToRayQuotient m)

/-- **Value of the residue-sign map on integral units.** Let $\mathfrak m$ be a modulus of a
number field $K$ and let $K_{\mathfrak m} \le K^\times$ be the group of ray elements. For every unit
$u$ of the ring of integers $\mathcal O_K$, the residue-sign map on integral units sends $u$ to the
image of $u$, viewed as an element of $K_{\mathfrak m}$, under the residue-sign homomorphism on
$K_{\mathfrak m}$. -/
@[simp] theorem integralUnitsToResidueSign_apply (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToResidueSign m u =
      residueSignMap m (integralUnitsToRayElements m u) := by
  change (rayElementsQuotientEquivResidueSign m)
    (integralUnitsToRayQuotient m u) = _
  rw [integralUnitsToRayQuotient_apply, rayElementsQuotientEquivResidueSign_mk]

/-- **Kernel of the ray-quotient map on integral units.** Let $\mathfrak m$ be a modulus of a
number field $K$, let $K_{\mathfrak m} \le K^\times$ be the group of ray elements and
$K_{\mathfrak m,1} \le K_{\mathfrak m}$ the ray-one subgroup. The kernel of the homomorphism
$\mathcal O_K^\times \to K_{\mathfrak m}/K_{\mathfrak m,1}$ sending a unit of the ring of integers
$\mathcal O_K$ to its coset is the subgroup of ray-one integral units, the units of $\mathcal O_K$
that lie in $K_{\mathfrak m,1}$. -/
@[simp] theorem integralUnitsToRayQuotient_ker (m : Modulus K) :
    (integralUnitsToRayQuotient m).ker = integralRayOneUnits m := by
  unfold integralUnitsToRayQuotient integralRayOneUnits
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- **Kernel of the residue-sign map on integral units.** Let $\mathfrak m$ be a modulus of a
number field $K$. The kernel of the residue-sign map on the unit group $\mathcal O_K^\times$ of the
ring of integers is the subgroup of ray-one integral units, the units of $\mathcal O_K$ whose image
in the group of ray elements modulo $\mathfrak m$ lies in its ray-one subgroup. -/
@[simp] theorem integralUnitsToResidueSign_ker (m : Modulus K) :
    (integralUnitsToResidueSign m).ker = integralRayOneUnits m := by
  unfold integralUnitsToResidueSign
  rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _),
    integralUnitsToRayQuotient_ker]

/-- **The inclusion of the ray-one integral units is injective.** Let $K$ be a number field
with ring of integers $\mathcal{O}_K$ and let $\mathfrak{m}$ be a modulus of $K$. The inclusion
homomorphism from the subgroup of ray-one integral units for $\mathfrak{m}$ into the unit group
$\mathcal{O}_K^\times$ is injective. -/
theorem integralRayOneUnitsInclusion_injective (m : Modulus K) :
    Function.Injective (integralRayOneUnitsInclusion m) := by
  intro a b h
  have h' : (a : (𝓞 K)ˣ) = (b : (𝓞 K)ˣ) := h
  exact Subtype.ext h'

/-- **Exactness of the ray sequence at the integral units.** Let $K$ be a number field with ring
of integers $\mathcal{O}_K$ and let $\mathfrak{m}$ be a modulus of $K$. Write $K_{\mathfrak{m}}$
for the group of ray elements for $\mathfrak{m}$, $K_{\mathfrak{m},1}$ for its ray-one subgroup,
and $U_{\mathfrak{m},1} \subseteq \mathcal{O}_K^\times$ for the subgroup of ray-one integral units.
Consider the sequence

$$U_{\mathfrak{m},1} \to \mathcal{O}_K^\times \to K_{\mathfrak{m}}/K_{\mathfrak{m},1}$$

whose first map is the inclusion and whose second map sends a unit to the class of its image in
$K_{\mathfrak{m}}$. For every $u \in \mathcal{O}_K^\times$, the class of $u$ is the identity if
and only if $u$ lies in the image of the first map; that is, the sequence is exact at
$\mathcal{O}_K^\times$.

Source: ATLAS `exactSeq_exact_at_units`. -/
theorem integralUnits_mulExact_quotient (m : Modulus K) :
    Function.MulExact (integralRayOneUnitsInclusion m)
      (integralUnitsToRayQuotient m) := by
  rw [MonoidHom.mulExact_iff, integralUnitsToRayQuotient_ker]
  exact (Subgroup.range_subtype _).symm

/-- **Exactness at the integral units, residue-sign form.** Let $K$ be a number field with ring
of integers $\mathcal{O}_K$ and let $\mathfrak{m}$ be a modulus of $K$ with finite part
$\mathfrak{m}_0$. Let $T_{\mathfrak{m}}$ be the residue-sign target of $\mathfrak{m}$: the product
of a copy of $\mathbb{Z}/2\mathbb{Z}$, written multiplicatively, for each real place in the
infinite part of $\mathfrak{m}$, with $(\mathcal{O}_K/\mathfrak{m}_0)^\times$. Let
$\rho \colon \mathcal{O}_K^\times \to T_{\mathfrak{m}}$ send a unit to the class of its image in
the quotient of the group of ray elements for $\mathfrak{m}$ by its ray-one subgroup, followed by
the canonical isomorphism of that quotient with $T_{\mathfrak{m}}$ induced by the residue-sign
map. Then for every $u \in \mathcal{O}_K^\times$, $\rho(u) = 1$ if and only if $u$ is in the image
of the inclusion of the ray-one integral units for $\mathfrak{m}$ into $\mathcal{O}_K^\times$. -/
theorem integralUnits_mulExact_residueSign (m : Modulus K) :
    Function.MulExact (integralRayOneUnitsInclusion m)
      (integralUnitsToResidueSign m) := by
  rw [MonoidHom.mulExact_iff, integralUnitsToResidueSign_ker]
  exact (Subgroup.range_subtype _).symm

end Modulus
end NumberField
