/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.IntegralUnits
import MathlibExt.NumberTheory.NumberField.RayClass.PrincipalIdeal
import MathlibExt.NumberTheory.NumberField.RayClass.Group

/-!
# Ray-element quotient to the ray class group (N406 E3)

Quotient stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the ray-element class map into the ray class group, its descent to the
ray-element quotient, representative rules, kernels, and exactness at the
quotient, plus the transported residue-sign corollary.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E3 lines 1110--1118
(`exactSeq_map3`) and 1284--1342 (`exactSeq_exact_at_quotient`).

Source-to-API map:
- ATLAS `exactSeq_map3`, lines 1110--1118, to `rayElementClassMap` and
  `rayQuotientToRayClassGroup` (`QuotientGroup.lift` of the `rayClassMap` after
  `principalRayIdealMap` composite);
- ATLAS `exactSeq_exact_at_quotient`, lines 1284--1342, to
  `rayQuotientToRayClassGroup_ker` and
  `integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup`.
- Representation differences: ATLAS works with `UnitsCoprime`,
  `UnitsCongruent_in_UnitsCoprime`, and `QuotientUnits`; here these are
  `rayElements m`, `rayOneElements m`, and `rayElements m ⧸ rayOneElements m`.
  ATLAS valuation/subtype reconstruction (lines 1206--1282) is replaced by the
  merged E2 lemmas `rayGroup_eq_map_rayOneElements` and
  `toPrincipalIdeal_eq_iff_exists_integralUnit_mul`; the integral-unit
  principal-ideal computation (lines 1160--1175) is replayed locally as
  `principalRayIdealMap_integralUnitsToRayElements`.
- The transported `residueSignToRayClassGroup` family has no ATLAS source span;
  it is the canonical corollary across `rayElementsQuotientEquivResidueSign`.

E3 partial-stage boundary: this module stops before `exactSeq_map4`
(lines 1120--1132), exactness at the ray class group (lines 1343--1429), and
coprime representatives / surjectivity / the six-term wrapper
(lines 1431--1480). It does not reimplement E1, E2, or the quotient
equivalence. Exactness holds only at the quotient: the kernel of
`rayElementClassMap` itself can be larger than `rayOneElements` (it need not
equal `rayOneElements`: it also contains the images of integral units, which
need not lie in `rayOneElements`), so no such kernel equality is claimed.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Ray-element class map.** For a modulus $\mathfrak m$ of a number field $K$, the ray-element
class map is the group homomorphism from the group of ray elements of $\mathfrak m$ to the ray
class group $\mathrm{Cl}_{\mathfrak m}$ that sends $x$ to the ray class of its principal
fractional ideal $(x)$, which is coprime to $\mathfrak m$; that is, the principal-ideal map
followed by the projection onto the ray class group.

Source: ATLAS `exactSeq_map3`, before the quotient lift. -/
noncomputable def rayElementClassMap (m : Modulus K) :
    rayElements m →* RayClassGroup m :=
  (rayClassMap m).comp (principalRayIdealMap m)

/-- **Value of the ray-element class map.** Let $\mathfrak m$ be a modulus of a number field $K$
and let $\mathrm{Cl}_{\mathfrak m}$ be its ray class group. For every ray element $x$ of
$\mathfrak m$, the ray-element class map sends $x$ to the ray class in $\mathrm{Cl}_{\mathfrak m}$
of the principal fractional ideal $(x)$, viewed as a fractional ideal coprime to $\mathfrak m$. -/
@[simp] theorem rayElementClassMap_apply (m : Modulus K) (x : rayElements m) :
    rayElementClassMap m x = rayClassMap m (principalRayIdealMap m x) :=
  rfl

/-- **Ray-one elements have trivial ray class.** Let $\mathfrak m$ be a modulus of a number field
$K$. Every ray-one element of $\mathfrak m$ lies in the kernel of the ray-element class map; that
is, its principal fractional ideal has trivial class in the ray class group
$\mathrm{Cl}_{\mathfrak m}$. -/
theorem rayOneElements_le_rayElementClassMap_ker (m : Modulus K) :
    rayOneElements m ≤ (rayElementClassMap m).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, rayElementClassMap_apply, rayClassMap_eq_one_iff]
  rw [rayGroup_eq_map_rayOneElements]
  exact Subgroup.mem_map_of_mem _ hx

/-- **Quotient-to-ray-class map.** For a modulus $\mathfrak m$ of a number field $K$, the
quotient-to-ray-class map is the group homomorphism from the quotient of the group of ray
elements of $\mathfrak m$ by the subgroup of ray-one elements to the ray class group
$\mathrm{Cl}_{\mathfrak m}$ induced by the ray-element class map: the class of a ray element $x$
goes to the ray class of its principal fractional ideal $(x)$. It is well defined because
ray-one elements lie in the kernel of the ray-element class map.

Source: ATLAS `exactSeq_map3`. -/
noncomputable def rayQuotientToRayClassGroup (m : Modulus K) :
    (rayElements m ⧸ rayOneElements m) →* RayClassGroup m :=
  QuotientGroup.lift (rayOneElements m) (rayElementClassMap m)
    (rayOneElements_le_rayElementClassMap_ker m)

/-- **Quotient-to-ray-class map on representatives.** Let $\mathfrak m$ be a modulus of a number
field $K$. For every ray element $x$ of $\mathfrak m$, the quotient-to-ray-class map sends the
class of $x$ modulo the ray-one elements to the image of $x$ under the ray-element class map. -/
@[simp] theorem rayQuotientToRayClassGroup_mk (m : Modulus K)
    (x : rayElements m) :
    rayQuotientToRayClassGroup m (QuotientGroup.mk x) =
      rayElementClassMap m x := by
  simp [rayQuotientToRayClassGroup]

/-- **Integral units generate the unit ideal.** Let $\mathfrak m$ be a modulus of a number field
$K$. For every unit $u \in \mathcal O_K^\times$, viewed as a ray element of $\mathfrak m$, the
principal fractional ideal $(u)$, as an element of the group of fractional ideals coprime to
$\mathfrak m$, is the identity element $\mathcal O_K$.

Source: ATLAS lines 1160--1175, an input to exactness at the quotient. -/
theorem principalRayIdealMap_integralUnitsToRayElements (m : Modulus K)
    (u : (𝓞 K)ˣ) :
    principalRayIdealMap m (integralUnitsToRayElements m u) = 1 := by
  apply Subtype.ext
  rw [principalRayIdealMap_apply]
  have h : toPrincipalIdeal (𝓞 K) K
      ((integralUnitsToRayElements m u : rayElements m) : Kˣ) =
      toPrincipalIdeal (𝓞 K) K 1 := by
    rw [toPrincipalIdeal_eq_iff_exists_integralUnit_mul]
    exact ⟨u, by simp [integralUnitsToRayElements_coe,
      integralUnitsToFieldUnits]⟩
  simpa using h

/-- **Exactness at the ray-element quotient (kernel form).** Let $\mathfrak m$ be a modulus of a
number field $K$. The kernel of the quotient-to-ray-class map, from the quotient of the ray
elements of $\mathfrak m$ by the ray-one elements to the ray class group
$\mathrm{Cl}_{\mathfrak m}$, equals the image of the map sending each unit
$u \in \mathcal O_K^\times$ to the class of $u$ in that quotient.

Source: ATLAS `exactSeq_exact_at_quotient`. -/
theorem rayQuotientToRayClassGroup_ker (m : Modulus K) :
    (rayQuotientToRayClassGroup m).ker =
      MonoidHom.range (integralUnitsToRayQuotient m) := by
  apply le_antisymm
  · intro q hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rayOneElements m) q
    rw [QuotientGroup.mk'_apply, rayQuotientToRayClassGroup_mk,
      rayElementClassMap_apply, rayClassMap_eq_one_iff] at hq
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp
      ((rayGroup_eq_map_rayOneElements m).symm ▸ hq)
    have htop : toPrincipalIdeal (𝓞 K) K (x : Kˣ) =
        toPrincipalIdeal (𝓞 K) K (y : Kˣ) := by
      have hcongr := congrArg Subtype.val hxy
      have hx : ((principalRayIdealMap m x : coprimeFractionalIdeals m) :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          toPrincipalIdeal (𝓞 K) K (x : Kˣ) :=
        principalRayIdealMap_apply m x
      have hy' : ((principalRayIdealMap m y : coprimeFractionalIdeals m) :
          (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
          toPrincipalIdeal (𝓞 K) K (y : Kˣ) :=
        principalRayIdealMap_apply m y
      rw [hx, hy'] at hcongr
      exact hcongr.symm
    obtain ⟨u, hu⟩ :=
      (toPrincipalIdeal_eq_iff_exists_integralUnit_mul (x : Kˣ) (y : Kˣ)).mp htop
    refine MonoidHom.mem_range.mpr ⟨u, ?_⟩
    rw [integralUnitsToRayQuotient_apply]
    symm
    change (x : rayElements m ⧸ rayOneElements m) =
      ((integralUnitsToRayElements m u : rayElements m) :
        rayElements m ⧸ rayOneElements m)
    rw [QuotientGroup.eq_iff_div_mem]
    have hdiv : x / integralUnitsToRayElements m u = y := by
      apply Subtype.ext
      simp only [Subgroup.coe_div, integralUnitsToRayElements_coe,
        integralUnitsToFieldUnits, RingHom.toMonoidHom_eq_coe]
      change (x : Kˣ) / Units.map (algebraMap (𝓞 K) K) u = (y : Kˣ)
      rw [hu, mul_comm]
      exact mul_div_cancel_right _ _
    rwa [hdiv]
  · intro q hq
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hq
    rw [MonoidHom.mem_ker, integralUnitsToRayQuotient_apply,
      rayQuotientToRayClassGroup_mk, rayElementClassMap_apply]
    rw [principalRayIdealMap_integralUnitsToRayElements, map_one]

/-- **Exactness at the ray-element quotient.** Let $\mathfrak m$ be a modulus of a number field
$K$, let $K_{\mathfrak m}$ be the group of ray elements (elements of $K^\times$ whose principal
ideal is coprime to the finite part of $\mathfrak m$), let $K_{\mathfrak m,1} \le K_{\mathfrak m}$
be the subgroup of ray-one elements, and let $\mathrm{Cl}_{\mathfrak m}$ be the ray class group
of $\mathfrak m$. In the sequence
$\mathcal O_K^\times \to K_{\mathfrak m}/K_{\mathfrak m,1} \to \mathrm{Cl}_{\mathfrak m}$,
where the first map sends a unit $u$ to the class of $u$ and the second sends the class of a ray
element $x$ to the ray class of the principal fractional ideal $(x)$, an element of
$K_{\mathfrak m}/K_{\mathfrak m,1}$ maps to the identity of $\mathrm{Cl}_{\mathfrak m}$ if and
only if it is the image of an integral unit.

Source: ATLAS `exactSeq_exact_at_quotient`. -/
theorem integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup
    (m : Modulus K) :
    Function.MulExact (integralUnitsToRayQuotient m)
      (rayQuotientToRayClassGroup m) := by
  rw [MonoidHom.mulExact_iff, rayQuotientToRayClassGroup_ker]

/-- **Ray class map on residues and signs.** Let $\mathfrak m$ be a modulus of a number field
$K$ with finite part $\mathfrak m_0$, let $K_{\mathfrak m}$ be the group of elements of $K^\times$
whose principal ideal is coprime to $\mathfrak m_0$, and let $K_{\mathfrak m,1}$ be its subgroup
of elements congruent to $1$ modulo $\mathfrak m_0$ and positive at every real place of
$\mathfrak m$. Let $T_{\mathfrak m}$ be the residue-sign target of $\mathfrak m$ and let
$\mathrm{Cl}_{\mathfrak m}$ be the ray class group of $\mathfrak m$. Let
$\psi : K_{\mathfrak m}/K_{\mathfrak m,1} \to T_{\mathfrak m}$ be the canonical isomorphism
induced by sending $x$ to its signs at the real places of $\mathfrak m$ and its residue modulo
$\mathfrak m_0$, and let $\phi : K_{\mathfrak m}/K_{\mathfrak m,1} \to \mathrm{Cl}_{\mathfrak m}$
be the homomorphism induced by sending $x \in K_{\mathfrak m}$ to the ray class of its principal
ideal $(x)$. The residue-sign-to-ray-class map is the group homomorphism
$\phi \circ \psi^{-1} : T_{\mathfrak m} \to \mathrm{Cl}_{\mathfrak m}$. -/
noncomputable def residueSignToRayClassGroup (m : Modulus K) :
    ResidueSignTarget m →* RayClassGroup m :=
  (rayQuotientToRayClassGroup m).comp
    (rayElementsQuotientEquivResidueSign m).symm.toMonoidHom

/-- **Residue-sign-to-ray-class map through the quotient isomorphism.** Let $\mathfrak m$ be a
modulus of a number field $K$ with finite part $\mathfrak m_0$, let $K_{\mathfrak m}$ be the
group of elements of $K^\times$ whose principal ideal is coprime to $\mathfrak m_0$, and let
$K_{\mathfrak m,1}$ be its subgroup of elements congruent to $1$ modulo $\mathfrak m_0$ and
positive at every real place of $\mathfrak m$. Let $T_{\mathfrak m}$ be the residue-sign target
of $\mathfrak m$, let $\mathrm{Cl}_{\mathfrak m}$ be the ray class group of $\mathfrak m$, let
$\psi : K_{\mathfrak m}/K_{\mathfrak m,1} \to T_{\mathfrak m}$ be the canonical isomorphism
induced by sending $x$ to its signs at the real places of $\mathfrak m$ and its residue modulo
$\mathfrak m_0$, and let $\phi : K_{\mathfrak m}/K_{\mathfrak m,1} \to \mathrm{Cl}_{\mathfrak m}$
be the homomorphism induced by sending $x$ to the ray class of its principal ideal $(x)$. Then
for every $q \in K_{\mathfrak m}/K_{\mathfrak m,1}$, the residue-sign-to-ray-class map
$T_{\mathfrak m} \to \mathrm{Cl}_{\mathfrak m}$ sends $\psi(q)$ to $\phi(q)$. -/
@[simp] theorem residueSignToRayClassGroup_equiv (m : Modulus K)
    (q : rayElements m ⧸ rayOneElements m) :
    residueSignToRayClassGroup m (rayElementsQuotientEquivResidueSign m q) =
      rayQuotientToRayClassGroup m q := by
  simp [residueSignToRayClassGroup]

/-- **Ray class map on residue-sign values.** Let $\mathfrak m$ be a modulus of a number field
$K$ and let $x$ be a ray element of $\mathfrak m$, that is, $x \in K^\times$ with principal ideal
coprime to the finite part of $\mathfrak m$. Then the residue-sign-to-ray-class map sends the
residue-sign value of $x$ (its signs at the real places of $\mathfrak m$ together with its
residue modulo the finite part) to the ray class of the principal ideal $(x)$. -/
theorem residueSignToRayClassGroup_residueSignMap (m : Modulus K)
    (x : rayElements m) :
    residueSignToRayClassGroup m (residueSignMap m x) =
      rayElementClassMap m x := by
  calc residueSignToRayClassGroup m (residueSignMap m x)
      = residueSignToRayClassGroup m
          (rayElementsQuotientEquivResidueSign m (QuotientGroup.mk x)) := by
        rw [rayElementsQuotientEquivResidueSign_mk]
    _ = rayQuotientToRayClassGroup m (QuotientGroup.mk x) :=
        residueSignToRayClassGroup_equiv m _
    _ = rayElementClassMap m x := rayQuotientToRayClassGroup_mk m x

/-- **The residue-sign transport square commutes.** Let $\mathfrak m$ be a modulus of a number
field $K$. The residue-sign map from the ray elements of $\mathfrak m$ to the residue-sign target,
followed by the transported residue-sign-to-ray-class map, equals the ray-element class map. -/
theorem residueSignToRayClassGroup_comp_residueSignMap (m : Modulus K) :
    (residueSignToRayClassGroup m).comp (residueSignMap m) =
      rayElementClassMap m := by
  ext x
  simp only [MonoidHom.comp_apply]
  exact residueSignToRayClassGroup_residueSignMap m x

/-- **Kernel of the ray class map on residue-sign values.** Let $\mathfrak m$ be a modulus of a
number field $K$. The kernel of the residue-sign-to-ray-class map from the residue-sign target
of $\mathfrak m$ to the ray class group of $\mathfrak m$ equals the image of the homomorphism
$\mathcal O_K^\times \to$ (residue-sign target) that sends a unit $u$ to its residue-sign value,
namely its signs at the real places of $\mathfrak m$ together with its residue modulo the finite
part of $\mathfrak m$. -/
theorem residueSignToRayClassGroup_ker (m : Modulus K) :
    (residueSignToRayClassGroup m).ker =
      MonoidHom.range (integralUnitsToResidueSign m) := by
  unfold residueSignToRayClassGroup integralUnitsToResidueSign
  change
    ((rayQuotientToRayClassGroup m).comp
      (rayElementsQuotientEquivResidueSign m).symm).ker =
    ((rayElementsQuotientEquivResidueSign m).toMonoidHom.comp
      (integralUnitsToRayQuotient m)).range
  rw [MonoidHom.ker_comp_mulEquiv, MonoidHom.range_comp,
    rayQuotientToRayClassGroup_ker, MulEquiv.symm_symm,
    MulEquiv.toMonoidHom_eq_coe]

/-- **Exactness at the residue-sign group.** Let $\mathfrak m$ be a modulus of a number field
$K$ with finite part $\mathfrak m_0$ and set of real places $\mathfrak m_\infty$, let
$\mathrm{Cl}_{\mathfrak m}$ be its ray class group, and let
$R_{\mathfrak m} = \{\pm 1\}^{\mathfrak m_\infty} \times (\mathcal O_K/\mathfrak m_0)^\times$.
Consider the maps $\mathcal O_K^\times \to R_{\mathfrak m} \to \mathrm{Cl}_{\mathfrak m}$. The
first sends a unit $u$ to its signs at the places in $\mathfrak m_\infty$ together with its class
in $(\mathcal O_K/\mathfrak m_0)^\times$. The second is the quotient-to-ray-class map transported
along the canonical isomorphism from the quotient of the ray elements by the ray-one elements
onto $R_{\mathfrak m}$, so it sends the image in $R_{\mathfrak m}$ of a ray element $x$ to the
ray class of the principal fractional ideal $(x)$. An element of $R_{\mathfrak m}$ maps to the
identity of $\mathrm{Cl}_{\mathfrak m}$ if and only if it is the image of an integral unit. -/
theorem integralUnitsToResidueSign_mulExact_residueSignToRayClassGroup
    (m : Modulus K) :
    Function.MulExact (integralUnitsToResidueSign m)
      (residueSignToRayClassGroup m) := by
  rw [MonoidHom.mulExact_iff, residueSignToRayClassGroup_ker]

end Modulus
end NumberField
