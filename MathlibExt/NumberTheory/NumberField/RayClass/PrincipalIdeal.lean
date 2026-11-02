/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.ResidueSign

/-!
# Principal-ideal bridge for ray elements (N406 E2)

Supporting stage for ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the principal-ideal map out of ray elements, equality of principal ideals
modulo integral units, and equality of the ray group with the image of
ray-one elements.

Source: `Atlas/NumberTheoryI/code/RayClassFields.lean`
(`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`), N406.

Source-to-API map:
- ATLAS principal-ideal membership for ray elements, lines 1054--1091,
  to `principalRayIdealMap` and `principalRayIdealMap_apply`;
- ATLAS congruent principal ideals lie in the ray group, lines 1093--1108,
  to the reverse inclusion of `rayGroup_eq_map_rayOneElements`;
- ATLAS integral-unit extraction from equality of principal ideals,
  lines 1160--1204, to `toPrincipalIdeal_eq_iff_exists_integralUnit_mul`;
- ATLAS valuation/subtype reconstruction, lines 1206--1247, is obsolete
  (current `rayElements` is definitionally the comap of `toPrincipalIdeal`)
  and is not ported;
- ATLAS ray-group containment in the principal image, lines 1249--1282,
  to the forward inclusion of `rayGroup_eq_map_rayOneElements`
  (strengthened here to an equality).

This is E2 supporting work: it does not include the quotient lift at
source lines 1110--1118, any exactness declarations at line 1284 onward,
or the full six-term exact sequence / full N406.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Principal ray ideal map.** Let $\mathfrak m$ be a modulus of a number field $K$ with ring of
integers $\mathcal O_K$. The principal ray ideal map is the group homomorphism from the group of
ray elements for $\mathfrak m$ (the $x \in K^\times$ whose principal ideal is coprime to
$\mathfrak m$) to the group of fractional ideals coprime to $\mathfrak m$ that sends $x$ to the
principal fractional ideal $x\mathcal O_K$. -/
noncomputable def principalRayIdealMap (m : Modulus K) :
    rayElements m →* coprimeFractionalIdeals m :=
  ((toPrincipalIdeal (𝓞 K) K).domRestrict (rayElements m)).codRestrict
    (coprimeFractionalIdeals m)
    (fun x => (mem_rayElements_iff m _).mp x.property)

/-- **Value of the principal ray ideal map.** Let $\mathfrak m$ be a modulus of a number field
$K$ with ring of integers $\mathcal O_K$. For every ray element $x \in K^\times$ for
$\mathfrak m$, the image of $x$ under the principal ray ideal map, viewed as an invertible
fractional ideal of $K$, is the principal fractional ideal $x\mathcal O_K$. -/
@[simp] theorem principalRayIdealMap_apply (m : Modulus K) (x : rayElements m) :
    (principalRayIdealMap m x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
  rfl

/-- **Principal ideals agree exactly up to an integral unit.** Let $K$ be a number field with ring
of integers $\mathcal O_K$. For all $x, y \in K^\times$, the principal fractional ideals
$x\mathcal O_K$ and $y\mathcal O_K$ are equal if and only if $x = uy$ for some unit
$u \in \mathcal O_K^\times$. -/
theorem toPrincipalIdeal_eq_iff_exists_integralUnit_mul (x y : Kˣ) :
    toPrincipalIdeal (𝓞 K) K x = toPrincipalIdeal (𝓞 K) K y ↔
      ∃ u : (𝓞 K)ˣ,
        x = Units.map (algebraMap (𝓞 K) K).toMonoidHom u * y := by
  constructor
  · intro h
    have hcoe : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) := by
      have := congrArg (fun u : (FractionalIdeal (𝓞 K)⁰ K)ˣ =>
        (u : FractionalIdeal (𝓞 K)⁰ K)) h
      rwa [coe_toPrincipalIdeal, coe_toPrincipalIdeal] at this
    rw [FractionalIdeal.spanSingleton_eq_spanSingleton] at hcoe
    obtain ⟨z, hz⟩ := hcoe
    refine ⟨z⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def] at hz
    have hU : Units.map (algebraMap (𝓞 K) K).toMonoidHom z * x = y := by
      apply Units.ext
      simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe]
      exact hz
    rw [map_inv, ← hU, inv_mul_cancel_left]
  · rintro ⟨u, rfl⟩
    rw [map_mul]
    have hunit : toPrincipalIdeal (𝓞 K) K
        (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = 1 := by
      apply Units.ext
      rw [Units.val_one, coe_toPrincipalIdeal]
      have hmem : FractionalIdeal.spanSingleton (𝓞 K)⁰
          (Units.map (algebraMap (𝓞 K) K).toMonoidHom u : Kˣ).val =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) := by
        rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
        refine ⟨u⁻¹, ?_⟩
        rw [Units.smul_def, Algebra.smul_def, Units.coe_map,
          RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
        rw [← map_mul, Units.inv_mul, map_one]
      rwa [FractionalIdeal.spanSingleton_one] at hmem
    rw [hunit, one_mul]

/-- **The ray group is the image of the ray-one elements.** Let $\mathfrak m$ be a modulus of a
number field $K$. The ray group of $\mathfrak m$ equals the image under the principal ray ideal
map of the subgroup of ray-one elements, that is, of the ray elements for $\mathfrak m$ that are
congruent to $1$ modulo the finite part of $\mathfrak m$ and positive at every real place in
its infinite part. -/
theorem rayGroup_eq_map_rayOneElements (m : Modulus K) :
    rayGroup m = (rayOneElements m).map (principalRayIdealMap m) := by
  apply le_antisymm
  · apply rayGroup_closure_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxmem : (⟨x, hx.1⟩ : rayElements m) ∈ rayOneElements m :=
      (mem_rayOneElements_iff m _).mpr ⟨hx.2.1, hx.2.2⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hxmem, ?_⟩
    apply Subtype.ext
    exact principalRayIdealMap_apply m _
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := Subgroup.mem_map.mp hz
    have hIsOne : IsRayElementOne m (x : Kˣ) := by
      obtain ⟨hcongr, hpos⟩ := (mem_rayOneElements_iff m x).mp hx
      exact ⟨x.property, hcongr, hpos⟩
    have hmem := mem_rayGroup_of_isRayElementOne m (x : Kˣ) hIsOne
    rw [← hzx]
    convert hmem using 1
    apply Subtype.ext
    exact (principalRayIdealMap_apply m x).symm

end Modulus
end NumberField
