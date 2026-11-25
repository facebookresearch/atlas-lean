/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.WeakApproximation
import MathlibExt.NumberTheory.NumberField.RayClass.InfiniteSign

/-!
# Combined residue-sign map and ray quotient equivalence (N406)

Quotient-isomorphism clause of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the product of the infinite-sign map and the finite-residue map on ray elements
is surjective with kernel the ray-one subgroup, so the ray-element quotient is
canonically equivalent to the residue-sign target.

Source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2194-L2647),
declaration
[`RayClassField.theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
The controlled approximation is `weak_approx_coprime_sign_finitePart`
(lines 2255--2568), product surjectivity is `signTimesFinitePart_surjective`
(lines 2576--2594), and the quotient packaging is `theorem_21_8_quotient_iso`
(lines 2607--2647).

Source-to-API map:
- ATLAS `signTimesFinitePart_surjective`, lines 2576--2594, to `residueSignMap`
  and `residueSignMap_surjective`;
- the kernel computation inside `theorem_21_8_quotient_iso`, lines 2607--2643,
  to `rayOneElements`, `residueSignMap_ker`, and `residueSignMap_eq_one_iff`;
- ATLAS quotient packaging, lines 2644--2647, to
  `rayElementsQuotientEquivResidueSign`.

The six-term exact sequence at source lines 1012--1480 remains a separate later
stage; this module does not complete all of N406.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Residue-sign target.** Let $m$ be a modulus of a number field $K$, with finite part the
nonzero ideal $\mathfrak{m}_0$ of the ring of integers $\mathcal{O}_K$ and infinite part the
finite set $S$ of real places of $K$. Let $G$ denote $\mathbb{Z}/2\mathbb{Z}$ written
multiplicatively, let $G^S$ denote the group of functions from $S$ to $G$ (one sign for each place
in $S$), and let $(\mathcal{O}_K/\mathfrak{m}_0)^\times$ denote the unit group of the quotient ring
$\mathcal{O}_K/\mathfrak{m}_0$. The residue-sign target of $m$ is the product group
$G^S \times (\mathcal{O}_K/\mathfrak{m}_0)^\times$. -/
abbrev ResidueSignTarget (m : Modulus K) :=
  (m.infinitePart → Multiplicative (ZMod 2)) ×
    (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))ˣ

/-- **Residue-sign map.** Let $m$ be a modulus of a number field $K$. The residue-sign map of $m$
is the group homomorphism from the ray elements of $m$ to the residue-sign target of $m$ that
sends a ray element $x$ to the pair formed by the image of $x$ under the infinite sign map of $m$
and the image of $x$ under the finite residue map of $m$. -/
noncomputable def residueSignMap (m : Modulus K) :
    rayElements m →* ResidueSignTarget m :=
  (infiniteSignMap m).prod (finiteResidueMap m)

/-- **Components of the residue-sign map.** Let $m$ be a modulus of a number field $K$. For every
ray element $x$ of $m$, the image of $x$ under the residue-sign map of $m$ is the pair whose first
component is the image of $x$ under the infinite sign map of $m$ and whose second component is the
image of $x$ under the finite residue map of $m$. -/
@[simp] theorem residueSignMap_apply (m : Modulus K) (x : rayElements m) :
    residueSignMap m x = (infiniteSignMap m x, finiteResidueMap m x) :=
  rfl

/-- **Ray-one subgroup.** Let $m$ be a modulus of a number field $K$. The ray-one subgroup of $m$ is
the subgroup of the ray elements of $m$ consisting of the ray elements $x$ that lie in the finite
ray-one subgroup of $m$ (those congruent to $1$ at the finite part of $m$) and in the subgroup of
ray elements positive at every real place in the infinite part of $m$. -/
def rayOneElements (m : Modulus K) : Subgroup (rayElements m) :=
  finiteRayOneElements m ⊓ positiveRayElements m

/-- **Membership in the ray-one subgroup.** Let $m$ be a modulus of a number field $K$. A ray
element $x$ of $m$ lies in the ray-one subgroup of $m$ if and only if $x$ is congruent to $1$ at
the finite part of $m$ and $x$ is positive at every real place in the infinite part of $m$. -/
@[simp] theorem mem_rayOneElements_iff (m : Modulus K) (x : rayElements m) :
    x ∈ rayOneElements m ↔
      CongruentOneAtFinitePart m (x : Kˣ) ∧
        PositiveAtInfinitePart m (x : Kˣ) := by
  simp [rayOneElements, mem_finiteRayOneElements_iff,
    mem_positiveRayElements_iff]

/-- Local lift of the private quotient-to-prime argument in
`FiniteCongruence`: a unit modulo the finite part avoids every supported prime. -/
private theorem isUnit_quotient_mk_not_mem_supported
    (m : Modulus K) {b : 𝓞 K}
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) : b ∉ v.asIdeal := by
  have H : ∀ a : 𝓞 K, a ∈ (m.finitePart : Ideal (𝓞 K)) →
      Ideal.Quotient.mk v.asIdeal a = 0 :=
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hv ha)
  have hunit : IsUnit (Ideal.Quotient.lift (m.finitePart : Ideal (𝓞 K))
      (Ideal.Quotient.mk v.asIdeal) H (Ideal.Quotient.mk _ b)) := hb.map _
  rw [Ideal.Quotient.lift_mk] at hunit
  intro hmem
  have hzero : Ideal.Quotient.mk v.asIdeal b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hzero] at hunit
  let _ : Nontrivial (𝓞 K ⧸ v.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  exact not_isUnit_zero hunit

/-- Every element of `Multiplicative (ZMod 2)` is `1` or `ofAdd 1`. -/
private theorem eq_one_or_ofAdd_one (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd 1 := by
  rcases Multiplicative.ofAdd.surjective a with ⟨b, rfl⟩
  fin_cases b <;> first | left; rfl | right; rfl

/-- **Surjectivity of the residue-sign map.** Let $m$ be a modulus of a number field $K$. Every
element of the residue-sign target of $m$ is the image of some ray element of $m$ under the
residue-sign map of $m$. -/
theorem residueSignMap_surjective (m : Modulus K) :
    Function.Surjective (residueSignMap m) := by
  classical
  intro ⟨s, u⟩
  obtain ⟨r, hr_unit, hr_lift, hr_ne_zero⟩ :
      ∃ r : 𝓞 K, IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r) ∧
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r =
          (u : 𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) ∧ r ≠ 0 := by
    by_cases htriv : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))
    · exact ⟨1, isUnit_one, Subsingleton.elim _ _, one_ne_zero⟩
    · rw [not_subsingleton_iff_nontrivial] at htriv
      let _ : Nontrivial (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
      obtain ⟨r, hr_lift⟩ :=
        Ideal.Quotient.mk_surjective (u : 𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))
      have hr_unit : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r) :=
        hr_lift ▸ u.isUnit
      have hr_ne_zero : r ≠ 0 := by
        intro h
        rw [h, map_zero] at hr_unit
        exact not_isUnit_zero hr_unit
      exact ⟨r, hr_unit, hr_lift, hr_ne_zero⟩
  have halg_ne : algebraMap (𝓞 K) K r ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
  have hr_not_mem : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v → r ∉ v.asIdeal :=
    fun v hv => isUnit_quotient_mk_not_mem_supported m hr_unit v hv
  have haval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v → v.valuation K (algebraMap (𝓞 K) K r) = 1 := by
    intro v hv
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
      (hr_not_mem v hv)
  let pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop :=
    fun wh => s wh = 1
  obtain ⟨x, hxne, hval, hsign⟩ :=
    exists_ne_zero_with_target_and_sign m (algebraMap (𝓞 K) K r) pos
      halg_ne haval
  let x_unit : Kˣ := Units.mk0 x hxne
  let a_unit : Kˣ := Units.mk0 (algebraMap (𝓞 K) K r) halg_ne
  have hx_mem : x_unit ∈ rayElements m :=
    mem_rayElements_of_valuation_eq_one m x_unit (fun v hv => (hval v hv).1)
  have ha_mem : a_unit ∈ rayElements m :=
    mem_rayElements_of_valuation_eq_one m a_unit (fun v hv => haval v hv)
  let X : rayElements m := ⟨x_unit, hx_mem⟩
  let A : rayElements m := ⟨a_unit, ha_mem⟩
  have hsign_X : infiniteSignMap m X = s := by
    funext ⟨w, hw⟩
    rw [infiniteSignMap_apply]
    change signAtRealPlace (↑(⟨w, hw⟩ : m.infinitePart) : RealPlace K)
      (X : Kˣ) = s ⟨w, hw⟩
    by_cases hpos : pos ⟨w, hw⟩
    · have hre := (hsign w hw).1 hpos
      have hposX : 0 < InfinitePlace.embedding_of_isReal
          (↑(⟨w, hw⟩ : m.infinitePart) : RealPlace K).property
          ((X : Kˣ) : K) := by
        simpa [X, x_unit] using hre
      have h1 : signAtRealPlace (↑(⟨w, hw⟩ : m.infinitePart) : RealPlace K)
          (X : Kˣ) = 1 :=
        (signAtRealPlace_apply_eq_one_iff _ _).mpr hposX
      rw [h1]
      exact hpos.symm
    · have hre := (hsign w hw).2 hpos
      have hreX : InfinitePlace.embedding_of_isReal
          (↑(⟨w, hw⟩ : m.infinitePart) : RealPlace K).property
          ((X : Kˣ) : K) < 0 := by
        simpa [X, x_unit] using hre
      have hne : signAtRealPlace
          (↑(⟨w, hw⟩ : m.infinitePart) : RealPlace K) (X : Kˣ) ≠ 1 := by
        intro hcon
        have hposX := (signAtRealPlace_apply_eq_one_iff _ _).mp hcon
        linarith
      rcases eq_one_or_ofAdd_one (signAtRealPlace
        (↑(⟨w, hw⟩ : m.infinitePart) : RealPlace K) (X : Kˣ)) with h | h
      · exact absurd h hne
      · rcases eq_one_or_ofAdd_one (s ⟨w, hw⟩) with hs | hs
        · exact absurd hs hpos
        · rw [h, hs]
  have hfin_X : finiteResidueMap m X = u := by
    have htriv : finiteResidueMap m (X * A⁻¹) = 1 := by
      apply finiteResidueMap_eq_one_of_valuation_le
      intro v hv
      have hval_XA : (((X * A⁻¹ : rayElements m) : Kˣ) : K) =
          x * (algebraMap (𝓞 K) K r)⁻¹ := by
        simp [X, A, Subgroup.coe_mul, x_unit, a_unit,
          Units.val_mul, Units.val_inv_eq_inv_val]
      have hsub : x * (algebraMap (𝓞 K) K r)⁻¹ - 1 =
          (x - algebraMap (𝓞 K) K r) * (algebraMap (𝓞 K) K r)⁻¹ := by
        rw [sub_mul, mul_inv_cancel₀ halg_ne]
      rw [hval_XA, hsub, Valuation.map_mul, Valuation.map_inv, haval v hv,
        inv_one, mul_one]
      exact (hval v hv).2
    have hmul : finiteResidueMap m X * (finiteResidueMap m A)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul, htriv]
    have hmap : finiteResidueMap m X = finiteResidueMap m A :=
      mul_inv_eq_one.mp hmul
    rw [hmap]
    have hab : algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K 1 =
        ((A : Kˣ) : K) := by
      simp [A, a_unit]
    have hA0 := finiteResidueMap_apply_of_div_eq m A r 1 hr_unit isUnit_one hab
    have hu_eq : hr_unit.unit = u := by
      apply Units.ext
      simp only [IsUnit.unit_spec, hr_lift]
    have h1_eq : IsUnit.unit (show
        IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) (1 : 𝓞 K))
        from isUnit_one) = 1 := by
      apply Units.ext
      simp
    rw [h1_eq, inv_one, mul_one, hu_eq] at hA0
    exact hA0
  refine ⟨X, Prod.ext ?_ ?_⟩
  · change (residueSignMap m X).1 = s
    rw [residueSignMap_apply]
    exact hsign_X
  · change (residueSignMap m X).2 = u
    rw [residueSignMap_apply]
    exact hfin_X

/-- **Kernel of the residue-sign map.** Let $m$ be a modulus of a number field $K$. The kernel of
the residue-sign map of $m$ is the ray-one subgroup of $m$. -/
@[simp] theorem residueSignMap_ker (m : Modulus K) :
    (residueSignMap m).ker = rayOneElements m := by
  unfold rayOneElements positiveRayElements
  rw [residueSignMap, MonoidHom.ker_prod, finiteResidueMap_ker, inf_comm]

/-- **Kernel criterion for the residue-sign map.** Let $m$ be a modulus of a number field $K$. A
ray element $x$ of $m$ is sent to $1$ by the residue-sign map of $m$ if and only if $x$ is a ray
element congruent to $1$ modulo $m$: $x$ is a ray element of $m$, $x$ is congruent to $1$ at the
finite part of $m$, and $x$ is positive at every real place in the infinite part of $m$. -/
theorem residueSignMap_eq_one_iff (m : Modulus K) (x : rayElements m) :
    residueSignMap m x = 1 ↔ IsRayElementOne m (x : Kˣ) := by
  rw [← MonoidHom.mem_ker, residueSignMap_ker]
  constructor
  · intro h
    obtain ⟨hfin, hpos⟩ := (mem_rayOneElements_iff m x).mp h
    exact ⟨x.property, hfin, hpos⟩
  · intro h
    exact (mem_rayOneElements_iff m x).mpr ⟨h.congruent, h.positive⟩

/-- **The residue-sign isomorphism.** Let $m$ be a modulus of a number field $K$. The residue-sign
isomorphism of $m$ is the group isomorphism from the quotient of the ray elements of $m$ by the
ray-one subgroup of $m$ onto the residue-sign target of $m$ induced by the residue-sign map, which
is surjective with kernel the ray-one subgroup; it sends the class of a ray element $x$ to the
image of $x$ under the residue-sign map. -/
noncomputable def rayElementsQuotientEquivResidueSign (m : Modulus K) :
    (rayElements m ⧸ rayOneElements m) ≃* ResidueSignTarget m := by
  haveI : (rayOneElements m).Normal :=
    residueSignMap_ker m ▸ (residueSignMap m).normal_ker
  exact (QuotientGroup.quotientMulEquivOfEq (residueSignMap_ker m).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residueSignMap_surjective m))

/-- **The residue-sign isomorphism on classes.** Let $m$ be a modulus of a number field $K$. For
every ray element $x$ of $m$, the residue-sign isomorphism of $m$ sends the class of $x$ in the
quotient of the ray elements of $m$ by the ray-one subgroup to the image of $x$ under the
residue-sign map of $m$. -/
@[simp] theorem rayElementsQuotientEquivResidueSign_mk (m : Modulus K)
    (x : rayElements m) :
    rayElementsQuotientEquivResidueSign m (QuotientGroup.mk x) =
      residueSignMap m x := by
  simp only [rayElementsQuotientEquivResidueSign, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  change QuotientGroup.kerLift (residueSignMap m) (QuotientGroup.mk x) = _
  rw [QuotientGroup.kerLift_mk]

end Modulus
end NumberField
