/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.RayGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Finite congruence, the finite ray-one subgroup, and admissible representatives (N406)

Source mapping (documentation only; no statement/proof changes):
* ATLAS source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1206-L2011),
  NumberTheoryI N406, Theorem 21.8, Section 21.3; the final declaration is
  [`RayClassField.theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
* Full source target: the ray-class exact sequence and canonical isomorphism
  `K^m / K^{m,1} ≃ {±1}^{#m∞} × (O_K / m₀)ˣ`. This file is only a finite-kernel
  prerequisite toward that target, not the full theorem.

Helper for ray-class congruence arguments: if `x + y ≠ 0` and both principal
fractional ideals `(x)`, `(y)` have `v`-adic count at least `n`, then so does
`(x + y)`. The nonzero cases go through the `v`-adic valuation and its
nonarchimedean inequality; the zero-summand cases are handled separately.

Main results:
* `rayElement_count_spanSingleton_eq_zero`: a member of `rayElements m` has
  principal fractional-ideal count zero at every finite prime supported by `m`.
* `rayElement_valuation_eq_one`: a ray element has valuation one at every finite
  prime supported by `m`.
* `mem_rayElements_of_valuation_eq_one`: converse valuation-one criterion —
  valuation one at every finite prime supported by `m` gives a ray element.
* `CongruentOneAtFinitePart.mul` / `.inv`: closure of the finite-part
  congruence under multiplication and inversion for ray elements.
* `finiteRayOneElements`: the subgroup of `rayElements m` cut out by the
  finite-part congruence.
* `exists_isUnit_mod_finitePart_div_eq`: every ray element is a quotient of
  two integers both coprime to the finite part of the modulus.
* `quotientUnits_div_eq_of_div_eq`: equal fraction values give equal
  finite-quotient units.
* `finiteResidueMap`: the finite-part residue homomorphism on ray elements.
* `finiteResidueMap_apply_of_div_eq`: computation API for `finiteResidueMap`
  from any admissible representative pair.
* `finiteResidueMap_eq_one_iff`: kernel of `finiteResidueMap` is the
  finite-part congruence.
* `finiteResidueMap_ker`: the kernel of `finiteResidueMap` equals
  `finiteRayOneElements`.
* `finiteResidueMap_eq_one_of_valuation_le`: valuation criterion for triviality
  of `finiteResidueMap` at every supported finite place.

Cumulative finite-kernel source map toward `RayClassField.theorem_21_8_quotient_iso`:
* PR #1035, `count_spanSingleton_add_ge_of_ne_zero`: principal-ideal-count
  counterpart of the finite-congruence multiplication step in
  `RayClassField.UnitsCongruent_subgroup'`; the source rewrites
  `ab - 1 = a * (b - 1) + (a - 1)` and applies `Valuation.map_add`, while the
  helper isolates preservation of a shared count bound under addition.
* PR #1039, `CongruentOneAtFinitePart.mul`, `.inv`, `finiteRayOneElements`:
  `rayElements m` corresponds to ambient `UnitsCoprime_subgroup' K 𝔪`, while
  `finiteRayOneElements m` packages exactly the finite congruence component of
  `UnitsCongruent_subgroup' K 𝔪`; the `mul`/`inv` proofs correspond to its
  finite-place `mul_mem'`/`inv_mem'` clauses, its separate infinite-place
  positivity clause lying outside this finite subgroup.
* PR #1043, `rayElement_valuation_eq_one`, `exists_isUnit_mod_finitePart_div_eq`:
  the former realizes the supported-place normalized-valuation-one property in
  ambient `UnitsCoprime_subgroup' K 𝔪` (compare
  `valuation_eq_one_of_spanSingleton_coprime'`); the latter is the native-API
  counterpart of `coprime_rep_exists`, writing a ray element as `a / b` with
  both integral images units modulo the finite part.
* PR #1046, `finiteResidueMap`, `finiteResidueMap_apply_of_div_eq`: native-API
  counterpart of `finitePartMapHom`; the computation theorem and its private
  implementation encode `coprime_rep_well_def`, namely independence of the
  admissible `a / b` and the value `a * b⁻¹` in quotient units.
* PR #1052, `finiteResidueMap_eq_one_iff`, `finiteResidueMap_ker`: native-API
  counterpart of `finitePartMapHom_ker_iff` and its subgroup-kernel packaging,
  identifying the kernel with `finiteRayOneElements` for the kernel computation
  used by `RayClassField.theorem_21_8_quotient_iso`.
* PR #1093, `mem_rayElements_of_valuation_eq_one`: converse bridge from
  normalized valuation one at every supported finite place to `rayElements m`
  membership; corresponds to the membership condition built into
  `UnitsCoprime_subgroup' K 𝔪`, used in `weak_approx_coprime_sign_finitePart`
  when its controlled approximation witness is packaged as an ambient coprime
  unit.
* PR #1107, `finiteResidueMap_eq_one_of_valuation_le`: the direct
  valuation-bound criterion for trivial finite residue, packaging the
  finite-place congruence implication used in the kernel calculation.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Private bridge: for `x ≠ 0`, the `v`-adic valuation is `exp (-count)`. -/
private theorem valuation_eq_exp_neg_count
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp
      (-FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ x
  have hr : r ≠ 0 := fun h => hx (by simp [h])
  have hs0 : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero s.property
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    v.intValuation_if_neg hr, v.intValuation_if_neg hs0, ← WithZero.exp_sub]
  congr 1
  have hI : FractionalIdeal.spanSingleton (𝓞 K)⁰
      (IsLocalization.mk' K r s) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hx
  have hrep : FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K r s)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) s)⁻¹ *
        ((Ideal.span {r} : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined K v hI hrep]
  ring

/-- **Lower bound for the exponent of a sum.** Let $K$ be a number field and $\mathfrak p$ a nonzero
prime ideal of $\mathcal O_K$. For $x \in K$ write $c_{\mathfrak p}(x)$ for the exponent of
$\mathfrak p$ in the principal fractional ideal $x \mathcal O_K$, with the convention
$c_{\mathfrak p}(0) = 0$. If $x, y \in K$ satisfy $x + y \neq 0$ and $n \in \mathbb Z$ satisfies
$n \le c_{\mathfrak p}(x)$ and $n \le c_{\mathfrak p}(y)$, then $n \le c_{\mathfrak p}(x + y)$.

Only $x + y \neq 0$ is assumed: $x$ or $y$ may be zero. -/
theorem count_spanSingleton_add_ge_of_ne_zero
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {x y : K} {n : ℤ} (hxy : x + y ≠ 0)
    (hx : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x))
    (hy : n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    n ≤ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x + y)) := by
  by_cases hxx : x = 0
  · subst hxx
    rw [zero_add] at hxy ⊢
    have h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (0 : K) = 0 :=
      FractionalIdeal.spanSingleton_zero
    rw [h0, FractionalIdeal.count_zero] at hx
    omega
  · by_cases hyy : y = 0
    · subst hyy
      rw [add_zero] at hxy ⊢
      have h0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (0 : K) = 0 :=
        FractionalIdeal.spanSingleton_zero
      rw [h0, FractionalIdeal.count_zero] at hy
      omega
    · have evx := valuation_eq_exp_neg_count v hxx
      have evy := valuation_eq_exp_neg_count v hyy
      have evxy := valuation_eq_exp_neg_count v hxy
      have hvx : v.valuation K x ≤ WithZero.exp (-n) := by
        rw [evx, WithZero.exp_le_exp]
        omega
      have hvy : v.valuation K y ≤ WithZero.exp (-n) := by
        rw [evy, WithZero.exp_le_exp]
        omega
      have hadd := Valuation.map_add (v.valuation K) x y
      have hle : v.valuation K (x + y) ≤ WithZero.exp (-n) :=
        le_trans hadd (max_le hvx hvy)
      rw [evxy, WithZero.exp_le_exp] at hle
      omega

/-- **Ray elements have order zero at the primes dividing the modulus.** Let $m$ be a
modulus of a number field $K$ and let $x \in K^\times$ be a ray element of $m$. Then for
every finite prime $\mathfrak p$ of $K$ dividing the finite part of $m$, the exponent of
$\mathfrak p$ in the principal fractional ideal $x \mathcal O_K$ is $0$. -/
theorem rayElement_count_spanSingleton_eq_zero
    (m : Modulus K) (x : Kˣ)
    (hx : x ∈ rayElements m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
  have h := (mem_rayElements_iff m x).mp hx
  rw [mem_coprimeFractionalIdeals_iff] at h
  have h0 := h v hv
  rwa [coe_toPrincipalIdeal] at h0

/-- **Ray elements have valuation one at the primes dividing the modulus.** Let $m$ be a
modulus of a number field $K$ and let $x \in K^\times$ be a ray element of $m$. Then for
every finite prime $\mathfrak p$ of $K$ dividing the finite part of $m$, the multiplicative
$\mathfrak p$-adic valuation of $x$ equals $1$.

Source: N406 §21.3, the supported-finite-place fact; compare
[`valuation_eq_one_of_spanSingleton_coprime'`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1206-L1248)
and `hx_coprime`. -/
theorem rayElement_valuation_eq_one
    (m : Modulus K) (x : rayElements m)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    v.valuation K (((x : Kˣ) : K)) = 1 := by
  rw [valuation_eq_exp_neg_count v (Units.ne_zero (x : Kˣ)),
    rayElement_count_spanSingleton_eq_zero m (x : Kˣ) x.property v hv,
    neg_zero, WithZero.exp_zero]

/-- **Elements of valuation one at the primes dividing a modulus are ray elements.** Let $K$ be a
number field, $\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, and
$a \in K^\times$. If the multiplicative $\mathfrak p$-adic valuation of $a$ equals $1$ at every
nonzero prime ideal $\mathfrak p$ of $\mathcal O_K$ containing $\mathfrak m_0$, then $a$ is
coprime to $\mathfrak m$, that is, a ray element of $\mathfrak m$: its principal fractional ideal
$(a)$ has exponent $0$ at every such $\mathfrak p$.

Source: N406 Section 21.3. This is the converse of `rayElement_valuation_eq_one`, the converse
valuation criterion used to turn the controlled approximation witness into a ray element; it is
a reusable bridge toward N406, not itself the full source theorem. -/
theorem mem_rayElements_of_valuation_eq_one
    (m : Modulus K) (a : Kˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v → v.valuation K ((a : K)) = 1) :
    a ∈ rayElements m := by
  rw [mem_rayElements_iff, mem_coprimeFractionalIdeals_iff]
  intro v hv
  rw [coe_toPrincipalIdeal]
  have hne : (a : K) ≠ 0 := Units.ne_zero a
  have hev := valuation_eq_exp_neg_count v hne
  have hval := h v hv
  rw [hev, ← WithZero.exp_zero] at hval
  have hcount := WithZero.exp_inj.mp hval
  omega

/-- **Product of two elements congruent to one at the finite part.** Let $m$ be a modulus
of a number field $K$ and let $x, y \in K^\times$ both be congruent to $1$ at the finite
part of $m$. If moreover $x$ is a ray element of $m$, then $xy$ is congruent to $1$ at the
finite part of $m$. -/
theorem CongruentOneAtFinitePart.mul
    {m : Modulus K} {x y : Kˣ}
    (hx : CongruentOneAtFinitePart m x)
    (hy : CongruentOneAtFinitePart m y)
    (hmem : x ∈ rayElements m) :
    CongruentOneAtFinitePart m (x * y) := by
  intro v hv
  by_cases hxy : ((x * y : Kˣ) : K) = 1
  · exact Or.inl hxy
  · by_cases hxx : (x : K) = 1
    · have hval : ((x * y : Kˣ) : K) = (y : K) := by
        simp [Units.val_mul, hxx]
      have hsub : ((x * y : Kˣ) : K) - 1 = (y : K) - 1 := by rw [hval]
      rcases hy v hv with h | h
      · exact Or.inl (by rw [hval, h])
      · exact Or.inr (by rwa [hsub])
    · by_cases hyy : (y : K) = 1
      · have hval : ((x * y : Kˣ) : K) = (x : K) := by
          simp [Units.val_mul, hyy]
        have hsub : ((x * y : Kˣ) : K) - 1 = (x : K) - 1 := by rw [hval]
        rcases hx v hv with h | h
        · exact absurd h hxx
        · exact Or.inr (by rwa [hsub])
      · rcases hx v hv with h | hbx
        · exact absurd h hxx
        · rcases hy v hv with h | hby
          · exact absurd h hyy
          · have hcx := rayElement_count_spanSingleton_eq_zero
              m x hmem v hv
            have hsuby : (y : K) - 1 ≠ 0 := sub_ne_zero.mpr hyy
            have hIx : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) ≠ 0 := by
              rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
              exact Units.ne_zero x
            have hIy : FractionalIdeal.spanSingleton (𝓞 K)⁰
                ((y : K) - 1) ≠ 0 := by
              rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
              exact hsuby
            have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰
                ((x : K) * ((y : K) - 1)) =
                FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) *
                  FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : K) - 1) :=
              (FractionalIdeal.spanSingleton_mul_spanSingleton _ _).symm
            have hcmul : FractionalIdeal.count K v
                (FractionalIdeal.spanSingleton (𝓞 K)⁰
                  ((x : K) * ((y : K) - 1))) =
                FractionalIdeal.count K v
                  (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) +
                FractionalIdeal.count K v
                  (FractionalIdeal.spanSingleton (𝓞 K)⁰ ((y : K) - 1)) := by
              rw [hmul, FractionalIdeal.count_mul K v hIx hIy]
            have hbmul : finiteExponent m v ≤ FractionalIdeal.count K v
                (FractionalIdeal.spanSingleton (𝓞 K)⁰
                  ((x : K) * ((y : K) - 1))) := by
              rw [hcmul, hcx, zero_add]
              exact hby
            have hid : (x : K) * ((y : K) - 1) + ((x : K) - 1) =
                ((x * y : Kˣ) : K) - 1 := by
              simp only [Units.val_mul]
              ring
            have hsum : (x : K) * ((y : K) - 1) + ((x : K) - 1) ≠ 0 := by
              rw [hid]
              exact sub_ne_zero.mpr hxy
            have hfin := count_spanSingleton_add_ge_of_ne_zero
              v hsum hbmul hbx
            rw [hid] at hfin
            exact Or.inr hfin

/-- **Inverses preserve congruence to one at the finite part.** Let $K$ be a number field and
$\mathfrak m$ a modulus of $K$. If a ray element $x$ of $\mathfrak m$ is congruent to $1$ at the
finite part of $\mathfrak m$, then so is $x^{-1}$. -/
theorem CongruentOneAtFinitePart.inv
    {m : Modulus K} {x : Kˣ}
    (hx : CongruentOneAtFinitePart m x)
    (hmem : x ∈ rayElements m) :
    CongruentOneAtFinitePart m x⁻¹ := by
  intro v hv
  by_cases hinv : ((x⁻¹ : Kˣ) : K) = 1
  · exact Or.inl hinv
  · by_cases hxx : (x : K) = 1
    · exfalso
      exact hinv (by simp [Units.val_inv_eq_inv_val, hxx])
    · rcases hx v hv with h | hbx
      · exact absurd h hxx
      · have hcx := rayElement_count_spanSingleton_eq_zero
          m x hmem v hv
        have hsub : (x : K) - 1 ≠ 0 := sub_ne_zero.mpr hxx
        have hsubinv : ((x⁻¹ : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hinv
        have hxne : (x : K) ≠ 0 := Units.ne_zero x
        have hI1 : FractionalIdeal.spanSingleton (𝓞 K)⁰
            (((x⁻¹ : Kˣ) : K) - 1) ≠ 0 := by
          rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact hsubinv
        have hIx : FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) ≠ 0 := by
          rw [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
          exact hxne
        have hid : (((x⁻¹ : Kˣ) : K) - 1) * (x : K) = -((x : K) - 1) := by
          rw [Units.val_inv_eq_inv_val]
          field_simp
          ring
        have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰
            (((x⁻¹ : Kˣ) : K) - 1) *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (-((x : K) - 1)) := by
          rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hid]
        have hcmul : FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton (𝓞 K)⁰ (-((x : K) - 1))) =
            FractionalIdeal.count K v
              (FractionalIdeal.spanSingleton (𝓞 K)⁰
                (((x⁻¹ : Kˣ) : K) - 1)) +
            FractionalIdeal.count K v
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) := by
          rw [← hmul, FractionalIdeal.count_mul K v hI1 hIx]
        have hneg : FractionalIdeal.spanSingleton (𝓞 K)⁰ (-((x : K) - 1)) =
            FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) - 1) := by
          apply le_antisymm
          · rw [FractionalIdeal.spanSingleton_le_iff_mem,
              FractionalIdeal.mem_spanSingleton]
            exact ⟨-1, by simp⟩
          · rw [FractionalIdeal.spanSingleton_le_iff_mem,
              FractionalIdeal.mem_spanSingleton]
            exact ⟨-1, by simp⟩
        rw [hneg, hcx, add_zero] at hcmul
        exact Or.inr (by omega)

/-- **The finite ray-one subgroup.** Let $K$ be a number field and $\mathfrak m$ a modulus of $K$
with finite part $\mathfrak m_0$. The finite ray-one subgroup of $\mathfrak m$ is the subgroup of
the group of ray elements of $\mathfrak m$ consisting of the $x$ that are congruent to $1$ at the
finite part of $\mathfrak m$: for every nonzero prime $\mathfrak p$ of $\mathcal O_K$ containing
$\mathfrak m_0$, either $x = 1$ or the exponent of $\mathfrak p$ in $(x - 1) \mathcal O_K$ is at
least the exponent of $\mathfrak p$ in $\mathfrak m_0$. -/
def finiteRayOneElements (m : Modulus K) : Subgroup (rayElements m) where
  carrier := { x | CongruentOneAtFinitePart m (x : Kˣ) }
  one_mem' := by
    simpa using congruentOneAtFinitePart_one m
  mul_mem' := by
    intro a b ha hb
    change CongruentOneAtFinitePart m ((a * b : rayElements m) : Kˣ)
    rw [Subgroup.coe_mul]
    exact CongruentOneAtFinitePart.mul ha hb a.property
  inv_mem' := by
    intro a ha
    change CongruentOneAtFinitePart m ((a⁻¹ : rayElements m) : Kˣ)
    rw [Subgroup.coe_inv]
    exact CongruentOneAtFinitePart.inv ha a.property

@[simp] theorem mem_finiteRayOneElements_iff (m : Modulus K)
    (x : rayElements m) :
    x ∈ finiteRayOneElements m ↔ CongruentOneAtFinitePart m (x : Kˣ) :=
  Iff.rfl

/-- **Coprime representation of ray elements.** Let $K$ be a number field and $\mathfrak m$ a
modulus of $K$ with finite part $\mathfrak m_0$, a nonzero ideal of $\mathcal O_K$. Every ray
element $x$ of $\mathfrak m$ can be written as $x = a / b$ in $K$ with $a, b \in \mathcal O_K$
whose residue classes are units of $\mathcal O_K / \mathfrak m_0$.

Source (N406 §21.3): the
[`coprime_rep_exists`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1553-L1747)
admissible integral numerator/denominator representation with both residues units. -/
theorem exists_isUnit_mod_finitePart_div_eq
    (m : Modulus K) (x : rayElements m) :
    ∃ a b : 𝓞 K,
      IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a) ∧
      IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b) ∧
      algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = ((x : Kˣ) : K) := by
  classical
  by_cases htriv : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))
  · obtain ⟨a₀, b₀, _, hab₀⟩ :=
        IsFractionRing.div_surjective (𝓞 K) ((x : Kˣ) : K)
    let _ : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    exact ⟨a₀, b₀, isUnit_of_subsingleton _, isUnit_of_subsingleton _,
      by rw [← hab₀]⟩
  · rw [not_subsingleton_iff_nontrivial] at htriv
    let _ : Nontrivial (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    obtain ⟨a₀, b₀, hb₀_mem, hab₀⟩ :=
      IsFractionRing.div_surjective (𝓞 K) ((x : Kˣ) : K)
    have hα_ne : ((x : Kˣ) : K) ≠ 0 := Units.ne_zero (x : Kˣ)
    have hα_val : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v → v.valuation K ((x : Kˣ) : K) = 1 :=
      fun v hv => rayElement_valuation_eq_one m x v hv
    have hI : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
    set S := (Ideal.finite_factors hI).toFinset with hS_def
    have hS_mem : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        v ∈ S ↔ (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal := by
      intro v
      rw [hS_def, Set.Finite.mem_toFinset]
      exact Ideal.dvd_iff_le
    let J : Ideal (𝓞 K) :=
      { carrier := {b | IsLocalization.IsInteger (𝓞 K)
          (algebraMap (𝓞 K) K b * ((x : Kˣ) : K))}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, IsLocalization.IsInteger, map_add,
            add_mul] at *
          obtain ⟨ca, hca⟩ := ha
          obtain ⟨cb, hcb⟩ := hb
          exact ⟨ca + cb, by rw [map_add, hca, hcb]⟩
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, map_zero, zero_mul]
          exact ⟨0, map_zero _⟩
        smul_mem' := fun c {b} hb => by
          simp only [Set.mem_ofPred_eq, IsLocalization.IsInteger, smul_eq_mul,
            map_mul, mul_assoc] at *
          obtain ⟨cb, hcb⟩ := hb
          exact ⟨c * cb, by rw [map_mul, hcb]⟩ }
    have hb₀_in_J : b₀ ∈ J := by
      change IsLocalization.IsInteger _ _
      rw [← hab₀, mul_div_cancel₀]
      · exact ⟨a₀, rfl⟩
      · exact map_ne_zero_of_mem_nonZeroDivisors _
          (IsFractionRing.injective (𝓞 K) K) hb₀_mem
    have hJ_ne_bot : J ≠ ⊥ := by
      intro h
      have hmem : b₀ ∈ (⊥ : Ideal (𝓞 K)) := h ▸ hb₀_in_J
      rw [Ideal.mem_bot] at hmem
      exact hα_ne (by rw [← hab₀]; simp [hmem])
    have hJ_not_le : ∀ v ∈ S, ¬(J ≤ v.asIdeal) := by
      intro v hv hle
      have hv_supp : finiteSupported m v := (hS_mem v).mp hv
      have hv_ne_top : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
      obtain ⟨c, hc_int, i, hi_mem, hc_notmem⟩ :=
        Ideal.exist_integer_multiples_notMem (K := K) hv_ne_top
          ({0, 1} : Finset (Fin 2))
          (fun i => if i = 0 then ((x : Kˣ) : K) else 1)
          (j := 1) (by simp) (by simp)
      have hc_is_int : IsLocalization.IsInteger (𝓞 K) c := by
        have h1 := hc_int 1 (by simp)
        simpa using h1
      have hcα_is_int : IsLocalization.IsInteger (𝓞 K)
          (c * ((x : Kˣ) : K)) := by
        have h0 := hc_int 0 (by simp)
        simpa using h0
      obtain ⟨b_int, hb_int⟩ := hc_is_int
      have hb_int_in_J : b_int ∈ J := by
        change IsLocalization.IsInteger _ _
        rw [hb_int]
        exact hcα_is_int
      have hb_int_mem : b_int ∈ v.asIdeal := hle hb_int_in_J
      have hv_c_ne1 : v.valuation K c ≠ 1 := by
        rw [← hb_int,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        rw [Ne, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        exact not_not.mpr hb_int_mem
      have hv_α_eq1 : v.valuation K ((x : Kˣ) : K) = 1 :=
        hα_val v hv_supp
      have hv_cα_ne1 : v.valuation K (c * ((x : Kˣ) : K)) ≠ 1 := by
        rw [map_mul, hv_α_eq1, mul_one]
        exact hv_c_ne1
      obtain ⟨a_int, ha_int⟩ := hcα_is_int
      have ha_int_mem : a_int ∈ v.asIdeal := by
        rw [← not_not (a := a_int ∈ v.asIdeal)]
        rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
        intro h_eq
        exact hv_cα_ne1 (by
          rw [← ha_int,
            IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
            h_eq])
      rcases i with ⟨i, hi⟩
      interval_cases i
      · simp only [Fin.mk_zero] at hc_notmem
        simp only [ite_true] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr
          ⟨a_int, ha_int_mem, ha_int⟩)
      · simp only [Fin.mk_one, one_ne_zero, ite_false, mul_one] at hc_notmem
        exact hc_notmem ((FractionalIdeal.mem_coeIdeal _).mpr
          ⟨b_int, hb_int_mem, hb_int⟩)
    have ⟨b, hb_in_J, hb_avoid⟩ : ∃ b ∈ J, ∀ v ∈ S, b ∉ v.asIdeal := by
      by_contra h
      push Not at h
      rcases S.eq_empty_or_nonempty with hS_empty | ⟨v₀, hv₀⟩
      · obtain ⟨v, hv, _⟩ := h b₀ hb₀_in_J
        rw [hS_empty] at hv
        exact (Finset.notMem_empty v hv).elim
      · have hsub : (J : Set (𝓞 K)) ⊆
            ⋃ v ∈ (↑S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))),
              (v.asIdeal : Set _) := by
          intro y hy
          obtain ⟨v, hv, hvx⟩ := h y hy
          exact Set.mem_biUnion (Finset.mem_coe.mpr hv) hvx
        rw [Ideal.subset_union_prime_finite S.finite_toSet v₀ v₀
          (fun i _ _ _ => i.isPrime)] at hsub
        obtain ⟨i, hi, hle⟩ := hsub
        exact hJ_not_le i (Finset.mem_coe.mp hi) hle
    obtain ⟨a, ha_eq⟩ : IsLocalization.IsInteger (𝓞 K)
        (algebraMap (𝓞 K) K b * ((x : Kˣ) : K)) := hb_in_J
    have ha_avoid : ∀ v ∈ S, a ∉ v.asIdeal := by
      intro v hv ha_mem
      have hb_mem_or : b ∈ v.asIdeal := by
        by_contra hb_not_mem
        have hv_b : v.intValuation b = 1 :=
          IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
            hb_not_mem
        have hv_a : v.intValuation a ≠ 1 :=
          (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.not.mpr
            (not_not.mpr ha_mem))
        have hmul : v.valuation K (algebraMap _ K a) =
            v.valuation K (algebraMap _ K b) *
              v.valuation K ((x : Kˣ) : K) := by
          rw [ha_eq, map_mul]
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          hv_b, hα_val v ((hS_mem v).mp hv), mul_one] at hmul
        exact hv_a hmul
      exact hb_avoid v hv hb_mem_or
    have isUnit_of_avoid : ∀ r : 𝓞 K, (∀ v ∈ S, r ∉ v.asIdeal) →
        IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r) := by
      intro r hr
      have hsup : Ideal.span {r} ⊔ (m.finitePart : Ideal (𝓞 K)) = ⊤ := by
        by_contra hne
        obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hne
        have hIM : (m.finitePart : Ideal (𝓞 K)) ≤ M :=
          le_trans le_sup_right hle
        have hMbot : M ≠ ⊥ := by
          intro hM
          rw [hM] at hIM
          exact hI (le_antisymm hIM bot_le)
        let P : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
          IsDedekindDomain.HeightOneSpectrum.ofPrime
            (Ideal.prime_of_isPrime hMbot hMmax.isPrime)
        have hrM : r ∈ M :=
          hle (Submodule.mem_sup_left (Ideal.mem_span_singleton_self r))
        have hPmem : P ∈ S := (hS_mem P).mpr hIM
        exact hr P hPmem hrM
      rw [Ideal.eq_top_iff_one] at hsup
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hsup
      obtain ⟨c, hc⟩ := (Ideal.mem_span_singleton).mp hx
      have key : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) r *
          Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c = 1 := by
        have h3 : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K))
            (r * c + y) = 1 := by
          rw [← hc, hxy]
          simp
        simpa only [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hy, add_zero,
          map_mul] using h3
      exact IsUnit.of_mul_eq_one _ key
    refine ⟨a, b, isUnit_of_avoid a ha_avoid, isUnit_of_avoid b hb_avoid, ?_⟩
    have hb_ne : algebraMap (𝓞 K) K b ≠ 0 := by
      intro h
      have hb0 : b = 0 :=
        IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero])
      have h0 : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b = 0 := by
        rw [hb0, map_zero]
      exact (isUnit_of_avoid b hb_avoid).ne_zero h0
    rw [ha_eq]
    exact mul_div_cancel_left₀ _ hb_ne

/-- **Equal fractions give equal residues modulo the finite part.** Let $m$ be a modulus
of a number field $K$ with finite part $\mathfrak m_0$, an ideal of $\mathcal O_K$, and
write $\bar x$ for the image of $x \in \mathcal O_K$ in $\mathcal O_K / \mathfrak m_0$.
Let $a, b, c, d \in \mathcal O_K$ be such that $\bar a$, $\bar b$, $\bar c$ and $\bar d$
are units. If $a / b = c / d$ in $K$, then $\bar a \bar b^{-1} = \bar c \bar d^{-1}$ in
the unit group $(\mathcal O_K / \mathfrak m_0)^\times$. -/
theorem quotientUnits_div_eq_of_div_eq
    (m : Modulus K) (a b c d : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hc : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c))
    (hd : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) d))
    (h : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      algebraMap (𝓞 K) K c / algebraMap (𝓞 K) K d) :
    ha.unit * hb.unit⁻¹ = hc.unit * hd.unit⁻¹ := by
  classical
  by_cases htriv : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))
  · let _ : Subsingleton (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    exact Subsingleton.elim _ _
  · rw [not_subsingleton_iff_nontrivial] at htriv
    let _ : Nontrivial (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K))) := htriv
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
      intro h0
      have hb0 : b = 0 :=
        IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
      exact hb.ne_zero (by rw [hb0, map_zero])
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      have hd0 : d = 0 :=
        IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
      exact hd.ne_zero (by rw [hd0, map_zero])
    have hcross := (div_eq_div_iff hbK hdK).mp h
    have had : a * d = b * c :=
      IsFractionRing.injective (𝓞 K) K (by simp [map_mul, hcross, mul_comm])
    have hmk : Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a *
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) d =
        Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b *
          Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) c := by
      rw [← map_mul, ← map_mul, had]
    have hu : ha.unit * hd.unit = hc.unit * hb.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec]
      exact hmk.trans (mul_comm _ _)
    have h2 := congrArg (fun u => u * hb.unit⁻¹ * hd.unit⁻¹) hu
    simpa [mul_comm, mul_assoc, mul_left_comm] using h2

private noncomputable def finiteResidueMapFn (m : Modulus K)
    (x : rayElements m) : (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))ˣ :=
  let e := exists_isUnit_mod_finitePart_div_eq m x
  let _a := Classical.choose e
  let h := Classical.choose_spec e
  let _b := Classical.choose h
  let hb := Classical.choose_spec h
  hb.1.unit * hb.2.1.unit⁻¹

private theorem finiteResidueMapFn_eq_of_div_eq
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K)) :
    finiteResidueMapFn m x = ha.unit * hb.unit⁻¹ := by
  have hs := Classical.choose_spec
    (Classical.choose_spec (exists_isUnit_mod_finitePart_div_eq m x))
  have hfn : finiteResidueMapFn m x = hs.1.unit * hs.2.1.unit⁻¹ := rfl
  rw [hfn]
  exact quotientUnits_div_eq_of_div_eq m _ _ a b hs.1 hs.2.1 ha hb
    (hs.2.2.trans hab.symm)

/-- **Finite residue map.** Let $K$ be a number field and $\mathfrak m$ a modulus of $K$ with finite
part $\mathfrak m_0$, a nonzero ideal of $\mathcal O_K$. The finite residue map of $\mathfrak m$ is
the group homomorphism from the ray elements of $\mathfrak m$ to
$(\mathcal O_K / \mathfrak m_0)^\times$ sending $x$ to $\bar a \bar b^{-1}$, where $x = a / b$ with
$a, b \in \mathcal O_K$ whose residue classes $\bar a, \bar b$ are units of
$\mathcal O_K / \mathfrak m_0$; such $a$ and $b$ exist, and the value does not depend on their
choice.

Source (N406 §21.3): the
[`finitePartMapHom`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1812-L1864)
finite component of the quotient isomorphism. -/
noncomputable def finiteResidueMap (m : Modulus K) :
    rayElements m →* (𝓞 K ⧸ (m.finitePart : Ideal (𝓞 K)))ˣ where
  toFun := finiteResidueMapFn m
  map_one' := by
    have h := finiteResidueMapFn_eq_of_div_eq m 1 1 1 isUnit_one isUnit_one
      (by simp)
    simpa using h
  map_mul' := fun x y => by
    obtain ⟨a1, b1, ha1, hb1, r1⟩ := exists_isUnit_mod_finitePart_div_eq m x
    obtain ⟨a2, b2, ha2, hb2, r2⟩ := exists_isUnit_mod_finitePart_div_eq m y
    have h12a : IsUnit
        (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) (a1 * a2)) := by
      rw [map_mul]
      exact IsUnit.mul ha1 ha2
    have h12b : IsUnit
        (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) (b1 * b2)) := by
      rw [map_mul]
      exact IsUnit.mul hb1 hb2
    have hfrac : algebraMap (𝓞 K) K (a1 * a2) / algebraMap (𝓞 K) K (b1 * b2) =
        (((x * y : rayElements m) : Kˣ) : K) := by
      rw [map_mul, map_mul, ← div_mul_div_comm, r1, r2, Subgroup.coe_mul,
        Units.val_mul]
    have hx := finiteResidueMapFn_eq_of_div_eq m x a1 b1 ha1 hb1 r1
    have hy := finiteResidueMapFn_eq_of_div_eq m y a2 b2 ha2 hb2 r2
    have hxy := finiteResidueMapFn_eq_of_div_eq m (x * y) (a1 * a2) (b1 * b2)
      h12a h12b hfrac
    have hu1 : h12a.unit = ha1.unit * ha2.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    have hu2 : h12b.unit = hb1.unit * hb2.unit := by
      apply Units.ext
      simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    change finiteResidueMapFn m (x * y) =
      finiteResidueMapFn m x * finiteResidueMapFn m y
    rw [hx, hy, hxy, hu1, hu2]
    simp [mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

/-- **Computing the finite residue map from a representation.** Let $K$ be a number field and
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$. Let $x$ be a ray element of
$\mathfrak m$, and let $a, b \in \mathcal O_K$ have residue classes $\bar a, \bar b$ that are
units of $\mathcal O_K / \mathfrak m_0$ and satisfy $a / b = x$ in $K$. Then the finite residue
map of $\mathfrak m$ sends $x$ to $\bar a \bar b^{-1}$ in $(\mathcal O_K / \mathfrak m_0)^\times$.

Source (N406 §21.3): the representation-independence computation
[`coprime_rep_well_def`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1757-L1810)
for the finite component. -/
theorem finiteResidueMap_apply_of_div_eq
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K)) :
    finiteResidueMap m x = ha.unit * hb.unit⁻¹ :=
  finiteResidueMapFn_eq_of_div_eq m x a b ha hb hab

private theorem not_mem_of_isUnit_quotient_mk
    {R : Type*} [CommRing R] {I p : Ideal R} (hIp : I ≤ p)
    (hp : p ≠ ⊤) {b : R}
    (hb : IsUnit (Ideal.Quotient.mk I b)) : b ∉ p := by
  have H : ∀ a : R, a ∈ I → Ideal.Quotient.mk p a = 0 :=
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hIp ha)
  have hunit : IsUnit (Ideal.Quotient.lift I (Ideal.Quotient.mk p) H
      (Ideal.Quotient.mk I b)) := hb.map _
  rw [Ideal.Quotient.lift_mk] at hunit
  intro hmem
  have hzero : Ideal.Quotient.mk p b = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hzero] at hunit
  let _ : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp
  exact not_isUnit_zero hunit

private theorem finiteExponent_eq_count_normalizedFactors
    (m : Modulus K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    finiteExponent m v =
      ((UniqueFactorizationMonoid.normalizedFactors
          (m.finitePart : Ideal (𝓞 K))).count v.asIdeal : ℤ) := by
  have hne : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
  unfold finiteExponent
  rw [FractionalIdeal.count_coe,
    Ideal.count_associates_factors_eq hne v.isPrime v.ne_bot]
  exact hne

private theorem mem_finitePart_iff_forall_primePow_mem
    (m : Modulus K) (r : 𝓞 K) :
    r ∈ (m.finitePart : Ideal (𝓞 K)) ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        finiteSupported m v →
          r ∈ v.asIdeal ^
            (UniqueFactorizationMonoid.normalizedFactors
              (m.finitePart : Ideal (𝓞 K))).count v.asIdeal := by
  have hI : (m.finitePart : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp m.finitePart.property
  conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hI]
  rw [Ideal.mem_iInf]
  constructor
  · intro h v hv
    have hv' := h v
    rwa [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
      v hI] at hv'
  · intro h v
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
      v hI]
    by_cases hv : finiteSupported m v
    · exact h v hv
    · have hcount : (UniqueFactorizationMonoid.normalizedFactors
          (m.finitePart : Ideal (𝓞 K))).count v.asIdeal = 0 := by
        apply Multiset.count_eq_zero.mpr
        intro hmem
        have hdvd : v.asIdeal ∣ (m.finitePart : Ideal (𝓞 K)) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
        have hle : (m.finitePart : Ideal (𝓞 K)) ≤ v.asIdeal :=
          Ideal.dvd_iff_le.mp hdvd
        exact hv hle
      simp only [hcount, pow_zero, Ideal.one_eq_top, Submodule.mem_top]

private theorem quotientUnits_div_eq_one_iff_sub_mem
    (m : Modulus K) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b)) :
    ha.unit * hb.unit⁻¹ = 1 ↔ a - b ∈ (m.finitePart : Ideal (𝓞 K)) := by
  rw [mul_inv_eq_one]
  constructor
  · intro h
    have hval := congrArg Units.val h
    simp only [IsUnit.unit_spec] at hval
    exact Ideal.Quotient.eq.mp hval
  · intro h
    apply Units.ext
    simp only [IsUnit.unit_spec]
    exact Ideal.Quotient.eq.mpr h

private theorem valuation_sub_one_eq_intValuation_sub
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : finiteSupported m v) :
    v.valuation K (((x : Kˣ) : K) - 1) = v.intValuation (a - b) := by
  have hbNotMem : b ∉ v.asIdeal :=
    not_mem_of_isUnit_quotient_mk hv v.isPrime.ne_top hb
  have hintB : v.intValuation b = 1 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hbNotMem
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
    intro h0
    have hb0 : b = 0 :=
      IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
    exact hbNotMem (by rw [hb0]; exact Submodule.zero_mem _)
  have hfrac : ((x : Kˣ) : K) - 1 =
      algebraMap (𝓞 K) K (a - b) / algebraMap (𝓞 K) K b := by
    rw [← hab, map_sub]
    field_simp
  rw [hfrac, Valuation.map_div,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hintB,
    div_one]

private theorem quotientUnits_div_eq_one_iff_congruent
    (m : Modulus K) (x : rayElements m) (a b : 𝓞 K)
    (ha : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) a))
    (hb : IsUnit (Ideal.Quotient.mk (m.finitePart : Ideal (𝓞 K)) b))
    (hab : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b =
      ((x : Kˣ) : K)) :
    ha.unit * hb.unit⁻¹ = 1 ↔ CongruentOneAtFinitePart m (x : Kˣ) := by
  rw [quotientUnits_div_eq_one_iff_sub_mem m a b ha hb,
    mem_finitePart_iff_forall_primePow_mem m (a - b)]
  constructor
  · intro h v hv
    by_cases hx : ((x : Kˣ) : K) = 1
    · exact Or.inl hx
    · refine Or.inr ?_
      have hmem := h v hv
      set n := (UniqueFactorizationMonoid.normalizedFactors
        (m.finitePart : Ideal (𝓞 K))).count v.asIdeal with hn
      have hle : v.intValuation (a - b) ≤ WithZero.exp (-(n : ℤ)) :=
        (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
          v (a - b) n).mpr hmem
      have hval := valuation_sub_one_eq_intValuation_sub m x a b hb hab v hv
      have hne : ((x : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hx
      have hexp := valuation_eq_exp_neg_count v hne
      rw [← hval] at hle
      rw [hexp, WithZero.exp_le_exp] at hle
      have hfe := finiteExponent_eq_count_normalizedFactors m v
      rw [← hn] at hfe
      omega
  · intro h v hv
    set n := (UniqueFactorizationMonoid.normalizedFactors
      (m.finitePart : Ideal (𝓞 K))).count v.asIdeal with hn
    by_cases hx : ((x : Kˣ) : K) = 1
    · have hbNotMem : b ∉ v.asIdeal :=
        not_mem_of_isUnit_quotient_mk hv v.isPrime.ne_top hb
      have hbK : algebraMap (𝓞 K) K b ≠ 0 := by
        intro h0
        have hb0 : b = 0 :=
          IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
        exact hbNotMem (by rw [hb0]; exact Submodule.zero_mem _)
      have h1 : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b = 1 := by
        rw [hab, hx]
      have hab1 : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b :=
        (div_eq_one_iff_eq hbK).mp h1
      have hab0 : a - b = 0 := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_sub, hab1, sub_self, map_zero]
      rw [hab0]
      exact Submodule.zero_mem _
    · have hle := (h v hv).resolve_left hx
      have hne : ((x : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr hx
      have hexp := valuation_eq_exp_neg_count v hne
      have hval := valuation_sub_one_eq_intValuation_sub m x a b hb hab v hv
      have hfe := finiteExponent_eq_count_normalizedFactors m v
      rw [← hn] at hfe
      have hcount : -(FractionalIdeal.count K v
          (FractionalIdeal.spanSingleton (𝓞 K)⁰
            (((x : Kˣ) : K) - 1))) ≤ -((n : ℕ) : ℤ) := by
        omega
      have hle' : v.valuation K (((x : Kˣ) : K) - 1) ≤
          WithZero.exp (-((n : ℕ) : ℤ)) := by
        rw [hexp, WithZero.exp_le_exp]
        exact hcount
      rw [hval] at hle'
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem
        v (a - b) n).mp hle'

/-- **Kernel criterion for the finite residue map.** Let $K$ be a number field and $\mathfrak m$ a
modulus of $K$. A ray element $x$ of $\mathfrak m$ is sent to $1$ by the finite residue map of
$\mathfrak m$ if and only if $x$ is congruent to $1$ at the finite part of $\mathfrak m$.

Source (N406 §21.3): helper
[`finitePartMapHom_ker_iff`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1996-L2011). -/
theorem finiteResidueMap_eq_one_iff (m : Modulus K) (x : rayElements m) :
    finiteResidueMap m x = 1 ↔ CongruentOneAtFinitePart m (x : Kˣ) := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_isUnit_mod_finitePart_div_eq m x
  rw [finiteResidueMap_apply_of_div_eq m x a b ha hb hab]
  exact quotientUnits_div_eq_one_iff_congruent m x a b ha hb hab

/-- **Kernel of the finite residue map.** Let $K$ be a number field and $\mathfrak m$ a modulus of
$K$. The kernel of the finite residue map of $\mathfrak m$ is the finite ray-one subgroup of
$\mathfrak m$.

Source (N406 §21.3): the finite kernel component used in the
[`theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2600-L2647). -/
theorem finiteResidueMap_ker (m : Modulus K) :
    (finiteResidueMap m).ker = finiteRayOneElements m := by
  ext x
  simp only [MonoidHom.mem_ker, mem_finiteRayOneElements_iff,
    finiteResidueMap_eq_one_iff]

/-- **Valuation criterion for the finite residue map to be trivial.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, and $z$ a ray element of
$\mathfrak m$. Suppose that at every nonzero prime ideal $\mathfrak p$ of $\mathcal O_K$
containing $\mathfrak m_0$, the multiplicative $\mathfrak p$-adic valuation of $z - 1$ is at most
$\exp(-e_{\mathfrak p})$, where $e_{\mathfrak p}$ is the exponent of $\mathfrak p$ in
$\mathfrak m_0$; equivalently, $z = 1$ or $z - 1$ has $\mathfrak p$-adic order at least
$e_{\mathfrak p}$. Then the finite residue map of $\mathfrak m$ sends $z$ to $1$ in
$(\mathcal O_K / \mathfrak m_0)^\times$.

Source: N406, Theorem 21.8, Section 21.3 (ATLAS NumberTheoryI item N406): the native-API
finite-congruence step corresponding to
[`finitePartMapHom_ker_iff`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1996-L2011),
used by the weak-approximation argument before residue/sign surjectivity and by
[`theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
It is not the generalized weak-approximation theorem and not the final N406
result. -/
theorem finiteResidueMap_eq_one_of_valuation_le
    (m : Modulus K) (z : rayElements m)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      finiteSupported m v →
        v.valuation K (((z : Kˣ) : K) - 1) ≤
          WithZero.exp (-(finiteExponent m v))) :
    finiteResidueMap m z = 1 := by
  rw [finiteResidueMap_eq_one_iff]
  intro v hv
  by_cases hx : (((z : Kˣ) : K)) = 1
  · exact Or.inl hx
  · refine Or.inr ?_
    have hne : (((z : Kˣ) : K) - 1) ≠ 0 := sub_ne_zero.mpr hx
    have hexp := valuation_eq_exp_neg_count v hne
    have hle := h v hv
    rw [hexp, WithZero.exp_le_exp] at hle
    omega

end Modulus
end NumberField
