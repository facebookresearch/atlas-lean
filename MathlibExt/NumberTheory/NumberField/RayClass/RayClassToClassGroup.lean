/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.QuotientToRayClass
import Mathlib.Algebra.Exact.Basic

/-!
# Ray-class-to-ordinary-class-group projection (N406 E4)

Exactness stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the ideal-class map on coprime fractional ideals, its descent to the ray
class group, representative rules, the kernel, and exactness at the ray
class group in raw quotient and residue-sign forms.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E4 lines 1120--1132
(`exactSeq_map4`) and 1343--1429 (`exactSeq_exact_at_ray_class`).

Source-to-API map:
- ATLAS `exactSeq_map4`, lines 1120--1132, to `coprimeIdealClassMap` and
  `rayClassToClassGroup` (`QuotientGroup.lift` of `ClassGroup.mk K` after the
  subgroup inclusion);
- ATLAS `exactSeq_exact_at_ray_class`, lines 1343--1429, to
  `rayClassToClassGroup_ker` and
  `rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup`.
- Representation differences: ATLAS works with `FracIdealsCoprime_subgroup`,
  `RayGroup`, and `RayClassGroup` over explicitly coprime subtypes; here these
  are `coprimeFractionalIdeals m`, `rayGroup m`, and `RayClassGroup m`.
  ATLAS lift well-definedness (lines 1124--1132) is discharged via the merged
  E2 lemma `rayGroup_eq_map_rayOneElements` plus `principalRayIdealMap_apply`;
  principal-ideal computations use `principalRayIdealMap_apply`.
  ATLAS reverse exactness (lines 1373--1429) chooses a coprime representative
  via `rayClassMap_surjective`, obtains a principal generator via
  `ClassGroup.mk_eq_one_iff` and `FractionalIdeal.isPrincipal_iff`, proves
  `a ≠ 0`, forms `Units.mk0 a`, and lands in `rayElements m` through the
  definitional `mem_rayElements_iff` comap criterion; the source's valuation
  reconstruction (the analogue of lines 1206--1247) is obsolete and not ported.
- The transported `residueSignToRayClassGroup` corollary has no ATLAS source
  span; it crosses `rayElementsQuotientEquivResidueSign` using E3's
  transported map and its range.

E4 partial-stage boundary: this module stops before projection surjectivity
(source lines 1431--1480, E5, which needs coprime ideal-class representatives)
and before the final six-term wrapper (E5). It does not reimplement E1--E3.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- **Ideal-class map on coprime fractional ideals.** Let $K$ be a number field, $\mathfrak m$ a
modulus of $K$, and $I_{\mathfrak m}$ the group of nonzero fractional ideals of $\mathcal O_K$
coprime to the finite part of $\mathfrak m$. The coprime ideal-class map is the group homomorphism
$I_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K)$ that sends $I$ to its ideal class $[I]$: the
inclusion of $I_{\mathfrak m}$ into the group of nonzero fractional ideals followed by the class
map.

Source: ATLAS `exactSeq_map4`, before the quotient lift. -/
noncomputable def coprimeIdealClassMap (m : Modulus K) :
    coprimeFractionalIdeals m →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (coprimeFractionalIdeals m).subtype

/-- **Value of the ideal-class map on a coprime ideal.** Let $K$ be a number field, $\mathfrak m$ a
modulus of $K$, and $I_{\mathfrak m}$ the group of nonzero fractional ideals of $\mathcal O_K$
coprime to the finite part of $\mathfrak m$. For every $I \in I_{\mathfrak m}$, the coprime
ideal-class map sends $I$ to the class $[I]$ in the class group $\mathrm{Cl}(\mathcal O_K)$ of $I$
viewed as a nonzero fractional ideal. -/
@[simp] theorem coprimeIdealClassMap_apply (m : Modulus K)
    (I : coprimeFractionalIdeals m) :
    coprimeIdealClassMap m I =
      ClassGroup.mk K ((coprimeFractionalIdeals m).subtype I) :=
  rfl

/-- **The ray group lies in the kernel of the ideal-class map.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$, $I_{\mathfrak m}$ the group of nonzero fractional ideals of
$\mathcal O_K$ coprime to the finite part of $\mathfrak m$, and $P_{\mathfrak m} \subseteq
I_{\mathfrak m}$ the ray group. Then $P_{\mathfrak m}$ is contained in the kernel of the coprime
ideal-class map $I_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K)$, $I \mapsto [I]$: every ideal in
$P_{\mathfrak m}$ has trivial class in $\mathrm{Cl}(\mathcal O_K)$. -/
theorem rayGroup_le_coprimeIdealClassMap_ker (m : Modulus K) :
    rayGroup m ≤ (coprimeIdealClassMap m).ker := by
  rw [rayGroup_eq_map_rayOneElements]
  intro y hy
  obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp hy
  rw [MonoidHom.mem_ker, coprimeIdealClassMap_apply, ClassGroup.mk_eq_one_iff,
    FractionalIdeal.isPrincipal_iff]
  refine ⟨((x : Kˣ) : K), ?_⟩
  have h := principalRayIdealMap_apply m x
  have hval : (((principalRayIdealMap m x :
      coprimeFractionalIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K) := by
    rw [h, coe_toPrincipalIdeal]
  simpa only [Subgroup.coe_subtype] using hval

/-- **Projection from the ray class group to the class group.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$, $I_{\mathfrak m}$ the group of nonzero fractional ideals of
$\mathcal O_K$ coprime to the finite part of $\mathfrak m$, $P_{\mathfrak m}$ the ray group, and
$\mathrm{Cl}_{\mathfrak m} = I_{\mathfrak m}/P_{\mathfrak m}$ the ray class group. The projection
$\mathrm{Cl}_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K)$ is the group homomorphism induced by the
coprime ideal-class map $I_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K)$, $I \mapsto [I]$, which is
trivial on $P_{\mathfrak m}$; it sends the ray class of $I$ to $[I]$.

Source: ATLAS `exactSeq_map4`. -/
noncomputable def rayClassToClassGroup (m : Modulus K) :
    RayClassGroup m →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift (rayGroup m) (coprimeIdealClassMap m)
    (rayGroup_le_coprimeIdealClassMap_ker m)

/-- **Projection to the class group on ray class representatives.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$, $I_{\mathfrak m}$ the group of nonzero fractional ideals of
$\mathcal O_K$ coprime to the finite part of $\mathfrak m$, and $\mathrm{Cl}_{\mathfrak m}$ the ray
class group. For every $I \in I_{\mathfrak m}$, the projection $\mathrm{Cl}_{\mathfrak m} \to
\mathrm{Cl}(\mathcal O_K)$ sends the ray class of $I$ to $[I]$, the value of the coprime
ideal-class map at $I$. -/
@[simp] theorem rayClassToClassGroup_rayClassMap (m : Modulus K)
    (I : coprimeFractionalIdeals m) :
    rayClassToClassGroup m (rayClassMap m I) = coprimeIdealClassMap m I := by
  simp [rayClassToClassGroup, rayClassMap]

/-- **The ideal-class map factors through the ray class group.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$, $I_{\mathfrak m}$ the group of nonzero fractional ideals of
$\mathcal O_K$ coprime to the finite part of $\mathfrak m$, $P_{\mathfrak m} \subseteq
I_{\mathfrak m}$ the ray group, and $\mathrm{Cl}_{\mathfrak m} = I_{\mathfrak m}/P_{\mathfrak m}$
the ray class group. As group homomorphisms, the quotient map $I_{\mathfrak m} \to
\mathrm{Cl}_{\mathfrak m}$ followed by the projection $\mathrm{Cl}_{\mathfrak m} \to
\mathrm{Cl}(\mathcal O_K)$ equals the coprime ideal-class map $I_{\mathfrak m} \to
\mathrm{Cl}(\mathcal O_K)$, $I \mapsto [I]$. -/
theorem rayClassToClassGroup_comp_rayClassMap (m : Modulus K) :
    (rayClassToClassGroup m).comp (rayClassMap m) = coprimeIdealClassMap m := by
  ext I
  simp only [MonoidHom.comp_apply]
  exact rayClassToClassGroup_rayClassMap m I

/-- **Projecting the image of a ray element to the class group.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, $I_{\mathfrak m}$ the group of
nonzero fractional ideals of $\mathcal O_K$ coprime to $\mathfrak m_0$, $\mathrm{Cl}_{\mathfrak m}$
the ray class group, $K_{\mathfrak m}$ the group of $x \in K^\times$ with
$x\mathcal O_K \in I_{\mathfrak m}$, and $K_{\mathfrak m,1} \subseteq K_{\mathfrak m}$ the subgroup
of those $x$ with $x \equiv 1 \pmod{\mathfrak m_0}$ that are positive at every real place in
$\mathfrak m$. For every $x \in K_{\mathfrak m}$, sending the class of $x$ through the map
$K_{\mathfrak m}/K_{\mathfrak m,1} \to \mathrm{Cl}_{\mathfrak m}$ that takes the class of $y$ to
the ray class of $y\mathcal O_K$, and then through the projection $\mathrm{Cl}_{\mathfrak m} \to
\mathrm{Cl}(\mathcal O_K)$, gives $[x\mathcal O_K]$, the value of the coprime ideal-class map at
$x\mathcal O_K \in I_{\mathfrak m}$. -/
theorem rayClassToClassGroup_rayQuotientToRayClassGroup (m : Modulus K)
    (x : rayElements m) :
    rayClassToClassGroup m (rayQuotientToRayClassGroup m (QuotientGroup.mk x)) =
      coprimeIdealClassMap m (principalRayIdealMap m x) := by
  rw [rayQuotientToRayClassGroup_mk, rayElementClassMap_apply,
    ← rayClassToClassGroup_rayClassMap]

/-- **Projecting the image of a residue-sign value to the class group.** Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, $I_{\mathfrak m}$ the group of
nonzero fractional ideals of $\mathcal O_K$ coprime to $\mathfrak m_0$, $\mathrm{Cl}_{\mathfrak m}$
the ray class group, and $K_{\mathfrak m}$ the group of $x \in K^\times$ with
$x\mathcal O_K \in I_{\mathfrak m}$. Let $T_{\mathfrak m}$ be the product of one group of order $2$
for each real place in $\mathfrak m$ with $(\mathcal O_K/\mathfrak m_0)^\times$, let
$\rho : K_{\mathfrak m} \to T_{\mathfrak m}$ be the residue-sign map, and let
$T_{\mathfrak m} \to \mathrm{Cl}_{\mathfrak m}$ be the residue-sign-to-ray-class map. For every
$x \in K_{\mathfrak m}$, sending $\rho(x)$ through this map and then through the projection
$\mathrm{Cl}_{\mathfrak m} \to \mathrm{Cl}(\mathcal O_K)$ gives $[x\mathcal O_K]$, the value of
the coprime ideal-class map at $x\mathcal O_K \in I_{\mathfrak m}$. -/
theorem rayClassToClassGroup_residueSignToRayClassGroup (m : Modulus K)
    (x : rayElements m) :
    rayClassToClassGroup m
        (residueSignToRayClassGroup m (residueSignMap m x)) =
      coprimeIdealClassMap m (principalRayIdealMap m x) := by
  rw [residueSignToRayClassGroup_residueSignMap,
    rayElementClassMap_apply, ← rayClassToClassGroup_rayClassMap]

/-- **Kernel of the projection from the ray class group to the class group.** Let $K$ be a number
field, $\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, $I_{\mathfrak m}$ the group
of nonzero fractional ideals of $\mathcal O_K$ coprime to $\mathfrak m_0$,
$\mathrm{Cl}_{\mathfrak m}$ the ray class group, $K_{\mathfrak m}$ the group of $x \in K^\times$
with $x\mathcal O_K \in I_{\mathfrak m}$, and $K_{\mathfrak m,1} \subseteq K_{\mathfrak m}$ the
subgroup of those $x$ with $x \equiv 1 \pmod{\mathfrak m_0}$ that are positive at every real place
in $\mathfrak m$. The kernel of the projection $\mathrm{Cl}_{\mathfrak m} \to
\mathrm{Cl}(\mathcal O_K)$ equals the image of the homomorphism
$K_{\mathfrak m}/K_{\mathfrak m,1} \to \mathrm{Cl}_{\mathfrak m}$ that sends the class of $x$ to
the ray class of $x\mathcal O_K$.

Source: ATLAS `exactSeq_exact_at_ray_class`. -/
theorem rayClassToClassGroup_ker (m : Modulus K) :
    (rayClassToClassGroup m).ker =
      MonoidHom.range (rayQuotientToRayClassGroup m) := by
  apply le_antisymm
  · intro c hc
    rw [MonoidHom.mem_ker] at hc
    obtain ⟨I, rfl⟩ := rayClassMap_surjective m c
    rw [rayClassToClassGroup_rayClassMap] at hc
    have hunfold : ClassGroup.mk K
        ((coprimeFractionalIdeals m).subtype I) = 1 := hc
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at hunfold
    obtain ⟨a, ha⟩ := hunfold
    have ha_val : ((((coprimeFractionalIdeals m).subtype I :
        (FractionalIdeal (𝓞 K)⁰ K)ˣ)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a := ha
    have ha_val' : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
      simpa only [Subgroup.coe_subtype] using ha_val
    have ha_ne : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, FractionalIdeal.spanSingleton_zero] at ha_val'
      exact Units.ne_zero (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ha_val'
    set α : Kˣ := Units.mk0 a ha_ne with hα
    have hI_eq_topi : (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        toPrincipalIdeal (𝓞 K) K α := by
      apply Units.ext
      show ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = _
      rw [coe_toPrincipalIdeal, hα, Units.val_mk0]
      exact ha_val'
    have hα_coprime : α ∈ rayElements m := by
      rw [mem_rayElements_iff, ← hI_eq_topi]
      exact I.property
    set γ : rayElements m := ⟨α, hα_coprime⟩ with hγ
    have hγ_eq : principalRayIdealMap m γ = I := by
      apply Subtype.ext
      have h := principalRayIdealMap_apply m γ
      rw [h, hI_eq_topi]
    refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk γ, ?_⟩
    rw [rayQuotientToRayClassGroup_mk, rayElementClassMap_apply, hγ_eq]
  · intro c hc
    obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hc
    rw [MonoidHom.mem_ker]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rayOneElements m) q
    rw [QuotientGroup.mk'_apply, rayQuotientToRayClassGroup_mk,
      rayElementClassMap_apply, rayClassToClassGroup_rayClassMap]
    rw [coprimeIdealClassMap_apply, ClassGroup.mk_eq_one_iff,
      FractionalIdeal.isPrincipal_iff]
    refine ⟨((x : Kˣ) : K), ?_⟩
    have h := principalRayIdealMap_apply m x
    have hval : (((principalRayIdealMap m x :
        coprimeFractionalIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : Kˣ) : K) := by
      rw [h, coe_toPrincipalIdeal]
    simpa only [Subgroup.coe_subtype] using hval

/-- **Exactness at the ray class group.** Let $K$ be a number field, $\mathfrak m$ a modulus of
$K$ with finite part $\mathfrak m_0$, $I_{\mathfrak m}$ the group of nonzero fractional ideals of
$\mathcal O_K$ coprime to $\mathfrak m_0$, $\mathrm{Cl}_{\mathfrak m}$ the ray class group,
$K_{\mathfrak m}$ the group of $x \in K^\times$ with $x\mathcal O_K \in I_{\mathfrak m}$, and
$K_{\mathfrak m,1} \subseteq K_{\mathfrak m}$ the subgroup of those $x$ with
$x \equiv 1 \pmod{\mathfrak m_0}$ that are positive at every real place in $\mathfrak m$. The
sequence $K_{\mathfrak m}/K_{\mathfrak m,1} \to \mathrm{Cl}_{\mathfrak m} \to
\mathrm{Cl}(\mathcal O_K)$ is exact at $\mathrm{Cl}_{\mathfrak m}$, where the first map sends the
class of $x$ to the ray class of $x\mathcal O_K$ and the second is the projection: a ray class
maps to the identity of $\mathrm{Cl}(\mathcal O_K)$ if and only if it lies in the image of the
first map.

Source: ATLAS `exactSeq_exact_at_ray_class`. -/
theorem rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup
    (m : Modulus K) :
    Function.MulExact (rayQuotientToRayClassGroup m)
      (rayClassToClassGroup m) := by
  rw [MonoidHom.mulExact_iff, rayClassToClassGroup_ker]

/-- **Exactness at the ray class group, residue-sign form.** Let $\mathfrak m$ be a modulus of a
number field $K$, with finite part the nonzero ideal $\mathfrak m_0$ of $\mathcal O_K$ and infinite
part the finite set $\mathfrak m_\infty$ of real places of $K$. Let $\varphi$ be the homomorphism
from the residue-sign group $\{\pm 1\}^{\mathfrak m_\infty} \times
(\mathcal O_K/\mathfrak m_0)^\times$ to the ray class group $\mathrm{Cl}_{\mathfrak m}(K)$ that
sends the signs at the places in $\mathfrak m_\infty$ and the residue class modulo $\mathfrak m_0$
of an element $x \in K^\times$ coprime to $\mathfrak m_0$ to the ray class of the principal ideal
$(x)$, and let $\pi \colon \mathrm{Cl}_{\mathfrak m}(K) \to \mathrm{Cl}(K)$ be the projection to
the ideal class group. Then a ray class $c$ satisfies $\pi(c) = 1$ if and only if $c$ lies in the
image of $\varphi$; that is, the sequence is exact at $\mathrm{Cl}_{\mathfrak m}(K)$. -/
theorem residueSignToRayClassGroup_mulExact_rayClassToClassGroup
    (m : Modulus K) :
    Function.MulExact (residueSignToRayClassGroup m)
      (rayClassToClassGroup m) := by
  rw [MonoidHom.mulExact_iff]
  have hrange : MonoidHom.range (residueSignToRayClassGroup m) =
      MonoidHom.range (rayQuotientToRayClassGroup m) := by
    unfold residueSignToRayClassGroup
    rw [MonoidHom.range_comp, MulEquiv.toMonoidHom_eq_coe,
      MulEquiv.range_eq_top, ← MonoidHom.range_eq_map]
  rw [hrange, ← rayClassToClassGroup_ker]

end Modulus
end NumberField
