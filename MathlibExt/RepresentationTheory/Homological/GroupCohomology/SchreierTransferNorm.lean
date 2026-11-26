/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransfer
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Transversal norms for multiplicative coefficient groups

Let G act by group automorphisms on a commutative group M. For a finite-index H ≤ G and right
transversal T, the multiplicative norm is N_T(d) = ∏ₜ t⁻¹·d. It commutes with natural powers,
sends H-fixed elements to G-fixed elements, and satisfies the multiplicative coboundary
identity cor_T(h ↦ (h·d)/d)(g) = (g·N_T(d))/N_T(d).

For a surjective homomorphism f : G → Q, a right transversal for ker(f) is equivalent to Q by
t ↦ f(t)⁻¹. This comparison permits independent source and quotient-group universes and does
not require the quotient to be finite.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u v

variable {G : Type u} [Group G] {H : Subgroup G}

/-- A kernel transversal identified with a quotient homomorphism codomain.

For a surjective f : G → Q, a right transversal for ker(f) is equivalent to Q. The equivalence
uses inversion to pass from right to left quotient conventions. -/
noncomputable def rightTransversalEquivCodomain
    {Q : Type v} [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (T : f.ker.RightTransversal) : (T : Set G) ≃ Q :=
  T.2.rightQuotientEquiv.symm |>.trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel f.ker) |>.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv

/-- Coordinates of the kernel-transversal equivalence.

The codomain element corresponding to t in a right transversal for ker(f) is f(t)⁻¹. -/
@[simp]
theorem rightTransversalEquivCodomain_apply
    {Q : Type v} [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (T : f.ker.RightTransversal) (t : (T : Set G)) :
    rightTransversalEquivCodomain f hf T t = f (t : G)⁻¹ := by
  unfold rightTransversalEquivCodomain
  change (QuotientGroup.quotientKerEquivOfSurjective f hf)
      (QuotientGroup.mk ((t : G)⁻¹)) = f (t : G)⁻¹
  rfl

variable {M : Type v} [CommGroup M] [MulDistribMulAction G M]

/-- Finite representatives for multiplicative norm products.

A right transversal for a finite-index subgroup H is finitely enumerated for the norm product. -/
noncomputable local instance rightTransversalNormFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The multiplicative norm of a chosen right transversal.

For d in a commutative coefficient group M with a G-action by group automorphisms, set N_T(d)
= ∏ₜ t⁻¹·d over the finite right transversal. -/
noncomputable def rightTransversalNorm (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) : M :=
  ∏ t : (T : Set G), (t : G)⁻¹ • d

/-- The inverse-translate product formula for the norm.

The value of rightTransversalNorm T d is ∏ₜ t⁻¹·d. -/
@[simp]
theorem rightTransversalNorm_apply (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) :
    rightTransversalNorm T d = ∏ t : (T : Set G), (t : G)⁻¹ • d :=
  rfl

/-- Natural powers commute with the transversal norm.

For n ∈ ℕ, the multiplicative norm satisfies N_T(d)ⁿ = N_T(dⁿ). -/
theorem rightTransversalNorm_pow (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) (n : ℕ) :
    (rightTransversalNorm T d) ^ n = rightTransversalNorm T (d ^ n) := by
  unfold rightTransversalNorm
  rw [← Finset.prod_pow Finset.univ n]
  apply Finset.prod_congr rfl
  intro t _
  exact (map_pow (MulDistribMulAction.toMonoidHom M (t : G)⁻¹) d n).symm

/-- The norm of a subgroup-fixed element is group-fixed.

If h·b = b for every h ∈ H, then g·N_T(b) = N_T(b) for every g ∈ G. -/
theorem rightTransversalNorm_fixed (T : H.RightTransversal)
    [H.FiniteIndex] (b : M) (hb : ∀ h : H, (h : G) • b = b)
    (g : G) : g • rightTransversalNorm T b = rightTransversalNorm T b := by
  unfold rightTransversalNorm
  rw [Finset.smul_prod']
  calc
    (∏ t : (T : Set G), g • ((t : G)⁻¹ • b)) =
        ∏ t : (T : Set G), (g * (t : G)⁻¹) • b := by
      apply Finset.prod_congr rfl
      intro t _
      rw [mul_smul]
    _ = ∏ t : (T : Set G),
        (g * (T.schreierRep t g : G)⁻¹) • b := by
      exact ((T.schreierRepEquiv g).prod_comp
        (fun t : (T : Set G) => (g * (t : G)⁻¹) • b)).symm
    _ = ∏ t : (T : Set G), (t : G)⁻¹ • b := by
      apply Finset.prod_congr rfl
      intro t _
      rw [← T.inv_mul_schreierFactor t g, mul_smul,
        hb (T.schreierFactor t g)]

/-- Transfer of a multiplicative coboundary.

For tg = a(t,g)r(t,g), the product ∏ₜ t⁻¹·((a(t,g)·d)/d) equals (g·N_T(d))/N_T(d). -/
theorem corestriction_mulCoboundary_product (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) (g : G) :
    (∏ t : (T : Set G),
      (t : G)⁻¹ • (((T.schreierFactor t g : H) : G) • d / d)) =
      g • rightTransversalNorm T d / rightTransversalNorm T d := by
  calc
    (∏ t : (T : Set G),
        (t : G)⁻¹ • (((T.schreierFactor t g : H) : G) • d / d)) =
      ∏ t : (T : Set G),
        ((g * (T.schreierRep t g : G)⁻¹) • d) / ((t : G)⁻¹ • d) := by
      apply Finset.prod_congr rfl
      intro t _
      have hdiv : (t : G)⁻¹ •
          (((T.schreierFactor t g : H) : G) • d / d) =
          ((t : G)⁻¹ • (((T.schreierFactor t g : H) : G) • d)) /
            ((t : G)⁻¹ • d) := by
        exact map_div (MulDistribMulAction.toMonoidHom M (t : G)⁻¹) _ _
      rw [hdiv, ← mul_smul, T.inv_mul_schreierFactor]
    _ = (∏ t : (T : Set G),
          (g * (T.schreierRep t g : G)⁻¹) • d) /
        (∏ t : (T : Set G), (t : G)⁻¹ • d) := by
      rw [Finset.prod_div_distrib]
    _ = (∏ t : (T : Set G), (g * (t : G)⁻¹) • d) /
        (∏ t : (T : Set G), (t : G)⁻¹ • d) := by
      congr 1
      simpa only [T.schreierRepEquiv_apply] using
        (T.schreierRepEquiv g).prod_comp
          (fun t : (T : Set G) => (g * (t : G)⁻¹) • d)
    _ = g • rightTransversalNorm T d / rightTransversalNorm T d := by
      unfold rightTransversalNorm
      congr 1
      rw [Finset.smul_prod']
      apply Finset.prod_congr rfl
      intro t _
      rw [mul_smul]

end groupCohomology
