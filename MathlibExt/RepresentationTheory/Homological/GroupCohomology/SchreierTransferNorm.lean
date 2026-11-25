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
# Right-transversal norms and multiplicative coboundaries

For a finite-index subgroup and a chosen right transversal, this file defines
the product of the inverse-translated conjugates of an element.  The Schreier
identity shows that degree-one transfer sends the multiplicative coboundary of
the element to the multiplicative coboundary of that product.

The product is also related to the codomain of any surjective group homomorphism
whose kernel is the subgroup.  No field norm, Kummer class, transversal
independence, degree-two transfer, or projection formula is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u v

variable {G : Type u} [Group G] {H : Subgroup G}

/-- A right transversal for the kernel of a surjection is equivalent to its
codomain.  The inverse in the formula reflects that a right transversal for
`H` becomes a system of left-coset representatives after inversion. -/
noncomputable def rightTransversalEquivCodomain
    {Q : Type v} [Group Q] (f : G →* Q) (hf : Function.Surjective f)
    (T : f.ker.RightTransversal) : (T : Set G) ≃ Q :=
  T.2.rightQuotientEquiv.symm |>.trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel f.ker) |>.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv

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

noncomputable local instance rightTransversalNormFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Product of the inverse-translated conjugates indexed by a chosen right
transversal. -/
noncomputable def rightTransversalNorm (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) : M :=
  ∏ t : (T : Set G), (t : G)⁻¹ • d

@[simp]
theorem rightTransversalNorm_apply (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) :
    rightTransversalNorm T d = ∏ t : (T : Set G), (t : G)⁻¹ • d :=
  rfl

/-- The right-transversal norm commutes with natural powers. -/
theorem rightTransversalNorm_pow (T : H.RightTransversal)
    [H.FiniteIndex] (d : M) (n : ℕ) :
    (rightTransversalNorm T d) ^ n = rightTransversalNorm T (d ^ n) := by
  unfold rightTransversalNorm
  rw [← Finset.prod_pow Finset.univ n]
  apply Finset.prod_congr rfl
  intro t _
  exact (map_pow (MulDistribMulAction.toMonoidHom M (t : G)⁻¹) d n).symm

/-- The right-transversal norm of an `H`-fixed element is `G`-fixed. -/
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

/-- Multiplicative cochain form of `cor(d d) = d(N d)`. -/
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
