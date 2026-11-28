/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- AI-assisted original formalization: Avocado; responsible human author: @toskua.
module

public import MathlibExt.GroupTheory.SchreierTransversal
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Schreier transfer in degrees zero and one

Let k be a commutative ring, A a k-linear representation of G, H ≤ G a finite-index subgroup
and T a right transversal. Write tg = a(t,g)r(t,g), with a(t,g) ∈ H and r(t,g) ∈ T. The
degree-zero norm is N_T(x) = ∑ₜ ρ(t⁻¹)x, and the degree-one transfer of c : H → A is
cor_T(c)(g) = ∑ₜ ρ(t⁻¹)c(a(t,g)).

The representative permutation and Schreier factor identity give cor_T(d⁰x) = d⁰(N_T(x)) and
preserve the one-cocycle equation c(h₁h₂) = ρ(h₁)c(h₂) + c(h₁). Thus the chosen-transversal
formula induces a linear map H¹(H,A|H) → H¹(G,A), computed by transferring a cocycle
representative.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for low-degree transfer.

For a finite-index subgroup H and right transversal T, the representative subtype T is given
its finite enumeration for the transfer sums. -/
noncomputable local instance corestrictionRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-zero norm of a right transversal.

For x ∈ A, define N_T(x) = ∑ₜ ρ(t⁻¹)x over the finite right transversal. This is a k-linear
endomorphism of the coefficient module A. -/
noncomputable def corestrictionZero (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] : A →ₗ[k] A := by
  exact ∑ t : (T : Set G), A.ρ (t : G)⁻¹

/-- The representative sum for the degree-zero norm.

The value of corestrictionZero A T at x is ∑ₜ ρ(t⁻¹)x. -/
@[simp]
theorem corestrictionZero_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (a : A) :
    corestrictionZero A T a =
      ∑ t : (T : Set G), A.ρ (t : G)⁻¹ a := by
  simp [corestrictionZero]

/-- The degree-one Schreier cochain transfer.

For c : H → A, define cor_T(c)(g) = ∑ₜ ρ(t⁻¹)c(a(t,g)), where tg = a(t,g)r(t,g). This is a
k-linear map from H-cochains to G-cochains. -/
noncomputable def corestrictionCochainOne (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    (H → A) →ₗ[k] (G → A) where
  toFun f g := by
    exact ∑ t : (T : Set G),
      A.ρ (t : G)⁻¹ (f (T.schreierFactor t g))
  map_add' f₁ f₂ := by
    funext g
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext g
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

/-- Values of the degree-one Schreier transfer.

At g ∈ G, the transferred cochain has value ∑ₜ ρ(t⁻¹)c(a(t,g)). -/
@[simp]
theorem corestrictionCochainOne_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) (g : G) :
    corestrictionCochainOne A T f g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.schreierFactor t g)) := by
  rfl

/-- A transferred degree-zero differential summand.

The Schreier decomposition gives ρ(t⁻¹)(ρ(a(t,g))x − x) = ρ(g r(t,g)⁻¹)x − ρ(t⁻¹)x. This term
identity uses the restricted H-action on the source. -/
theorem corestrictionCochainOne_d₀₁_term (A : Rep k G)
    (T : H.RightTransversal) (a : A) (t : (T : Set G)) (g : G) :
    A.ρ (t : G)⁻¹
        ((Rep.res (Subgroup.subtype H) A).ρ (T.schreierFactor t g) a - a) =
      A.ρ (g * (T.schreierRep t g : G)⁻¹) a -
        A.ρ (t : G)⁻¹ a := by
  rw [map_sub]
  congr 1
  change A.ρ (t : G)⁻¹
      (A.ρ (T.schreierFactor t g : G) a) = _
  rw [← Module.End.mul_apply, ← map_mul,
    T.inv_mul_schreierFactor t g]

/-- Reindexing the leading norm term by a representative permutation.

For fixed g, the sum ∑ₜ ρ(g r(t,g)⁻¹)x equals ∑ₜ ρ(g t⁻¹)x, since t ↦ r(t,g) permutes T. -/
theorem sum_rho_mul_schreierRep_inv (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (a : A) (g : G) :
    ∑ t : (T : Set G), A.ρ (g * (T.schreierRep t g : G)⁻¹) a =
      ∑ t : (T : Set G), A.ρ (g * (t : G)⁻¹) a :=
  (T.schreierRepEquiv g).sum_comp
    (fun t : (T : Set G) => A.ρ (g * (t : G)⁻¹) a)

/-- Transfer commutes with the first cochain differential.

For d⁰x(h) = ρ(h)x − x, the chosen degree-one transfer satisfies cor_T(d⁰x) = d⁰(N_T(x)). -/
theorem corestrictionCochainOne_d₀₁ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (a : A) :
    corestrictionCochainOne A T
        ((groupCohomology.d₀₁ (Rep.res (Subgroup.subtype H) A)).hom a) =
      (groupCohomology.d₀₁ A).hom (corestrictionZero A T a) := by
  funext g
  rw [corestrictionCochainOne_apply]
  simp only [d₀₁_hom_apply, corestrictionZero_apply]
  change
    (∑ t : (T : Set G),
      A.ρ (t : G)⁻¹
        ((Rep.res (Subgroup.subtype H) A).ρ
          (T.schreierFactor t g) a - a)) =
      A.ρ g (∑ t : (T : Set G), A.ρ (t : G)⁻¹ a) -
        ∑ t : (T : Set G), A.ρ (t : G)⁻¹ a
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          ((Rep.res (Subgroup.subtype H) A).ρ
            (T.schreierFactor t g) a - a)) =
        ∑ t : (T : Set G),
          (A.ρ (g * (T.schreierRep t g : G)⁻¹) a -
            A.ρ (t : G)⁻¹ a) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCochainOne_d₀₁_term A T a t g
  rw [hterms]
  rw [Finset.sum_sub_distrib, sum_rho_mul_schreierRep_inv]
  rw [map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [← Module.End.mul_apply, ← map_mul]

/-- A Schreier summand of the one-cocycle equation.

For an H-one-cocycle c, the summand ρ(t⁻¹)c(a(t,g₁g₂)) equals ρ(g₁r(t,g₁)⁻¹)c(a(r(t,g₁),g₂)) +
ρ(t⁻¹)c(a(t,g₁)). -/
theorem corestrictionCochainOne_mul_term (A : Rep k G)
    (T : H.RightTransversal)
    (f : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ : G) :
    A.ρ (t : G)⁻¹ (f (T.schreierFactor t (g₁ * g₂))) =
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (f (T.schreierFactor (T.schreierRep t g₁) g₂)) +
        A.ρ (t : G)⁻¹ (f (T.schreierFactor t g₁)) := by
  rw [T.schreierFactor_mul t g₁ g₂]
  have hf := (groupCohomology.mem_cocycles₁_iff f).mp f.property
    (T.schreierFactor t g₁)
    (T.schreierFactor (T.schreierRep t g₁) g₂)
  rw [hf, map_add]
  congr 1
  change A.ρ (t : G)⁻¹
      (A.ρ (T.schreierFactor t g₁ : G)
        (f (T.schreierFactor (T.schreierRep t g₁) g₂))) = _
  rw [← Module.End.mul_apply, ← map_mul,
    T.inv_mul_schreierFactor t g₁]

/-- Reindexing the leading one-cocycle sum.

For any c : H → A, summing ρ(g₁r(t,g₁)⁻¹)c(a(r(t,g₁),g₂)) over T gives ρ(g₁) times the
transfer sum at g₂. -/
theorem sum_rho_mul_schreierRep_inv_factor (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) (g₁ g₂ : G) :
    (∑ t : (T : Set G),
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
        (f (T.schreierFactor (T.schreierRep t g₁) g₂))) =
      A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (f (T.schreierFactor t g₂))) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (f (T.schreierFactor (T.schreierRep t g₁) g₂))) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (t : G)⁻¹) (f (T.schreierFactor t g₂)) :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g₁ * (t : G)⁻¹) (f (T.schreierFactor t g₂)))
    _ = ∑ t : (T : Set G),
        A.ρ g₁ (A.ρ (t : G)⁻¹ (f (T.schreierFactor t g₂))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (f (T.schreierFactor t g₂))) := by
      rw [map_sum]

/-- Degree-one transfer preserves cocycles.

If c is an H-one-cocycle for the restricted representation A|H, its transferred cochain
satisfies the G-one-cocycle equation. -/
theorem corestrictionCochainOne_mem_cocycles₁ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionCochainOne A T f ∈ groupCohomology.cocycles₁ A := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro g₁ g₂
  rw [corestrictionCochainOne_apply,
    corestrictionCochainOne_apply, corestrictionCochainOne_apply]
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.schreierFactor t (g₁ * g₂)))) =
      ∑ t : (T : Set G),
        (A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (f (T.schreierFactor (T.schreierRep t g₁) g₂)) +
          A.ρ (t : G)⁻¹ (f (T.schreierFactor t g₁))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCochainOne_mul_term A T f t g₁ g₂
  rw [hterms, Finset.sum_add_distrib,
    sum_rho_mul_schreierRep_inv_factor]

/-- The linear transfer map on one-cocycles.

Restrict the chosen-transversal degree-one cochain map to Z¹(H,A|H), obtaining a k-linear map
to Z¹(G,A). -/
noncomputable def corestrictionCocyclesOne (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.cocycles₁ A where
  toFun f := ⟨corestrictionCochainOne A T f,
    corestrictionCochainOne_mem_cocycles₁ A T f⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    change corestrictionCochainOne A T
        ((f₁ + f₂ : groupCohomology.cocycles₁
          (Rep.res (Subgroup.subtype H) A)) : H → A) = _
    exact map_add (corestrictionCochainOne A T) (f₁ : H → A) (f₂ : H → A)
  map_smul' r f := by
    apply Subtype.ext
    change corestrictionCochainOne A T
        ((r • f : groupCohomology.cocycles₁
          (Rep.res (Subgroup.subtype H) A)) : H → A) = _
    exact map_smul (corestrictionCochainOne A T) r (f : H → A)

/-- The cochain underlying a transferred one-cocycle.

For c ∈ Z¹(H,A|H), the underlying G-cochain of corestrictionCocyclesOne A T c is
corestrictionCochainOne A T c. -/
@[simp]
theorem coe_corestrictionCocyclesOne (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A)) :
    (corestrictionCocyclesOne A T f : G → A) =
      corestrictionCochainOne A T f :=
  rfl

/-- The class of a transferred one-cocycle.

Transfer an H-one-cocycle by the chosen Schreier formula and project the resulting G-one-
cocycle to H¹(G,A). -/
noncomputable def corestrictionCocycleOneClass (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H1 A :=
  (groupCohomology.H1π A).hom.comp (corestrictionCocyclesOne A T)

/-- Coboundaries vanish under the transferred class map.

The kernel of the source projection Z¹(H,A|H) → H¹(H,A|H) is contained in the kernel of the
transferred class map to H¹(G,A). -/
theorem corestrictionCocycleOneClass_ker (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    LinearMap.ker
        (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A)).hom ≤
      LinearMap.ker (corestrictionCocycleOneClass A T) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  apply (groupCohomology.H1π_eq_zero_iff _).2
  have hboundary : (f : H → A) ∈
      groupCohomology.coboundaries₁
        (Rep.res (Subgroup.subtype H) A) :=
    (groupCohomology.H1π_eq_zero_iff f).1 hf
  rcases hboundary with ⟨a, ha⟩
  refine ⟨corestrictionZero A T a, ?_⟩
  change (groupCohomology.d₀₁ A).hom (corestrictionZero A T a) =
    corestrictionCochainOne A T f
  rw [← corestrictionCochainOne_d₀₁]
  exact congrArg (corestrictionCochainOne A T) ha

/-- The degree-one cohomology map of a right transversal.

The chosen Schreier transfer descends through the quotient by source coboundaries to a
k-linear map H¹(H,A|H) → H¹(G,A). -/
noncomputable def corestrictionH1OfRightTransversal (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.H1 (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H1 A :=
  let q := (LinearMap.ker
      (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A)).hom).liftQ
    (corestrictionCocycleOneClass A T)
    (corestrictionCocycleOneClass_ker A T)
  let e :=
    (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A)).hom
      |>.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective
          (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A))).1
            inferInstance)
  q.comp e.symm.toLinearMap

/-- The degree-one transfer on a represented class.

For an H-one-cocycle c, applying the chosen H¹ transfer to its class gives the class of the
transferred G-one-cocycle. -/
@[simp]
theorem corestrictionH1OfRightTransversal_H1π (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH1OfRightTransversal A T
        (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A) f) =
      groupCohomology.H1π A (corestrictionCocyclesOne A T f) := by
  change (LinearMap.ker
      (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A)).hom).liftQ
        (corestrictionCocycleOneClass A T)
        (corestrictionCocycleOneClass_ker A T)
        (((groupCohomology.H1π (Rep.res (Subgroup.subtype H) A)).hom
          |>.quotKerEquivOfSurjective
            ((ModuleCat.epi_iff_surjective
              (groupCohomology.H1π
                (Rep.res (Subgroup.subtype H) A))).1 inferInstance)).symm
          (groupCohomology.H1π (Rep.res (Subgroup.subtype H) A) f)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end groupCohomology
