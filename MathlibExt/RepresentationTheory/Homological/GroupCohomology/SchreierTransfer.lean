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
# Schreier data for low-degree group-cohomological transfer

For a subgroup `H ≤ G` and a chosen right transversal `T`, every product
`t * g`, with `t ∈ T`, has a unique decomposition

`t * g = h(t,g) * overline(t * g)`

with `h(t,g) ∈ H` and `overline(t * g) ∈ T`.  This file packages the
representative and factor, proves their identity and multiplication laws, and
records the resulting permutation of the transversal.  It then defines the
degree-zero norm and the degree-one cochain sum used by cohomological
corestriction.  The differential identity and one-cocycle calculation give a
degree-one cohomology map for each chosen transversal.

Independence of that choice is not proved here, so no canonical
transversal-free corestriction is defined.  No degree-two transfer,
projection formula, norm-residue comparison, or Kummer-Steinberg vanishing is
asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- A finite-index right transversal has its actual finite type of representatives. -/
noncomputable local instance corestrictionRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Degree-zero norm associated to a chosen finite right transversal. -/
noncomputable def corestrictionZero (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] : A →ₗ[k] A := by
  exact ∑ t : (T : Set G), A.ρ (t : G)⁻¹

@[simp]
theorem corestrictionZero_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (a : A) :
    corestrictionZero A T a =
      ∑ t : (T : Set G), A.ρ (t : G)⁻¹ a := by
  simp [corestrictionZero]

/-- Degree-one cochain sum associated to a chosen finite right transversal.
The input is a cochain for the restricted `H`-representation and the output
is a cochain for `G`. -/
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

@[simp]
theorem corestrictionCochainOne_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) (g : G) :
    corestrictionCochainOne A T f g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.schreierFactor t g)) := by
  rfl

/-- A single summand of the transferred coboundary, rewritten using the
Schreier decomposition. -/
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

/-- Reindexing the first half of the transferred coboundary by the
permutation of the transversal induced by `g`. -/
theorem sum_rho_mul_schreierRep_inv (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (a : A) (g : G) :
    ∑ t : (T : Set G), A.ρ (g * (T.schreierRep t g : G)⁻¹) a =
      ∑ t : (T : Set G), A.ρ (g * (t : G)⁻¹) a :=
  (T.schreierRepEquiv g).sum_comp
    (fun t : (T : Set G) => A.ρ (g * (t : G)⁻¹) a)

/-- Degree-zero and degree-one transfer commute with the first
inhomogeneous differential: `cor(d a) = d(N a)`. -/
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

/-- A single summand of the transfer of a one-cocycle, expanded using the
Schreier factor identity. -/
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

/-- Reindexing the first sum in the transferred one-cocycle equation. -/
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

/-- The chosen-transversal degree-one cochain transfer sends one-cocycles to
one-cocycles. -/
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

/-- The chosen-transversal degree-one cochain transfer restricted to
one-cocycles. -/
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

@[simp]
theorem coe_corestrictionCocyclesOne (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A)) :
    (corestrictionCocyclesOne A T f : G → A) =
      corestrictionCochainOne A T f :=
  rfl

/-- The H¹ class of a transferred one-cocycle before descending through
the source H¹ quotient. -/
noncomputable def corestrictionCocycleOneClass (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H1 A :=
  (groupCohomology.H1π A).hom.comp (corestrictionCocyclesOne A T)

/-- Transferred one-cocycle classes annihilate source coboundaries. -/
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

/-- Degree-one cohomological transfer associated to a chosen finite right
transversal.  Independence of the transversal is not asserted here. -/
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

/-- The chosen-transversal H¹ transfer computes on a presented class by
transferring its one-cocycle representative. -/
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
