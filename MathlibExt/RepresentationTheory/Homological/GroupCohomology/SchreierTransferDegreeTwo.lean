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

/-!
# Degree-two chosen-transversal group-cohomological transfer

For a finite-index subgroup `H ≤ G`, a chosen right transversal `T`, and a
`G`-representation `A`, this file defines the standard degree-two
inhomogeneous cochain transfer

`cor²(f)(g₁,g₂) = Σ t, t⁻¹ · f(h(t,g₁), h(overline(tg₁),g₂))`.

It proves compatibility with the degree-one differential, sends two-cocycles
to two-cocycles and two-coboundaries to two-coboundaries, and descends to a
degree-two cohomology map.  All statements retain the chosen transversal
explicitly.  No independence of that choice, projection formula, norm-residue
comparison, or Kummer-Steinberg vanishing is asserted.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance corestrictionDegreeTwoRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Degree-two cochain transfer associated to a chosen finite right
transversal. -/
noncomputable def corestrictionCochainTwo (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    (H × H → A) →ₗ[k] (G × G → A) where
  toFun f p := ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹
      (f (T.schreierFactor t p.1,
        T.schreierFactor (T.schreierRep t p.1) p.2))
  map_add' f₁ f₂ := by
    funext p
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext p
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem corestrictionCochainTwo_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H → A) (g₁ g₂ : G) :
    corestrictionCochainTwo A T f (g₁, g₂) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (f (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂)) :=
  rfl

/-- A single summand in the compatibility of degree-two transfer with
`d₁₂`. -/
theorem corestrictionCochainTwo_d₁₂_term (A : Rep k G)
    (T : H.RightTransversal) (b : H → A)
    (t : (T : Set G)) (g₁ g₂ : G) :
    A.ρ (t : G)⁻¹
        ((groupCohomology.d₁₂ (Rep.res (Subgroup.subtype H) A)).hom b
          (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂)) =
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (b (T.schreierFactor (T.schreierRep t g₁) g₂)) -
        A.ρ (t : G)⁻¹ (b (T.schreierFactor t (g₁ * g₂))) +
          A.ρ (t : G)⁻¹ (b (T.schreierFactor t g₁)) := by
  simp only [d₁₂_hom_apply, map_add, map_sub]
  rw [← T.schreierFactor_mul t g₁ g₂]
  congr 2
  change A.ρ (t : G)⁻¹
      (A.ρ (T.schreierFactor t g₁ : G)
        (b (T.schreierFactor (T.schreierRep t g₁) g₂))) = _
  rw [← Module.End.mul_apply, ← map_mul,
    T.inv_mul_schreierFactor t g₁]

/-- Degree-one and degree-two chosen-transversal transfers commute with the
inhomogeneous differential `d₁₂`. -/
theorem corestrictionCochainTwo_d₁₂ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (b : H → A) :
    corestrictionCochainTwo A T
        ((groupCohomology.d₁₂ (Rep.res (Subgroup.subtype H) A)).hom b) =
      (groupCohomology.d₁₂ A).hom (corestrictionCochainOne A T b) := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochainTwo_apply]
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          ((groupCohomology.d₁₂ (Rep.res (Subgroup.subtype H) A)).hom b
            (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂))) =
      ∑ t : (T : Set G),
        (A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (b (T.schreierFactor (T.schreierRep t g₁) g₂)) -
          A.ρ (t : G)⁻¹ (b (T.schreierFactor t (g₁ * g₂))) +
            A.ρ (t : G)⁻¹ (b (T.schreierFactor t g₁))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCochainTwo_d₁₂_term A T b t g₁ g₂
  rw [hterms]
  simp only [d₁₂_hom_apply, corestrictionCochainOne_apply]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_rho_mul_schreierRep_inv_factor]

/-- Reindexing the leading sum in the transferred two-cocycle equation. -/
theorem sum_rho_mul_schreierRep_inv_twoFactor (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H → A) (g₁ g₂ g₃ : G) :
    (∑ t : (T : Set G),
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
        (f (T.schreierFactor (T.schreierRep t g₁) g₂,
          T.schreierFactor
            (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) =
      A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃))) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (f (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (t : G)⁻¹)
          (f (T.schreierFactor t g₂,
            T.schreierFactor (T.schreierRep t g₂) g₃)) :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g₁ * (t : G)⁻¹)
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃)))
    _ = ∑ t : (T : Set G),
        A.ρ g₁
          (A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃))) := by
      rw [map_sum]

/-- A single summand of the transferred two-cocycle equation. -/
theorem corestrictionCochainTwo_cocycle_term (A : Rep k G)
    (T : H.RightTransversal)
    (f : groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ g₃ : G) :
    A.ρ (t : G)⁻¹
        (f (T.schreierFactor t (g₁ * g₂),
            T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃) +
          f (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂)) =
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (f (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) +
        A.ρ (t : G)⁻¹
          (f (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃))) := by
  rw [T.schreierFactor_mul t g₁ g₂,
    T.schreierRep_mul t g₁ g₂,
    T.schreierFactor_mul (T.schreierRep t g₁) g₂ g₃]
  have hf := (groupCohomology.mem_cocycles₂_iff f).mp f.property
    (T.schreierFactor t g₁)
    (T.schreierFactor (T.schreierRep t g₁) g₂)
    (T.schreierFactor
      (T.schreierRep (T.schreierRep t g₁) g₂) g₃)
  rw [hf, map_add]
  congr 1
  change A.ρ (t : G)⁻¹
      (A.ρ (T.schreierFactor t g₁ : G)
        (f (T.schreierFactor (T.schreierRep t g₁) g₂,
          T.schreierFactor
            (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) = _
  rw [← Module.End.mul_apply, ← map_mul,
    T.inv_mul_schreierFactor t g₁]

/-- Degree-two chosen-transversal cochain transfer sends two-cocycles to
two-cocycles. -/
theorem corestrictionCochainTwo_mem_cocycles₂ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionCochainTwo A T f ∈ groupCohomology.cocycles₂ A := by
  rw [groupCohomology.mem_cocycles₂_iff]
  intro g₁ g₂ g₃
  rw [corestrictionCochainTwo_apply, corestrictionCochainTwo_apply,
    corestrictionCochainTwo_apply, corestrictionCochainTwo_apply]
  rw [← Finset.sum_add_distrib]
  simp_rw [← map_add]
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (f (T.schreierFactor t (g₁ * g₂),
              T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃) +
            f (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂))) =
      ∑ t : (T : Set G),
        (A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (f (T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) +
          A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃)))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCochainTwo_cocycle_term A T f t g₁ g₂ g₃
  rw [hterms, Finset.sum_add_distrib,
    sum_rho_mul_schreierRep_inv_twoFactor]

/-- Degree-two cochain transfer restricted to two-cocycles. -/
noncomputable def corestrictionCocyclesTwo (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.cocycles₂ A where
  toFun f := ⟨corestrictionCochainTwo A T f,
    corestrictionCochainTwo_mem_cocycles₂ A T f⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    change corestrictionCochainTwo A T
        ((f₁ + f₂ : groupCohomology.cocycles₂
          (Rep.res (Subgroup.subtype H) A)) : H × H → A) = _
    exact map_add (corestrictionCochainTwo A T)
      (f₁ : H × H → A) (f₂ : H × H → A)
  map_smul' r f := by
    apply Subtype.ext
    change corestrictionCochainTwo A T
        ((r • f : groupCohomology.cocycles₂
          (Rep.res (Subgroup.subtype H) A)) : H × H → A) = _
    exact map_smul (corestrictionCochainTwo A T) r (f : H × H → A)

@[simp]
theorem coe_corestrictionCocyclesTwo (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A)) :
    (corestrictionCocyclesTwo A T f : G × G → A) =
      corestrictionCochainTwo A T f :=
  rfl

/-- The H² class of a transferred two-cocycle before descending through the
source H² quotient. -/
noncomputable def corestrictionCocycleTwoClass (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H2 A :=
  (groupCohomology.H2π A).hom.comp (corestrictionCocyclesTwo A T)

/-- Transferred two-cocycle classes annihilate source two-coboundaries. -/
theorem corestrictionCocycleTwoClass_ker (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    LinearMap.ker
        (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A)).hom ≤
      LinearMap.ker (corestrictionCocycleTwoClass A T) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  apply (groupCohomology.H2π_eq_zero_iff _).2
  have hboundary : (f : H × H → A) ∈
      groupCohomology.coboundaries₂
        (Rep.res (Subgroup.subtype H) A) :=
    (groupCohomology.H2π_eq_zero_iff f).1 hf
  rcases hboundary with ⟨b, hb⟩
  refine ⟨corestrictionCochainOne A T b, ?_⟩
  change (groupCohomology.d₁₂ A).hom (corestrictionCochainOne A T b) =
    corestrictionCochainTwo A T f
  rw [← corestrictionCochainTwo_d₁₂]
  exact congrArg (corestrictionCochainTwo A T) hb

/-- Degree-two cohomological transfer associated to a chosen finite right
transversal.  Independence of the transversal is not asserted here. -/
noncomputable def corestrictionH2OfRightTransversal (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.H2 (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H2 A :=
  let q := (LinearMap.ker
      (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A)).hom).liftQ
    (corestrictionCocycleTwoClass A T)
    (corestrictionCocycleTwoClass_ker A T)
  let e :=
    (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A)).hom
      |>.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective
          (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A))).1
            inferInstance)
  q.comp e.symm.toLinearMap

/-- The chosen-transversal H² transfer computes on a presented class by
transferring its two-cocycle representative. -/
@[simp]
theorem corestrictionH2OfRightTransversal_H2π (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH2OfRightTransversal A T
        (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A) f) =
      groupCohomology.H2π A (corestrictionCocyclesTwo A T f) := by
  change (LinearMap.ker
      (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A)).hom).liftQ
        (corestrictionCocycleTwoClass A T)
        (corestrictionCocycleTwoClass_ker A T)
        (((groupCohomology.H2π (Rep.res (Subgroup.subtype H) A)).hom
          |>.quotKerEquivOfSurjective
            ((ModuleCat.epi_iff_surjective
              (groupCohomology.H2π
                (Rep.res (Subgroup.subtype H) A))).1 inferInstance)).symm
          (groupCohomology.H2π (Rep.res (Subgroup.subtype H) A) f)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end groupCohomology
