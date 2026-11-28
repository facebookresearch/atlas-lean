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
# Schreier transfer on binary cochains and degree-two classes

Let k be a commutative ring, A a G-representation, H ≤ G a finite-index subgroup and T a right
transversal. For t₀ = t, write t₀g₁ = a₀t₁ and t₁g₂ = a₁t₂. The binary transfer is
cor_T²(f)(g₁,g₂) = ∑ₜ ρ(t⁻¹)f(a₀,a₁).

It commutes with the degree-one differential d¹b(g₁,g₂) = ρ(g₁)b(g₂) − b(g₁g₂) + b(g₁),
preserves two-cocycles, and induces a linear map H²(H,A|H) → H²(G,A). On a represented class
this map is computed by the transferred binary cocycle.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for binary cochain transfer.

The finite-index hypothesis gives a finite enumeration of T for the degree-two sum. -/
noncomputable local instance corestrictionDegreeTwoRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-two Schreier cochain transfer.

For f : H × H → A and successive factors a₀,a₁ of t₀g₁ = a₀t₁ and t₁g₂ = a₁t₂, sum
ρ(t₀⁻¹)f(a₀,a₁) over t₀ ∈ T. This is a k-linear map from binary H-cochains to binary
G-cochains. -/
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

/-- The binary representative formula for transfer.

At (g₁,g₂), the transfer is ∑ₜ ρ(t⁻¹)f(a(t,g₁),a(r(t,g₁),g₂)). -/
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

/-- An inverse-weighted degree-one differential term.

For successive factors a₀,a₁, the weighted differential ρ(t⁻¹)d¹b(a₀,a₁) has the three terms
with signs +,−,+: the updated leading action, the factor of g₁g₂, and the factor of g₁. -/
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

/-- Binary transfer commutes with the degree-one differential.

For b : H → A, cor_T²(d¹b) = d¹(cor_T¹b), with the restricted H-action on the source and
G-action on the target. -/
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

/-- Reindexing a transfer sum with two remaining factors.

The sum starting at r(t,g₁) on the remaining pair (g₂,g₃), weighted by ρ(g₁r(t,g₁)⁻¹), equals
ρ(g₁) times the ordinary binary transfer sum on that pair. -/
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

/-- The two-cocycle identity on a Schreier scan.

For an H-two-cocycle f and successive factors a₀,a₁,a₂, apply its identity f(a₀a₁,a₂) +
f(a₀,a₁) = ρ(a₀)f(a₁,a₂) + f(a₀,a₁a₂) and then weight by ρ(t⁻¹). The leading action becomes
ρ(g₁r(t,g₁)⁻¹). -/
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

/-- Binary transfer preserves two-cocycles.

An H-two-cocycle for A|H is sent by the chosen-transversal binary transfer to a G-two-cocycle
for A. -/
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

/-- The transfer map on two-cocycles.

Restrict the k-linear binary transfer to obtain Z²(H,A|H) → Z²(G,A). -/
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

/-- The cochain underlying a transferred two-cocycle.

The binary G-cochain underlying corestrictionCocyclesTwo A T f is corestrictionCochainTwo A T
f. -/
@[simp]
theorem coe_corestrictionCocyclesTwo (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A)) :
    (corestrictionCocyclesTwo A T f : G × G → A) =
      corestrictionCochainTwo A T f :=
  rfl

/-- The class of a transferred two-cocycle.

Transfer an H-two-cocycle and project its resulting G-two-cocycle to H²(G,A). -/
noncomputable def corestrictionCocycleTwoClass (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    groupCohomology.cocycles₂ (Rep.res (Subgroup.subtype H) A) →ₗ[k]
      groupCohomology.H2 A :=
  (groupCohomology.H2π A).hom.comp (corestrictionCocyclesTwo A T)

/-- Two-coboundaries vanish under the transferred class map.

The kernel of Z²(H,A|H) → H²(H,A|H) is contained in the kernel of the chosen-transversal
transferred class map to H²(G,A). -/
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

/-- The degree-two cohomology transfer of a right transversal.

The binary transfer descends through the source coboundary quotient to a k-linear map
H²(H,A|H) → H²(G,A). -/
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

/-- Degree-two transfer on a binary cocycle class.

Applying the chosen H² transfer to the class of an H-two-cocycle gives the class of its
transferred G-two-cocycle. -/
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
