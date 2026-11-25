/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Original implementation: Avocado.
module

public import MathlibExt.GroupTheory.SchreierTransversalComposition

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionNaturality

/-!
# Transitivity prerequisites for finite-index Schreier corestriction

For a subgroup `H ≤ G`, a subgroup `K ≤ H`, and right transversals for both
steps, multiplying representatives gives a right transversal for
`K.map H.subtype ≤ G`.  This file packages that product transversal and its
Schreier decomposition, then uses transversal independence to compare direct
and iterated corestriction.

No field-theoretic, Kummer, or norm-residue claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators



namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G} {K : Subgroup H}

/-- A finite-index right transversal has finitely many actual representatives. -/
noncomputable local instance corestrictionTransitivityRightTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- The image of a finite-index subgroup of a finite-index subgroup has
finite index in the ambient group. -/
theorem finiteIndex_map_subtype [K.FiniteIndex] [H.FiniteIndex] :
    (K.map H.subtype).FiniteIndex :=
  ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
      Subgroup.FiniteIndex.index_ne_zero⟩

noncomputable local instance corestrictionTransitivityMapFiniteIndex
    [K.FiniteIndex] [H.FiniteIndex] : (K.map H.subtype).FiniteIndex :=
  finiteIndex_map_subtype

/-- Restricting from `G` to the image of `K` and then along the canonical
equivalence agrees with successive restriction through `H`. -/
noncomputable def mapSubtypeResIso (A : Rep k G) :
    Rep.res
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (Rep.res (Subgroup.subtype (K.map H.subtype)) A) ≅
      Rep.res (Subgroup.subtype K) (Rep.res (Subgroup.subtype H) A) :=
  eqToIso (by rfl)

@[simp]
theorem mapSubtypeResIso_hom_apply (A : Rep k G)
    (x : A) : (mapSubtypeResIso (H := H) (K := K) A).hom x = x :=
  rfl

/-- Cochain-level transitivity for the compatible product right
transversal in degree one. -/
theorem corestrictionCochainOne_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : K.map H.subtype → A) :
    corestrictionCochainOne A (S.product T) f =
      corestrictionCochainOne A T
        (corestrictionCochainOne (Rep.res (Subgroup.subtype H) A) S
          (fun k => f
            (K.equivMapOfInjective H.subtype H.subtype_injective k))) := by
  funext g
  rw [corestrictionCochainOne_apply, corestrictionCochainOne_apply]
  simp_rw [corestrictionCochainOne_apply]
  calc
    (∑ r : ((S.product T : Set G)),
        A.ρ (r : G)⁻¹ (f ((S.product T).schreierFactor r g))) =
      ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f ((S.product T).schreierFactor (S.productEquiv T p) g)) :=
      ((S.productEquiv T).sum_comp
        (fun r : ((S.product T : Set G)) =>
          A.ρ (r : G)⁻¹ (f ((S.product T).schreierFactor r g)))).symm
    _ = ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f (K.equivMapOfInjective H.subtype H.subtype_injective
            (S.schreierFactor p.1 (T.schreierFactor p.2 g)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [S.product_schreierFactor T p.1 p.2 g]
    _ = ∑ t : (T : Set G), ∑ s : (S : Set H),
        A.ρ (t : G)⁻¹
          (A.ρ ((s : H) : G)⁻¹
            (f (K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor s (T.schreierFactor t g))))) := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      unfold Subgroup.RightTransversal.productRep
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    _ = ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (∑ s : (S : Set H),
            A.ρ ((s : H) : G)⁻¹
              (f (K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor s (T.schreierFactor t g))))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_sum]

/-- Cocycle-level transitivity for the compatible product right transversal
in degree one. -/
theorem corestrictionCocyclesOne_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionCocyclesOne A (S.product T) f =
      corestrictionCocyclesOne A T
        (corestrictionCocyclesOne (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.mapCocycles₁
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom f)) := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change corestrictionCochainOne A (S.product T) f g =
    corestrictionCochainOne A T
      (corestrictionCochainOne (Rep.res (Subgroup.subtype H) A) S
        (fun k => f
          (K.equivMapOfInjective H.subtype H.subtype_injective k))) g
  exact congrFun (corestrictionCochainOne_product A S T f) g

/-- Chosen-transversal degree-one corestriction is transitive for compatible
product transversals. -/
theorem corestrictionH1OfRightTransversal_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH1OfRightTransversal A (S.product T) x =
      corestrictionH1OfRightTransversal A T
        (corestrictionH1OfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 1 x)) := by
  induction x using groupCohomology.H1_induction_on with
  | _ f =>
      rw [corestrictionH1OfRightTransversal_H1π]
      have hmap := groupCohomology.H1π_comp_map_apply
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (mapSubtypeResIso (H := H) (K := K) A).hom f
      rw [hmap, corestrictionH1OfRightTransversal_H1π,
        corestrictionH1OfRightTransversal_H1π]
      exact congrArg (groupCohomology.H1π A)
        (corestrictionCocyclesOne_product A S T f)

/-- Canonical degree-one finite-index corestriction is transitive along a
subgroup chain. -/
theorem corestrictionH1_trans (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH1 (H := K.map H.subtype) A x =
      corestrictionH1 (H := H) A
        (corestrictionH1 (H := K) (Rep.res (Subgroup.subtype H) A)
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 1 x)) := by
  let S : K.RightTransversal := default
  let T : H.RightTransversal := default
  rw [corestrictionH1_eq_of_rightTransversal A (S.product T),
    corestrictionH1_eq_of_rightTransversal A T,
    corestrictionH1_eq_of_rightTransversal
      (Rep.res (Subgroup.subtype H) A) S]
  exact corestrictionH1OfRightTransversal_product A S T x

/-- Cochain-level transitivity for the compatible product right
transversal in degree two. -/
theorem corestrictionCochainTwo_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : (K.map H.subtype) × (K.map H.subtype) → A) :
    corestrictionCochainTwo A (S.product T) f =
      corestrictionCochainTwo A T
        (corestrictionCochainTwo (Rep.res (Subgroup.subtype H) A) S
          (fun p => f
            (K.equivMapOfInjective H.subtype H.subtype_injective p.1,
              K.equivMapOfInjective H.subtype H.subtype_injective p.2))) := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochainTwo_apply, corestrictionCochainTwo_apply]
  simp_rw [corestrictionCochainTwo_apply]
  calc
    (∑ r : ((S.product T : Set G)),
        A.ρ (r : G)⁻¹
          (f ((S.product T).schreierFactor r g₁,
            (S.product T).schreierFactor
              ((S.product T).schreierRep r g₁) g₂))) =
      ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f ((S.product T).schreierFactor (S.productEquiv T p) g₁,
            (S.product T).schreierFactor
              ((S.product T).schreierRep (S.productEquiv T p) g₁) g₂)) :=
      ((S.productEquiv T).sum_comp
        (fun r : ((S.product T : Set G)) =>
          A.ρ (r : G)⁻¹
            (f ((S.product T).schreierFactor r g₁,
              (S.product T).schreierFactor
                ((S.product T).schreierRep r g₁) g₂)))).symm
    _ = ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f (K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor p.1 (T.schreierFactor p.2 g₁)),
            K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor
                (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
                (T.schreierFactor (T.schreierRep p.2 g₁) g₂)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [S.product_schreierFactor T p.1 p.2 g₁,
        S.product_schreierRep T p.1 p.2 g₁,
        S.product_schreierFactor T
          (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
          (T.schreierRep p.2 g₁) g₂]
    _ = ∑ t : (T : Set G), ∑ s : (S : Set H),
        A.ρ (t : G)⁻¹
          (A.ρ ((s : H) : G)⁻¹
            (f (K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor s (T.schreierFactor t g₁)),
              K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor
                  (S.schreierRep s (T.schreierFactor t g₁))
                  (T.schreierFactor (T.schreierRep t g₁) g₂))))) := by
      rw [Fintype.sum_prod_type_right]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      unfold Subgroup.RightTransversal.productRep
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    _ = ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (∑ s : (S : Set H),
            A.ρ ((s : H) : G)⁻¹
              (f (K.equivMapOfInjective H.subtype H.subtype_injective
                  (S.schreierFactor s (T.schreierFactor t g₁)),
                K.equivMapOfInjective H.subtype H.subtype_injective
                  (S.schreierFactor
                    (S.schreierRep s (T.schreierFactor t g₁))
                    (T.schreierFactor (T.schreierRep t g₁) g₂))))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_sum]

/-- Cocycle-level transitivity for the compatible product right transversal
in degree two. -/
theorem corestrictionCocyclesTwo_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionCocyclesTwo A (S.product T) f =
      corestrictionCocyclesTwo A T
        (corestrictionCocyclesTwo (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.mapCocycles₂
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom f)) := by
  apply groupCohomology.cocycles₂_ext
  intro g₁ g₂
  change corestrictionCochainTwo A (S.product T) f (g₁, g₂) =
    corestrictionCochainTwo A T
      (corestrictionCochainTwo (Rep.res (Subgroup.subtype H) A) S
        (fun p => f
          (K.equivMapOfInjective H.subtype H.subtype_injective p.1,
            K.equivMapOfInjective H.subtype H.subtype_injective p.2)))
      (g₁, g₂)
  exact congrFun (corestrictionCochainTwo_product A S T f) (g₁, g₂)

/-- Chosen-transversal degree-two corestriction is transitive for compatible
product transversals. -/
theorem corestrictionH2OfRightTransversal_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH2OfRightTransversal A (S.product T) x =
      corestrictionH2OfRightTransversal A T
        (corestrictionH2OfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 2 x)) := by
  induction x using groupCohomology.H2_induction_on with
  | _ f =>
      rw [corestrictionH2OfRightTransversal_H2π]
      have hmap := groupCohomology.H2π_comp_map_apply
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (mapSubtypeResIso (H := H) (K := K) A).hom f
      rw [hmap, corestrictionH2OfRightTransversal_H2π,
        corestrictionH2OfRightTransversal_H2π]
      exact congrArg (groupCohomology.H2π A)
        (corestrictionCocyclesTwo_product A S T f)

/-- Canonical degree-two finite-index corestriction is transitive along a
subgroup chain. -/
theorem corestrictionH2_trans (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH2 (H := K.map H.subtype) A x =
      corestrictionH2 (H := H) A
        (corestrictionH2 (H := K) (Rep.res (Subgroup.subtype H) A)
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 2 x)) := by
  let S : K.RightTransversal := default
  let T : H.RightTransversal := default
  rw [corestrictionH2_eq_of_rightTransversal A (S.product T),
    corestrictionH2_eq_of_rightTransversal A T,
    corestrictionH2_eq_of_rightTransversal
      (Rep.res (Subgroup.subtype H) A) S]
  exact corestrictionH2OfRightTransversal_product A S T x

end groupCohomology
