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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionTransitivity
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality

/-!
# Transitivity of canonical degree-three corestriction

For a subgroup chain `K ≤ H ≤ G`, compatible product right transversals
identify direct degree-three transfer with the composite transfer through
`H`.  Transversal independence then gives transitivity of canonical `H³`
corestriction.

No field-theoretic, Kummer, norm-residue, or Bloch--Kato claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G} {K : Subgroup H}

noncomputable local instance corestrictionH3TransitivityTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

noncomputable local instance corestrictionH3TransitivityMapFiniteIndex
    [K.FiniteIndex] [H.FiniteIndex] : (K.map H.subtype).FiniteIndex :=
  finiteIndex_map_subtype

/-- Cochain-level transitivity for the compatible product right transversal
in degree three. -/
theorem corestrictionCochainThree_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : (K.map H.subtype) × (K.map H.subtype) ×
      (K.map H.subtype) → A) :
    corestrictionCochainThree A (S.product T) f =
      corestrictionCochainThree A T
        (corestrictionCochainThree (Rep.res (Subgroup.subtype H) A) S
          (fun p => f
            (K.equivMapOfInjective H.subtype H.subtype_injective p.1,
              K.equivMapOfInjective H.subtype H.subtype_injective p.2.1,
              K.equivMapOfInjective H.subtype H.subtype_injective p.2.2))) := by
  funext p
  rcases p with ⟨g₁, g₂, g₃⟩
  rw [corestrictionCochainThree_apply, corestrictionCochainThree_apply]
  simp_rw [corestrictionCochainThree_apply]
  calc
    (∑ r : ((S.product T : Set G)),
        A.ρ (r : G)⁻¹
          (f ((S.product T).schreierFactor r g₁,
            (S.product T).schreierFactor
              ((S.product T).schreierRep r g₁) g₂,
            (S.product T).schreierFactor
              ((S.product T).schreierRep
                ((S.product T).schreierRep r g₁) g₂) g₃))) =
      ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f ((S.product T).schreierFactor (S.productEquiv T p) g₁,
            (S.product T).schreierFactor
              ((S.product T).schreierRep (S.productEquiv T p) g₁) g₂,
            (S.product T).schreierFactor
              ((S.product T).schreierRep
                ((S.product T).schreierRep (S.productEquiv T p) g₁) g₂) g₃)) :=
      ((S.productEquiv T).sum_comp
        (fun r : ((S.product T : Set G)) =>
          A.ρ (r : G)⁻¹
            (f ((S.product T).schreierFactor r g₁,
              (S.product T).schreierFactor
                ((S.product T).schreierRep r g₁) g₂,
              (S.product T).schreierFactor
                ((S.product T).schreierRep
                  ((S.product T).schreierRep r g₁) g₂) g₃)))).symm
    _ = ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f (K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor p.1 (T.schreierFactor p.2 g₁)),
            K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor
                (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
                (T.schreierFactor (T.schreierRep p.2 g₁) g₂)),
            K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor
                (S.schreierRep
                  (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
                  (T.schreierFactor (T.schreierRep p.2 g₁) g₂))
                (T.schreierFactor
                  (T.schreierRep (T.schreierRep p.2 g₁) g₂) g₃)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [S.product_schreierFactor T p.1 p.2 g₁,
        S.product_schreierRep T p.1 p.2 g₁,
        S.product_schreierFactor T
          (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
          (T.schreierRep p.2 g₁) g₂,
        S.product_schreierRep T
          (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
          (T.schreierRep p.2 g₁) g₂,
        S.product_schreierFactor T
          (S.schreierRep
            (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
            (T.schreierFactor (T.schreierRep p.2 g₁) g₂))
          (T.schreierRep (T.schreierRep p.2 g₁) g₂) g₃]
    _ = ∑ t : (T : Set G), ∑ s : (S : Set H),
        A.ρ (t : G)⁻¹
          (A.ρ ((s : H) : G)⁻¹
            (f (K.equivMapOfInjective H.subtype H.subtype_injective
                  (S.schreierFactor s (T.schreierFactor t g₁)),
              K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor
                  (S.schreierRep s (T.schreierFactor t g₁))
                  (T.schreierFactor (T.schreierRep t g₁) g₂)),
              K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor
                  (S.schreierRep
                    (S.schreierRep s (T.schreierFactor t g₁))
                    (T.schreierFactor (T.schreierRep t g₁) g₂))
                  (T.schreierFactor
                    (T.schreierRep (T.schreierRep t g₁) g₂) g₃))))) := by
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
                    (T.schreierFactor (T.schreierRep t g₁) g₂)),
                K.equivMapOfInjective H.subtype H.subtype_injective
                  (S.schreierFactor
                    (S.schreierRep
                      (S.schreierRep s (T.schreierFactor t g₁))
                      (T.schreierFactor (T.schreierRep t g₁) g₂))
                    (T.schreierFactor
                      (T.schreierRep (T.schreierRep t g₁) g₂) g₃))))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_sum]

/-- Cocycle-level transitivity for compatible product right transversals in
degree three. -/
theorem corestrictionCocyclesThree_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : cocycles₃
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionCocyclesThree A (S.product T) f =
      corestrictionCocyclesThree A T
        (corestrictionCocyclesThree (Rep.res (Subgroup.subtype H) A) S
          (mapCocycles₃
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom f)) := by
  apply cocycles₃_ext
  intro g₁ g₂ g₃
  change corestrictionCochainThree A (S.product T) f (g₁, g₂, g₃) =
    corestrictionCochainThree A T
      (corestrictionCochainThree (Rep.res (Subgroup.subtype H) A) S
        (fun p => f
          (K.equivMapOfInjective H.subtype H.subtype_injective p.1,
            K.equivMapOfInjective H.subtype H.subtype_injective p.2.1,
            K.equivMapOfInjective H.subtype H.subtype_injective p.2.2)))
      (g₁, g₂, g₃)
  exact congrFun (corestrictionCochainThree_product A S T f) (g₁, g₂, g₃)

/-- Chosen-transversal degree-three corestriction is transitive for
compatible product transversals. -/
theorem corestrictionH3OfRightTransversal_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH3OfRightTransversal A (S.product T) x =
      corestrictionH3OfRightTransversal A T
        (corestrictionH3OfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S
          (map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 3 x)) := by
  induction x using H3_induction_on with
  | _ f =>
      rw [corestrictionH3OfRightTransversal_H3π]
      have hmap := H3π_comp_map_apply
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (mapSubtypeResIso (H := H) (K := K) A).hom f
      rw [hmap, corestrictionH3OfRightTransversal_H3π,
        corestrictionH3OfRightTransversal_H3π]
      exact congrArg (H3π A)
        (corestrictionCocyclesThree_product A S T f)

/-- Canonical degree-three finite-index corestriction is transitive along a
subgroup chain. -/
theorem corestrictionH3_trans (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH3 (H := K.map H.subtype) A x =
      corestrictionH3 (H := H) A
        (corestrictionH3 (H := K) (Rep.res (Subgroup.subtype H) A)
          (map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 3 x)) := by
  let S : K.RightTransversal := default
  let T : H.RightTransversal := default
  rw [corestrictionH3_eq_of_rightTransversal A (S.product T),
    corestrictionH3_eq_of_rightTransversal A T,
    corestrictionH3_eq_of_rightTransversal
      (Rep.res (Subgroup.subtype H) A) S]
  exact corestrictionH3OfRightTransversal_product A S T x

end groupCohomology
