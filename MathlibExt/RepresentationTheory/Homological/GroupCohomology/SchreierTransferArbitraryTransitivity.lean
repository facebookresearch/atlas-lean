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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionTransitivity
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryDifferential

/-!
# Transitivity of arbitrary Schreier transfer

For a chain of finite-index subgroups, the arbitrary-degree Schreier
transfer through the product right transversal is the composite of the two
successive transfers.  The proof first identifies the full Schreier scan
and factor tuple for the product transversal, then descends the resulting
cochain identity to cohomology.
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

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionArbitraryTransitivityFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

noncomputable local instance corestrictionArbitraryTransitivityMapFiniteIndex
    [K.FiniteIndex] [H.FiniteIndex] : (K.map H.subtype).FiniteIndex :=
  finiteIndex_map_subtype

/-- Cochain-level transitivity of arbitrary-degree Schreier transfer for
the compatible product right transversal. -/
theorem corestrictionCochain_product
    (A : Rep k G) (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex] (n : ℕ)
    (f : (Fin n → K.map H.subtype) → A) :
    corestrictionCochain A (S.product T) n f =
      corestrictionCochain A T n
        (corestrictionCochain (Rep.res (Subgroup.subtype H) A) S n
          (fun q ↦ f (fun i ↦
            K.equivMapOfInjective H.subtype H.subtype_injective (q i)))) := by
  funext g
  rw [corestrictionCochain_apply, corestrictionCochain_apply]
  simp_rw [corestrictionCochain_apply]
  calc
    (∑ r : ((S.product T : Set G)),
        A.ρ (r : G)⁻¹
          (f ((S.product T).schreierFactorTuple r g))) =
      ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f ((S.product T).schreierFactorTuple
            (S.productEquiv T p) g)) :=
      ((S.productEquiv T).sum_comp
        (fun r : ((S.product T : Set G)) ↦
          A.ρ (r : G)⁻¹
            (f ((S.product T).schreierFactorTuple r g)))).symm
    _ = ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f (fun i ↦
            K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactorTuple p.1
                (T.schreierFactorTuple p.2 g) i))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [S.product_schreierFactorTuple T]
    _ = ∑ t : (T : Set G), ∑ s : (S : Set H),
        A.ρ (t : G)⁻¹
          (A.ρ ((s : H) : G)⁻¹
            (f (fun i ↦
              K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactorTuple s
                  (T.schreierFactorTuple t g) i)))) := by
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
              (f (fun i ↦
                K.equivMapOfInjective H.subtype H.subtype_injective
                  (S.schreierFactorTuple s
                    (T.schreierFactorTuple t g) i)))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_sum]

/-- The arbitrary-degree product-transversal identity as an equality of
inhomogeneous cochain maps. -/
theorem corestrictionCochains_product
    (A : Rep k G) (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex] :
    corestrictionCochains A (S.product T) =
      (groupCohomology.cochainsMap
          (K.equivMapOfInjective H.subtype
            H.subtype_injective).toMonoidHom
          (mapSubtypeResIso (H := H) (K := K) A).hom ≫
        corestrictionCochains (Rep.res (Subgroup.subtype H) A) S) ≫
      corestrictionCochains A T := by
  ext n f g
  exact congrFun (corestrictionCochain_product A S T n f) g

set_option backward.isDefEq.respectTransparency false in
/-- Chosen-transversal corestriction is transitive in every cohomological
degree for compatible product transversals. -/
theorem corestrictionOfRightTransversal_product
    (A : Rep k G) (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A (S.product T) n =
      (groupCohomology.map
          (K.equivMapOfInjective H.subtype
            H.subtype_injective).toMonoidHom
          (mapSubtypeResIso (H := H) (K := K) A).hom n ≫
        corestrictionOfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S n) ≫
      corestrictionOfRightTransversal A T n := by
  simpa only [corestrictionOfRightTransversal,
    ← HomologicalComplex.homologyMap_comp] using
    congrArg (fun q ↦ HomologicalComplex.homologyMap q n)
      (corestrictionCochains_product A S T)

/-- Elementwise arbitrary-degree transitivity for compatible product right
transversals. -/
theorem corestrictionOfRightTransversal_product_apply
    (A : Rep k G) (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex] (n : ℕ)
    (x : groupCohomology
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A) n) :
    corestrictionOfRightTransversal A (S.product T) n x =
      corestrictionOfRightTransversal A T n
        (corestrictionOfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S n
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype
              H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom n x)) := by
  exact ConcreteCategory.congr_hom
    (corestrictionOfRightTransversal_product A S T n) x

end groupCohomology
