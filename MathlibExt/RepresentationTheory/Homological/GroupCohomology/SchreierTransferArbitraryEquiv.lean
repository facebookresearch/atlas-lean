/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.GroupTheory.SchreierTransversalEquiv
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionEquiv
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryDifferential
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryNaturality

/-!
# Schreier transfer under an equivalence of groups

For e : G ≃* G′, the image e(T) of a finite right transversal T for H is a right transversal
for e(H). The representative scan and subgroup factor tuple commute with e, so the degree-n
transfer for e(T), pulled back to G, is the degree-n transfer for T after pulling H-cochains
back along H ≃* e(H).

The equality holds on cochains, cochain complexes and cohomology in every degree. It also
holds with a G-equivariant coefficient morphism from the pulled-back G′-representation to a
G-representation.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G G' : Type u} [CommRing k] [Group G] [Group G']
variable {H : Subgroup G}

/-- Finite index of a subgroup image under a group equivalence.

For e : G ≃* G′ and finite-index H ≤ G, the image subgroup e(H) has finite index in G′. -/
noncomputable local instance corestrictionArbitraryEquivMapFiniteIndex
    (e : G ≃* G') [H.FiniteIndex] :
    (H.map e.toMonoidHom).FiniteIndex :=
  Subgroup.FiniteIndex.map_of_surjective H e.surjective

/-- Finite representatives for group-equivalence transfer sums.

A right transversal for a finite-index subgroup is given a finite enumeration for transfer
under group equivalences. -/
noncomputable local instance corestrictionArbitraryEquivFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- Finite representatives of the transported transversal.

For e : G ≃* G′ and finite-index H, the image transversal e(T) is finitely enumerated. -/
noncomputable local instance corestrictionArbitraryMappedRepresentativeFintype
    (e : G ≃* G') (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.mapMulEquiv e : Set G') :=
  @Fintype.ofFinite _ (T.mapMulEquiv e).2.finite_right

/-- The tuple transfer formula after group transport.

Pulling back the transfer for e(T) along e equals transferring with T after applying H ≃* e(H)
to each subgroup tuple coordinate. The coefficients are the G′-representation restricted along
e. -/
theorem corestrictionCochain_mapMulEquiv
    (e : G ≃* G') (A : Rep k G')
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (f : (Fin n → H.map e.toMonoidHom) → A) :
    (fun g ↦ corestrictionCochain A (T.mapMulEquiv e) n f
      (fun i ↦ e (g i))) =
      corestrictionCochain (Rep.res e.toMonoidHom A) T n
        (fun q ↦ f (fun i ↦ H.mapMulEquivEquiv e (q i))) := by
  funext g
  rw [corestrictionCochain_apply, corestrictionCochain_apply]
  calc
    (∑ t : ((T.mapMulEquiv e : Set G')),
        A.ρ (t : G')⁻¹
          (f ((T.mapMulEquiv e).schreierFactorTuple t
            (fun i ↦ e (g i))))) =
      ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f ((T.mapMulEquiv e).schreierFactorTuple
            (T.mapMulEquivRepEquiv e t) (fun i ↦ e (g i)))) :=
      ((T.mapMulEquivRepEquiv e).sum_comp
        (fun t : ((T.mapMulEquiv e : Set G')) ↦
          A.ρ (t : G')⁻¹
            (f ((T.mapMulEquiv e).schreierFactorTuple t
              (fun i ↦ e (g i)))))).symm
    _ = ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f (fun i ↦ H.mapMulEquivEquiv e
            (T.schreierFactorTuple t g i))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [T.mapMulEquiv_schreierFactorTuple e]
    _ = ∑ t : (T : Set G),
        (Rep.res e.toMonoidHom A).ρ (t : G)⁻¹
          (f (fun i ↦ H.mapMulEquivEquiv e
            (T.schreierFactorTuple t g i))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact congrArg
        (fun q : G' ↦ A.ρ q
          (f (fun i ↦ H.mapMulEquivEquiv e
            (T.schreierFactorTuple t g i))))
        (map_inv e (t : G)).symm

/-- The cochain-complex square for group transport.

The transfer cochain map for e(T) followed by pullback along e equals pullback along H ≃*
e(H), with its coefficient comparison, followed by the transfer cochain map for T. -/
theorem corestrictionCochains_mapMulEquiv
    (e : G ≃* G') (A : Rep k G')
    (T : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCochains A (T.mapMulEquiv e) ≫
        groupCohomology.cochainsMap e.toMonoidHom
          (𝟙 (Rep.res e.toMonoidHom A)) =
      groupCohomology.cochainsMap
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom ≫
        corestrictionCochains (Rep.res e.toMonoidHom A) T := by
  ext n f g
  exact congrFun (corestrictionCochain_mapMulEquiv e A T n f) g

set_option backward.isDefEq.respectTransparency false in
/-- The arbitrary-degree cohomology square for group transport.

In degree n, pullback along e after transfer from e(H) to G′ equals transfer from H to G after
pullback along the induced subgroup equivalence. -/
theorem corestrictionOfRightTransversal_mulEquiv
    (e : G ≃* G') (A : Rep k G')
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A (T.mapMulEquiv e) n ≫
        groupCohomology.map e.toMonoidHom
          (𝟙 (Rep.res e.toMonoidHom A)) n =
      groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom n ≫
        corestrictionOfRightTransversal
          (Rep.res e.toMonoidHom A) T n := by
  simpa only [corestrictionOfRightTransversal,
    ← HomologicalComplex.homologyMap_comp] using
    congrArg (fun q ↦ HomologicalComplex.homologyMap q n)
      (corestrictionCochains_mapMulEquiv e A T)

/-- Elementwise group transport of a transferred class.

For x ∈ Hⁿ(e(H),A|e(H)), pulling its transferred class back to G gives the T-transfer of its
pullback to H, using the restricted coefficient representation. -/
theorem corestrictionOfRightTransversal_mulEquiv_apply
    (e : G ≃* G') (A : Rep k G')
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (x : groupCohomology
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) n) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) n
        (corestrictionOfRightTransversal A (T.mapMulEquiv e) n x) =
      corestrictionOfRightTransversal (Rep.res e.toMonoidHom A) T n
        (groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom n x) := by
  exact ConcreteCategory.congr_hom
    (corestrictionOfRightTransversal_mulEquiv e A T n) x

/-- Elementwise simultaneous group and coefficient transport.

For φ : e* A → B, the pullback-and-coefficient image of an e(T)-transferred class equals the
T-transfer of its subgroup pullback with the restricted coefficient morphism. -/
theorem corestrictionOfRightTransversal_mulEquiv_hom_apply
    (e : G ≃* G') {A : Rep k G'} {B : Rep k G}
    (phi : Rep.res e.toMonoidHom A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (x : groupCohomology
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) n) :
    groupCohomology.map e.toMonoidHom phi n
        (corestrictionOfRightTransversal A (T.mapMulEquiv e) n x) =
      corestrictionOfRightTransversal B T n
        (groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H phi) n x) := by
  have hambient :
      groupCohomology.map e.toMonoidHom phi n =
        groupCohomology.map e.toMonoidHom
            (𝟙 (Rep.res e.toMonoidHom A)) n ≫
          groupCohomology.map (MonoidHom.id G) phi n := by
    rw [← groupCohomology.map_comp]
    rfl
  have hsubgroup :
      groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H phi) n =
        groupCohomology.map
            (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom n ≫
          groupCohomology.map (MonoidHom.id H)
            ((Rep.resFunctor (Subgroup.subtype H)).map phi) n := by
    rw [← groupCohomology.map_comp]
    rfl
  calc
    groupCohomology.map e.toMonoidHom phi n
        (corestrictionOfRightTransversal A (T.mapMulEquiv e) n x) =
      groupCohomology.map (MonoidHom.id G) phi n
        (groupCohomology.map e.toMonoidHom
          (𝟙 (Rep.res e.toMonoidHom A)) n
          (corestrictionOfRightTransversal A
            (T.mapMulEquiv e) n x)) := by
      rw [hambient]
      rfl
    _ = groupCohomology.map (MonoidHom.id G) phi n
        (corestrictionOfRightTransversal
          (Rep.res e.toMonoidHom A) T n
          (groupCohomology.map
            (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom n x)) := by
      rw [corestrictionOfRightTransversal_mulEquiv_apply e A T n x]
    _ = corestrictionOfRightTransversal B T n
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map phi) n
          (groupCohomology.map
            (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom n x)) :=
      corestrictionOfRightTransversal_naturality_apply phi T n _
    _ = corestrictionOfRightTransversal B T n
        (groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H phi) n x) := by
      congr 1
      rw [hsubgroup]
      rfl

/-- The cohomology square for group and coefficient transport.

For e : G ≃* G′ and φ : e* A → B, transfer along e(H) followed by the group-and-coefficient
map equals the subgroup group-and-coefficient map followed by transfer along H, in every
degree. -/
theorem corestrictionOfRightTransversal_mulEquiv_hom
    (e : G ≃* G') {A : Rep k G'} {B : Rep k G}
    (phi : Rep.res e.toMonoidHom A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A (T.mapMulEquiv e) n ≫
        groupCohomology.map e.toMonoidHom phi n =
      groupCohomology.map
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H phi) n ≫
        corestrictionOfRightTransversal B T n := by
  ext x
  exact corestrictionOfRightTransversal_mulEquiv_hom_apply
    e phi T n x

end groupCohomology
