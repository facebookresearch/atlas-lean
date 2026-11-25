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
# Arbitrary Schreier transfer under group equivalences

Transporting a right transversal along an equivalence of ambient groups
commutes with its complete Schreier scan and factor tuple.  Consequently
the associated Schreier transfer commutes with change of groups on
cochains and cohomology in every degree.
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

noncomputable local instance corestrictionArbitraryEquivMapFiniteIndex
    (e : G ≃* G') [H.FiniteIndex] :
    (H.map e.toMonoidHom).FiniteIndex :=
  Subgroup.FiniteIndex.map_of_surjective H e.surjective

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionArbitraryEquivFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- The actual mapped representative type is finite under the original
subgroup finite-index hypothesis. -/
noncomputable local instance corestrictionArbitraryMappedRepresentativeFintype
    (e : G ≃* G') (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.mapMulEquiv e : Set G') :=
  @Fintype.ofFinite _ (T.mapMulEquiv e).2.finite_right

/-- Arbitrary-degree cochain transfer commutes with transport by an
ambient multiplicative equivalence. -/
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

/-- Transport by an ambient group equivalence commutes with arbitrary
Schreier transfer as a square of inhomogeneous cochain maps. -/
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
/-- Chosen-transversal corestriction commutes with transport by an ambient
group equivalence in every cohomological degree. -/
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

/-- Elementwise arbitrary-degree transport of chosen-transversal
corestriction along an ambient group equivalence. -/
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

/-- Simultaneous ambient-group and coefficient naturality of arbitrary-degree
chosen-transversal corestriction. -/
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

/-- Morphism-square form of simultaneous ambient-group and coefficient
naturality for arbitrary chosen-transversal corestriction. -/
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
