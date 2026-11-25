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

public import MathlibExt.GroupTheory.SchreierTransversalEquiv
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionTransitivity

/-!
# Corestriction under an equivalence of ambient groups

This file transports a right transversal along a multiplicative equivalence
and proves that the associated degree-one and degree-two Schreier transfers
commute with the induced change of groups.  Transversal independence then
gives naturality of canonical finite-index corestriction in degrees one and
two.

The coefficient representation is transported by restriction along the
ambient equivalence, with variants for a further explicit coefficient
morphism.  No unrelated coefficient modules are identified without such a
morphism.  No field-theoretic, Kummer, norm-residue, or higher-degree claim is
made here.
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
variable {K : Subgroup H}

/-- The two restrictions of a coefficient representation associated with a
subgroup and an ambient multiplicative equivalence agree on the nose. -/
noncomputable def mulEquivSubgroupResIso (e : G ≃* G')
    (H : Subgroup G) (A : Rep k G') :
    Rep.res (H.mapMulEquivEquiv e).toMonoidHom
        (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) ≅
      Rep.res (Subgroup.subtype H) (Rep.res e.toMonoidHom A) :=
  eqToIso (by rfl)

@[simp]
theorem mulEquivSubgroupResIso_hom_apply (e : G ≃* G')
    (H : Subgroup G) (A : Rep k G') (a : A) :
    (mulEquivSubgroupResIso e H A).hom a = a :=
  rfl

/-- Coefficient comparison for subgroup transport when the image subgroup is
identified with a separately bundled equal subgroup. -/
noncomputable def mulEquivSubgroupResIsoOfEq (e : G ≃* G')
    (H : Subgroup G) (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') (A : Rep k G') :
    Rep.res (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
        (Rep.res (Subgroup.subtype H') A) ≅
      Rep.res (Subgroup.subtype H) (Rep.res e.toMonoidHom A) :=
  eqToIso (by subst H'; rfl)

@[simp]
theorem mulEquivSubgroupResIsoOfEq_hom_apply (e : G ≃* G')
    (H : Subgroup G) (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') (A : Rep k G') (a : A) :
    (mulEquivSubgroupResIsoOfEq e H H' h A).hom a = a := by
  subst H'
  rfl

/-- The coefficient morphism on a transported subgroup induced by a
morphism out of the restricted ambient representation. -/
noncomputable def mulEquivSubgroupResHom (e : G ≃* G')
    (H : Subgroup G) {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B) :
    Rep.res (H.mapMulEquivEquiv e).toMonoidHom
        (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) ⟶
      Rep.res (Subgroup.subtype H) B :=
  (mulEquivSubgroupResIso e H A).hom ≫
    (Rep.resFunctor (Subgroup.subtype H)).map φ

/-- The analogous coefficient morphism when the image subgroup is identified
with a separately bundled equal subgroup. -/
noncomputable def mulEquivSubgroupResHomOfEq (e : G ≃* G')
    (H : Subgroup G) (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B) :
    Rep.res (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
        (Rep.res (Subgroup.subtype H') A) ⟶
      Rep.res (Subgroup.subtype H) B :=
  (mulEquivSubgroupResIsoOfEq e H H' h A).hom ≫
    (Rep.resFunctor (Subgroup.subtype H)).map φ

noncomputable local instance corestrictionEquivMapFiniteIndex
    (e : G ≃* G') [H.FiniteIndex] :
    (H.map e.toMonoidHom).FiniteIndex :=
  Subgroup.FiniteIndex.map_of_surjective H e.surjective

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionEquivRightTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- The actual mapped representative type is finite under the original
subgroup finite-index hypothesis. -/
noncomputable local instance corestrictionEquivMappedRepresentativeFintype
    (e : G ≃* G') (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.mapMulEquiv e : Set G') :=
  @Fintype.ofFinite _ (T.mapMulEquiv e).2.finite_right

/-- Degree-one cochain transfer commutes with transport by an ambient
multiplicative equivalence. -/
theorem corestrictionCochainOne_mapMulEquiv (e : G ≃* G')
    (A : Rep k G') (T : H.RightTransversal) [H.FiniteIndex]
    (f : H.map e.toMonoidHom → A) :
    (fun g => corestrictionCochainOne A (T.mapMulEquiv e) f (e g)) =
      corestrictionCochainOne (Rep.res e.toMonoidHom A) T
        (fun h => f (H.mapMulEquivEquiv e h)) := by
  funext g
  rw [corestrictionCochainOne_apply, corestrictionCochainOne_apply]
  calc
    (∑ t : ((T.mapMulEquiv e : Set G')),
        A.ρ (t : G')⁻¹
          (f ((T.mapMulEquiv e).schreierFactor t (e g)))) =
      ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f ((T.mapMulEquiv e).schreierFactor
            (T.mapMulEquivRepEquiv e t) (e g))) :=
      ((T.mapMulEquivRepEquiv e).sum_comp
        (fun t : ((T.mapMulEquiv e : Set G')) =>
          A.ρ (t : G')⁻¹
            (f ((T.mapMulEquiv e).schreierFactor t (e g))))).symm
    _ = ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [T.mapMulEquiv_schreierFactor e]
    _ = ∑ t : (T : Set G),
        (Rep.res e.toMonoidHom A).ρ (t : G)⁻¹
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact congrArg
        (fun q : G' => A.ρ q
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g))))
        (map_inv e (t : G)).symm

/-- Degree-two cochain transfer commutes with transport by an ambient
multiplicative equivalence. -/
theorem corestrictionCochainTwo_mapMulEquiv (e : G ≃* G')
    (A : Rep k G') (T : H.RightTransversal) [H.FiniteIndex]
    (f : (H.map e.toMonoidHom) × (H.map e.toMonoidHom) → A) :
    (fun p => corestrictionCochainTwo A (T.mapMulEquiv e) f
        (e p.1, e p.2)) =
      corestrictionCochainTwo (Rep.res e.toMonoidHom A) T
        (fun p => f (H.mapMulEquivEquiv e p.1,
          H.mapMulEquivEquiv e p.2)) := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochainTwo_apply, corestrictionCochainTwo_apply]
  calc
    (∑ t : ((T.mapMulEquiv e : Set G')),
        A.ρ (t : G')⁻¹
          (f ((T.mapMulEquiv e).schreierFactor t (e g₁),
            (T.mapMulEquiv e).schreierFactor
              ((T.mapMulEquiv e).schreierRep t (e g₁)) (e g₂)))) =
      ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f ((T.mapMulEquiv e).schreierFactor
                (T.mapMulEquivRepEquiv e t) (e g₁),
            (T.mapMulEquiv e).schreierFactor
              ((T.mapMulEquiv e).schreierRep
                (T.mapMulEquivRepEquiv e t) (e g₁)) (e g₂))) :=
      ((T.mapMulEquivRepEquiv e).sum_comp
        (fun t : ((T.mapMulEquiv e : Set G')) =>
          A.ρ (t : G')⁻¹
            (f ((T.mapMulEquiv e).schreierFactor t (e g₁),
              (T.mapMulEquiv e).schreierFactor
                ((T.mapMulEquiv e).schreierRep t (e g₁)) (e g₂))))).symm
    _ = ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g₁),
            H.mapMulEquivEquiv e
              (T.schreierFactor (T.schreierRep t g₁) g₂))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [T.mapMulEquiv_schreierRep e,
        T.mapMulEquiv_schreierFactor e,
        T.mapMulEquiv_schreierFactor e]
    _ = ∑ t : (T : Set G),
        (Rep.res e.toMonoidHom A).ρ (t : G)⁻¹
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g₁),
            H.mapMulEquivEquiv e
              (T.schreierFactor (T.schreierRep t g₁) g₂))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact congrArg
        (fun q : G' => A.ρ q
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g₁),
            H.mapMulEquivEquiv e
              (T.schreierFactor (T.schreierRep t g₁) g₂))))
        (map_inv e (t : G)).symm

/-- Representative-level degree-one corestriction commutes with transport
by an ambient multiplicative equivalence. -/
theorem mapCocycles₁_corestrictionCocyclesOne_mulEquiv
    (e : G ≃* G') (A : Rep k G') (T : H.RightTransversal)
    [H.FiniteIndex]
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.mapCocycles₁ e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A))
        (corestrictionCocyclesOne A (T.mapMulEquiv e) f) =
      corestrictionCocyclesOne (Rep.res e.toMonoidHom A) T
        (groupCohomology.mapCocycles₁
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom f) := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change corestrictionCochainOne A (T.mapMulEquiv e) f (e g) =
    corestrictionCochainOne (Rep.res e.toMonoidHom A) T
      (fun h => f (H.mapMulEquivEquiv e h)) g
  exact congrFun (corestrictionCochainOne_mapMulEquiv e A T f) g

/-- Representative-level degree-two corestriction commutes with transport
by an ambient multiplicative equivalence. -/
theorem mapCocycles₂_corestrictionCocyclesTwo_mulEquiv
    (e : G ≃* G') (A : Rep k G') (T : H.RightTransversal)
    [H.FiniteIndex]
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.mapCocycles₂ e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A))
        (corestrictionCocyclesTwo A (T.mapMulEquiv e) z) =
      corestrictionCocyclesTwo (Rep.res e.toMonoidHom A) T
        (groupCohomology.mapCocycles₂
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom z) := by
  apply groupCohomology.cocycles₂_ext
  intro g₁ g₂
  change corestrictionCochainTwo A (T.mapMulEquiv e) z
      (e g₁, e g₂) =
    corestrictionCochainTwo (Rep.res e.toMonoidHom A) T
      (fun p => z (H.mapMulEquivEquiv e p.1,
        H.mapMulEquivEquiv e p.2)) (g₁, g₂)
  exact congrFun (corestrictionCochainTwo_mapMulEquiv e A T z) (g₁, g₂)

/-- Chosen-transversal degree-one corestriction commutes with transport by
an ambient multiplicative equivalence. -/
theorem corestrictionH1OfRightTransversal_mulEquiv
    (e : G ≃* G') (A : Rep k G') (T : H.RightTransversal)
    [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) 1
        (corestrictionH1OfRightTransversal A (T.mapMulEquiv e) x) =
      corestrictionH1OfRightTransversal (Rep.res e.toMonoidHom A) T
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 1 x) := by
  induction x using groupCohomology.H1_induction_on with
  | _ f =>
      calc
        groupCohomology.map e.toMonoidHom
            (𝟙 (Rep.res e.toMonoidHom A)) 1
            (corestrictionH1OfRightTransversal A (T.mapMulEquiv e)
              (groupCohomology.H1π
                (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) f)) =
          groupCohomology.H1π (Rep.res e.toMonoidHom A)
            (groupCohomology.mapCocycles₁ e.toMonoidHom
              (𝟙 (Rep.res e.toMonoidHom A))
              (corestrictionCocyclesOne A (T.mapMulEquiv e) f)) := by
            rw [corestrictionH1OfRightTransversal_H1π]
            exact groupCohomology.H1π_comp_map_apply e.toMonoidHom
              (𝟙 (Rep.res e.toMonoidHom A)) _
        _ = groupCohomology.H1π (Rep.res e.toMonoidHom A)
            (corestrictionCocyclesOne (Rep.res e.toMonoidHom A) T
              (groupCohomology.mapCocycles₁
                (H.mapMulEquivEquiv e).toMonoidHom
                (mulEquivSubgroupResIso e H A).hom f)) :=
          congrArg (groupCohomology.H1π (Rep.res e.toMonoidHom A))
            (mapCocycles₁_corestrictionCocyclesOne_mulEquiv e A T f)
        _ = corestrictionH1OfRightTransversal (Rep.res e.toMonoidHom A) T
            (groupCohomology.H1π
              (Rep.res (Subgroup.subtype H) (Rep.res e.toMonoidHom A))
              (groupCohomology.mapCocycles₁
                (H.mapMulEquivEquiv e).toMonoidHom
                (mulEquivSubgroupResIso e H A).hom f)) :=
          (corestrictionH1OfRightTransversal_H1π
            (Rep.res e.toMonoidHom A) T _).symm
        _ = corestrictionH1OfRightTransversal (Rep.res e.toMonoidHom A) T
            (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
              (mulEquivSubgroupResIso e H A).hom 1
              (groupCohomology.H1π
                (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) f)) := by
          rw [groupCohomology.H1π_comp_map_apply]

/-- Chosen-transversal degree-two corestriction commutes with transport by
an ambient multiplicative equivalence. -/
theorem corestrictionH2OfRightTransversal_mulEquiv
    (e : G ≃* G') (A : Rep k G') (T : H.RightTransversal)
    [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) 2
        (corestrictionH2OfRightTransversal A (T.mapMulEquiv e) x) =
      corestrictionH2OfRightTransversal (Rep.res e.toMonoidHom A) T
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 2 x) := by
  induction x using groupCohomology.H2_induction_on with
  | _ z =>
      calc
        groupCohomology.map e.toMonoidHom
            (𝟙 (Rep.res e.toMonoidHom A)) 2
            (corestrictionH2OfRightTransversal A (T.mapMulEquiv e)
              (groupCohomology.H2π
                (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) z)) =
          groupCohomology.H2π (Rep.res e.toMonoidHom A)
            (groupCohomology.mapCocycles₂ e.toMonoidHom
              (𝟙 (Rep.res e.toMonoidHom A))
              (corestrictionCocyclesTwo A (T.mapMulEquiv e) z)) := by
            rw [corestrictionH2OfRightTransversal_H2π]
            exact groupCohomology.H2π_comp_map_apply e.toMonoidHom
              (𝟙 (Rep.res e.toMonoidHom A)) _
        _ = groupCohomology.H2π (Rep.res e.toMonoidHom A)
            (corestrictionCocyclesTwo (Rep.res e.toMonoidHom A) T
              (groupCohomology.mapCocycles₂
                (H.mapMulEquivEquiv e).toMonoidHom
                (mulEquivSubgroupResIso e H A).hom z)) :=
          congrArg (groupCohomology.H2π (Rep.res e.toMonoidHom A))
            (mapCocycles₂_corestrictionCocyclesTwo_mulEquiv e A T z)
        _ = corestrictionH2OfRightTransversal (Rep.res e.toMonoidHom A) T
            (groupCohomology.H2π
              (Rep.res (Subgroup.subtype H) (Rep.res e.toMonoidHom A))
              (groupCohomology.mapCocycles₂
                (H.mapMulEquivEquiv e).toMonoidHom
                (mulEquivSubgroupResIso e H A).hom z)) :=
          (corestrictionH2OfRightTransversal_H2π
            (Rep.res e.toMonoidHom A) T _).symm
        _ = corestrictionH2OfRightTransversal (Rep.res e.toMonoidHom A) T
            (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
              (mulEquivSubgroupResIso e H A).hom 2
              (groupCohomology.H2π
                (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) z)) := by
          rw [groupCohomology.H2π_comp_map_apply]

/-- Elementwise naturality of canonical degree-one corestriction under an
equivalence of ambient groups. -/
theorem corestrictionH1_mulEquiv_apply (e : G ≃* G')
    (A : Rep k G') [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) 1
        (corestrictionH1 (H := H.map e.toMonoidHom) A x) =
      corestrictionH1 (H := H) (Rep.res e.toMonoidHom A)
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 1 x) := by
  let T : H.RightTransversal := default
  rw [corestrictionH1_eq_of_rightTransversal A (T.mapMulEquiv e),
    corestrictionH1_eq_of_rightTransversal (Rep.res e.toMonoidHom A) T]
  exact corestrictionH1OfRightTransversal_mulEquiv e A T x

/-- Elementwise naturality of canonical degree-two corestriction under an
equivalence of ambient groups. -/
theorem corestrictionH2_mulEquiv_apply (e : G ≃* G')
    (A : Rep k G') [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) 2
        (corestrictionH2 (H := H.map e.toMonoidHom) A x) =
      corestrictionH2 (H := H) (Rep.res e.toMonoidHom A)
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 2 x) := by
  let T : H.RightTransversal := default
  rw [corestrictionH2_eq_of_rightTransversal A (T.mapMulEquiv e),
    corestrictionH2_eq_of_rightTransversal (Rep.res e.toMonoidHom A) T]
  exact corestrictionH2OfRightTransversal_mulEquiv e A T x

/-- Linear-map square for degree-one canonical corestriction under an
equivalence of ambient groups. -/
theorem corestrictionH1_mulEquiv (e : G ≃* G')
    (A : Rep k G') [H.FiniteIndex] :
    (groupCohomology.map e.toMonoidHom
      (𝟙 (Rep.res e.toMonoidHom A)) 1).hom.comp
        (corestrictionH1 (H := H.map e.toMonoidHom) A) =
      (corestrictionH1 (H := H) (Rep.res e.toMonoidHom A)).comp
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 1).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH1_mulEquiv_apply e A x

/-- Linear-map square for degree-two canonical corestriction under an
equivalence of ambient groups. -/
theorem corestrictionH2_mulEquiv (e : G ≃* G')
    (A : Rep k G') [H.FiniteIndex] :
    (groupCohomology.map e.toMonoidHom
      (𝟙 (Rep.res e.toMonoidHom A)) 2).hom.comp
        (corestrictionH2 (H := H.map e.toMonoidHom) A) =
      (corestrictionH2 (H := H) (Rep.res e.toMonoidHom A)).comp
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 2).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH2_mulEquiv_apply e A x

/-- Degree-one corestriction naturality under simultaneous transport of the
ambient group and a coefficient morphism. -/
theorem corestrictionH1_mulEquiv_hom_apply
    (e : G ≃* G') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B) [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.map e.toMonoidHom φ 1
        (corestrictionH1 (H := H.map e.toMonoidHom) A x) =
      corestrictionH1 (H := H) B
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H φ) 1 x) := by
  calc
    groupCohomology.map e.toMonoidHom φ 1
        (corestrictionH1 (H := H.map e.toMonoidHom) A x) =
      groupCohomology.map (MonoidHom.id G) φ 1
        (groupCohomology.map e.toMonoidHom
          (𝟙 (Rep.res e.toMonoidHom A)) 1
          (corestrictionH1 (H := H.map e.toMonoidHom) A x)) := by
            rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_comp]
            rfl
    _ = groupCohomology.map (MonoidHom.id G) φ 1
        (corestrictionH1 (H := H) (Rep.res e.toMonoidHom A)
          (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom 1 x)) := by
      rw [corestrictionH1_mulEquiv_apply e A x]
    _ = corestrictionH1 (H := H) B
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 1
          (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom 1 x)) :=
      corestrictionH1_naturality_apply φ _
    _ = corestrictionH1 (H := H) B
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H φ) 1 x) := by
      congr 1
      rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_comp]
      rfl

/-- Degree-two corestriction naturality under simultaneous transport of the
ambient group and a coefficient morphism. -/
theorem corestrictionH2_mulEquiv_hom_apply
    (e : G ≃* G') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B) [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    groupCohomology.map e.toMonoidHom φ 2
        (corestrictionH2 (H := H.map e.toMonoidHom) A x) =
      corestrictionH2 (H := H) B
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H φ) 2 x) := by
  calc
    groupCohomology.map e.toMonoidHom φ 2
        (corestrictionH2 (H := H.map e.toMonoidHom) A x) =
      groupCohomology.map (MonoidHom.id G) φ 2
        (groupCohomology.map e.toMonoidHom
          (𝟙 (Rep.res e.toMonoidHom A)) 2
          (corestrictionH2 (H := H.map e.toMonoidHom) A x)) := by
            rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_comp]
            rfl
    _ = groupCohomology.map (MonoidHom.id G) φ 2
        (corestrictionH2 (H := H) (Rep.res e.toMonoidHom A)
          (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom 2 x)) := by
      rw [corestrictionH2_mulEquiv_apply e A x]
    _ = corestrictionH2 (H := H) B
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 2
          (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom 2 x)) :=
      corestrictionH2_naturality_apply φ _
    _ = corestrictionH2 (H := H) B
        (groupCohomology.map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H φ) 2 x) := by
      congr 1
      rw [← ConcreteCategory.comp_apply, ← groupCohomology.map_comp]
      rfl

/-- Canonical degree-one corestriction is natural under an ambient
equivalence even when the transported subgroup is presented by a separately
bundled equal subgroup. -/
theorem corestrictionH1_mulEquivOfEq_apply
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') (A : Rep k G')
    [H.FiniteIndex] [H'.FiniteIndex]
    (x : groupCohomology.H1 (Rep.res (Subgroup.subtype H') A)) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) 1
        (corestrictionH1 (H := H') A x) =
      corestrictionH1 (H := H) (Rep.res e.toMonoidHom A)
        (groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResIsoOfEq e H H' h A).hom 1 x) := by
  subst H'
  exact corestrictionH1_mulEquiv_apply e A x

/-- Canonical degree-two corestriction is natural under an ambient
equivalence even when the transported subgroup is presented by a separately
bundled equal subgroup. -/
theorem corestrictionH2_mulEquivOfEq_apply
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') (A : Rep k G')
    [H.FiniteIndex] [H'.FiniteIndex]
    (x : groupCohomology.H2 (Rep.res (Subgroup.subtype H') A)) :
    groupCohomology.map e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A)) 2
        (corestrictionH2 (H := H') A x) =
      corestrictionH2 (H := H) (Rep.res e.toMonoidHom A)
        (groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResIsoOfEq e H H' h A).hom 2 x) := by
  subst H'
  exact corestrictionH2_mulEquiv_apply e A x

/-- Degree-one corestriction naturality with both a coefficient morphism and
a separately bundled equal image subgroup. -/
theorem corestrictionH1_mulEquivOfEq_hom_apply
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B)
    [H.FiniteIndex] [H'.FiniteIndex]
    (x : groupCohomology.H1 (Rep.res (Subgroup.subtype H') A)) :
    groupCohomology.map e.toMonoidHom φ 1
        (corestrictionH1 (H := H') A x) =
      corestrictionH1 (H := H) B
        (groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResHomOfEq e H H' h φ) 1 x) := by
  subst H'
  exact corestrictionH1_mulEquiv_hom_apply e φ x

/-- Degree-two corestriction naturality with both a coefficient morphism and
a separately bundled equal image subgroup. -/
theorem corestrictionH2_mulEquivOfEq_hom_apply
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B)
    [H.FiniteIndex] [H'.FiniteIndex]
    (x : groupCohomology.H2 (Rep.res (Subgroup.subtype H') A)) :
    groupCohomology.map e.toMonoidHom φ 2
        (corestrictionH2 (H := H') A x) =
      corestrictionH2 (H := H) B
        (groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResHomOfEq e H H' h φ) 2 x) := by
  subst H'
  exact corestrictionH2_mulEquiv_hom_apply e φ x

/-- Linear-map form of degree-one corestriction naturality for an identified
image subgroup. -/
theorem corestrictionH1_mulEquivOfEq
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') (A : Rep k G')
    [H.FiniteIndex] [H'.FiniteIndex] :
    (groupCohomology.map e.toMonoidHom
      (𝟙 (Rep.res e.toMonoidHom A)) 1).hom.comp
        (corestrictionH1 (H := H') A) =
      (corestrictionH1 (H := H) (Rep.res e.toMonoidHom A)).comp
        (groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResIsoOfEq e H H' h A).hom 1).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH1_mulEquivOfEq_apply e H' h A x

/-- Linear-map form of degree-two corestriction naturality for an identified
image subgroup. -/
theorem corestrictionH2_mulEquivOfEq
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') (A : Rep k G')
    [H.FiniteIndex] [H'.FiniteIndex] :
    (groupCohomology.map e.toMonoidHom
      (𝟙 (Rep.res e.toMonoidHom A)) 2).hom.comp
        (corestrictionH2 (H := H') A) =
      (corestrictionH2 (H := H) (Rep.res e.toMonoidHom A)).comp
        (groupCohomology.map
          (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResIsoOfEq e H H' h A).hom 2).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH2_mulEquivOfEq_apply e H' h A x

/-- Coefficient comparison in subgroup-chain transitivity when the image of
the inner subgroup is presented by a separately bundled equal subgroup. -/
noncomputable def mapSubtypeResIsoOfEq
    {J : Subgroup G} (h : K.map H.subtype = J) (A : Rep k G) :
    Rep.res
        ((K.equivMapOfInjective H.subtype H.subtype_injective).trans
          (MulEquiv.subgroupCongr h)).toMonoidHom
        (Rep.res (Subgroup.subtype J) A) ≅
      Rep.res (Subgroup.subtype K) (Rep.res (Subgroup.subtype H) A) :=
  eqToIso (by subst J; rfl)

@[simp]
theorem mapSubtypeResIsoOfEq_hom_apply
    {J : Subgroup G} (h : K.map H.subtype = J) (A : Rep k G)
    (a : A) :
    (mapSubtypeResIsoOfEq (H := H) (K := K) h A).hom a = a := by
  subst J
  rfl

/-- Degree-one subgroup-chain transitivity with a separately bundled equal
presentation of the image subgroup. -/
theorem corestrictionH1_trans_of_eq
    {J : Subgroup G} (h : K.map H.subtype = J) (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex] [J.FiniteIndex]
    (x : groupCohomology.H1 (Rep.res (Subgroup.subtype J) A)) :
    corestrictionH1 (H := J) A x =
      corestrictionH1 (H := H) A
        (corestrictionH1 (H := K) (Rep.res (Subgroup.subtype H) A)
          (groupCohomology.map
            ((K.equivMapOfInjective H.subtype H.subtype_injective).trans
              (MulEquiv.subgroupCongr h)).toMonoidHom
            (mapSubtypeResIsoOfEq (H := H) (K := K) h A).hom 1 x)) := by
  subst J
  exact corestrictionH1_trans A x

/-- Degree-two subgroup-chain transitivity with a separately bundled equal
presentation of the image subgroup. -/
theorem corestrictionH2_trans_of_eq
    {J : Subgroup G} (h : K.map H.subtype = J) (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex] [J.FiniteIndex]
    (x : groupCohomology.H2 (Rep.res (Subgroup.subtype J) A)) :
    corestrictionH2 (H := J) A x =
      corestrictionH2 (H := H) A
        (corestrictionH2 (H := K) (Rep.res (Subgroup.subtype H) A)
          (groupCohomology.map
            ((K.equivMapOfInjective H.subtype H.subtype_injective).trans
              (MulEquiv.subgroupCongr h)).toMonoidHom
            (mapSubtypeResIsoOfEq (H := H) (K := K) h A).hom 2 x)) := by
  subst J
  exact corestrictionH2_trans A x

end groupCohomology
