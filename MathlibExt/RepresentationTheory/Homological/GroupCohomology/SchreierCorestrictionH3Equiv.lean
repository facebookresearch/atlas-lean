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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionEquiv
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3Naturality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH3Transitivity

/-!
# Degree-three corestriction under group equivalences

This file extends the canonical Schreier corestriction equivalence API to
degree three.  It proves cochain and cocycle transport, canonical naturality
under ambient multiplicative equivalences, simultaneous coefficient
naturality, and subgroup-chain transitivity for separately bundled equal
image subgroups.

No field-theoretic, Kummer, norm-residue, or Bloch--Kato claim is made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G G' : Type u} [CommRing k] [Group G] [Group G']
variable {H : Subgroup G}

noncomputable local instance corestrictionH3EquivMapFiniteIndex
    (e : G ≃* G') [H.FiniteIndex] :
    (H.map e.toMonoidHom).FiniteIndex :=
  Subgroup.FiniteIndex.map_of_surjective H e.surjective

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance corestrictionH3EquivTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- The original mapped representative type is finite under the original
subgroup finite-index hypothesis. -/
noncomputable local instance corestrictionH3EquivMappedRepresentativeFintype
    (e : G ≃* G') (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.mapMulEquiv e : Set G') :=
  @Fintype.ofFinite _ (T.mapMulEquiv e).2.finite_right

/-- Degree-three cochain transfer commutes with transport by an ambient
multiplicative equivalence. -/
theorem corestrictionCochainThree_mapMulEquiv (e : G ≃* G')
    (A : Rep k G') (T : H.RightTransversal) [H.FiniteIndex]
    (f : (H.map e.toMonoidHom) × (H.map e.toMonoidHom) ×
      (H.map e.toMonoidHom) → A) :
    (fun p => corestrictionCochainThree A (T.mapMulEquiv e) f
        (e p.1, e p.2.1, e p.2.2)) =
      corestrictionCochainThree (Rep.res e.toMonoidHom A) T
        (fun p => f (H.mapMulEquivEquiv e p.1,
          H.mapMulEquivEquiv e p.2.1,
          H.mapMulEquivEquiv e p.2.2)) := by
  funext p
  rcases p with ⟨g₁, g₂, g₃⟩
  rw [corestrictionCochainThree_apply, corestrictionCochainThree_apply]
  calc
    (∑ t : ((T.mapMulEquiv e : Set G')),
        A.ρ (t : G')⁻¹
          (f ((T.mapMulEquiv e).schreierFactor t (e g₁),
            (T.mapMulEquiv e).schreierFactor
              ((T.mapMulEquiv e).schreierRep t (e g₁)) (e g₂),
            (T.mapMulEquiv e).schreierFactor
              ((T.mapMulEquiv e).schreierRep
                ((T.mapMulEquiv e).schreierRep t (e g₁)) (e g₂)) (e g₃)))) =
      ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f ((T.mapMulEquiv e).schreierFactor
                (T.mapMulEquivRepEquiv e t) (e g₁),
            (T.mapMulEquiv e).schreierFactor
              ((T.mapMulEquiv e).schreierRep
                (T.mapMulEquivRepEquiv e t) (e g₁)) (e g₂),
            (T.mapMulEquiv e).schreierFactor
              ((T.mapMulEquiv e).schreierRep
                ((T.mapMulEquiv e).schreierRep
                  (T.mapMulEquivRepEquiv e t) (e g₁)) (e g₂)) (e g₃))) :=
      ((T.mapMulEquivRepEquiv e).sum_comp
        (fun t : ((T.mapMulEquiv e : Set G')) =>
          A.ρ (t : G')⁻¹
            (f ((T.mapMulEquiv e).schreierFactor t (e g₁),
              (T.mapMulEquiv e).schreierFactor
                ((T.mapMulEquiv e).schreierRep t (e g₁)) (e g₂),
              (T.mapMulEquiv e).schreierFactor
                ((T.mapMulEquiv e).schreierRep
                  ((T.mapMulEquiv e).schreierRep t (e g₁)) (e g₂)) (e g₃))))).symm
    _ = ∑ t : (T : Set G),
        A.ρ (e (t : G))⁻¹
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g₁),
            H.mapMulEquivEquiv e
              (T.schreierFactor (T.schreierRep t g₁) g₂),
            H.mapMulEquivEquiv e
              (T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [T.mapMulEquiv_schreierRep e,
        T.mapMulEquiv_schreierRep e,
        T.mapMulEquiv_schreierFactor e,
        T.mapMulEquiv_schreierFactor e,
        T.mapMulEquiv_schreierFactor e]
    _ = ∑ t : (T : Set G),
        (Rep.res e.toMonoidHom A).ρ (t : G)⁻¹
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g₁),
            H.mapMulEquivEquiv e
              (T.schreierFactor (T.schreierRep t g₁) g₂),
            H.mapMulEquivEquiv e
              (T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact congrArg
        (fun q : G' => A.ρ q
          (f (H.mapMulEquivEquiv e (T.schreierFactor t g₁),
            H.mapMulEquivEquiv e
              (T.schreierFactor (T.schreierRep t g₁) g₂),
            H.mapMulEquivEquiv e
              (T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃))))
        (map_inv e (t : G)).symm

/-- Representative-level degree-three corestriction commutes with transport
by an ambient multiplicative equivalence. -/
theorem mapCocycles₃_corestrictionCocyclesThree_mulEquiv
    (e : G ≃* G') (A : Rep k G') (T : H.RightTransversal)
    [H.FiniteIndex]
    (z : cocycles₃
      (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    mapCocycles₃ e.toMonoidHom
        (𝟙 (Rep.res e.toMonoidHom A))
        (corestrictionCocyclesThree A (T.mapMulEquiv e) z) =
      corestrictionCocyclesThree (Rep.res e.toMonoidHom A) T
        (mapCocycles₃
          (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom z) := by
  apply cocycles₃_ext
  intro g₁ g₂ g₃
  change corestrictionCochainThree A (T.mapMulEquiv e) z
      (e g₁, e g₂, e g₃) =
    corestrictionCochainThree (Rep.res e.toMonoidHom A) T
      (fun p => z (H.mapMulEquivEquiv e p.1,
        H.mapMulEquivEquiv e p.2.1,
        H.mapMulEquivEquiv e p.2.2)) (g₁, g₂, g₃)
  exact congrFun (corestrictionCochainThree_mapMulEquiv e A T z)
    (g₁, g₂, g₃)

/-- Chosen-transversal degree-three corestriction commutes with transport by
an ambient multiplicative equivalence. -/
theorem corestrictionH3OfRightTransversal_mulEquiv
    (e : G ≃* G') (A : Rep k G') (T : H.RightTransversal)
    [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) 3
        (corestrictionH3OfRightTransversal A (T.mapMulEquiv e) x) =
      corestrictionH3OfRightTransversal (Rep.res e.toMonoidHom A) T
        (map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 3 x) := by
  induction x using H3_induction_on with
  | _ z =>
      calc
        map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) 3
            (corestrictionH3OfRightTransversal A (T.mapMulEquiv e)
              (H3π (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) z)) =
          H3π (Rep.res e.toMonoidHom A)
            (mapCocycles₃ e.toMonoidHom
              (𝟙 (Rep.res e.toMonoidHom A))
              (corestrictionCocyclesThree A (T.mapMulEquiv e) z)) := by
            rw [corestrictionH3OfRightTransversal_H3π]
            exact H3π_comp_map_apply e.toMonoidHom
              (𝟙 (Rep.res e.toMonoidHom A)) _
        _ = H3π (Rep.res e.toMonoidHom A)
            (corestrictionCocyclesThree (Rep.res e.toMonoidHom A) T
              (mapCocycles₃ (H.mapMulEquivEquiv e).toMonoidHom
                (mulEquivSubgroupResIso e H A).hom z)) :=
          congrArg (H3π (Rep.res e.toMonoidHom A))
            (mapCocycles₃_corestrictionCocyclesThree_mulEquiv e A T z)
        _ = corestrictionH3OfRightTransversal (Rep.res e.toMonoidHom A) T
            (H3π (Rep.res (Subgroup.subtype H) (Rep.res e.toMonoidHom A))
              (mapCocycles₃ (H.mapMulEquivEquiv e).toMonoidHom
                (mulEquivSubgroupResIso e H A).hom z)) :=
          (corestrictionH3OfRightTransversal_H3π
            (Rep.res e.toMonoidHom A) T _).symm
        _ = corestrictionH3OfRightTransversal (Rep.res e.toMonoidHom A) T
            (map (H.mapMulEquivEquiv e).toMonoidHom
              (mulEquivSubgroupResIso e H A).hom 3
              (H3π (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) z)) := by
          rw [H3π_comp_map_apply]

/-- Elementwise naturality of canonical degree-three corestriction under an
equivalence of ambient groups. -/
theorem corestrictionH3_mulEquiv_apply (e : G ≃* G')
    (A : Rep k G') [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) 3
        (corestrictionH3 (H := H.map e.toMonoidHom) A x) =
      corestrictionH3 (H := H) (Rep.res e.toMonoidHom A)
        (map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResIso e H A).hom 3 x) := by
  let T : H.RightTransversal := default
  rw [corestrictionH3_eq_of_rightTransversal A (T.mapMulEquiv e),
    corestrictionH3_eq_of_rightTransversal (Rep.res e.toMonoidHom A) T]
  exact corestrictionH3OfRightTransversal_mulEquiv e A T x

/-- Degree-three corestriction naturality under simultaneous transport of
the ambient group and a coefficient morphism. -/
theorem corestrictionH3_mulEquiv_hom_apply
    (e : G ≃* G') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B) [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A)) :
    map e.toMonoidHom φ 3
        (corestrictionH3 (H := H.map e.toMonoidHom) A x) =
      corestrictionH3 (H := H) B
        (map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H φ) 3 x) := by
  calc
    map e.toMonoidHom φ 3
        (corestrictionH3 (H := H.map e.toMonoidHom) A x) =
      map (MonoidHom.id G) φ 3
        (map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) 3
          (corestrictionH3 (H := H.map e.toMonoidHom) A x)) := by
            rw [← ConcreteCategory.comp_apply, ← map_comp]
            rfl
    _ = map (MonoidHom.id G) φ 3
        (corestrictionH3 (H := H) (Rep.res e.toMonoidHom A)
          (map (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom 3 x)) := by
      rw [corestrictionH3_mulEquiv_apply e A x]
    _ = corestrictionH3 (H := H) B
        (map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 3
          (map (H.mapMulEquivEquiv e).toMonoidHom
            (mulEquivSubgroupResIso e H A).hom 3 x)) :=
      corestrictionH3_naturality_apply φ _
    _ = corestrictionH3 (H := H) B
        (map (H.mapMulEquivEquiv e).toMonoidHom
          (mulEquivSubgroupResHom e H φ) 3 x) := by
      congr 1
      rw [← ConcreteCategory.comp_apply, ← map_comp]
      rfl

/-- Degree-three corestriction naturality with both a coefficient morphism
and a separately bundled equal image subgroup. -/
theorem corestrictionH3_mulEquivOfEq_hom_apply
    (e : G ≃* G') (H' : Subgroup G')
    (h : H.map e.toMonoidHom = H') {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B)
    [H.FiniteIndex] [H'.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype H') A)) :
    map e.toMonoidHom φ 3 (corestrictionH3 (H := H') A x) =
      corestrictionH3 (H := H) B
        (map (H.mapMulEquivEquivOfEq e H' h).toMonoidHom
          (mulEquivSubgroupResHomOfEq e H H' h φ) 3 x) := by
  subst H'
  exact corestrictionH3_mulEquiv_hom_apply e φ x

/-- Degree-three subgroup-chain transitivity with a separately bundled equal
presentation of the image subgroup. -/
theorem corestrictionH3_trans_of_eq
    {K : Subgroup H} {J : Subgroup G}
    (h : K.map H.subtype = J) (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex] [J.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype J) A)) :
    corestrictionH3 (H := J) A x =
      corestrictionH3 (H := H) A
        (corestrictionH3 (H := K) (Rep.res (Subgroup.subtype H) A)
          (map
            ((K.equivMapOfInjective H.subtype H.subtype_injective).trans
              (MulEquiv.subgroupCongr h)).toMonoidHom
            (mapSubtypeResIsoOfEq (H := H) (K := K) h A).hom 3 x)) := by
  subst J
  exact corestrictionH3_trans A x

end groupCohomology
