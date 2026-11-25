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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionH2

/-!
# Coefficient naturality of finite-index corestriction

For a morphism of `G`-representations, mapping coefficients commutes with
finite-index Schreier corestriction in degrees one and two.  The proof is
first given on cochains and cocycle representatives for an arbitrary right
transversal, then descended to the canonical cohomology maps and packaged as
LinearMap squares.

No field-theoretic, Kummer, norm-residue, or projection-formula claim is made
here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance corestrictionNaturalityRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Mapping coefficients commutes with the chosen-transversal degree-one
cochain transfer. -/
theorem corestrictionCochainOne_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (f : H → A) :
    (fun g => φ.hom (corestrictionCochainOne A T f g)) =
      corestrictionCochainOne B T (fun h => φ.hom (f h)) := by
  funext g
  rw [corestrictionCochainOne_apply,
    corestrictionCochainOne_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Rep.hom_comm_apply φ (t : G)⁻¹ (f (T.schreierFactor t g))

/-- Mapping coefficients commutes with the chosen-transversal degree-two
cochain transfer. -/
theorem corestrictionCochainTwo_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] (z : H × H → A) :
    (fun p => φ.hom (corestrictionCochainTwo A T z p)) =
      corestrictionCochainTwo B T (fun p => φ.hom (z p)) := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochainTwo_apply,
    corestrictionCochainTwo_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Rep.hom_comm_apply φ (t : G)⁻¹
    (z (T.schreierFactor t g₁,
      T.schreierFactor (T.schreierRep t g₁) g₂))

/-- Representative-level coefficient naturality for chosen-transversal
degree-one transfer. -/
theorem mapCocycles₁_corestrictionCocyclesOne
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.mapCocycles₁ (MonoidHom.id G) φ
        (corestrictionCocyclesOne A T f) =
      corestrictionCocyclesOne B T
        (groupCohomology.mapCocycles₁ (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) f) := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change φ.hom (corestrictionCochainOne A T f g) =
    corestrictionCochainOne B T (fun h => φ.hom (f h)) g
  exact congrFun (corestrictionCochainOne_naturality φ T f) g

/-- Representative-level coefficient naturality for chosen-transversal
degree-two transfer. -/
theorem mapCocycles₂_corestrictionCocyclesTwo
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.mapCocycles₂ (MonoidHom.id G) φ
        (corestrictionCocyclesTwo A T z) =
      corestrictionCocyclesTwo B T
        (groupCohomology.mapCocycles₂ (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) z) := by
  apply groupCohomology.cocycles₂_ext
  intro g₁ g₂
  change φ.hom (corestrictionCochainTwo A T z (g₁, g₂)) =
    corestrictionCochainTwo B T (fun p => φ.hom (z p)) (g₁, g₂)
  exact congrFun
    (corestrictionCochainTwo_naturality φ T z) (g₁, g₂)

/-- Coefficient naturality of chosen-transversal degree-one corestriction. -/
theorem corestrictionH1OfRightTransversal_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (x : groupCohomology.H1 (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.map (MonoidHom.id G) φ 1
        (corestrictionH1OfRightTransversal A T x) =
      corestrictionH1OfRightTransversal B T
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 1 x) := by
  induction x using groupCohomology.H1_induction_on with
  | _ f =>
      calc
        groupCohomology.map (MonoidHom.id G) φ 1
            (corestrictionH1OfRightTransversal A T
              (groupCohomology.H1π
                (Rep.res (Subgroup.subtype H) A) f)) =
          groupCohomology.H1π B
            (groupCohomology.mapCocycles₁ (MonoidHom.id G) φ
              (corestrictionCocyclesOne A T f)) := by
            rw [corestrictionH1OfRightTransversal_H1π]
            exact groupCohomology.H1π_comp_map_apply
              (MonoidHom.id G) φ (corestrictionCocyclesOne A T f)
        _ = groupCohomology.H1π B
            (corestrictionCocyclesOne B T
              (groupCohomology.mapCocycles₁ (MonoidHom.id H)
                ((Rep.resFunctor (Subgroup.subtype H)).map φ) f)) :=
          congrArg (groupCohomology.H1π B)
            (mapCocycles₁_corestrictionCocyclesOne φ T f)
        _ = corestrictionH1OfRightTransversal B T
            (groupCohomology.H1π (Rep.res (Subgroup.subtype H) B)
              (groupCohomology.mapCocycles₁ (MonoidHom.id H)
                ((Rep.resFunctor (Subgroup.subtype H)).map φ) f)) :=
          (corestrictionH1OfRightTransversal_H1π B T _).symm
        _ = corestrictionH1OfRightTransversal B T
            (groupCohomology.map (MonoidHom.id H)
              ((Rep.resFunctor (Subgroup.subtype H)).map φ) 1
              (groupCohomology.H1π
                (Rep.res (Subgroup.subtype H) A) f)) := by
          have hmap := groupCohomology.H1π_comp_map_apply
            (MonoidHom.id H)
            ((Rep.resFunctor (Subgroup.subtype H)).map φ) f
          rw [hmap]

/-- Coefficient naturality of chosen-transversal degree-two corestriction. -/
theorem corestrictionH2OfRightTransversal_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (x : groupCohomology.H2 (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.map (MonoidHom.id G) φ 2
        (corestrictionH2OfRightTransversal A T x) =
      corestrictionH2OfRightTransversal B T
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 2 x) := by
  induction x using groupCohomology.H2_induction_on with
  | _ z =>
      calc
        groupCohomology.map (MonoidHom.id G) φ 2
            (corestrictionH2OfRightTransversal A T
              (groupCohomology.H2π
                (Rep.res (Subgroup.subtype H) A) z)) =
          groupCohomology.H2π B
            (groupCohomology.mapCocycles₂ (MonoidHom.id G) φ
              (corestrictionCocyclesTwo A T z)) := by
            rw [corestrictionH2OfRightTransversal_H2π]
            exact groupCohomology.H2π_comp_map_apply
              (MonoidHom.id G) φ (corestrictionCocyclesTwo A T z)
        _ = groupCohomology.H2π B
            (corestrictionCocyclesTwo B T
              (groupCohomology.mapCocycles₂ (MonoidHom.id H)
                ((Rep.resFunctor (Subgroup.subtype H)).map φ) z)) :=
          congrArg (groupCohomology.H2π B)
            (mapCocycles₂_corestrictionCocyclesTwo φ T z)
        _ = corestrictionH2OfRightTransversal B T
            (groupCohomology.H2π (Rep.res (Subgroup.subtype H) B)
              (groupCohomology.mapCocycles₂ (MonoidHom.id H)
                ((Rep.resFunctor (Subgroup.subtype H)).map φ) z)) :=
          (corestrictionH2OfRightTransversal_H2π B T _).symm
        _ = corestrictionH2OfRightTransversal B T
            (groupCohomology.map (MonoidHom.id H)
              ((Rep.resFunctor (Subgroup.subtype H)).map φ) 2
              (groupCohomology.H2π
                (Rep.res (Subgroup.subtype H) A) z)) := by
          have hmap := groupCohomology.H2π_comp_map_apply
            (MonoidHom.id H)
            ((Rep.resFunctor (Subgroup.subtype H)).map φ) z
          rw [hmap]

/-- Elementwise coefficient naturality of canonical degree-one
corestriction. -/
theorem corestrictionH1_naturality_apply
    {A B : Rep k G} (φ : A ⟶ B) [H.FiniteIndex]
    (x : groupCohomology.H1 (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.map (MonoidHom.id G) φ 1 (corestrictionH1 A x) =
      corestrictionH1 B
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 1 x) := by
  let T : H.RightTransversal := default
  rw [corestrictionH1_eq_of_rightTransversal A T,
    corestrictionH1_eq_of_rightTransversal B T]
  exact corestrictionH1OfRightTransversal_naturality φ T x

/-- Elementwise coefficient naturality of canonical degree-two
corestriction. -/
theorem corestrictionH2_naturality_apply
    {A B : Rep k G} (φ : A ⟶ B) [H.FiniteIndex]
    (x : groupCohomology.H2 (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.map (MonoidHom.id G) φ 2 (corestrictionH2 A x) =
      corestrictionH2 B
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 2 x) := by
  let T : H.RightTransversal := default
  rw [corestrictionH2_eq_of_rightTransversal A T,
    corestrictionH2_eq_of_rightTransversal B T]
  exact corestrictionH2OfRightTransversal_naturality φ T x

/-- LinearMap square expressing coefficient naturality of canonical
degree-one corestriction. -/
theorem corestrictionH1_naturality
    {A B : Rep k G} (φ : A ⟶ B) [H.FiniteIndex] :
    (groupCohomology.map (MonoidHom.id G) φ 1).hom.comp
        (corestrictionH1 A) =
      (corestrictionH1 B).comp
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 1).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH1_naturality_apply φ x

/-- LinearMap square expressing coefficient naturality of canonical
degree-two corestriction. -/
theorem corestrictionH2_naturality
    {A B : Rep k G} (φ : A ⟶ B) [H.FiniteIndex] :
    (groupCohomology.map (MonoidHom.id G) φ 2).hom.comp
        (corestrictionH2 A) =
      (corestrictionH2 B).comp
        (groupCohomology.map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 2).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH2_naturality_apply φ x

end groupCohomology
