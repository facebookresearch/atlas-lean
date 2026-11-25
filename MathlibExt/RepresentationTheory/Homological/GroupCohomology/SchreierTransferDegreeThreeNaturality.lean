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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeFunctoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree

/-!
# Coefficient naturality of chosen-transversal degree-three transfer

For a morphism of `G`-representations, mapping coefficients commutes with
the degree-three Schreier transfer attached to a fixed right transversal.
The comparison is provided on cochains, cocycles, presented `H3` classes,
and as bundled linear-map squares.

The transversal remains explicit.  Independence of its choice and a
canonical degree-three corestriction have not yet been constructed, so no
canonical naturality, field-theoretic, Kummer, or Bloch--Kato claim is made.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance corestrictionDegreeThreeNaturalityTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Mapping coefficients commutes with the chosen-transversal degree-three
cochain transfer. -/
theorem corestrictionCochainThree_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (z : H × H × H → A) :
    (fun p => φ.hom (corestrictionCochainThree A T z p)) =
      corestrictionCochainThree B T (fun p => φ.hom (z p)) := by
  funext p
  rcases p with ⟨g₁, g₂, g₃⟩
  rw [corestrictionCochainThree_apply,
    corestrictionCochainThree_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact Rep.hom_comm_apply φ (t : G)⁻¹
    (z (T.schreierFactor t g₁,
      T.schreierFactor (T.schreierRep t g₁) g₂,
      T.schreierFactor
        (T.schreierRep (T.schreierRep t g₁) g₂) g₃))

/-- Bundled linear-map square for coefficient naturality on degree-three
cochains. -/
theorem corestrictionCochainThree_naturality_linearMap
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] :
    (cochainsMap₃ (k := k) (A := A) (B := B)
      (MonoidHom.id G) φ).hom.comp
        (corestrictionCochainThree A T) =
      (corestrictionCochainThree B T).comp
        (cochainsMap₃ (k := k)
          (A := Rep.res (Subgroup.subtype H) A)
          (B := Rep.res (Subgroup.subtype H) B)
          (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ)).hom := by
  apply LinearMap.ext
  intro z
  funext p
  exact congrFun (corestrictionCochainThree_naturality φ T z) p

/-- Representative-level coefficient naturality for chosen-transversal
degree-three transfer. -/
theorem mapCocycles₃_corestrictionCocyclesThree
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    mapCocycles₃ (MonoidHom.id G) φ
        (corestrictionCocyclesThree A T z) =
      corestrictionCocyclesThree B T
        (mapCocycles₃ (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) z) := by
  apply cocycles₃_ext
  intro g₁ g₂ g₃
  change φ.hom (corestrictionCochainThree A T z (g₁, g₂, g₃)) =
    corestrictionCochainThree B T (fun p => φ.hom (z p)) (g₁, g₂, g₃)
  exact congrFun
    (corestrictionCochainThree_naturality φ T z) (g₁, g₂, g₃)

/-- Bundled linear-map square for coefficient naturality on transferred
degree-three cocycles. -/
theorem corestrictionCocyclesThree_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] :
    (mapCocycles₃ (MonoidHom.id G) φ).hom.comp
        (corestrictionCocyclesThree A T) =
      (corestrictionCocyclesThree B T).comp
        (mapCocycles₃ (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ)).hom := by
  apply LinearMap.ext
  intro z
  exact mapCocycles₃_corestrictionCocyclesThree φ T z

/-- Naturality on a presented `H3` class: mapping after transfer agrees
with transferring the mapped cocycle representative. -/
theorem map_corestrictionH3OfRightTransversal_H3π
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    map (MonoidHom.id G) φ 3
        (corestrictionH3OfRightTransversal A T
          (H3π (Rep.res (Subgroup.subtype H) A) z)) =
      H3π B
        (corestrictionCocyclesThree B T
          (mapCocycles₃ (MonoidHom.id H)
            ((Rep.resFunctor (Subgroup.subtype H)).map φ) z)) := by
  rw [corestrictionH3OfRightTransversal_H3π]
  calc
    map (MonoidHom.id G) φ 3
        (H3π A (corestrictionCocyclesThree A T z)) =
      H3π B
        (mapCocycles₃ (MonoidHom.id G) φ
          (corestrictionCocyclesThree A T z)) :=
      H3π_comp_map_apply (MonoidHom.id G) φ _
    _ = H3π B
        (corestrictionCocyclesThree B T
          (mapCocycles₃ (MonoidHom.id H)
            ((Rep.resFunctor (Subgroup.subtype H)).map φ) z)) :=
      congrArg (H3π B)
        (mapCocycles₃_corestrictionCocyclesThree φ T z)

/-- Elementwise coefficient naturality of chosen-transversal degree-three
corestriction. -/
theorem corestrictionH3OfRightTransversal_naturality_apply
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex]
    (x : H3 (Rep.res (Subgroup.subtype H) A)) :
    map (MonoidHom.id G) φ 3
        (corestrictionH3OfRightTransversal A T x) =
      corestrictionH3OfRightTransversal B T
        (map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 3 x) := by
  induction x using H3_induction_on with
  | _ z =>
      calc
        map (MonoidHom.id G) φ 3
            (corestrictionH3OfRightTransversal A T
              (H3π (Rep.res (Subgroup.subtype H) A) z)) =
          H3π B
            (corestrictionCocyclesThree B T
              (mapCocycles₃ (MonoidHom.id H)
                ((Rep.resFunctor (Subgroup.subtype H)).map φ) z)) :=
          map_corestrictionH3OfRightTransversal_H3π φ T z
        _ = corestrictionH3OfRightTransversal B T
            (H3π (Rep.res (Subgroup.subtype H) B)
              (mapCocycles₃ (MonoidHom.id H)
                ((Rep.resFunctor (Subgroup.subtype H)).map φ) z)) :=
          (corestrictionH3OfRightTransversal_H3π B T _).symm
        _ = corestrictionH3OfRightTransversal B T
            (map (MonoidHom.id H)
              ((Rep.resFunctor (Subgroup.subtype H)).map φ) 3
              (H3π (Rep.res (Subgroup.subtype H) A) z)) := by
          rw [H3π_comp_map_apply]

/-- Bundled linear-map square for coefficient naturality of the
chosen-transversal degree-three corestriction. -/
theorem corestrictionH3OfRightTransversal_naturality
    {A B : Rep k G} (φ : A ⟶ B)
    (T : H.RightTransversal) [H.FiniteIndex] :
    (map (MonoidHom.id G) φ 3).hom.comp
        (corestrictionH3OfRightTransversal A T) =
      (corestrictionH3OfRightTransversal B T).comp
        (map (MonoidHom.id H)
          ((Rep.resFunctor (Subgroup.subtype H)).map φ) 3).hom := by
  apply LinearMap.ext
  intro x
  exact corestrictionH3OfRightTransversal_naturality_apply φ T x

end groupCohomology
