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
# Coefficient naturality of degree-three Schreier transfer

For a finite-index H ≤ G, fixed right transversal T and G-equivariant linear map φ : A → B,
the ternary transfer satisfies φ∘cor_T³(z) = cor_T³(φ∘z). The same square commutes on three-
cocycles and on degree-three classes.

The identities are given both on individual cochains or represented classes and as equalities
of the bundled linear maps. The coefficient map on H is the restriction of φ.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for degree-three coefficient naturality.

The finite-index hypothesis supplies a finite enumeration of T for comparing the ternary
transfer sums under a coefficient map. -/
noncomputable local instance corestrictionDegreeThreeNaturalityTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Coefficient maps commute with ternary transfer.

For a G-equivariant linear φ : A → B and ternary H-cochain z, postcomposition by φ commutes
with cor_T³. -/
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

/-- The linear-map square for ternary coefficient naturality.

The G-cochain coefficient map composed with the ternary transfer for A equals the transfer for
B composed with the restricted H-cochain coefficient map. -/
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

/-- Coefficient maps commute with transferred three-cocycles.

Mapping a transferred H-three-cocycle by φ equals transferring its image under the restricted
coefficient morphism. -/
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

/-- The linear-map square on three-cocycles.

The map on G-three-cocycles induced by φ composed with transfer for A equals transfer for B
composed with the induced map on H-three-cocycles. -/
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

/-- Coefficient naturality on a represented degree-three class.

For a three-cocycle z, mapping the class of its transfer by φ gives the class of the transfer
of the restricted coefficient image of z. -/
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

/-- Coefficient naturality on an arbitrary degree-three class.

For x ∈ H³(H,A|H), mapping its transferred class into H³(G,B) equals transferring its
restricted coefficient image in H³(H,B|H). -/
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

/-- The linear-map square for degree-three cohomology.

The degree-three G-coefficient map after the chosen transfer for A equals the chosen transfer
for B after the degree-three restricted H-coefficient map. -/
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
