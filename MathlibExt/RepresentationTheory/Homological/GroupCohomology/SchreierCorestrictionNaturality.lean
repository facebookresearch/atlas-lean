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

Let `G` be a group, `k` a commutative ring, `H ≤ G` a finite-index subgroup, and `φ : A → B` a
morphism of representations. Applying `φ` to the finite right-transversal cochain sum equals
transferring the cochain with coefficients mapped by `φ`. This equality holds for arbitrary
cochains and cocycles in degrees one and two.

The induced cohomology maps satisfy `φ_* ∘ cor_A^i = cor_B^i ∘ (Res φ)_*` for `i = 1,2`, both
for a prescribed right transversal and for canonical corestriction. Here the two coefficient
maps use the identity group homomorphisms on `G` and `H`, respectively.
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For every cochain `f : H → A`, `φ ∘
corestrictionCochainOne A T f = corestrictionCochainOne B T (φ ∘ f)`. The transfer has value
`∑ t∈T, ρ(t⁻¹) f(h_T(t,g))`, with `t g = h_T(t,g) r_T(t,g)`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For every cochain `z : H × H → A`, `φ ∘
corestrictionCochainTwo A T z = corestrictionCochainTwo B T (φ ∘ z)`. The transfer sends
`(g₁,g₂)` to `∑ t∈T, ρ(t⁻¹) z(h_T(t,g₁),h_T(r_T(t,g₁),g₂))`, using `t g=h_T(t,g)r_T(t,g)`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For `f ∈ Z¹(H,Res A)`, `mapCocycles₁ (id G) φ
(corestrictionCocyclesOne A T f) = corestrictionCocyclesOne B T (mapCocycles₁ (id H) (Res φ)
f)`, with `Res φ=(Rep.resFunctor (Subgroup.subtype H)).map φ`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For `z ∈ Z²(H,Res A)`, `mapCocycles₂ (id G) φ
(corestrictionCocyclesTwo A T z) = corestrictionCocyclesTwo B T (mapCocycles₂ (id H) (Res φ)
z)`, with `Res φ` the restricted coefficient morphism. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For `x ∈ H¹(H,Res A)`,
`φ_*^1(corestrictionH1OfRightTransversal A T x) = corestrictionH1OfRightTransversal B T ((Res
φ)_*^1 x)`. The induced coefficient maps are `map (id G) φ 1` and `map (id H) (Res φ) 1`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `φ : A → B` a morphism of
representations, and `T` a right transversal. For `x ∈ H²(H,Res A)`,
`φ_*^2(corestrictionH2OfRightTransversal A T x) = corestrictionH2OfRightTransversal B T ((Res
φ)_*^2 x)`. The induced coefficient maps are `map (id G) φ 2` and `map (id H) (Res φ) 2`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `φ : A → B` a morphism
of representations. For `x ∈ H¹(H,Res A)`, `map (id G) φ 1 (corestrictionH1 A x) =
corestrictionH1 B (map (id H) (Res φ) 1 x)`, where `Res φ=(Rep.resFunctor (Subgroup.subtype
H)).map φ`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `φ : A → B` a morphism
of representations. For `x ∈ H²(H,Res A)`, `map (id G) φ 2 (corestrictionH2 A x) =
corestrictionH2 B (map (id H) (Res φ) 2 x)`, with `Res φ` the coefficient morphism restricted
to `H`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `φ : A → B` a morphism
of representations. The linear maps `H¹(H,Res A) → H¹(G,B)` satisfy `φ_*^1 ∘ corestrictionH1 A
= corestrictionH1 B ∘ (Res φ)_*^1`, where `φ_*^1=(map (id G) φ 1).hom` and `(Res φ)_*^1=(map
(id H) (Res φ) 1).hom`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `φ : A → B` a morphism
of representations. The linear maps `H²(H,Res A) → H²(G,B)` satisfy `φ_*^2 ∘ corestrictionH2 A
= corestrictionH2 B ∘ (Res φ)_*^2`, where `φ_*^2=(map (id G) φ 2).hom` and `(Res φ)_*^2=(map
(id H) (Res φ) 2).hom`. -/
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
