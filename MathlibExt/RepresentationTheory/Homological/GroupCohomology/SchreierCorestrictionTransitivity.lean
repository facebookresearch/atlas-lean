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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierCorestrictionNaturality

/-!
# Transitivity of corestriction in degrees one and two

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `K ≤ H` finite index.
Put `J=K.map H.subtype` and let `q : K ≃* J` be the canonical image equivalence. Right
transversals `S` for `K ≤ H` and `T` for `H ≤ G` have a product transversal for `J ≤ G`, with
representatives `s t` in this order.

The product-transversal transfer equals the successive cochain, cocycle, and cohomology
transfers through `H`, in degrees one and two. The coefficient isomorphism `q^*(Res_J A) ≅
Res_K(Res_H A)` makes the two subgroup presentations agree. For canonical corestriction,
`cor_J^G = cor_H^G ∘ cor_K^H ∘ q^*` in both degrees.
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

/-- For a group `M`, a finite-index subgroup `J ≤ M`, and a right transversal `T`, the subtype `(T
: Set M)` has a finite enumeration. This local `Fintype` structure supplies the finite
representative sets for transfer sums. -/
noncomputable local instance corestrictionTransitivityRightTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- Let `G` be a group, `H ≤ G` a finite-index subgroup, and `K ≤ H` finite index in `H`. Then
`K.map H.subtype ≤ G` has finite index in `G`. Its index is the product `[H:K] [G:H]`. -/
theorem finiteIndex_map_subtype [K.FiniteIndex] [H.FiniteIndex] :
    (K.map H.subtype).FiniteIndex :=
  ⟨by
    rw [Subgroup.index_map_subtype]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
      Subgroup.FiniteIndex.index_ne_zero⟩

noncomputable local instance corestrictionTransitivityMapFiniteIndex
    [K.FiniteIndex] [H.FiniteIndex] : (K.map H.subtype).FiniteIndex :=
  finiteIndex_map_subtype

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, `K ≤ H`, and `A : Rep k G`. Put `J=K.map
H.subtype` and `q=K.equivMapOfInjective H.subtype H.subtype_injective : K ≃* J`. The
isomorphism `mapSubtypeResIso A : q^*(Res_J A) ≅ Res_K(Res_H A)` is the identity on the
underlying coefficient module. -/
noncomputable def mapSubtypeResIso (A : Rep k G) :
    Rep.res
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (Rep.res (Subgroup.subtype (K.map H.subtype)) A) ≅
      Rep.res (Subgroup.subtype K) (Rep.res (Subgroup.subtype H) A) :=
  eqToIso (by rfl)

@[simp]
theorem mapSubtypeResIso_hom_apply (A : Rep k G)
    (x : A) : (mapSubtypeResIso (H := H) (K := K) A).hom x = x :=
  rfl

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Set `J=K.map H.subtype` and let `q : K ≃* J` be its image equivalence. For right
transversals `S` of `K` in `H`, `T` of `H` in `G`, and any `f : J → A`, `Tr_{S.product T}^A f
= Tr_T^A(Tr_S^{Res_H A}(f ∘ q))`. The representatives of the product transversal are `s t`. -/
theorem corestrictionCochainOne_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : K.map H.subtype → A) :
    corestrictionCochainOne A (S.product T) f =
      corestrictionCochainOne A T
        (corestrictionCochainOne (Rep.res (Subgroup.subtype H) A) S
          (fun k => f
            (K.equivMapOfInjective H.subtype H.subtype_injective k))) := by
  funext g
  rw [corestrictionCochainOne_apply, corestrictionCochainOne_apply]
  simp_rw [corestrictionCochainOne_apply]
  calc
    (∑ r : ((S.product T : Set G)),
        A.ρ (r : G)⁻¹ (f ((S.product T).schreierFactor r g))) =
      ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f ((S.product T).schreierFactor (S.productEquiv T p) g)) :=
      ((S.productEquiv T).sum_comp
        (fun r : ((S.product T : Set G)) =>
          A.ρ (r : G)⁻¹ (f ((S.product T).schreierFactor r g)))).symm
    _ = ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f (K.equivMapOfInjective H.subtype H.subtype_injective
            (S.schreierFactor p.1 (T.schreierFactor p.2 g)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [S.product_schreierFactor T p.1 p.2 g]
    _ = ∑ t : (T : Set G), ∑ s : (S : Set H),
        A.ρ (t : G)⁻¹
          (A.ρ ((s : H) : G)⁻¹
            (f (K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor s (T.schreierFactor t g))))) := by
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
                (S.schreierFactor s (T.schreierFactor t g))))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_sum]

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Put `J=K.map H.subtype`, let `q : K ≃* J`, and set `τ=(mapSubtypeResIso A).hom`.
For right transversals `S,T` of the two inclusions and `f ∈ Z¹(J,Res_J A)`, `Tr^Z_{S.product
T} f = Tr_T^Z(Tr_S^Z(mapCocycles₁ q τ f))`, with coefficients `A` and `Res_H A` on the outer
and inner sums. -/
theorem corestrictionCocyclesOne_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionCocyclesOne A (S.product T) f =
      corestrictionCocyclesOne A T
        (corestrictionCocyclesOne (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.mapCocycles₁
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom f)) := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change corestrictionCochainOne A (S.product T) f g =
    corestrictionCochainOne A T
      (corestrictionCochainOne (Rep.res (Subgroup.subtype H) A) S
        (fun k => f
          (K.equivMapOfInjective H.subtype H.subtype_injective k))) g
  exact congrFun (corestrictionCochainOne_product A S T f) g

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Put `J=K.map H.subtype`, let `q : K ≃* J`, and set `τ=(mapSubtypeResIso A).hom`.
For right transversals `S` of `K` in `H`, `T` of `H` in `G`, and `x ∈ H¹(J,Res_J A)`,
`cor_{S.product T}^A x = cor_T^A(cor_S^{Res_H A}(map q τ 1 x))`. -/
theorem corestrictionH1OfRightTransversal_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH1OfRightTransversal A (S.product T) x =
      corestrictionH1OfRightTransversal A T
        (corestrictionH1OfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 1 x)) := by
  induction x using groupCohomology.H1_induction_on with
  | _ f =>
      rw [corestrictionH1OfRightTransversal_H1π]
      have hmap := groupCohomology.H1π_comp_map_apply
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (mapSubtypeResIso (H := H) (K := K) A).hom f
      rw [hmap, corestrictionH1OfRightTransversal_H1π,
        corestrictionH1OfRightTransversal_H1π]
      exact congrArg (groupCohomology.H1π A)
        (corestrictionCocyclesOne_product A S T f)

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Put `J=K.map H.subtype`, let `q : K ≃* J` be the canonical image equivalence, and
let `τ=(mapSubtypeResIso A).hom` compare `q^*(Res_J A)` with `Res_K(Res_H A)`. For `x ∈
H¹(J,Res_J A)`, `cor_J^G x = cor_H^G(cor_K^H(map q τ 1 x))`. -/
theorem corestrictionH1_trans (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H1
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH1 (H := K.map H.subtype) A x =
      corestrictionH1 (H := H) A
        (corestrictionH1 (H := K) (Rep.res (Subgroup.subtype H) A)
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 1 x)) := by
  let S : K.RightTransversal := default
  let T : H.RightTransversal := default
  rw [corestrictionH1_eq_of_rightTransversal A (S.product T),
    corestrictionH1_eq_of_rightTransversal A T,
    corestrictionH1_eq_of_rightTransversal
      (Rep.res (Subgroup.subtype H) A) S]
  exact corestrictionH1OfRightTransversal_product A S T x

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Put `J=K.map H.subtype` and let `q : K ≃* J`. For right transversals `S` of `K` in
`H`, `T` of `H` in `G`, and any `f : J × J → A`, `Tr_{S.product T}^A f = Tr_T^A(Tr_S^{Res_H
A}(f ∘ q²))`. The product representatives are `s t` in that order. -/
theorem corestrictionCochainTwo_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : (K.map H.subtype) × (K.map H.subtype) → A) :
    corestrictionCochainTwo A (S.product T) f =
      corestrictionCochainTwo A T
        (corestrictionCochainTwo (Rep.res (Subgroup.subtype H) A) S
          (fun p => f
            (K.equivMapOfInjective H.subtype H.subtype_injective p.1,
              K.equivMapOfInjective H.subtype H.subtype_injective p.2))) := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochainTwo_apply, corestrictionCochainTwo_apply]
  simp_rw [corestrictionCochainTwo_apply]
  calc
    (∑ r : ((S.product T : Set G)),
        A.ρ (r : G)⁻¹
          (f ((S.product T).schreierFactor r g₁,
            (S.product T).schreierFactor
              ((S.product T).schreierRep r g₁) g₂))) =
      ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f ((S.product T).schreierFactor (S.productEquiv T p) g₁,
            (S.product T).schreierFactor
              ((S.product T).schreierRep (S.productEquiv T p) g₁) g₂)) :=
      ((S.productEquiv T).sum_comp
        (fun r : ((S.product T : Set G)) =>
          A.ρ (r : G)⁻¹
            (f ((S.product T).schreierFactor r g₁,
              (S.product T).schreierFactor
                ((S.product T).schreierRep r g₁) g₂)))).symm
    _ = ∑ p : ↥(S : Set H) × ↥(T : Set G),
        A.ρ (S.productRep T p)⁻¹
          (f (K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor p.1 (T.schreierFactor p.2 g₁)),
            K.equivMapOfInjective H.subtype H.subtype_injective
              (S.schreierFactor
                (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
                (T.schreierFactor (T.schreierRep p.2 g₁) g₂)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [S.product_schreierFactor T p.1 p.2 g₁,
        S.product_schreierRep T p.1 p.2 g₁,
        S.product_schreierFactor T
          (S.schreierRep p.1 (T.schreierFactor p.2 g₁))
          (T.schreierRep p.2 g₁) g₂]
    _ = ∑ t : (T : Set G), ∑ s : (S : Set H),
        A.ρ (t : G)⁻¹
          (A.ρ ((s : H) : G)⁻¹
            (f (K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor s (T.schreierFactor t g₁)),
              K.equivMapOfInjective H.subtype H.subtype_injective
                (S.schreierFactor
                  (S.schreierRep s (T.schreierFactor t g₁))
                  (T.schreierFactor (T.schreierRep t g₁) g₂))))) := by
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
                    (T.schreierFactor (T.schreierRep t g₁) g₂))))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [map_sum]

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Put `J=K.map H.subtype`, let `q : K ≃* J`, and set `τ=(mapSubtypeResIso A).hom`.
For right transversals `S,T` of the two inclusions and `f ∈ Z²(J,Res_J A)`, `Tr^Z_{S.product
T} f = Tr_T^Z(Tr_S^Z(mapCocycles₂ q τ f))`, using coefficients `A` and `Res_H A` for the outer
and inner transfers. -/
theorem corestrictionCocyclesTwo_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (f : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionCocyclesTwo A (S.product T) f =
      corestrictionCocyclesTwo A T
        (corestrictionCocyclesTwo (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.mapCocycles₂
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom f)) := by
  apply groupCohomology.cocycles₂_ext
  intro g₁ g₂
  change corestrictionCochainTwo A (S.product T) f (g₁, g₂) =
    corestrictionCochainTwo A T
      (corestrictionCochainTwo (Rep.res (Subgroup.subtype H) A) S
        (fun p => f
          (K.equivMapOfInjective H.subtype H.subtype_injective p.1,
            K.equivMapOfInjective H.subtype H.subtype_injective p.2)))
      (g₁, g₂)
  exact congrFun (corestrictionCochainTwo_product A S T f) (g₁, g₂)

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Set `J=K.map H.subtype`, let `q : K ≃* J`, and set `τ=(mapSubtypeResIso A).hom`.
For right transversals `S` of `K` in `H`, `T` of `H` in `G`, and `x ∈ H²(J,Res_J A)`,
`cor_{S.product T}^A x = cor_T^A(cor_S^{Res_H A}(map q τ 2 x))`. -/
theorem corestrictionH2OfRightTransversal_product (A : Rep k G)
    (S : K.RightTransversal) (T : H.RightTransversal)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH2OfRightTransversal A (S.product T) x =
      corestrictionH2OfRightTransversal A T
        (corestrictionH2OfRightTransversal
          (Rep.res (Subgroup.subtype H) A) S
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 2 x)) := by
  induction x using groupCohomology.H2_induction_on with
  | _ f =>
      rw [corestrictionH2OfRightTransversal_H2π]
      have hmap := groupCohomology.H2π_comp_map_apply
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
        (mapSubtypeResIso (H := H) (K := K) A).hom f
      rw [hmap, corestrictionH2OfRightTransversal_H2π,
        corestrictionH2OfRightTransversal_H2π]
      exact congrArg (groupCohomology.H2π A)
        (corestrictionCocyclesTwo_product A S T f)

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G` finite index, `K ≤ H` finite index, and `A
: Rep k G`. Put `J=K.map H.subtype`, let `q : K ≃* J` be the image equivalence, and put
`τ=(mapSubtypeResIso A).hom : q^*(Res_J A) → Res_K(Res_H A)`. For `x ∈ H²(J,Res_J A)`,
`cor_J^G x = cor_H^G(cor_K^H(map q τ 2 x))`. -/
theorem corestrictionH2_trans (A : Rep k G)
    [K.FiniteIndex] [H.FiniteIndex]
    (x : groupCohomology.H2
      (Rep.res (Subgroup.subtype (K.map H.subtype)) A)) :
    corestrictionH2 (H := K.map H.subtype) A x =
      corestrictionH2 (H := H) A
        (corestrictionH2 (H := K) (Rep.res (Subgroup.subtype H) A)
          (groupCohomology.map
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom
            (mapSubtypeResIso (H := H) (K := K) A).hom 2 x)) := by
  let S : K.RightTransversal := default
  let T : H.RightTransversal := default
  rw [corestrictionH2_eq_of_rightTransversal A (S.product T),
    corestrictionH2_eq_of_rightTransversal A T,
    corestrictionH2_eq_of_rightTransversal
      (Rep.res (Subgroup.subtype H) A) S]
  exact corestrictionH2OfRightTransversal_product A S T x

end groupCohomology
