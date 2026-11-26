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
# Degree-three transfer under group equivalences

Let `k` be a commutative ring, `e : G ≃* G'` an equivalence of groups, `H ≤ G` finite index,
and `H' = e(H)`. The induced equivalence `q : H ≃* H'` transports right transversals and their
Schreier factors. For `A : Rep k G'`, pullback along `e` carries the degree-three transfer
from `H'` to `G'` to the transfer from `H` to `G`, after the canonical subgroup coefficient
comparison.

The same identity holds for cochains, cocycles, and cohomology, and also with a morphism `e^*A
→ B` of coefficients. Equal presentations of the image subgroup are accommodated by their
induced subgroup equivalences. For a finite-index chain `K ≤ H ≤ G`, the canonical
degree-three transfers compose after identifying `K` with its image in `G`.
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

/-- For a group `M`, a finite-index subgroup `J ≤ M`, and a right transversal `T` for `J`, the
representative subtype `(T : Set M)` has a finite enumeration. This is the local `Fintype`
structure used for the finite transfer sums. -/
noncomputable local instance corestrictionH3EquivTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- Let `e : G ≃* G'` be an equivalence of groups, `H ≤ G` finite index, and `T` a right
transversal for `H`. Its image `T.mapMulEquiv e` is a right transversal for `H.map
e.toMonoidHom`, and the subtype `(T.mapMulEquiv e : Set G')` has a finite enumeration. -/
noncomputable local instance corestrictionH3EquivMappedRepresentativeFintype
    (e : G ≃* G') (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.mapMulEquiv e : Set G') :=
  @Fintype.ofFinite _ (T.mapMulEquiv e).2.finite_right

/-- Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, `H ≤ G` finite index, `T` a
right transversal, and `A : Rep k G'`. Put `H' = H.map e.toMonoidHom`, `q = H.mapMulEquivEquiv
e : H ≃* H'`, and `B = Rep.res e.toMonoidHom A`. For any cochain `f : H' × H' × H' → A`,
`(Tr_{e(T)}^A f)(e g₁,e g₂,e g₃) = Tr_T^B(f ∘ q³)(g₁,g₂,g₃)`, where `Tr` is the Schreier
three-cochain sum with weights `ρ(t⁻¹)`. -/
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

/-- Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, `H ≤ G` finite index, `T` a
right transversal, and `A : Rep k G'`. Put `H' = e(H)`, `q : H ≃* H'` for the induced
equivalence, and `B = e^*A`. For `z ∈ Z³(H',Res A)`, `e^*(corestrictionCocyclesThree A
(T.mapMulEquiv e) z) = corestrictionCocyclesThree B T (mapCocycles₃ q γ z)`, where `γ =
(mulEquivSubgroupResIso e H A).hom : q^*(Res A) → Res B`. -/
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

/-- Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, `H ≤ G` finite index, `T` a
right transversal, and `A : Rep k G'`. Write `H'=e(H)`, `q : H ≃* H'`, `B=e^*A`, and
`γ=(mulEquivSubgroupResIso e H A).hom`. For `x ∈ H³(H',Res A)`, `map e (𝟙 B) 3
(corestrictionH3OfRightTransversal A (T.mapMulEquiv e) x) = corestrictionH3OfRightTransversal
B T (map q γ 3 x)`. -/
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

/-- Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, `H ≤ G` finite index, and `A
: Rep k G'`. Put `H'=e(H)`, `q=H.mapMulEquivEquiv e : H ≃* H'`, `B=e^*A`, and
`γ=(mulEquivSubgroupResIso e H A).hom`. For `x ∈ H³(H',Res A)`, `map e (𝟙 B) 3 (cor_{H'}^{G'}
x) = cor_H^G (map q γ 3 x)` in `H³(G,B)`. -/
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

/-- Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, `H ≤ G` finite index, `A :
Rep k G'`, `B : Rep k G`, and `φ : e^*A → B`. Put `H'=e(H)`, `q=H.mapMulEquivEquiv e`, and
`ψ=mulEquivSubgroupResHom e H φ : q^*(Res A) → Res B`. For `x ∈ H³(H',Res A)`, `map e φ 3
(cor_{H'}^{G'} x) = cor_H^G (map q ψ 3 x)`. -/
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

/-- Let `k` be a commutative ring, `e : G ≃* G'` a group equivalence, and `H ≤ G`, `H' ≤ G'`
finite-index subgroups with `h : H.map e.toMonoidHom = H'`. For `A : Rep k G'`, `B : Rep k G`,
and `φ : e^*A → B`, set `q=H.mapMulEquivEquivOfEq e H' h` and `ψ=mulEquivSubgroupResHomOfEq e
H H' h φ`. For `x ∈ H³(H',Res A)`, `map e φ 3 (cor_{H'}^{G'} x) = cor_H^G (map q ψ 3 x)`. -/
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

/-- Let `k` be a commutative ring, `G` a group, `H ≤ G`, `K ≤ H`, and `J ≤ G`, with `K`, `H`, and
`J` finite index in their respective ambient groups. Suppose `h : K.map H.subtype = J`, and
let `A : Rep k G`. Write `q : K ≃* J` for the injective-image equivalence followed by
`MulEquiv.subgroupCongr h`, and `τ=(mapSubtypeResIsoOfEq h A).hom`. For `x ∈ H³(J,Res A)`,
`cor_J^G(x) = cor_H^G(cor_K^H(map q τ 3 x))`, where the intermediate coefficients are `Res_H
A`. -/
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
