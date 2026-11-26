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
# Corestriction under ambient group equivalences and subgroup identifications

Let k be a commutative ring, e:G≅G' an equivalence of groups in universe u, H≤G of finite index,
and A a k-linear G'-representation. The subgroup H_e=e(H) is equivalent to H. The coefficient
comparison Res_{e_H}(Res_{H_e}A)≅Res_H(Res_e A) is the identity on A. For degrees n=1,2,
pullback along e commutes with canonical corestriction after this subgroup comparison.

Transporting a right transversal T to e(T) gives the corresponding cochain and cocycle
identities. The one-cochain transfer is Σ_tρ(t⁻¹)f(h_T(t,g)); the two-cochain transfer uses the
successive Schreier factors h_T(t,g) and h_T(r_T(t,g),j). These formulas give naturality first
for chosen transversals and then for the canonical cohomology maps.

The same square allows a coefficient morphism Res_e A→B and an explicit equality identifying
e(H) with another subgroup H'. For a subgroup chain K≤H≤G, an identification of the image of K
with J≤G gives the degree-one and degree-two transitivity formulas after the coefficient
comparison Res_i(Res_J A)≅Res_K(Res_H A) for the induced equivalence i:K≅J.
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. This gives an isomorphism of the two H-representations obtained by first restricting to H_e
and then along e_H, or first along e and then to H. Both group actions are h↦ρ_A(e(h)). -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. The forward and inverse maps leave every coefficient a∈A unchanged. The
subgroup equality h is used in the induced group equivalence e_H and both restricted coefficient
actions. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. For a k-linear G-representation B and coefficient morphism φ:A_e→B, the induced H-morphism
φ_H:Res_{e_H}(Res_{H_e}A)→Res_H B is α_H.hom≫Res_H(φ). Its coefficient value is the same
additive function φ(a). -/
noncomputable def mulEquivSubgroupResHom (e : G ≃* G')
    (H : Subgroup G) {A : Rep k G'} {B : Rep k G}
    (φ : Rep.res e.toMonoidHom A ⟶ B) :
    Rep.res (H.mapMulEquivEquiv e).toMonoidHom
        (Rep.res (Subgroup.subtype (H.map e.toMonoidHom)) A) ⟶
      Rep.res (Subgroup.subtype H) B :=
  (mulEquivSubgroupResIso e H A).hom ≫
    (Rep.resFunctor (Subgroup.subtype H)).map φ

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. For a G-representation B and φ:A_e→B, the induced subgroup coefficient
map is φ_H=α_H.hom≫Res_H(φ):Res_{e_H}(Res_{H'}A)→Res_H B. The group equivalence e_H retains the
specified image equality h. -/
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

/-- Let M be a group in universe u, J≤M a finite-index subgroup, and T a right transversal. Its
representative set T⊆M is finite, giving the finite indexing set for the Schreier corestriction
sums. The ambient group M itself may be infinite. -/
noncomputable local instance corestrictionEquivRightTransversalFintype
    {M : Type u} [Group M] {J : Subgroup M}
    (T : J.RightTransversal) [J.FiniteIndex] : Fintype (T : Set M) :=
  @Fintype.ofFinite (T : Set M) (T.2.finite_right)

/-- Let G,G' be groups in universe u, e:G≅G' a multiplicative equivalence, H≤G of finite index, and
T a right transversal for H. Its transported transversal e(T) for e(H) has finite representative
set. The map t↦e(t) identifies the two representative sets. -/
noncomputable local instance corestrictionEquivMappedRepresentativeFintype
    (e : G ≃* G') (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.mapMulEquiv e : Set G') :=
  @Fintype.ofFinite _ (T.mapMulEquiv e).2.finite_right

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. Assume H has finite index in G. For a right transversal T, let T'=e(T) and f:H_e→A.
Then Tr_{T'}^A(f)(e(g))=Tr_T^{A_e}(f∘e_H)(g) for every g∈G. The right-hand sum is
Σ_{t∈T}ρ_A(e(t⁻¹))f(e_H(h_T(t,g))), where t g=h_T(t,g)r_T(t,g) is the Schreier decomposition. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. Assume H has finite index in G. For a right transversal T, T'=e(T), and f:H_e²→A,
Tr_{T'}^A(f)(e(g),e(j))=Tr_T^{A_e}(f∘(e_H×e_H))(g,j). The right-hand sum is
Σ_tρ_A(e(t⁻¹))f(e_H(h_T(t,g)),e_H(h_T(r_T(t,g),j))), using t g=h_T(t,g)r_T(t,g). -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Let T be a right transversal, T'=e(T), and
z∈Z¹(H_e,Res_{H_e}A). With e^*,e_H^* the induced cycle maps using identity and α_H.hom
coefficients, e^*(Tr_{T'}z)=Tr_T(e_H^*z) in Z¹(G,A_e). -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. For a right transversal T, T'=e(T), and z∈Z²(H_e,Res_{H_e}A),
the cycle pullbacks satisfy e^*(Tr_{T'}z)=Tr_T(e_H^*z) in Z²(G,A_e). Ambient pullback uses
identity coefficients, and subgroup pullback uses α_H.hom. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Write e^* for the cohomology map with identity coefficient on
A_e, and e_H^* for subgroup pullback with coefficient morphism α_H.hom. For a right transversal
T, T'=e(T), and x∈H¹(H_e,Res_{H_e}A), e^*(cor_{T'}(x))=cor_T(e_H^*x) in H¹(G,A_e). The two
corestrictions use the transported transversals. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Write e^* for the cohomology map with identity coefficient on
A_e, and e_H^* for subgroup pullback with coefficient morphism α_H.hom. For a right transversal
T, T'=e(T), and x∈H²(H_e,Res_{H_e}A), e^*(cor_{T'}(x))=cor_T(e_H^*x) in H²(G,A_e). The subgroup
coefficient comparison precedes the source-group corestriction. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Write e^* for the cohomology map with identity coefficient on
A_e, and e_H^* for subgroup pullback with coefficient morphism α_H.hom. For
x∈H¹(H_e,Res_{H_e}A), e^*(cor_{H_e}^{G'}(x))=cor_H^G(e_H^*x). The equality lies in H¹(G,A_e),
and both corestrictions are the transversal-independent maps. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Write e^* for the cohomology map with identity coefficient on
A_e, and e_H^* for subgroup pullback with coefficient morphism α_H.hom. For
x∈H²(H_e,Res_{H_e}A), e^*(cor_{H_e}^{G'}(x))=cor_H^G(e_H^*x). The equality lies in H²(G,A_e),
and both corestrictions are the transversal-independent maps. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Write e^* for the cohomology map with identity coefficient on
A_e, and e_H^* for subgroup pullback with coefficient morphism α_H.hom. As k-linear maps
H¹(H_e,Res_{H_e}A)→H¹(G,A_e), e^*∘cor_{H_e}^{G'}=cor_H^G∘e_H^*. This is equality of the full
degree-one maps with the stated coefficient comparison. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. Write e^* for the cohomology map with identity coefficient on
A_e, and e_H^* for subgroup pullback with coefficient morphism α_H.hom. As k-linear maps
H²(H_e,Res_{H_e}A)→H²(G,A_e), e^*∘cor_{H_e}^{G'}=cor_H^G∘e_H^*. This is equality of the full
degree-two maps with the stated coefficient comparison. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. For a G-representation B and φ:A_e→B, put
φ_H=α_H.hom≫Res_H(φ). If x∈H¹(H_e,Res_{H_e}A), then
map_{e,φ}(cor_{H_e}^{G'}x)=cor_H^G(map_{e_H,φ_H}x) in H¹(G,B). Both group pullbacks use their
displayed coefficient morphisms. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G' be a multiplicative equivalence and H≤G. Put H_e=e(H), e_H:H≅H_e, and
A_e=Res_e A. The coefficient comparison α_H:Res_{e_H}(Res_{H_e}A)≅Res_H A_e is the identity on
A. Assume H has finite index in G. For a G-representation B and φ:A_e→B, put
φ_H=α_H.hom≫Res_H(φ). If x∈H²(H_e,Res_{H_e}A), then
map_{e,φ}(cor_{H_e}^{G'}x)=cor_H^G(map_{e_H,φ_H}x) in H²(G,B). Both group pullbacks use their
displayed coefficient morphisms. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. Assume H≤G and H'≤G' have finite index. For x∈H¹(H',Res_{H'}A),
map_{e,id}(cor_{H'}^{G'}x)=cor_H^G(map_{e_H,α_H.hom}x) in H¹(G,A_e). The image-subgroup equality
h is retained in the subgroup equivalence and its coefficient comparison. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. Assume H≤G and H'≤G' have finite index. For x∈H²(H',Res_{H'}A),
map_{e,id}(cor_{H'}^{G'}x)=cor_H^G(map_{e_H,α_H.hom}x) in H²(G,A_e). The image-subgroup equality
h is retained in the subgroup equivalence and its coefficient comparison. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. Assume H≤G and H'≤G' have finite index. For a G-representation B and
φ:A_e→B, put φ_H=α_H.hom≫Res_H(φ). For x∈H¹(H',Res_{H'}A),
map_{e,φ}(cor_{H'}^{G'}x)=cor_H^G(map_{e_H,φ_H}x) in H¹(G,B). -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. Assume H≤G and H'≤G' have finite index. For a G-representation B and
φ:A_e→B, put φ_H=α_H.hom≫Res_H(φ). For x∈H²(H',Res_{H'}A),
map_{e,φ}(cor_{H'}^{G'}x)=cor_H^G(map_{e_H,φ_H}x) in H²(G,B). -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. Assume H≤G and H'≤G' have finite index. As k-linear maps
H¹(H',Res_{H'}A)→H¹(G,A_e), map_{e,id}∘cor_{H'}^{G'}=cor_H^G∘map_{e_H,α_H.hom}. The identity
coefficient on ambient pullback and α_H.hom on subgroup pullback give the complete square. -/
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

/-- Let k be a commutative ring, G,G' groups, and A a k-linear G'-representation, all in the given
universe u. Let e:G≅G', H≤G, H'≤G', and h:e(H)=H'. Put A_e=Res_e A, and let e_H:H≅H' be the
equivalence determined by e,h. The comparison α_H:Res_{e_H}(Res_{H'}A)≅Res_H A_e is the identity
coefficient isomorphism. Assume H≤G and H'≤G' have finite index. As k-linear maps
H²(H',Res_{H'}A)→H²(G,A_e), map_{e,id}∘cor_{H'}^{G'}=cor_H^G∘map_{e_H,α_H.hom}. The identity
coefficient on ambient pullback and α_H.hom on subgroup pullback give the complete square. -/
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

/-- Let k be a commutative ring, G a group, H≤G, K≤H, J≤G, and h:K.map(H↪G)=J, with a k-linear
G-representation A in universe u. Let i:K≅J be the induced inclusion-image equivalence. The
coefficient isomorphism η:Res_i(Res_J A)≅Res_K(Res_H A) is the identity on A; both K-actions are
restriction along the composite inclusions. -/
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

/-- Let k be a commutative ring, G a group, H≤G, K≤H, and J≤G the specified image of K, with
h:K.map(H↪G)=J. Let A be a k-linear G-representation in universe u, and assume K≤H, H≤G, and J≤G
all have finite index. With i:K≅J and η:Res_i(Res_J A)≅Res_K(Res_H A), every x∈H¹(J,Res_J A)
satisfies cor_J^G(x)=cor_H^G(cor_K^H(map_{i,η.hom}(x))). The intermediate coefficient for
cor_K^H is Res_H A. -/
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

/-- Let k be a commutative ring, G a group, H≤G, K≤H, and J≤G the specified image of K, with
h:K.map(H↪G)=J. Let A be a k-linear G-representation in universe u, and assume K≤H, H≤G, and J≤G
all have finite index. With i:K≅J and η:Res_i(Res_J A)≅Res_K(Res_H A), every x∈H²(J,Res_J A)
satisfies cor_J^G(x)=cor_H^G(cor_K^H(map_{i,η.hom}(x))). The intermediate coefficient for
cor_K^H is Res_H A. -/
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
