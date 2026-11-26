/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryIndependence

/-!
# Schreier transfer and pullback along a surjective homomorphism

A surjective group homomorphism π : G′ → G identifies the right cosets of H ≤ G with those of
π⁻¹H. Choosing lifts of a right transversal T gives a right transversal T′ for π⁻¹H, and π
identifies their representatives. The representative updates, full tuple scans and subgroup
factor tuples commute with π.

For finite-index H and a G-representation A, pullback of the T-transfer equals the T′-transfer
of the pulled-back cochain. This yields commuting squares on cochain complexes and in every
cohomology degree. Independence of the transversal gives the corresponding canonical
corestriction-inflation identity.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace Subgroup.RightTransversal

universe u

variable {G G' : Type u} [Group G] [Group G']
variable {H : Subgroup G}

/-- A lifted representative of a preimage right coset.

For surjective π : G′ → G and right transversal T of H, choose a π-preimage of the
T-representative of the image of a right coset of π⁻¹H. -/
noncomputable def comapSurjectiveRep
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (q : Quotient (QuotientGroup.rightRel (H.comap pi))) : G' :=
  Function.surjInv hpi
    (T.2.toRightFun (pi (Quotient.out q)))

/-- The image of the selected lifted representative.

Applying π to the chosen representative of a preimage coset gives the T-representative of its
image coset. -/
@[simp]
theorem map_comapSurjectiveRep
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (q : Quotient (QuotientGroup.rightRel (H.comap pi))) :
    pi (comapSurjectiveRep pi hpi T q) =
      T.2.toRightFun (pi (Quotient.out q)) :=
  Function.surjInv_eq hpi _

/-- The chosen lift represents its preimage coset.

The quotient class of comapSurjectiveRep π hπ T q is q in the right quotient by π⁻¹H. -/
theorem mk_comapSurjectiveRep
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (q : Quotient (QuotientGroup.rightRel (H.comap pi))) :
    Quotient.mk'' (comapSurjectiveRep pi hpi T q) = q := by
  calc
    Quotient.mk'' (comapSurjectiveRep pi hpi T q) =
        Quotient.mk'' (Quotient.out q) := by
      symm
      apply Quotient.sound'
      apply QuotientGroup.rightRel_apply.mpr
      change pi (comapSurjectiveRep pi hpi T q *
        (Quotient.out q)⁻¹) ∈ H
      rw [map_mul, map_inv, map_comapSurjectiveRep]
      exact T.2.toRightFun_mul_inv_mem (pi (Quotient.out q))
    _ = q := q.out_eq'

/-- The right transversal pulled back along a surjection.

The chosen lifts of the T-representatives form a right transversal for H.comap π in G′. -/
noncomputable def comapSurjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) :
    (H.comap pi).RightTransversal :=
  ⟨Set.range (comapSurjectiveRep pi hpi T),
    Subgroup.isComplement_range_right
      (mk_comapSurjectiveRep pi hpi T)⟩

/-- Lifted representatives map into the target transversal.

If s belongs to the pulled-back transversal in G′, then π(s) belongs to T in G. -/
theorem map_mem_of_mem_comapSurjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (s : G') (hs : s ∈ (comapSurjective pi hpi T : Set G')) :
    pi s ∈ (T : Set G) := by
  rcases hs with ⟨q, rfl⟩
  rw [map_comapSurjectiveRep]
  exact (T.2.toRightFun (pi (Quotient.out q))).property

/-- The map from lifted representatives to target representatives.

The pulled-back transversal maps to T by s ↦ π(s), with membership in T given by its
construction. -/
noncomputable def comapSurjectiveRepMap
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) :
    ((comapSurjective pi hpi T : Set G')) → (T : Set G) :=
  fun s => ⟨pi s, map_mem_of_mem_comapSurjective pi hpi T s s.property⟩

/-- Ambient coordinates of the representative projection.

The underlying value in G of comapSurjectiveRepMap π hπ T s is π(s). -/
@[simp]
theorem coe_comapSurjectiveRepMap
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (s : (comapSurjective pi hpi T : Set G')) :
    (comapSurjectiveRepMap pi hpi T s : G) = pi (s : G') :=
  rfl

/-- Injectivity of the projection on lifted representatives.

Two representatives in the chosen pulled-back transversal with the same image under π are
equal. -/
theorem comapSurjectiveRepMap_injective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) :
    Function.Injective (comapSurjectiveRepMap pi hpi T) := by
  intro s₁ s₂ hs
  apply Subtype.ext
  have hrel : (s₁ : G') * (s₂ : G')⁻¹ ∈ H.comap pi := by
    change pi ((s₁ : G') * (s₂ : G')⁻¹) ∈ H
    rw [map_mul, map_inv]
    have hs' : pi (s₁ : G') = pi (s₂ : G') :=
      congrArg Subtype.val hs
    rw [hs']
    simp
  have huniq :=
    (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp
      (comapSurjective pi hpi T).2 (s₁ : G'))
  exact congrArg Subtype.val (huniq.unique
    (y₁ := s₁) (y₂ := s₂) (by simp) hrel)

/-- Surjectivity of the projection on lifted representatives.

Every representative t ∈ T is the image under π of a representative in the pulled-back
transversal. -/
theorem comapSurjectiveRepMap_surjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) :
    Function.Surjective (comapSurjectiveRepMap pi hpi T) := by
  intro t
  let g' : G' := Function.surjInv hpi (t : G)
  let q : Quotient (QuotientGroup.rightRel (H.comap pi)) :=
    Quotient.mk'' g'
  let s : (comapSurjective pi hpi T : Set G') :=
    ⟨comapSurjectiveRep pi hpi T q, ⟨q, rfl⟩⟩
  refine ⟨s, Subtype.ext ?_⟩
  change pi (comapSurjectiveRep pi hpi T q) = (t : G)
  rw [map_comapSurjectiveRep]
  have hq₁ : Quotient.mk'' (Quotient.out q) = q := q.out_eq'
  have hq₂ : q = Quotient.mk'' g' := rfl
  have hq := hq₁.trans hq₂
  have hrel' : Quotient.out q * g'⁻¹ ∈ H.comap pi :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact' hq.symm)
  have hrel : pi (Quotient.out q) * (t : G)⁻¹ ∈ H := by
    change pi (Quotient.out q * g'⁻¹) ∈ H at hrel'
    rw [map_mul, map_inv, Function.surjInv_eq hpi (t : G)] at hrel'
    exact hrel'
  have huniq :=
    (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp
      T.2 (pi (Quotient.out q)))
  exact congrArg Subtype.val (huniq.unique
    (y₁ := T.2.toRightFun (pi (Quotient.out q))) (y₂ := t)
    (T.2.mul_inv_toRightFun_mem (pi (Quotient.out q))) hrel)

/-- The equivalence between lifted and target representatives.

The map s ↦ π(s) identifies the pulled-back right transversal for π⁻¹H with T. -/
noncomputable def comapSurjectiveRepEquiv
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) :
    ((comapSurjective pi hpi T : Set G')) ≃ (T : Set G) :=
  Equiv.ofBijective (comapSurjectiveRepMap pi hpi T)
    ⟨comapSurjectiveRepMap_injective pi hpi T,
      comapSurjectiveRepMap_surjective pi hpi T⟩

/-- Coordinates of the lifted-transversal equivalence.

The representative corresponding to s under the equivalence with T has ambient value π(s). -/
@[simp]
theorem coe_comapSurjectiveRepEquiv
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (s : (comapSurjective pi hpi T : Set G')) :
    (comapSurjectiveRepEquiv pi hpi T s : G) = pi (s : G') :=
  rfl

/-- Schreier representative updates commute with a surjection.

Projecting the representative update of s by g ∈ G′ equals updating π(s) by π(g) in T. -/
theorem map_comapSurjective_schreierRep
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal)
    (s : (comapSurjective pi hpi T : Set G')) (g : G') :
    comapSurjectiveRepMap pi hpi T
        ((comapSurjective pi hpi T).schreierRep s g) =
      T.schreierRep (comapSurjectiveRepMap pi hpi T s) (pi g) := by
  let S := comapSurjective pi hpi T
  let sT := comapSurjectiveRepMap pi hpi T s
  let rS := S.schreierRep s g
  let rT := T.schreierRep sT (pi g)
  have hrS : pi (rS : G') ∈ (T : Set G) :=
    map_mem_of_mem_comapSurjective pi hpi T rS rS.property
  let rS' : (T : Set G) := ⟨pi (rS : G'), hrS⟩
  have hrTmem : ((sT : G) * pi g) * (rT : G)⁻¹ ∈ H := by
    dsimp only [rT]
    have hmul := T.schreierFactor_mul_schreierRep sT (pi g)
    rw [← hmul]
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using
      (T.schreierFactor sT (pi g)).property
  have hrSmem : ((sT : G) * pi g) * (rS' : G)⁻¹ ∈ H := by
    have hmul := S.schreierFactor_mul_schreierRep s g
    have hmapped := congrArg pi hmul
    simp only [map_mul] at hmapped
    change pi (S.schreierFactor s g : G') * pi (rS : G') =
      pi (s : G') * pi g at hmapped
    change (pi (s : G') * pi g) * (pi (rS : G'))⁻¹ ∈ H
    rw [← hmapped]
    have hfactor : pi (S.schreierFactor s g : G') ∈ H :=
      (S.schreierFactor s g).property
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hfactor
  have huniq :=
    (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp
      T.2 ((sT : G) * pi g))
  have heq : rS' = rT := huniq.unique
    (y₁ := rS') (y₂ := rT) hrSmem hrTmem
  exact Subtype.ext (congrArg Subtype.val heq)

/-- Complete representative scans commute with a surjection.

Projecting each step of a tuple scan in the lifted transversal gives the T-scan of the
coordinatewise image tuple under π. -/
theorem map_comapSurjective_schreierRepScan
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) {n : ℕ}
    (s : (comapSurjective pi hpi T : Set G'))
    (g : Fin n → G') (i : Fin (n + 1)) :
    comapSurjectiveRepMap pi hpi T
        ((comapSurjective pi hpi T).schreierRepScan s g i) =
      T.schreierRepScan (comapSurjectiveRepMap pi hpi T s)
        (fun j => pi (g j)) i := by
  induction i using Fin.induction with
  | zero =>
      simp only [schreierRepScan_get_zero]
  | succ i ih =>
      rw [schreierRepScan_get_succ, schreierRepScan_get_succ]
      rw [map_comapSurjective_schreierRep, ih]

/-- Subgroup factor tuples commute with a surjection.

The image under π of each factor in the π⁻¹H-scan is the corresponding H-factor of the
projected tuple scan. -/
theorem map_comapSurjective_schreierFactorTuple
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) {n : ℕ}
    (s : (comapSurjective pi hpi T : Set G'))
    (g : Fin n → G') (i : Fin n) :
    pi (((comapSurjective pi hpi T).schreierFactorTuple s g i :
        H.comap pi) : G') =
      (T.schreierFactorTuple
        (comapSurjectiveRepMap pi hpi T s) (fun j => pi (g j)) i : H) := by
  have hscan (j : Fin (n + 1)) :
      pi (((comapSurjective pi hpi T).schreierRepScan s g j :
          (comapSurjective pi hpi T : Set G')) : G') =
        (T.schreierRepScan (comapSurjectiveRepMap pi hpi T s)
          (fun t => pi (g t)) j : G) :=
    congrArg Subtype.val
      (map_comapSurjective_schreierRepScan pi hpi T s g j)
  rw [schreierFactorTuple_coe, schreierFactorTuple_coe]
  rw [map_mul, map_mul, map_inv]
  rw [← coe_comapSurjectiveRepMap,
    map_comapSurjective_schreierRepScan, hscan]

end Subgroup.RightTransversal

namespace groupCohomology

universe u

variable {k G G' : Type u} [CommRing k] [Group G] [Group G']
variable {H : Subgroup G}

/-- The coefficient identification for two successive restrictions.

For π : G′ → G, the representation restricted first to H then along π : π⁻¹H → H is isomorphic
to the representation pulled back to G′ then restricted to π⁻¹H. The comparison is the
identity on coefficient elements. -/
noncomputable def comapSubgroupResIso
    (pi : G' →* G) (H : Subgroup G) (A : Rep k G) :
    Rep.res (pi.subgroupComap H)
        (Rep.res H.subtype A) ≅
      Rep.res (H.comap pi).subtype (Rep.res pi A) :=
  eqToIso (by rfl)

/-- Values of the preimage-subgroup coefficient comparison.

The forward coefficient comparison sends each x ∈ A to x. -/
@[simp]
theorem comapSubgroupResIso_hom_apply
    (pi : G' →* G) (H : Subgroup G) (A : Rep k G) (x : A) :
    (comapSubgroupResIso pi H A).hom x = x :=
  rfl

/-- The linear map of the preimage-subgroup coefficient comparison.

The underlying linear map of comapSubgroupResIso π H A is the identity. -/
@[simp]
theorem comapSubgroupResIso_hom_toLinearMap
    (pi : G' →* G) (H : Subgroup G) (A : Rep k G) :
    (comapSubgroupResIso pi H A).hom.hom.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact comapSubgroupResIso_hom_apply pi H A x

/-- Finite target representatives for surjective pullback.

For finite-index H, the target transversal T is finitely enumerated for the pullback-transfer
comparison. -/
noncomputable local instance surjectivePullbackTargetTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Finite lifted representatives for surjective pullback.

For surjective π and finite-index H, the pulled-back transversal of π⁻¹H is finitely
enumerated. -/
noncomputable local instance surjectivePullbackSourceTransversalFintype
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (T : H.RightTransversal) [H.FiniteIndex] :
    Fintype (T.comapSurjective pi hpi : Set G') :=
  @Fintype.ofFinite (T.comapSurjective pi hpi : Set G')
    ((T.comapSurjective pi hpi).2.finite_right)

/-- The tuple transfer formula under surjective pullback.

Pullback along π of the T-transfer equals transfer with the lifted transversal of the cochain
pulled back along π : π⁻¹H → H, with coefficients π* A. -/
theorem corestrictionCochain_comapSurjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ) (f : (Fin n → H) → A) :
    (fun g : Fin n → G' =>
      corestrictionCochain A T n f (fun i => pi (g i))) =
      corestrictionCochain (Rep.res pi A)
        (T.comapSurjective pi hpi) n
        (fun h => f (fun i => pi.subgroupComap H (h i))) := by
  funext g
  rw [corestrictionCochain_apply, corestrictionCochain_apply]
  let S := T.comapSurjective pi hpi
  let e := T.comapSurjectiveRepEquiv pi hpi
  calc
    (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (f (T.schreierFactorTuple t (fun i => pi (g i))))) =
      ∑ s : (S : Set G'),
        A.ρ (e s : G)⁻¹
          (f (T.schreierFactorTuple (e s)
            (fun i => pi (g i)))) := by
      exact (e.sum_comp (fun t : (T : Set G) =>
        A.ρ (t : G)⁻¹
          (f (T.schreierFactorTuple t (fun i => pi (g i)))))).symm
    _ = ∑ s : (S : Set G'),
        (Rep.res pi A).ρ (s : G')⁻¹
          (f (fun i => pi.subgroupComap H
            (S.schreierFactorTuple s g i))) := by
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [e, S]
      rw [show (T.comapSurjectiveRepEquiv pi hpi s : G) =
          pi (s : G') by rfl]
      congr 1
      · change A.ρ ((pi (s : G'))⁻¹) =
          A.ρ (pi ((s : G')⁻¹))
        exact congrArg A.ρ (map_inv pi (s : G')).symm
      · apply congrArg f
        funext i
        apply Subtype.ext
        change (T.schreierFactorTuple
            (T.comapSurjectiveRepMap pi hpi s)
            (fun j => pi (g j)) i : G) =
          pi ((T.comapSurjective pi hpi).schreierFactorTuple
            s g i : G')
        exact (T.map_comapSurjective_schreierFactorTuple
          pi hpi s g i).symm

/-- The cochain-complex square for surjective pullback.

Transfer from H to G followed by cochain pullback along π equals pullback to π⁻¹H, with the
canonical coefficient comparison, followed by transfer to G′ using the lifted transversal. -/
theorem corestrictionCochains_comapSurjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCochains A T ≫
        groupCohomology.cochainsMap pi
          (𝟙 (Rep.res pi A)) =
      groupCohomology.cochainsMap (pi.subgroupComap H)
          (comapSubgroupResIso pi H A).hom ≫
        corestrictionCochains (Rep.res pi A)
          (T.comapSurjective pi hpi) := by
  ext n f g
  exact congrFun
    (corestrictionCochain_comapSurjective pi hpi A T n f) g

set_option backward.isDefEq.respectTransparency false in
/-- The chosen-transfer square for inflation along a surjection.

In every degree n, transfer from H to G followed by pullback along π equals subgroup pullback
to π⁻¹H followed by transfer with the pulled-back transversal to G′. -/
theorem corestrictionOfRightTransversal_comapSurjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    corestrictionOfRightTransversal A T n ≫
        groupCohomology.map pi (𝟙 (Rep.res pi A)) n =
      groupCohomology.map (pi.subgroupComap H)
          (comapSubgroupResIso pi H A).hom n ≫
        corestrictionOfRightTransversal (Rep.res pi A)
          (T.comapSurjective pi hpi) n := by
  simpa only [corestrictionOfRightTransversal,
    ← HomologicalComplex.homologyMap_comp] using
    congrArg (fun q => HomologicalComplex.homologyMap q n)
      (corestrictionCochains_comapSurjective pi hpi A T)

/-- Canonical corestriction commutes with surjective inflation.

For surjective π : G′ → G and finite-index H ≤ G, inflation after canonical corestriction
equals canonical corestriction from π⁻¹H after the subgroup inflation, with the identity
coefficient comparison. -/
@[reassoc]
theorem schreierCorestriction_comapSurjective
    (pi : G' →* G) (hpi : Function.Surjective pi)
    (A : Rep k G) [H.FiniteIndex] (n : ℕ) :
    schreierCorestriction H A n ≫
        groupCohomology.map pi (𝟙 (Rep.res pi A)) n =
      groupCohomology.map (pi.subgroupComap H)
          (comapSubgroupResIso pi H A).hom n ≫
        schreierCorestriction (H.comap pi) (Rep.res pi A) n := by
  let T : H.RightTransversal := default
  rw [schreierCorestriction_eq_of_rightTransversal H A T n]
  rw [schreierCorestriction_eq_of_rightTransversal
    (H.comap pi) (Rep.res pi A) (T.comapSurjective pi hpi) n]
  exact corestrictionOfRightTransversal_comapSurjective
    pi hpi A T n

end groupCohomology
