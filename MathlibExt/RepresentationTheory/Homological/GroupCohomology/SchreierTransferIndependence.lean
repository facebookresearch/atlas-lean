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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransfer

/-!
# The explicit boundary comparing degree-one transfers

Two right transversals T and U match by their right cosets. Write t = c(t)u(t) with c(t) ∈ H
and u(t) ∈ U. Matching commutes with right multiplication, and the Schreier factors satisfy
a_T(t,g)c(r_T(t,g)) = c(t)a_U(u(t),g).

For finite-index H and an H-one-cocycle z with coefficients in a G-representation, set B⁰(z) =
∑ₜ ρ(t⁻¹)z(c(t)). Then cor_T¹(z) − cor_U¹(z) = d⁰(−B⁰(z)). Thus both transferred cocycles have
the same class in H¹(G,A), and the chosen degree-one cohomology maps agree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace Subgroup.RightTransversal

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- The matching representative in another right transversal.

For t ∈ T, decompose t = c(t)u(t) using the right transversal U. This defines u(t) ∈ U in the
same right coset of H. -/
noncomputable def changeRep (T U : H.RightTransversal)
    (t : (T : Set G)) : (U : Set G) :=
  (U.2.equiv (t : G)).2

/-- The subgroup factor comparing two representatives.

For t ∈ T and its matching u(t) ∈ U, this is c(t) ∈ H with t = c(t)u(t). -/
noncomputable def changeFactor (T U : H.RightTransversal)
    (t : (T : Set G)) : H :=
  (U.2.equiv (t : G)).1

/-- The change-of-representative decomposition.

The comparison factor and matching representative satisfy c(t)u(t) = t in G. -/
theorem changeFactor_mul_changeRep (T U : H.RightTransversal)
    (t : (T : Set G)) :
    (changeFactor T U t : G) * (changeRep T U t : G) = (t : G) :=
  U.2.equiv_fst_mul_equiv_snd (t : G)

/-- The inverse identity for representative change.

From t = c(t)u(t), obtain t⁻¹c(t) = u(t)⁻¹. -/
theorem inv_mul_changeFactor (T U : H.RightTransversal)
    (t : (T : Set G)) :
    (t : G)⁻¹ * (changeFactor T U t : G) =
      (changeRep T U t : G)⁻¹ := by
  rw [← changeFactor_mul_changeRep T U t]
  group

/-- The right-coset matching equivalence of transversals.

Matching each t ∈ T with the representative of its right coset in U is an equivalence T ≃ U.
Its inverse matches U-representatives back to T. -/
noncomputable def changeRepEquiv (T U : H.RightTransversal) :
    (T : Set G) ≃ (U : Set G) where
  toFun := changeRep T U
  invFun := changeRep U T
  left_inv t := by
    change (T.2.equiv (((U.2.equiv (t : G)).2 : G))).2 = t
    have hcoset : RightCosetEquivalence H
        ((U.2.equiv (t : G)).2 : G) (t : G) :=
      (U.2.rightCosetEquivalence_equiv_snd (t : G)).symm
    have h := T.2.equiv_snd_eq_iff_rightCosetEquivalence.mpr hcoset
    rw [T.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem t.property] at h
    exact h
  right_inv u := by
    change (U.2.equiv (((T.2.equiv (u : G)).2 : G))).2 = u
    have hcoset : RightCosetEquivalence H
        ((T.2.equiv (u : G)).2 : G) (u : G) :=
      (T.2.rightCosetEquivalence_equiv_snd (u : G)).symm
    have h := U.2.equiv_snd_eq_iff_rightCosetEquivalence.mpr hcoset
    rw [U.2.equiv_snd_eq_self_of_mem_of_one_mem H.one_mem u.property] at h
    exact h

/-- Values of the right-coset matching equivalence.

The equivalence from T to U sends t to changeRep T U t. -/
@[simp]
theorem changeRepEquiv_apply (T U : H.RightTransversal)
    (t : (T : Set G)) :
    changeRepEquiv T U t = changeRep T U t :=
  rfl

/-- Compatibility of representative change with a Schreier step.

For tg = a_T(t,g)r_T(t,g) and t = c(t)u(t), the updated representatives satisfy u(r_T(t,g)) =
r_U(u(t),g), while a_T(t,g)c(r_T(t,g)) = c(t)a_U(u(t),g). -/
theorem changeDecomposition (T U : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    (T.schreierFactor t g * changeFactor T U (T.schreierRep t g),
        changeRep T U (T.schreierRep t g)) =
      (changeFactor T U t * U.schreierFactor (changeRep T U t) g,
        U.schreierRep (changeRep T U t) g) := by
  calc
    (T.schreierFactor t g * changeFactor T U (T.schreierRep t g),
        changeRep T U (T.schreierRep t g)) =
        U.2.equiv
          ((T.schreierFactor t g : G) * (T.schreierRep t g : G)) := by
      rw [U.2.equiv_mul_left]
      rfl
    _ = U.2.equiv ((t : G) * g) := by
      rw [T.schreierFactor_mul_schreierRep]
    _ = U.2.equiv
        ((changeFactor T U t : G) * ((changeRep T U t : G) * g)) := by
      rw [← mul_assoc, changeFactor_mul_changeRep]
    _ = (changeFactor T U t * U.schreierFactor (changeRep T U t) g,
        U.schreierRep (changeRep T U t) g) := by
      rw [U.2.equiv_mul_left]
      rfl

/-- Representative matching commutes with right multiplication.

Matching the T-representative after multiplying by g gives the U-representative obtained by
multiplying the matched starting representative by g. -/
theorem changeRep_schreierRep (T U : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    changeRep T U (T.schreierRep t g) =
      U.schreierRep (changeRep T U t) g := by
  have h := congrArg (fun p : H × (U : Set G) => p.2)
    (changeDecomposition T U t g)
  exact h

/-- The factor identity for changing transversals.

For t ∈ T, the subgroup factors satisfy a_T(t,g)c(r_T(t,g)) = c(t)a_U(u(t),g), in that
multiplication order. -/
theorem schreierFactor_mul_changeFactor (T U : H.RightTransversal)
    (t : (T : Set G)) (g : G) :
    T.schreierFactor t g * changeFactor T U (T.schreierRep t g) =
      changeFactor T U t * U.schreierFactor (changeRep T U t) g := by
  have h := congrArg (fun p : H × (U : Set G) => p.1)
    (changeDecomposition T U t g)
  exact h

end Subgroup.RightTransversal

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for the unary change-of-transversal sum.

The finite-index hypothesis supplies a finite enumeration of the right transversal for the
degree-zero comparison cochain. -/
noncomputable local instance corestrictionIndependenceRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-zero change-of-transversal coefficient.

For c : H → A, define B⁰(c) = ∑ₜ ρ(t⁻¹)c(c_TU(t)), where t = c_TU(t)u(t) compares T with U.
This is a k-linear map from unary H-cochains to A. -/
noncomputable def corestrictionChangeZero (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    (H → A) →ₗ[k] A where
  toFun f := ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (f (T.changeFactor U t))
  map_add' f₁ f₂ := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

/-- The representative formula for the degree-zero comparison.

The comparison coefficient is ∑ₜ ρ(t⁻¹)c(T.changeFactor U t). -/
@[simp]
theorem corestrictionChangeZero_apply (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) :
    corestrictionChangeZero A T U f =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.changeFactor U t)) :=
  rfl

/-- A one-cocycle transfer term after representative change.

For an H-one-cocycle c, the T-transfer summand equals the matched U-transfer summand plus
ρ(t⁻¹)c(c_TU(t)) minus ρ(g r_T(t,g)⁻¹)c(c_TU(r_T(t,g))). -/
theorem corestrictionCochainOne_change_term (A : Rep k G)
    (T U : H.RightTransversal)
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g : G) :
    A.ρ (t : G)⁻¹ (f (T.schreierFactor t g)) =
      A.ρ (T.changeRep U t : G)⁻¹
          (f (U.schreierFactor (T.changeRep U t) g)) +
        A.ρ (t : G)⁻¹ (f (T.changeFactor U t)) -
        A.ρ (g * (T.schreierRep t g : G)⁻¹)
          (f (T.changeFactor U (T.schreierRep t g))) := by
  let R := Rep.res (Subgroup.subtype H) A
  let hT := T.schreierFactor t g
  let t' := T.schreierRep t g
  let a := T.changeFactor U t
  let a' := T.changeFactor U t'
  let u := T.changeRep U t
  let hU := U.schreierFactor u g
  have hfactor : hT * a' = a * hU :=
    T.schreierFactor_mul_changeFactor U t g
  have hvalues : R.ρ hT (f a') + f hT =
      R.ρ a (f hU) + f a := by
    calc
      R.ρ hT (f a') + f hT = f (hT * a') :=
        ((mem_cocycles₁_iff f).mp f.property hT a').symm
      _ = f (a * hU) := congrArg f hfactor
      _ = R.ρ a (f hU) + f a :=
        (mem_cocycles₁_iff f).mp f.property a hU
  have hf : f hT = R.ρ a (f hU) + f a - R.ρ hT (f a') := by
    rw [← hvalues]
    abel
  change A.ρ (t : G)⁻¹ (f hT) = _
  rw [hf, map_sub, map_add]
  change A.ρ (t : G)⁻¹ (A.ρ (a : G) (f hU)) +
      A.ρ (t : G)⁻¹ (f a) -
      A.ρ (t : G)⁻¹ (A.ρ (hT : G) (f a')) = _
  rw [← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul,
    T.inv_mul_changeFactor U t,
    T.inv_mul_schreierFactor t g]

/-- Reindexing unary transfer by matching right cosets.

The U-transfer sum indexed by the matching representatives u(t), t ∈ T, equals the U-transfer
sum indexed directly by u ∈ U. -/
theorem sum_changeRep_corestriction_term (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) (g : G) :
    (∑ t : (T : Set G),
      A.ρ (T.changeRep U t : G)⁻¹
        (f (U.schreierFactor (T.changeRep U t) g))) =
      ∑ u : (U : Set G),
        A.ρ (u : G)⁻¹ (f (U.schreierFactor u g)) :=
  (T.changeRepEquiv U).sum_comp
    (fun u : (U : Set G) =>
      A.ρ (u : G)⁻¹ (f (U.schreierFactor u g)))

/-- Reindexing the translated change-of-transversal coefficient.

The sum of c(c_TU(r_T(t,g))) weighted by ρ(g r_T(t,g)⁻¹) equals ρ(g)B⁰(c). -/
theorem sum_schreierRep_changeFactor (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (f : H → A) (g : G) :
    (∑ t : (T : Set G),
      A.ρ (g * (T.schreierRep t g : G)⁻¹)
        (f (T.changeFactor U (T.schreierRep t g)))) =
      A.ρ g
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (f (T.changeFactor U t))) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g * (T.schreierRep t g : G)⁻¹)
          (f (T.changeFactor U (T.schreierRep t g)))) =
      ∑ t : (T : Set G),
        A.ρ (g * (t : G)⁻¹) (f (T.changeFactor U t)) :=
      (T.schreierRepEquiv g).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g * (t : G)⁻¹) (f (T.changeFactor U t)))
    _ = ∑ t : (T : Set G),
        A.ρ g (A.ρ (t : G)⁻¹ (f (T.changeFactor U t))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ g
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (f (T.changeFactor U t))) := by
      rw [map_sum]

/-- The degree-one transfer difference is a signed boundary.

For an H-one-cocycle c, cor_T¹(c) − cor_U¹(c) = d⁰(−corestrictionChangeZero A T U c). The
minus sign fixes the orientation of the comparison. -/
theorem corestrictionCochainOne_sub_eq_d₀₁_change (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype H) A)) :
    corestrictionCochainOne A T f - corestrictionCochainOne A U f =
      (groupCohomology.d₀₁ A).hom
        (-corestrictionChangeZero A T U f) := by
  funext g
  rw [Pi.sub_apply, corestrictionCochainOne_apply,
    corestrictionCochainOne_apply, d₀₁_hom_apply,
    corestrictionChangeZero_apply, map_neg]
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (f (T.schreierFactor t g))) =
      ∑ t : (T : Set G),
        (A.ρ (T.changeRep U t : G)⁻¹
              (f (U.schreierFactor (T.changeRep U t) g)) +
          A.ρ (t : G)⁻¹ (f (T.changeFactor U t)) -
          A.ρ (g * (T.schreierRep t g : G)⁻¹)
            (f (T.changeFactor U (T.schreierRep t g)))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCochainOne_change_term A T U f t g
  rw [hterms, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_changeRep_corestriction_term,
    sum_schreierRep_changeFactor]
  abel

/-- Transferred one-cocycles have transversal-independent classes.

For every H-one-cocycle c, its transfers with T and U have the same class in H¹(G,A). -/
theorem corestrictionCocyclesOne_H1π_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (f : groupCohomology.cocycles₁
      (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.H1π A (corestrictionCocyclesOne A T f) =
      groupCohomology.H1π A (corestrictionCocyclesOne A U f) := by
  rw [← sub_eq_zero, ← map_sub]
  apply (groupCohomology.H1π_eq_zero_iff _).2
  refine ⟨-corestrictionChangeZero A T U f, ?_⟩
  change (groupCohomology.d₀₁ A).hom
      (-corestrictionChangeZero A T U f) =
    corestrictionCochainOne A T f - corestrictionCochainOne A U f
  exact (corestrictionCochainOne_sub_eq_d₀₁_change A T U f).symm

/-- The transferred degree-one class map is independent of the transversal.

The linear maps from H-one-cocycles to H¹(G,A) defined with T and U are equal. -/
theorem corestrictionCocycleOneClass_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCocycleOneClass A T =
      corestrictionCocycleOneClass A U := by
  apply LinearMap.ext
  intro f
  exact corestrictionCocyclesOne_H1π_independent A T U f

/-- The degree-one cohomology transfer is independent of the transversal.

The induced linear maps H¹(H,A|H) → H¹(G,A) obtained from T and U are equal. -/
theorem corestrictionH1OfRightTransversal_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionH1OfRightTransversal A T =
      corestrictionH1OfRightTransversal A U := by
  apply LinearMap.ext
  intro x
  induction x using groupCohomology.H1_induction_on with
  | _ f =>
      rw [corestrictionH1OfRightTransversal_H1π,
        corestrictionH1OfRightTransversal_H1π]
      exact corestrictionCocyclesOne_H1π_independent A T U f

end groupCohomology
