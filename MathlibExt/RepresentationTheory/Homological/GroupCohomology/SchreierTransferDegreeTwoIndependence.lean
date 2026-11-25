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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwo
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferIndependence

/-!
# Independence of degree-two Schreier transfer from the transversal

The change factors comparing two finite right transversals determine an
explicit degree-one cochain.  For a subgroup two-cocycle, its differential is
the difference of the two chosen-transversal degree-two transfers.  It follows
that the induced maps on `H²` agree.

No projection formula, norm-residue comparison, or Kummer--Steinberg
vanishing is asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance corestrictionDegreeTwoIndependenceTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The unsummed degree-one change term attached to one representative. -/
def corestrictionChangeOneInner {A : Type u} [AddCommGroup A]
    (T U : H.RightTransversal)
    (z : H × H → A) (t : (T : Set G)) (g : G) : A :=
  z (T.schreierFactor t g,
      T.changeFactor U (T.schreierRep t g)) -
    z (T.changeFactor U t,
      U.schreierFactor (T.changeRep U t) g)

/-- The explicit degree-one homotopy term comparing the degree-two transfer
cochains associated to `T` and `U`. -/
noncomputable def corestrictionChangeOne (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    (H × H → A) →ₗ[k] (G → A) where
  toFun z g := ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (corestrictionChangeOneInner T U z t g)
  map_add' z₁ z₂ := by
    funext g
    simp only [corestrictionChangeOneInner, Pi.add_apply, map_add,
      add_sub_add_comm, Finset.sum_add_distrib]
  map_smul' r z := by
    funext g
    simp only [corestrictionChangeOneInner, Pi.smul_apply]
    simp_rw [← smul_sub]
    simp only [map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem corestrictionChangeOne_apply (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H → A) (g : G) :
    corestrictionChangeOne A T U z g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (corestrictionChangeOneInner T U z t g) :=
  rfl

/-- The subgroup-level cocycle identity underlying the degree-two
change-of-transversal homotopy. -/
theorem corestrictionChangeOneInner_cocycle (A : Rep k G)
    (T U : H.RightTransversal)
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ : G) :
    (Rep.res (Subgroup.subtype H) A).ρ (T.schreierFactor t g₁)
        (corestrictionChangeOneInner T U z
          (T.schreierRep t g₁) g₂) -
      corestrictionChangeOneInner T U z t (g₁ * g₂) +
      corestrictionChangeOneInner T U z t g₁ =
        z (T.schreierFactor t g₁,
          T.schreierFactor (T.schreierRep t g₁) g₂) -
        (Rep.res (Subgroup.subtype H) A).ρ (T.changeFactor U t)
          (z (U.schreierFactor (T.changeRep U t) g₁,
            U.schreierFactor
              (U.schreierRep (T.changeRep U t) g₁) g₂)) := by
  let R := Rep.res (Subgroup.subtype H) A
  let t₁ := T.schreierRep t g₁
  let t₂ := T.schreierRep t₁ g₂
  let a₀ := T.changeFactor U t
  let a₁ := T.changeFactor U t₁
  let a₂ := T.changeFactor U t₂
  let u₀ := T.changeRep U t
  let u₁ := T.changeRep U t₁
  let x₁ := T.schreierFactor t g₁
  let x₂ := T.schreierFactor t₁ g₂
  let y₁ := U.schreierFactor u₀ g₁
  let y₂ := U.schreierFactor u₁ g₂
  have hx₁ : x₁ * a₁ = a₀ * y₁ :=
    T.schreierFactor_mul_changeFactor U t g₁
  have hx₂ : x₂ * a₂ = a₁ * y₂ :=
    T.schreierFactor_mul_changeFactor U t₁ g₂
  have hzX := (groupCohomology.mem_cocycles₂_iff z).mp z.property x₁ x₂ a₂
  have hzM := (groupCohomology.mem_cocycles₂_iff z).mp z.property x₁ a₁ y₂
  have hzU := (groupCohomology.mem_cocycles₂_iff z).mp z.property a₀ y₁ y₂
  have hzX' : R.ρ x₁ (z (x₂, a₂)) - z (x₁ * x₂, a₂) +
      z (x₁, a₁ * y₂) - z (x₁, x₂) = 0 := by
    rw [← hx₂]
    calc
      _ = (R.ρ x₁ (z (x₂, a₂)) + z (x₁, x₂ * a₂)) -
          (z (x₁ * x₂, a₂) + z (x₁, x₂)) := by abel
      _ = 0 := sub_eq_zero.mpr hzX.symm
  have hzM' : R.ρ x₁ (z (a₁, y₂)) - z (a₀ * y₁, y₂) +
      z (x₁, a₁ * y₂) - z (x₁, a₁) = 0 := by
    rw [← hx₁]
    calc
      _ = (R.ρ x₁ (z (a₁, y₂)) + z (x₁, a₁ * y₂)) -
          (z (x₁ * a₁, y₂) + z (x₁, a₁)) := by abel
      _ = 0 := sub_eq_zero.mpr hzM.symm
  have hzU' : R.ρ a₀ (z (y₁, y₂)) - z (a₀ * y₁, y₂) +
      z (a₀, y₁ * y₂) - z (a₀, y₁) = 0 := by
    calc
      _ = (R.ρ a₀ (z (y₁, y₂)) + z (a₀, y₁ * y₂)) -
          (z (a₀ * y₁, y₂) + z (a₀, y₁)) := by abel
      _ = 0 := sub_eq_zero.mpr hzU.symm
  change R.ρ x₁
      (z (x₂, a₂) - z (a₁, y₂)) -
    (z (T.schreierFactor t (g₁ * g₂),
        T.changeFactor U (T.schreierRep t (g₁ * g₂))) -
      z (a₀, U.schreierFactor u₀ (g₁ * g₂))) +
    (z (x₁, a₁) - z (a₀, y₁)) =
      z (x₁, x₂) - R.ρ a₀
        (z (y₁, U.schreierFactor (U.schreierRep u₀ g₁) g₂))
  rw [T.schreierFactor_mul t g₁ g₂,
    T.schreierRep_mul t g₁ g₂,
    U.schreierFactor_mul u₀ g₁ g₂]
  have hu₁ : u₁ = U.schreierRep u₀ g₁ :=
    T.changeRep_schreierRep U t g₁
  rw [← hu₁]
  change R.ρ x₁ (z (x₂, a₂) - z (a₁, y₂)) -
      (z (x₁ * x₂, a₂) - z (a₀, y₁ * y₂)) +
      (z (x₁, a₁) - z (a₀, y₁)) =
    z (x₁, x₂) - R.ρ a₀ (z (y₁, y₂))
  rw [map_sub]
  rw [← sub_eq_zero]
  calc
    _ =
        (R.ρ x₁ (z (x₂, a₂)) - z (x₁ * x₂, a₂) +
          z (x₁, a₁ * y₂) - z (x₁, x₂)) -
        (R.ρ x₁ (z (a₁, y₂)) - z (a₀ * y₁, y₂) +
          z (x₁, a₁ * y₂) - z (x₁, a₁)) +
        (R.ρ a₀ (z (y₁, y₂)) - z (a₀ * y₁, y₂) +
          z (a₀, y₁ * y₂) - z (a₀, y₁)) := by
      abel
    _ = 0 := by rw [hzX', hzM', hzU']; abel

/-- Reindexing the leading differential term by the Schreier permutation. -/
theorem sum_schreierRep_changeOneInner (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H → A) (g₁ g₂ : G) :
    (∑ t : (T : Set G),
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
        (corestrictionChangeOneInner T U z
          (T.schreierRep t g₁) g₂)) =
      A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (corestrictionChangeOneInner T U z t g₂)) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (corestrictionChangeOneInner T U z
            (T.schreierRep t g₁) g₂)) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (t : G)⁻¹)
          (corestrictionChangeOneInner T U z t g₂) :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g₁ * (t : G)⁻¹)
            (corestrictionChangeOneInner T U z t g₂))
    _ = ∑ t : (T : Set G),
        A.ρ g₁
          (A.ρ (t : G)⁻¹
            (corestrictionChangeOneInner T U z t g₂)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeOneInner T U z t g₂)) := by
      rw [map_sum]

/-- The differential comparison for a single representative. -/
theorem corestrictionChangeOne_d₁₂_term (A : Rep k G)
    (T U : H.RightTransversal)
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ : G) :
    A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (corestrictionChangeOneInner T U z
            (T.schreierRep t g₁) g₂) -
        A.ρ (t : G)⁻¹
          (corestrictionChangeOneInner T U z t (g₁ * g₂)) +
        A.ρ (t : G)⁻¹
          (corestrictionChangeOneInner T U z t g₁) =
      A.ρ (t : G)⁻¹
          (z (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂)) -
        A.ρ (T.changeRep U t : G)⁻¹
          (z (U.schreierFactor (T.changeRep U t) g₁,
            U.schreierFactor
              (U.schreierRep (T.changeRep U t) g₁) g₂)) := by
  have h := congrArg (A.ρ (t : G)⁻¹)
    (corestrictionChangeOneInner_cocycle A T U z t g₁ g₂)
  simp only [map_sub, map_add] at h
  change A.ρ (t : G)⁻¹
        (A.ρ (T.schreierFactor t g₁ : G)
          (corestrictionChangeOneInner T U z
            (T.schreierRep t g₁) g₂)) -
      A.ρ (t : G)⁻¹
        (corestrictionChangeOneInner T U z t (g₁ * g₂)) +
      A.ρ (t : G)⁻¹
        (corestrictionChangeOneInner T U z t g₁) =
      A.ρ (t : G)⁻¹
        (z (T.schreierFactor t g₁,
          T.schreierFactor (T.schreierRep t g₁) g₂)) -
      A.ρ (t : G)⁻¹
        (A.ρ (T.changeFactor U t : G)
          (z (U.schreierFactor (T.changeRep U t) g₁,
            U.schreierFactor
              (U.schreierRep (T.changeRep U t) g₁) g₂))) at h
  rw [← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul,
    T.inv_mul_schreierFactor t g₁,
    T.inv_mul_changeFactor U t] at h
  exact h

/-- Reindexing the `U`-transfer summands along the equivalence of
transversals. -/
theorem sum_changeRep_corestrictionTwo_term (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H → A) (g₁ g₂ : G) :
    (∑ t : (T : Set G),
      A.ρ (T.changeRep U t : G)⁻¹
        (z (U.schreierFactor (T.changeRep U t) g₁,
          U.schreierFactor
            (U.schreierRep (T.changeRep U t) g₁) g₂))) =
      ∑ u : (U : Set G),
        A.ρ (u : G)⁻¹
          (z (U.schreierFactor u g₁,
            U.schreierFactor (U.schreierRep u g₁) g₂)) :=
  (T.changeRepEquiv U).sum_comp
    (fun u : (U : Set G) =>
      A.ρ (u : G)⁻¹
        (z (U.schreierFactor u g₁,
          U.schreierFactor (U.schreierRep u g₁) g₂)))

/-- The differential of the explicit degree-one change cochain is the
difference of the two chosen-transversal degree-two transfers. -/
theorem corestrictionChangeOne_d₁₂ (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A)) :
    (groupCohomology.d₁₂ A).hom (corestrictionChangeOne A T U z) =
      corestrictionCochainTwo A T z - corestrictionCochainTwo A U z := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  simp only [d₁₂_hom_apply, corestrictionChangeOne_apply,
    corestrictionCochainTwo_apply, Pi.sub_apply]
  rw [← sum_schreierRep_changeOneInner A T U z g₁ g₂]
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (corestrictionChangeOneInner T U z
            (T.schreierRep t g₁) g₂)) -
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeOneInner T U z t (g₁ * g₂))) +
        ∑ t : (T : Set G),
          A.ρ (t : G)⁻¹ (corestrictionChangeOneInner T U z t g₁) =
      ∑ t : (T : Set G),
        (A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (corestrictionChangeOneInner T U z
                (T.schreierRep t g₁) g₂) -
            A.ρ (t : G)⁻¹
              (corestrictionChangeOneInner T U z t (g₁ * g₂)) +
            A.ρ (t : G)⁻¹
              (corestrictionChangeOneInner T U z t g₁)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ t : (T : Set G),
        (A.ρ (t : G)⁻¹
              (z (T.schreierFactor t g₁,
                T.schreierFactor (T.schreierRep t g₁) g₂)) -
            A.ρ (T.changeRep U t : G)⁻¹
              (z (U.schreierFactor (T.changeRep U t) g₁,
                U.schreierFactor
                  (U.schreierRep (T.changeRep U t) g₁) g₂))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact corestrictionChangeOne_d₁₂_term A T U z t g₁ g₂
    _ = (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (z (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂))) -
        ∑ t : (T : Set G),
          A.ρ (T.changeRep U t : G)⁻¹
            (z (U.schreierFactor (T.changeRep U t) g₁,
              U.schreierFactor
                (U.schreierRep (T.changeRep U t) g₁) g₂)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (z (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂))) -
        ∑ u : (U : Set G),
          A.ρ (u : G)⁻¹
            (z (U.schreierFactor u g₁,
              U.schreierFactor (U.schreierRep u g₁) g₂)) := by
      rw [sum_changeRep_corestrictionTwo_term]

/-- The `H²` classes of a transferred two-cocycle do not depend on the
chosen finite right transversal. -/
theorem corestrictionCocyclesTwo_H2π_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : groupCohomology.cocycles₂
      (Rep.res (Subgroup.subtype H) A)) :
    groupCohomology.H2π A (corestrictionCocyclesTwo A T z) =
      groupCohomology.H2π A (corestrictionCocyclesTwo A U z) := by
  rw [← sub_eq_zero, ← map_sub]
  apply (groupCohomology.H2π_eq_zero_iff _).2
  refine ⟨corestrictionChangeOne A T U z, ?_⟩
  change (groupCohomology.d₁₂ A).hom
      (corestrictionChangeOne A T U z) =
    corestrictionCochainTwo A T z - corestrictionCochainTwo A U z
  exact corestrictionChangeOne_d₁₂ A T U z

/-- The linear map from two-cocycles to target `H²` is independent of the
chosen finite right transversal. -/
theorem corestrictionCocycleTwoClass_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCocycleTwoClass A T =
      corestrictionCocycleTwoClass A U := by
  apply LinearMap.ext
  intro z
  exact corestrictionCocyclesTwo_H2π_independent A T U z

/-- Chosen-transversal degree-two cohomological transfer is independent of
the finite right transversal. -/
theorem corestrictionH2OfRightTransversal_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionH2OfRightTransversal A T =
      corestrictionH2OfRightTransversal A U := by
  apply LinearMap.ext
  intro x
  induction x using groupCohomology.H2_induction_on with
  | _ z =>
      rw [corestrictionH2OfRightTransversal_H2π,
        corestrictionH2OfRightTransversal_H2π]
      exact corestrictionCocyclesTwo_H2π_independent A T U z

end groupCohomology
