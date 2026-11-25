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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwoIndependence

/-!
# Independence of degree-three Schreier transfer from the transversal

The change factors comparing two finite right transversals determine an
explicit degree-two prism cochain.  For a subgroup three-cocycle, its
differential is the difference of the two chosen-transversal degree-three
transfers.  It follows that the induced maps on `H³` agree.

Canonical packaging and coefficient naturality are provided in downstream
modules.  No field-theoretic, Kummer, norm-residue, or Bloch--Kato claim is
made here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance corestrictionDegreeThreeIndependenceTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The unsummed positive degree-two prism term comparing two right
transversals. -/
def corestrictionChangeTwoInner {A : Type u} [AddCommGroup A]
    (T U : H.RightTransversal)
    (z : H × H × H → A) (t : (T : Set G)) (g₁ g₂ : G) : A :=
  z (T.schreierFactor t g₁,
      T.schreierFactor (T.schreierRep t g₁) g₂,
      T.changeFactor U
        (T.schreierRep (T.schreierRep t g₁) g₂)) -
    z (T.schreierFactor t g₁,
      T.changeFactor U (T.schreierRep t g₁),
      U.schreierFactor
        (T.changeRep U (T.schreierRep t g₁)) g₂) +
    z (T.changeFactor U t,
      U.schreierFactor (T.changeRep U t) g₁,
      U.schreierFactor
        (U.schreierRep (T.changeRep U t) g₁) g₂)

/-- The explicit degree-two prism cochain comparing degree-three transfer
cochains associated to `T` and `U`. -/
noncomputable def corestrictionChangeTwo (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    (H × H × H → A) →ₗ[k] (G × G → A) where
  toFun z p := ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (corestrictionChangeTwoInner T U z t p.1 p.2)
  map_add' z₁ z₂ := by
    funext p
    simp only [corestrictionChangeTwoInner, Pi.add_apply, map_add,
      add_sub_add_comm, Finset.sum_add_distrib]
    abel
  map_smul' r z := by
    funext p
    simp only [corestrictionChangeTwoInner, Pi.smul_apply]
    simp_rw [← smul_sub, ← smul_add, map_smul]
    simp only [RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem corestrictionChangeTwo_apply (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H × H → A) (g₁ g₂ : G) :
    corestrictionChangeTwo A T U z (g₁, g₂) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (corestrictionChangeTwoInner T U z t g₁ g₂) :=
  rfl

/-- The subgroup-level cocycle identity underlying the degree-three
change-of-transversal prism homotopy. -/
theorem corestrictionChangeTwoInner_cocycle (A : Rep k G)
    (T U : H.RightTransversal)
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ g₃ : G) :
    (Rep.res (Subgroup.subtype H) A).ρ (T.schreierFactor t g₁)
        (corestrictionChangeTwoInner T U z
          (T.schreierRep t g₁) g₂ g₃) -
      corestrictionChangeTwoInner T U z t (g₁ * g₂) g₃ +
      corestrictionChangeTwoInner T U z t g₁ (g₂ * g₃) -
      corestrictionChangeTwoInner T U z t g₁ g₂ =
        (Rep.res (Subgroup.subtype H) A).ρ (T.changeFactor U t)
          (z (U.schreierFactor (T.changeRep U t) g₁,
            U.schreierFactor
              (U.schreierRep (T.changeRep U t) g₁) g₂,
            U.schreierFactor
              (U.schreierRep
                (U.schreierRep (T.changeRep U t) g₁) g₂) g₃)) -
        z (T.schreierFactor t g₁,
          T.schreierFactor (T.schreierRep t g₁) g₂,
          T.schreierFactor
            (T.schreierRep (T.schreierRep t g₁) g₂) g₃) := by
  let R := Rep.res (Subgroup.subtype H) A
  let t₁ := T.schreierRep t g₁
  let t₂ := T.schreierRep t₁ g₂
  let t₃ := T.schreierRep t₂ g₃
  let a₀ := T.changeFactor U t
  let a₁ := T.changeFactor U t₁
  let a₂ := T.changeFactor U t₂
  let a₃ := T.changeFactor U t₃
  let u₀ := T.changeRep U t
  let u₁ := T.changeRep U t₁
  let u₂ := T.changeRep U t₂
  let x₁ := T.schreierFactor t g₁
  let x₂ := T.schreierFactor t₁ g₂
  let x₃ := T.schreierFactor t₂ g₃
  let y₁ := U.schreierFactor u₀ g₁
  let y₂ := U.schreierFactor u₁ g₂
  let y₃ := U.schreierFactor u₂ g₃
  have hx₁ : x₁ * a₁ = a₀ * y₁ :=
    T.schreierFactor_mul_changeFactor U t g₁
  have hx₂ : x₂ * a₂ = a₁ * y₂ :=
    T.schreierFactor_mul_changeFactor U t₁ g₂
  have hx₃ : x₃ * a₃ = a₂ * y₃ :=
    T.schreierFactor_mul_changeFactor U t₂ g₃
  have hzX := (mem_cocycles₃_def z).mp z.property x₁ x₂ x₃ a₃
  have hzM₁ := (mem_cocycles₃_def z).mp z.property x₁ x₂ a₂ y₃
  have hzM₂ := (mem_cocycles₃_def z).mp z.property x₁ a₁ y₂ y₃
  have hzU := (mem_cocycles₃_def z).mp z.property a₀ y₁ y₂ y₃
  rw [hx₃] at hzX
  rw [hx₂] at hzM₁
  rw [hx₁] at hzM₂
  have hu₁ : u₁ = U.schreierRep u₀ g₁ :=
    T.changeRep_schreierRep U t g₁
  have hu₂ : u₂ = U.schreierRep u₁ g₂ :=
    T.changeRep_schreierRep U t₁ g₂
  unfold corestrictionChangeTwoInner
  rw [← hu₁, ← hu₂]
  rw [T.schreierFactor_mul t g₁ g₂,
    T.schreierRep_mul t g₁ g₂,
    T.schreierFactor_mul t₁ g₂ g₃,
    T.schreierRep_mul t₁ g₂ g₃,
    U.schreierFactor_mul u₀ g₁ g₂,
    U.schreierRep_mul u₀ g₁ g₂,
    U.schreierFactor_mul u₁ g₂ g₃]
  rw [← hu₁, ← hu₂]
  change R.ρ x₁
      (z (x₂, x₃, a₃) - z (x₂, a₂, y₃) + z (a₁, y₂, y₃)) -
    (z (x₁ * x₂, x₃, a₃) - z (x₁ * x₂, a₂, y₃) +
      z (a₀, y₁ * y₂, y₃)) +
    (z (x₁, x₂ * x₃, a₃) - z (x₁, a₁, y₂ * y₃) +
      z (a₀, y₁, y₂ * y₃)) -
    (z (x₁, x₂, a₂) - z (x₁, a₁, y₂) + z (a₀, y₁, y₂)) =
      R.ρ a₀ (z (y₁, y₂, y₃)) - z (x₁, x₂, x₃)
  simp only [map_add, map_sub]
  rw [← sub_eq_zero]
  calc
    _ =
        (R.ρ x₁ (z (x₂, x₃, a₃)) - z (x₁ * x₂, x₃, a₃) +
          z (x₁, x₂ * x₃, a₃) - z (x₁, x₂, a₂ * y₃) +
          z (x₁, x₂, x₃)) -
        (R.ρ x₁ (z (x₂, a₂, y₃)) - z (x₁ * x₂, a₂, y₃) +
          z (x₁, a₁ * y₂, y₃) - z (x₁, x₂, a₂ * y₃) +
          z (x₁, x₂, a₂)) +
        (R.ρ x₁ (z (a₁, y₂, y₃)) - z (a₀ * y₁, y₂, y₃) +
          z (x₁, a₁ * y₂, y₃) - z (x₁, a₁, y₂ * y₃) +
          z (x₁, a₁, y₂)) -
        (R.ρ a₀ (z (y₁, y₂, y₃)) - z (a₀ * y₁, y₂, y₃) +
          z (a₀, y₁ * y₂, y₃) - z (a₀, y₁, y₂ * y₃) +
          z (a₀, y₁, y₂)) := by
      abel
    _ = 0 := by rw [hzX, hzM₁, hzM₂, hzU]; abel

/-- Reindexing the leading differential term of the degree-two prism by the
Schreier permutation. -/
theorem sum_schreierRep_changeTwoInner (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H × H → A) (g₁ g₂ g₃ : G) :
    (∑ t : (T : Set G),
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
        (corestrictionChangeTwoInner T U z
          (T.schreierRep t g₁) g₂ g₃)) =
      A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeTwoInner T U z t g₂ g₃)) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (corestrictionChangeTwoInner T U z
            (T.schreierRep t g₁) g₂ g₃)) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (t : G)⁻¹)
          (corestrictionChangeTwoInner T U z t g₂ g₃) :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g₁ * (t : G)⁻¹)
            (corestrictionChangeTwoInner T U z t g₂ g₃))
    _ = ∑ t : (T : Set G),
        A.ρ g₁
          (A.ρ (t : G)⁻¹
            (corestrictionChangeTwoInner T U z t g₂ g₃)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeTwoInner T U z t g₂ g₃)) := by
      rw [map_sum]

/-- The differential comparison for one representative in degree three. -/
theorem corestrictionChangeTwo_d₂₃_term (A : Rep k G)
    (T U : H.RightTransversal)
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ g₃ : G) :
    A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (corestrictionChangeTwoInner T U z
            (T.schreierRep t g₁) g₂ g₃) -
        A.ρ (t : G)⁻¹
          (corestrictionChangeTwoInner T U z t (g₁ * g₂) g₃) +
        A.ρ (t : G)⁻¹
          (corestrictionChangeTwoInner T U z t g₁ (g₂ * g₃)) -
        A.ρ (t : G)⁻¹
          (corestrictionChangeTwoInner T U z t g₁ g₂) =
      A.ρ (T.changeRep U t : G)⁻¹
          (z (U.schreierFactor (T.changeRep U t) g₁,
            U.schreierFactor
              (U.schreierRep (T.changeRep U t) g₁) g₂,
            U.schreierFactor
              (U.schreierRep
                (U.schreierRep (T.changeRep U t) g₁) g₂) g₃)) -
        A.ρ (t : G)⁻¹
          (z (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) := by
  have h := congrArg (A.ρ (t : G)⁻¹)
    (corestrictionChangeTwoInner_cocycle A T U z t g₁ g₂ g₃)
  simp only [map_sub, map_add] at h
  change A.ρ (t : G)⁻¹
        (A.ρ (T.schreierFactor t g₁ : G)
          (corestrictionChangeTwoInner T U z
            (T.schreierRep t g₁) g₂ g₃)) -
      A.ρ (t : G)⁻¹
        (corestrictionChangeTwoInner T U z t (g₁ * g₂) g₃) +
      A.ρ (t : G)⁻¹
        (corestrictionChangeTwoInner T U z t g₁ (g₂ * g₃)) -
      A.ρ (t : G)⁻¹
        (corestrictionChangeTwoInner T U z t g₁ g₂) =
      A.ρ (t : G)⁻¹
        (A.ρ (T.changeFactor U t : G)
          (z (U.schreierFactor (T.changeRep U t) g₁,
            U.schreierFactor
              (U.schreierRep (T.changeRep U t) g₁) g₂,
            U.schreierFactor
              (U.schreierRep
                (U.schreierRep (T.changeRep U t) g₁) g₂) g₃))) -
      A.ρ (t : G)⁻¹
        (z (T.schreierFactor t g₁,
          T.schreierFactor (T.schreierRep t g₁) g₂,
          T.schreierFactor
            (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) at h
  rw [← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul,
    T.inv_mul_schreierFactor t g₁,
    T.inv_mul_changeFactor U t] at h
  exact h

/-- Reindexing the `U`-degree-three transfer summands along the equivalence
of transversals. -/
theorem sum_changeRep_corestrictionThree_term (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H × H → A) (g₁ g₂ g₃ : G) :
    (∑ t : (T : Set G),
      A.ρ (T.changeRep U t : G)⁻¹
        (z (U.schreierFactor (T.changeRep U t) g₁,
          U.schreierFactor
            (U.schreierRep (T.changeRep U t) g₁) g₂,
          U.schreierFactor
            (U.schreierRep
              (U.schreierRep (T.changeRep U t) g₁) g₂) g₃))) =
      ∑ u : (U : Set G),
        A.ρ (u : G)⁻¹
          (z (U.schreierFactor u g₁,
            U.schreierFactor (U.schreierRep u g₁) g₂,
            U.schreierFactor
              (U.schreierRep (U.schreierRep u g₁) g₂) g₃)) :=
  (T.changeRepEquiv U).sum_comp
    (fun u : (U : Set G) =>
      A.ρ (u : G)⁻¹
        (z (U.schreierFactor u g₁,
          U.schreierFactor (U.schreierRep u g₁) g₂,
          U.schreierFactor
            (U.schreierRep (U.schreierRep u g₁) g₂) g₃)))

/-- The differential of the explicit degree-two prism cochain is the
`U`-transfer minus the `T`-transfer. -/
theorem corestrictionChangeTwo_d₂₃ (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    (d₂₃ A).hom (corestrictionChangeTwo A T U z) =
      corestrictionCochainThree A U z -
        corestrictionCochainThree A T z := by
  funext p
  rcases p with ⟨g₁, g₂, g₃⟩
  simp only [d₂₃_hom_apply, corestrictionChangeTwo_apply,
    corestrictionCochainThree_apply, Pi.sub_apply]
  rw [← sum_schreierRep_changeTwoInner A T U z g₁ g₂ g₃]
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (corestrictionChangeTwoInner T U z
            (T.schreierRep t g₁) g₂ g₃)) -
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeTwoInner T U z t (g₁ * g₂) g₃)) +
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeTwoInner T U z t g₁ (g₂ * g₃))) -
        ∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (corestrictionChangeTwoInner T U z t g₁ g₂) =
      ∑ t : (T : Set G),
        (A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (corestrictionChangeTwoInner T U z
                (T.schreierRep t g₁) g₂ g₃) -
            A.ρ (t : G)⁻¹
              (corestrictionChangeTwoInner T U z t (g₁ * g₂) g₃) +
            A.ρ (t : G)⁻¹
              (corestrictionChangeTwoInner T U z t g₁ (g₂ * g₃)) -
            A.ρ (t : G)⁻¹
              (corestrictionChangeTwoInner T U z t g₁ g₂)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
    _ = ∑ t : (T : Set G),
        (A.ρ (T.changeRep U t : G)⁻¹
            (z (U.schreierFactor (T.changeRep U t) g₁,
              U.schreierFactor
                (U.schreierRep (T.changeRep U t) g₁) g₂,
              U.schreierFactor
                (U.schreierRep
                  (U.schreierRep (T.changeRep U t) g₁) g₂) g₃)) -
          A.ρ (t : G)⁻¹
            (z (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) := by
      apply Finset.sum_congr rfl
      intro t _
      exact corestrictionChangeTwo_d₂₃_term A T U z t g₁ g₂ g₃
    _ = (∑ t : (T : Set G),
          A.ρ (T.changeRep U t : G)⁻¹
            (z (U.schreierFactor (T.changeRep U t) g₁,
              U.schreierFactor
                (U.schreierRep (T.changeRep U t) g₁) g₂,
              U.schreierFactor
                (U.schreierRep
                  (U.schreierRep (T.changeRep U t) g₁) g₂) g₃))) -
        ∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (z (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ u : (U : Set G),
          A.ρ (u : G)⁻¹
            (z (U.schreierFactor u g₁,
              U.schreierFactor (U.schreierRep u g₁) g₂,
              U.schreierFactor
                (U.schreierRep (U.schreierRep u g₁) g₂) g₃)) -
        ∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (z (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) := by
      rw [sum_changeRep_corestrictionThree_term]

/-- The `H³` classes of a transferred three-cocycle do not depend on the
chosen finite right transversal. -/
theorem corestrictionCocyclesThree_H3π_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    H3π A (corestrictionCocyclesThree A T z) =
      H3π A (corestrictionCocyclesThree A U z) := by
  rw [← sub_eq_zero, ← map_sub]
  apply (H3π_eq_zero_iff _).2
  refine ⟨-corestrictionChangeTwo A T U z, ?_⟩
  change (d₂₃ A).hom (-corestrictionChangeTwo A T U z) =
    corestrictionCochainThree A T z - corestrictionCochainThree A U z
  rw [map_neg, corestrictionChangeTwo_d₂₃]
  module

/-- The linear map from three-cocycles to target `H³` is independent of the
chosen finite right transversal. -/
theorem corestrictionCocycleThreeClass_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCocycleThreeClass A T =
      corestrictionCocycleThreeClass A U := by
  apply LinearMap.ext
  intro z
  exact corestrictionCocyclesThree_H3π_independent A T U z

/-- Chosen-transversal degree-three cohomological transfer is independent of
the finite right transversal. -/
theorem corestrictionH3OfRightTransversal_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionH3OfRightTransversal A T =
      corestrictionH3OfRightTransversal A U := by
  apply LinearMap.ext
  intro x
  induction x using H3_induction_on with
  | _ z =>
      rw [corestrictionH3OfRightTransversal_H3π,
        corestrictionH3OfRightTransversal_H3π]
      exact corestrictionCocyclesThree_H3π_independent A T U z

end groupCohomology
