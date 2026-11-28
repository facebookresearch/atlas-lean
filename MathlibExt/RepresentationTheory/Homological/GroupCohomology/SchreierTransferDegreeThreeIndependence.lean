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

public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree
public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwoIndependence

/-!
# The explicit boundary comparing degree-three transfers

Let T and U be right transversals for a finite-index H ≤ G. In coupled scans write tᵢgᵢ₊₁ =
aᵢtᵢ₊₁, uᵢgᵢ₊₁ = bᵢuᵢ₊₁ and tᵢ = cᵢuᵢ. For a ternary H-cochain z, define B²(z)(g₁,g₂) = ∑ₜ
ρ(t⁻¹)(z(a₀,a₁,c₂) − z(a₀,c₁,b₁) + z(c₀,b₀,b₁)).

For an H-three-cocycle with coefficients in a G-representation, its differential has
orientation d²B²(z) = cor_U³(z) − cor_T³(z). The two transferred classes in H³(G,A) are
therefore equal, and their induced degree-three cohomology maps agree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for the ternary change-of-transversal sum.

The finite-index hypothesis gives a finite enumeration of T for the degree-two comparison
cochain. -/
noncomputable local instance corestrictionDegreeThreeIndependenceTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-two comparison summand for two transversals.

For a ternary cochain z with values in any additive commutative group, the coupled scans give
the summand z(a₀,a₁,c₂) − z(a₀,c₁,b₁) + z(c₀,b₀,b₁), with tᵢ = cᵢuᵢ. -/
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

/-- The linear degree-two change-of-transversal cochain.

For a ternary H-cochain z with coefficients in A, sum the three-term comparison summand with
inverse weights ρ(t⁻¹) over T. This defines a k-linear map to binary G-cochains. -/
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

/-- Values of the degree-two comparison cochain.

At (g₁,g₂), the comparison cochain is ∑ₜ ρ(t⁻¹)corestrictionChangeTwoInner T U z t g₁ g₂. -/
@[simp]
theorem corestrictionChangeTwo_apply (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex]
    (z : H × H × H → A) (g₁ g₂ : G) :
    corestrictionChangeTwo A T U z (g₁, g₂) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (corestrictionChangeTwoInner T U z t g₁ g₂) :=
  rfl

/-- The local differential of the ternary comparison summand.

For an H-three-cocycle z, the local differential of the comparison summand has signs +,−,+,−
and equals ρ(c₀)z(b₀,b₁,b₂) − z(a₀,a₁,a₂) on the coupled scans. -/
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

/-- Reindexing the leading ternary comparison term.

The sum of the comparison summand on (g₂,g₃) starting at r_T(t,g₁), weighted by
ρ(g₁r_T(t,g₁)⁻¹), equals ρ(g₁) times its ordinary inverse-weighted sum. -/
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

/-- The weighted differential of a ternary comparison summand.

Weighting the local +,−,+,− differential by ρ(t⁻¹) gives the matched U-transfer summand of z
minus the T-transfer summand. -/
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

/-- Reindexing the ternary transfer across matched transversals.

The U-transfer sum indexed by u(t) for t ∈ T equals the sum indexed directly by the
representatives of U. -/
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

/-- The reversed degree-three transfer difference is an explicit boundary.

For an H-three-cocycle z, d²(corestrictionChangeTwo A T U z) = cor_U³(z) − cor_T³(z). -/
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

/-- Transferred three-cocycles have transversal-independent classes.

For any H-three-cocycle z, transferring with T or U gives G-three-cocycles with the same image
in H³(G,A). -/
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

/-- The transferred degree-three class map is independent of the transversal.

The linear maps from H-three-cocycles to H³(G,A) defined using T and U are equal. -/
theorem corestrictionCocycleThreeClass_independent (A : Rep k G)
    (T U : H.RightTransversal) [H.FiniteIndex] :
    corestrictionCocycleThreeClass A T =
      corestrictionCocycleThreeClass A U := by
  apply LinearMap.ext
  intro z
  exact corestrictionCocyclesThree_H3π_independent A T U z

/-- The degree-three cohomology transfer is independent of the transversal.

The chosen maps H³(H,A|H) → H³(G,A) obtained from T and U are equal. -/
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
