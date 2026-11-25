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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwoFunctoriality
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferCupProjection
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeThree

/-!
# The chosen-transversal H1 x H2 to H3 cup projection formula

For a `G`-one-cocycle `x` and an `H`-two-cocycle `y`, this file constructs
an explicit degree-two cochain whose boundary measures the difference
between the transfer of `res(x) cup y` and `x cup cor(y)`.  It then proves
the corresponding representative and class-level projection formulas.

The right transversal remains explicit.  No independence of that choice,
canonical degree-three corestriction, field-theoretic, Kummer, norm-residue,
or Bloch--Kato claim is made.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance cupOneTwoProjectionTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-two cochain measuring the failure of the `(1,2)` cup
projection formula to hold strictly on cochains. -/
noncomputable def cupProjectionHomotopyOneTwo
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H × H → B) : G × G → (A ⊗ B : Rep k G) :=
  fun p => ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
      B.ρ (t : G)⁻¹
        (y (T.schreierFactor t p.1,
          T.schreierFactor (T.schreierRep t p.1) p.2))

@[simp]
theorem cupProjectionHomotopyOneTwo_apply
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H × H → B) (g h : G) :
    cupProjectionHomotopyOneTwo A B T x y (g, h) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (t : G)⁻¹
            (y (T.schreierFactor t g,
              T.schreierFactor (T.schreierRep t g) h)) :=
  rfl

private theorem tensor_rho_tmul_one_two
    (A B : Rep k G) (g : G) (a : A) (b : B) :
    (A ⊗ B : Rep k G).ρ g (a ⊗ₜ[k] b) =
      A.ρ g a ⊗ₜ[k] B.ρ g b := by
  change TensorProduct.map (A.ρ g) (B.ρ g) (a ⊗ₜ[k] b) = _
  rw [TensorProduct.map_tmul]

/-- The three non-leading terms of the degree-two homotopy boundary combine
by the subgroup two-cocycle identity. -/
theorem cupProjectionHomotopyOneTwo_cocycle_terms
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A)
    (y : cocycles₂ (Rep.res (Subgroup.subtype H) B))
    (g h i : G) :
    cupProjectionHomotopyOneTwo A B T x y (g * h, i) -
        cupProjectionHomotopyOneTwo A B T x y (g, h * i) +
          cupProjectionHomotopyOneTwo A B T x y (g, h) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g * (T.schreierRep t g : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i)) := by
  rw [cupProjectionHomotopyOneTwo_apply,
    cupProjectionHomotopyOneTwo_apply,
    cupProjectionHomotopyOneTwo_apply,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  let u : A := A.ρ (t : G)⁻¹ (x (t : G))
  let q₁ : B := B.ρ (t : G)⁻¹
    (y (T.schreierFactor t (g * h),
      T.schreierFactor (T.schreierRep t (g * h)) i))
  let q₂ : B := B.ρ (t : G)⁻¹
    (y (T.schreierFactor t g,
      T.schreierFactor (T.schreierRep t g) (h * i)))
  let q₃ : B := B.ρ (t : G)⁻¹
    (y (T.schreierFactor t g,
      T.schreierFactor (T.schreierRep t g) h))
  let q₀ : B := B.ρ (g * (T.schreierRep t g : G)⁻¹)
    (y (T.schreierFactor (T.schreierRep t g) h,
      T.schreierFactor
        (T.schreierRep (T.schreierRep t g) h) i))
  have hy := corestrictionCochainTwo_cocycle_term B T y t g h i
  simp only [map_add] at hy
  have hy' : q₁ + q₃ = q₀ + q₂ := hy
  have htmul := congrArg (fun v : B => u ⊗ₜ[k] v) hy'
  simp only [TensorProduct.tmul_add] at htmul
  change u ⊗ₜ[k] q₁ - u ⊗ₜ[k] q₂ + u ⊗ₜ[k] q₃ =
    u ⊗ₜ[k] q₀
  calc
    u ⊗ₜ[k] q₁ - u ⊗ₜ[k] q₂ + u ⊗ₜ[k] q₃ =
        (u ⊗ₜ[k] q₁ + u ⊗ₜ[k] q₃) - u ⊗ₜ[k] q₂ := by
      abel
    _ = (u ⊗ₜ[k] q₀ + u ⊗ₜ[k] q₂) - u ⊗ₜ[k] q₂ := by
      rw [htmul]
    _ = u ⊗ₜ[k] q₀ := add_sub_cancel_right _ _

/-- Acting on the degree-two homotopy reindexes through the Schreier
permutation of the transversal. -/
theorem rho_cupProjectionHomotopyOneTwo
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H × H → B) (g h i : G) :
    (A ⊗ B : Rep k G).ρ g
        (cupProjectionHomotopyOneTwo A B T x y (h, i)) =
      ∑ t : (T : Set G),
        A.ρ (g * (T.schreierRep t g : G)⁻¹)
            (x (T.schreierRep t g : G)) ⊗ₜ[k]
          B.ρ (g * (T.schreierRep t g : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i)) := by
  rw [cupProjectionHomotopyOneTwo_apply, map_sum]
  calc
    (∑ t : (T : Set G),
        (A ⊗ B : Rep k G).ρ g
          (A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
            B.ρ (t : G)⁻¹
              (y (T.schreierFactor t h,
                T.schreierFactor (T.schreierRep t h) i)))) =
      ∑ t : (T : Set G),
        A.ρ (g * (t : G)⁻¹) (x (t : G)) ⊗ₜ[k]
          B.ρ (g * (t : G)⁻¹)
            (y (T.schreierFactor t h,
              T.schreierFactor (T.schreierRep t h) i)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [tensor_rho_tmul_one_two]
      congr 1
      · rw [← Module.End.mul_apply, ← map_mul]
      · rw [← Module.End.mul_apply, ← map_mul]
    _ = _ :=
      (T.schreierRepEquiv g).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g * (t : G)⁻¹) (x (t : G)) ⊗ₜ[k]
            B.ρ (g * (t : G)⁻¹)
              (y (T.schreierFactor t h,
                T.schreierFactor (T.schreierRep t h) i))) |>.symm

/-- The cup with the transferred degree-two right factor, written as the
corresponding reindexed transversal sum. -/
theorem cupCochainOneTwo_corestrictionCochainTwo
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H × H → B) (g h i : G) :
    cupCochainOneTwo A B x (corestrictionCochainTwo B T y) (g, h, i) =
      ∑ t : (T : Set G),
        x g ⊗ₜ[k]
          B.ρ (g * (T.schreierRep t g : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i)) := by
  rw [cupCochainOneTwo_apply,
    corestrictionCochainTwo_apply, map_sum, TensorProduct.tmul_sum]
  calc
    (∑ t : (T : Set G),
        x g ⊗ₜ[k]
          B.ρ g
            (B.ρ (t : G)⁻¹
              (y (T.schreierFactor t h,
                T.schreierFactor (T.schreierRep t h) i)))) =
      ∑ t : (T : Set G),
        x g ⊗ₜ[k]
          B.ρ (g * (t : G)⁻¹)
            (y (T.schreierFactor t h,
              T.schreierFactor (T.schreierRep t h) i)) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [← Module.End.mul_apply, ← map_mul]
    _ = _ :=
      (T.schreierRepEquiv g).sum_comp
        (fun t : (T : Set G) =>
          x g ⊗ₜ[k]
            B.ρ (g * (t : G)⁻¹)
              (y (T.schreierFactor t h,
                T.schreierFactor (T.schreierRep t h) i))) |>.symm

/-- A transferred restricted `(1,2)` cup summand split into the projection
term and the two homotopy terms. -/
theorem corestrictionCupOneTwo_term
    (A B : Rep k G) (T : H.RightTransversal)
    (x : cocycles₁ A)
    (y : cocycles₂ (Rep.res (Subgroup.subtype H) B))
    (t : (T : Set G)) (g h i : G) :
    (A ⊗ B : Rep k G).ρ (t : G)⁻¹
        (cupCochainOneTwo
          (Rep.res (Subgroup.subtype H) A)
          (Rep.res (Subgroup.subtype H) B)
          (fun a : H => x (a : G)) y
          (T.schreierFactor t g,
            T.schreierFactor (T.schreierRep t g) h,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g) h) i)) =
      x g ⊗ₜ[k]
          B.ρ (g * (T.schreierRep t g : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i)) +
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g * (T.schreierRep t g : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i)) -
        A.ρ (g * (T.schreierRep t g : G)⁻¹)
            (x (T.schreierRep t g : G)) ⊗ₜ[k]
          B.ρ (g * (T.schreierRep t g : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i)) := by
  rw [cupCochainOneTwo_apply, tensor_rho_tmul_one_two]
  have hB :
      B.ρ (t : G)⁻¹
          (B.ρ (T.schreierFactor t g : G)
            (y (T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i))) =
        B.ρ (g * (T.schreierRep t g : G)⁻¹)
          (y (T.schreierFactor (T.schreierRep t g) h,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g) h) i)) := by
    rw [← Module.End.mul_apply, ← map_mul,
      T.inv_mul_schreierFactor t g]
  change A.ρ (t : G)⁻¹ (x (T.schreierFactor t g : G)) ⊗ₜ[k]
      B.ρ (t : G)⁻¹
        (B.ρ (T.schreierFactor t g : G)
          (y (T.schreierFactor (T.schreierRep t g) h,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g) h) i))) = _
  rw [hB, rho_inv_schreierFactor_cocycle A T x t g,
    TensorProduct.sub_tmul, TensorProduct.add_tmul]

/-- Cochain-level `(1,2)` projection formula.  The transferred restricted
cup is the cup with the transferred right factor minus the boundary of the
explicit degree-two homotopy. -/
theorem corestrictionCochainThree_cup_one_two
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : cocycles₁ A)
    (y : cocycles₂ (Rep.res (Subgroup.subtype H) B)) :
    corestrictionCochainThree (A ⊗ B) T
        (cupCochainOneTwo
          (Rep.res (Subgroup.subtype H) A)
          (Rep.res (Subgroup.subtype H) B)
          (fun h : H => x (h : G)) y) =
      cupCochainOneTwo A B x (corestrictionCochainTwo B T y) -
        (d₂₃ (A ⊗ B)).hom
          (cupProjectionHomotopyOneTwo A B T x y) := by
  funext p
  rcases p with ⟨g, h, i⟩
  rw [corestrictionCochainThree_apply]
  have hterms :
      (∑ t : (T : Set G),
        (A ⊗ B : Rep k G).ρ (t : G)⁻¹
          (cupCochainOneTwo
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (fun a : H => x (a : G)) y
            (T.schreierFactor t g,
              T.schreierFactor (T.schreierRep t g) h,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g) h) i))) =
        ∑ t : (T : Set G),
          (x g ⊗ₜ[k]
              B.ρ (g * (T.schreierRep t g : G)⁻¹)
                (y (T.schreierFactor (T.schreierRep t g) h,
                  T.schreierFactor
                    (T.schreierRep (T.schreierRep t g) h) i)) +
            A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
              B.ρ (g * (T.schreierRep t g : G)⁻¹)
                (y (T.schreierFactor (T.schreierRep t g) h,
                  T.schreierFactor
                    (T.schreierRep (T.schreierRep t g) h) i)) -
            A.ρ (g * (T.schreierRep t g : G)⁻¹)
                (x (T.schreierRep t g : G)) ⊗ₜ[k]
              B.ρ (g * (T.schreierRep t g : G)⁻¹)
                (y (T.schreierFactor (T.schreierRep t g) h,
                  T.schreierFactor
                    (T.schreierRep (T.schreierRep t g) h) i))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCupOneTwo_term A B T x y t g h i
  rw [hterms, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← cupCochainOneTwo_corestrictionCochainTwo A B T x y g h i]
  rw [← cupProjectionHomotopyOneTwo_cocycle_terms A B T x y g h i]
  rw [← rho_cupProjectionHomotopyOneTwo A B T x y g h i]
  simp only [Pi.sub_apply, d₂₃_hom_apply]
  abel

/-- Representative-level chosen-transversal `(1,2)` projection formula. -/
theorem corestrictionH3OfRightTransversal_cupCocycleOneTwo
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : cocycles₁ A)
    (y : cocycles₂ (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH3OfRightTransversal (A ⊗ B) T
        (H3π (Rep.res (Subgroup.subtype H) (A ⊗ B))
          (mapCocycles₃ (MonoidHom.id H)
            (Rep.resTensorIso (Subgroup.subtype H) A B).hom
            (cupCocycleOneTwo
              (Rep.res (Subgroup.subtype H) A)
              (Rep.res (Subgroup.subtype H) B)
              (mapCocycles₁ (Subgroup.subtype H) (𝟙 _) x) y))) =
      H3π (A ⊗ B)
        (cupCocycleOneTwo A B x
          (corestrictionCocyclesTwo B T y)) := by
  rw [corestrictionH3OfRightTransversal_H3π]
  apply (H3π_eq_iff _ _).2
  refine ⟨-cupProjectionHomotopyOneTwo A B T x y, ?_⟩
  change (d₂₃ (A ⊗ B)).hom
      (-cupProjectionHomotopyOneTwo A B T x y) =
    corestrictionCochainThree (A ⊗ B) T
      (cupCochainOneTwo
        (Rep.res (Subgroup.subtype H) A)
        (Rep.res (Subgroup.subtype H) B)
        (fun h : H => x (h : G)) y) -
      cupCochainOneTwo A B x (corestrictionCochainTwo B T y)
  rw [map_neg, corestrictionCochainThree_cup_one_two]
  abel

/-- Chosen-transversal H1 x H2 to H3 projection formula:
`cor(res(x) cup y) = x cup cor(y)`. -/
theorem corestrictionH3OfRightTransversal_cupOneTwo
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : H1 A) (y : H2 (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH3OfRightTransversal (A ⊗ B) T
        (map (MonoidHom.id H)
          (Rep.resTensorIso (Subgroup.subtype H) A B).hom 3
          (cupOneTwo
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (map (Subgroup.subtype H) (𝟙 _) 1 x) y)) =
      cupOneTwo A B x (corestrictionH2OfRightTransversal B T y) := by
  induction x using H1_induction_on with
  | _ x =>
      induction y using H2_induction_on with
      | _ y =>
          rw [← ConcreteCategory.comp_apply, H1π_comp_map]
          simp only [ConcreteCategory.comp_apply]
          rw [cupOneTwo_H1π_H2π]
          rw [← ConcreteCategory.comp_apply, H3π_comp_map]
          simp only [ConcreteCategory.comp_apply]
          rw [corestrictionH3OfRightTransversal_cupCocycleOneTwo]
          rw [corestrictionH2OfRightTransversal_H2π,
            cupOneTwo_H1π_H2π]

end groupCohomology
