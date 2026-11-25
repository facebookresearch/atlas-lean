/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwo
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneOneMapOfHom
public import MathlibExt.RepresentationTheory.Rep.ResTensor

/-!
# A chosen-transversal cup projection formula

This file develops the first cup-product projection formula for the explicit
right-transversal transfer.  For a `G`-one-cocycle `x` and an
`H`-one-cocycle `y`, the transfer of `res(x) ∪ y` differs from
`x ∪ cor(y)` by the boundary of an explicit degree-one homotopy.

The transversal remains an explicit parameter.  No independence of that
choice, finite-etale comparison, norm-residue map, or Kummer-Steinberg
vanishing is asserted.
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

noncomputable local instance cupProjectionRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The explicit one-cochain measuring the failure of the cup projection
formula to hold strictly at cochain level. -/
noncomputable def cupProjectionHomotopyOneOne
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H → B) : G → (A ⊗ B : Rep k G) :=
  fun g => ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
      B.ρ (t : G)⁻¹ (y (T.schreierFactor t g))

@[simp]
theorem cupProjectionHomotopyOneOne_apply
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H → B) (g : G) :
    cupProjectionHomotopyOneOne A B T x y g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (t : G)⁻¹ (y (T.schreierFactor t g)) :=
  rfl

/-- The restriction cocycle identity rewritten along one Schreier
decomposition. -/
theorem rho_inv_schreierFactor_cocycle (A : Rep k G)
    (T : H.RightTransversal) (x : groupCohomology.cocycles₁ A)
    (t : (T : Set G)) (g : G) :
    A.ρ (t : G)⁻¹ (x (T.schreierFactor t g : G)) =
      x g + A.ρ (t : G)⁻¹ (x (t : G)) -
        A.ρ (g * (T.schreierRep t g : G)⁻¹)
          (x (T.schreierRep t g : G)) := by
  have hx_tg := (groupCohomology.mem_cocycles₁_iff x).mp x.property
    (t : G) g
  have hx_hr := (groupCohomology.mem_cocycles₁_iff x).mp x.property
    (T.schreierFactor t g : G) (T.schreierRep t g : G)
  rw [T.schreierFactor_mul_schreierRep t g] at hx_hr
  have hraw :
      A.ρ (T.schreierFactor t g : G)
          (x (T.schreierRep t g : G)) +
        x (T.schreierFactor t g : G) =
      A.ρ (t : G) (x g) + x (t : G) :=
    hx_hr.symm.trans hx_tg
  have hacted := congrArg (fun z => A.ρ (t : G)⁻¹ z) hraw
  rw [map_add, map_add] at hacted
  have hleft :
      A.ρ (t : G)⁻¹
          (A.ρ (T.schreierFactor t g : G)
            (x (T.schreierRep t g : G))) =
        A.ρ (g * (T.schreierRep t g : G)⁻¹)
          (x (T.schreierRep t g : G)) := by
    rw [← Module.End.mul_apply, ← map_mul,
      T.inv_mul_schreierFactor t g]
  have hright :
      A.ρ (t : G)⁻¹ (A.ρ (t : G) (x g)) = x g := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  rw [hleft, hright] at hacted
  exact eq_sub_of_add_eq ((add_comm _ _).trans hacted)

private theorem tensor_rho_tmul (A B : Rep k G) (g : G)
    (a : A) (b : B) :
    (A ⊗ B : Rep k G).ρ g (a ⊗ₜ[k] b) =
      A.ρ g a ⊗ₜ[k] B.ρ g b := by
  change TensorProduct.map (A.ρ g) (B.ρ g) (a ⊗ₜ[k] b) = _
  rw [TensorProduct.map_tmul]

/-- Splitting the homotopy cochain at a product by the one-cocycle law for
the subgroup input. -/
theorem cupProjectionHomotopyOneOne_mul
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A)
    (y : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) B))
    (g₁ g₂ : G) :
    cupProjectionHomotopyOneOne A B T x y (g₁ * g₂) =
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂))) +
        cupProjectionHomotopyOneOne A B T x y g₁ := by
  rw [cupProjectionHomotopyOneOne_apply,
    cupProjectionHomotopyOneOne_apply]
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (t : G)⁻¹ (y (T.schreierFactor t (g₁ * g₂)))) =
      ∑ t : (T : Set G),
        (A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
            B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (y (T.schreierFactor (T.schreierRep t g₁) g₂)) +
          A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
            B.ρ (t : G)⁻¹ (y (T.schreierFactor t g₁))) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [corestrictionCochainOne_mul_term B T y t g₁ g₂,
      TensorProduct.tmul_add]
  rw [hterms, Finset.sum_add_distrib]

/-- Acting on the homotopy cochain reindexes through the Schreier
permutation of the transversal. -/
theorem rho_cupProjectionHomotopyOneOne
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H → B) (g₁ g₂ : G) :
    (A ⊗ B : Rep k G).ρ g₁
        (cupProjectionHomotopyOneOne A B T x y g₂) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (x (T.schreierRep t g₁ : G)) ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂)) := by
  rw [cupProjectionHomotopyOneOne_apply, map_sum]
  calc
    (∑ t : (T : Set G),
        (A ⊗ B : Rep k G).ρ g₁
          (A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
            B.ρ (t : G)⁻¹ (y (T.schreierFactor t g₂)))) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (t : G)⁻¹) (x (t : G)) ⊗ₜ[k]
          B.ρ (g₁ * (t : G)⁻¹) (y (T.schreierFactor t g₂)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [tensor_rho_tmul]
      congr 1
      · rw [← Module.End.mul_apply, ← map_mul]
      · rw [← Module.End.mul_apply, ← map_mul]
    _ = _ :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g₁ * (t : G)⁻¹) (x (t : G)) ⊗ₜ[k]
            B.ρ (g₁ * (t : G)⁻¹)
              (y (T.schreierFactor t g₂))) |>.symm

/-- The cup with the transferred right factor, written as the corresponding
reindexed transversal sum. -/
theorem cupCochainOneOne_corestrictionCochainOne
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H → B) (g₁ g₂ : G) :
    groupCohomology.cupCochainOneOne A B x
        (corestrictionCochainOne B T y) (g₁, g₂) =
      ∑ t : (T : Set G),
        x g₁ ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂)) := by
  rw [groupCohomology.cupCochainOneOne_apply,
    corestrictionCochainOne_apply, map_sum, TensorProduct.tmul_sum]
  calc
    (∑ t : (T : Set G),
        x g₁ ⊗ₜ[k]
          B.ρ g₁ (B.ρ (t : G)⁻¹ (y (T.schreierFactor t g₂)))) =
      ∑ t : (T : Set G),
        x g₁ ⊗ₜ[k]
          B.ρ (g₁ * (t : G)⁻¹) (y (T.schreierFactor t g₂)) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [← Module.End.mul_apply, ← map_mul]
    _ = _ :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          x g₁ ⊗ₜ[k]
            B.ρ (g₁ * (t : G)⁻¹) (y (T.schreierFactor t g₂))) |>.symm

/-- A single transferred restricted-cup summand, split into the projection
term and the two homotopy terms. -/
theorem corestrictionCupOneOne_term
    (A B : Rep k G) (T : H.RightTransversal)
    (x : groupCohomology.cocycles₁ A)
    (y : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) B))
    (t : (T : Set G)) (g₁ g₂ : G) :
    (A ⊗ B : Rep k G).ρ (t : G)⁻¹
        (groupCohomology.cupCochainOneOne
          (Rep.res (Subgroup.subtype H) A)
          (Rep.res (Subgroup.subtype H) B)
          (fun h : H => x (h : G)) y
          (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂)) =
      x g₁ ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂)) +
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂)) -
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (x (T.schreierRep t g₁ : G)) ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂)) := by
  rw [groupCohomology.cupCochainOneOne_apply, tensor_rho_tmul]
  have hB :
      B.ρ (t : G)⁻¹
          (B.ρ (T.schreierFactor t g₁ : G)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂))) =
        B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (y (T.schreierFactor (T.schreierRep t g₁) g₂)) := by
    rw [← Module.End.mul_apply, ← map_mul,
      T.inv_mul_schreierFactor t g₁]
  change A.ρ (t : G)⁻¹ (x (T.schreierFactor t g₁ : G)) ⊗ₜ[k]
      B.ρ (t : G)⁻¹
        (B.ρ (T.schreierFactor t g₁ : G)
          (y (T.schreierFactor (T.schreierRep t g₁) g₂))) = _
  rw [hB, rho_inv_schreierFactor_cocycle A T x t g₁,
    TensorProduct.sub_tmul, TensorProduct.add_tmul]

/-- Cochain-level projection formula.  The transferred restricted cup is
the cup with the transferred right factor minus the boundary of the explicit
homotopy cochain. -/
theorem corestrictionCochainTwo_cup_one_one
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : groupCohomology.cocycles₁ A)
    (y : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) B)) :
    corestrictionCochainTwo (A ⊗ B) T
        (groupCohomology.cupCochainOneOne
          (Rep.res (Subgroup.subtype H) A)
          (Rep.res (Subgroup.subtype H) B)
          (fun h : H => x (h : G)) y) =
      groupCohomology.cupCochainOneOne A B x
          (corestrictionCochainOne B T y) -
        (groupCohomology.d₁₂ (A ⊗ B)).hom
          (cupProjectionHomotopyOneOne A B T x y) := by
  funext p
  rcases p with ⟨g₁, g₂⟩
  rw [corestrictionCochainTwo_apply]
  have hterms :
      (∑ t : (T : Set G),
        (A ⊗ B : Rep k G).ρ (t : G)⁻¹
          (groupCohomology.cupCochainOneOne
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (fun h : H => x (h : G)) y
            (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂))) =
      ∑ t : (T : Set G),
        (x g₁ ⊗ₜ[k]
            B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (y (T.schreierFactor (T.schreierRep t g₁) g₂)) +
          A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
            B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (y (T.schreierFactor (T.schreierRep t g₁) g₂)) -
          A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (x (T.schreierRep t g₁ : G)) ⊗ₜ[k]
            B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (y (T.schreierFactor (T.schreierRep t g₁) g₂))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCupOneOne_term A B T x y t g₁ g₂
  rw [hterms, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← cupCochainOneOne_corestrictionCochainOne A B T x y g₁ g₂]
  have hq := cupProjectionHomotopyOneOne_mul A B T x y g₁ g₂
  have hq' :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
            (y (T.schreierFactor (T.schreierRep t g₁) g₂))) =
      cupProjectionHomotopyOneOne A B T x y (g₁ * g₂) -
        cupProjectionHomotopyOneOne A B T x y g₁ :=
    eq_sub_of_add_eq hq.symm
  rw [hq']
  rw [← rho_cupProjectionHomotopyOneOne A B T x y g₁ g₂]
  simp only [Pi.sub_apply, groupCohomology.d₁₂_hom_apply]
  abel

/-- Representative-level H² projection formula for a restricted left
one-cocycle and a subgroup one-cocycle. -/
theorem corestrictionH2OfRightTransversal_cupCocycleOneOne
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : groupCohomology.cocycles₁ A)
    (y : groupCohomology.cocycles₁ (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH2OfRightTransversal (A ⊗ B) T
        (groupCohomology.H2π
          (Rep.res (Subgroup.subtype H) (A ⊗ B))
          (groupCohomology.mapCocycles₂ (MonoidHom.id H)
            (Rep.resTensorIso (Subgroup.subtype H) A B).hom
            (groupCohomology.cupCocycleOneOne
              (Rep.res (Subgroup.subtype H) A)
              (Rep.res (Subgroup.subtype H) B)
              (groupCohomology.mapCocycles₁
                (Subgroup.subtype H) (𝟙 _) x) y))) =
      groupCohomology.H2π (A ⊗ B)
        (groupCohomology.cupCocycleOneOne A B x
          (corestrictionCocyclesOne B T y)) := by
  rw [corestrictionH2OfRightTransversal_H2π]
  apply (groupCohomology.H2π_eq_iff _ _).2
  refine ⟨-cupProjectionHomotopyOneOne A B T x y, ?_⟩
  change (groupCohomology.d₁₂ (A ⊗ B)).hom
      (-cupProjectionHomotopyOneOne A B T x y) =
    corestrictionCochainTwo (A ⊗ B) T
      (groupCohomology.cupCochainOneOne
        (Rep.res (Subgroup.subtype H) A)
        (Rep.res (Subgroup.subtype H) B)
        (fun h : H => x (h : G)) y) -
      groupCohomology.cupCochainOneOne A B x
        (corestrictionCochainOne B T y)
  rw [map_neg, corestrictionCochainTwo_cup_one_one]
  abel

/-- Chosen-transversal H¹×H¹→H² projection formula:
`cor(res(x) ∪ y) = x ∪ cor(y)`.  The coefficient comparison is the
identity-on-carriers restriction/tensor isomorphism. -/
theorem corestrictionH2OfRightTransversal_cupOneOne
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : groupCohomology.H1 A)
    (y : groupCohomology.H1 (Rep.res (Subgroup.subtype H) B)) :
    corestrictionH2OfRightTransversal (A ⊗ B) T
        (groupCohomology.map (MonoidHom.id H)
          (Rep.resTensorIso (Subgroup.subtype H) A B).hom 2
          (groupCohomology.cupOneOne
            (Rep.res (Subgroup.subtype H) A)
            (Rep.res (Subgroup.subtype H) B)
            (groupCohomology.map (Subgroup.subtype H) (𝟙 _) 1 x) y)) =
      groupCohomology.cupOneOne A B x
        (corestrictionH1OfRightTransversal B T y) := by
  induction x using groupCohomology.H1_induction_on with
  | _ x =>
      induction y using groupCohomology.H1_induction_on with
      | _ y =>
          rw [← ConcreteCategory.comp_apply,
            groupCohomology.H1π_comp_map]
          simp only [ConcreteCategory.comp_apply]
          rw [groupCohomology.cupOneOne_H1π_H1π]
          rw [← ConcreteCategory.comp_apply,
            groupCohomology.H2π_comp_map]
          simp only [ConcreteCategory.comp_apply]
          rw [corestrictionH2OfRightTransversal_cupCocycleOneOne]
          rw [corestrictionH1OfRightTransversal_H1π,
            groupCohomology.cupOneOne_H1π_H1π]

end groupCohomology
