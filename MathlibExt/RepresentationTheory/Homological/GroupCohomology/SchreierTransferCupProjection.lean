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
# The degree-one by degree-one cup projection formula

Let A and B be G-representations over a commutative ring k, let H ≤ G have finite index and
let T be a right transversal. For a G-one-cocycle x and an H-one-cocycle y, define K¹(g) = ∑ₜ
ρ_A(t⁻¹)x(t) ⊗ ρ_B(t⁻¹)y(a(t,g)).

The cochain identity is cor_T²(x|H ∪ y) = x ∪ cor_T¹(y) − d¹K¹, with coefficient order A ⊗ B.
Thus in degree two, cor_T(res(x) ∪ y) = x ∪ cor_T(y), after the canonical comparison A|H ⊗ B|H
≅ (A ⊗ B)|H. The formula holds both for represented cocycle classes and for arbitrary H¹
classes.
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

/-- Finite representatives for the one-by-one cup projection formula.

The finite-index hypothesis gives a finite enumeration of T for the tensor-valued comparison
sum. -/
noncomputable local instance cupProjectionRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-one cochain measuring the cup projection difference.

For arbitrary x : G → A and y : H → B, define K¹(g) = ∑ₜ ρ_A(t⁻¹)x(t) ⊗ ρ_B(t⁻¹)y(a(t,g)),
with A first and B second in the tensor product. -/
noncomputable def cupProjectionHomotopyOneOne
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H → B) : G → (A ⊗ B : Rep k G) :=
  fun g => ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
      B.ρ (t : G)⁻¹ (y (T.schreierFactor t g))

/-- Values of the one-by-one projection cochain.

At g, the projection cochain is the sum of the inverse-translated x(t) tensored with the
inverse-translated y(a(t,g)). -/
@[simp]
theorem cupProjectionHomotopyOneOne_apply
    (A B : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (x : G → A) (y : H → B) (g : G) :
    cupProjectionHomotopyOneOne A B T x y g =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹ (x (t : G)) ⊗ₜ[k]
          B.ρ (t : G)⁻¹ (y (T.schreierFactor t g)) :=
  rfl

/-- The cocycle value of a Schreier factor.

For a G-one-cocycle x and tg = a(t,g)u, the identity is ρ(t⁻¹)x(a(t,g)) = x(g) + ρ(t⁻¹)x(t) −
ρ(gu⁻¹)x(u). -/
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

/-- The product identity for the one-by-one projection cochain.

If y is an H-one-cocycle, K¹(g₁g₂) is K¹(g₁) plus the sum with first tensor factor
ρ_A(t⁻¹)x(t) and second factor ρ_B(g₁r(t,g₁)⁻¹)y(a(r(t,g₁),g₂)). -/
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

/-- The tensor action on the one-by-one projection cochain.

Applying g₁ to K¹(g₂) and reindexing by u = r(t,g₁) gives terms ρ_A(g₁u⁻¹)x(u) ⊗
ρ_B(g₁u⁻¹)y(a(u,g₂)). -/
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

/-- The cup product with a transferred one-cochain.

The value of x ∪ cor_T¹(y) at (g₁,g₂) is the sum of x(g₁) ⊗ ρ_B(g₁r(t,g₁)⁻¹)y(a(r(t,g₁),g₂)). -/
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

/-- The transferred one-by-one cup summand.

For one-cocycles x and y, the inverse-weighted restricted cup summand equals the corresponding
x(g₁) term plus the comparison term from x(t) minus the translated comparison term from
x(r(t,g₁)). The second tensor factor is common to these three terms. -/
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

/-- The one-by-one cochain projection identity with its boundary.

For a G-one-cocycle x and H-one-cocycle y, cor_T²(x|H ∪ y) = x ∪ cor_T¹(y) −
d¹(cupProjectionHomotopyOneOne A B T x y). -/
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

/-- The cup projection formula on one-cocycle representatives.

The transferred degree-two class of the restricted cup of x and y equals the class of the cup
of x with the transferred one-cocycle y. The source coefficients are identified by the
canonical restriction–tensor isomorphism. -/
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

/-- The one-by-one projection formula on cohomology classes.

For x ∈ H¹(G,A) and y ∈ H¹(H,B|H), cor_T(res(x) ∪ y) = x ∪ cor_T(y) in H²(G,A ⊗ B), using the
canonical restriction–tensor coefficient comparison. -/
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
