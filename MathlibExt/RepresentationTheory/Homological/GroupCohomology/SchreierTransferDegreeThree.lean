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

public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThree
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferDegreeTwo

/-!
# Degree-three chosen-transversal group-cohomological transfer

For a finite-index subgroup `H ≤ G` and a chosen right transversal, this
file defines the standard degree-three inhomogeneous cochain transfer.  It
proves compatibility with `d₂₃`, preservation of three-cocycles and
three-coboundaries, and descends the construction to an `H³` map with an
explicit representative formula.

The right transversal remains part of the API.  Independence of that choice,
canonical degree-three corestriction, a restriction/corestriction index
formula, and any Kummer or Bloch--Kato consequence are not asserted here.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

noncomputable local instance corestrictionDegreeThreeRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Degree-three cochain transfer associated to a chosen finite right
transversal. -/
noncomputable def corestrictionCochainThree (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    (H × H × H → A) →ₗ[k] (G × G × G → A) where
  toFun f p := ∑ t : (T : Set G),
    A.ρ (t : G)⁻¹
      (f (T.schreierFactor t p.1,
        T.schreierFactor (T.schreierRep t p.1) p.2.1,
        T.schreierFactor
          (T.schreierRep (T.schreierRep t p.1) p.2.1) p.2.2))
  map_add' f₁ f₂ := by
    funext p
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext p
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

@[simp]
theorem corestrictionCochainThree_apply (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H × H → A) (g₁ g₂ g₃ : G) :
    corestrictionCochainThree A T f (g₁, g₂, g₃) =
      ∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          (f (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) :=
  rfl

/-- A single summand in the compatibility of degree-three transfer with
`d₂₃`. -/
theorem corestrictionCochainThree_d₂₃_term (A : Rep k G)
    (T : H.RightTransversal) (b : H × H → A)
    (t : (T : Set G)) (g₁ g₂ g₃ : G) :
    A.ρ (t : G)⁻¹
        ((d₂₃ (Rep.res (Subgroup.subtype H) A)).hom b
          (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) =
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (b (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) -
        A.ρ (t : G)⁻¹
          (b (T.schreierFactor t (g₁ * g₂),
            T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃)) +
        A.ρ (t : G)⁻¹
          (b (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃))) -
        A.ρ (t : G)⁻¹
          (b (T.schreierFactor t g₁,
            T.schreierFactor (T.schreierRep t g₁) g₂)) := by
  simp only [d₂₃_hom_apply, map_add, map_sub]
  rw [← T.schreierFactor_mul t g₁ g₂,
    ← T.schreierFactor_mul (T.schreierRep t g₁) g₂ g₃,
    ← T.schreierRep_mul t g₁ g₂]
  have hlead :
      A.ρ (t : G)⁻¹
          ((Rep.res (Subgroup.subtype H) A).ρ (T.schreierFactor t g₁)
            (b (T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep t (g₁ * g₂)) g₃))) =
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (b (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep t (g₁ * g₂)) g₃)) := by
    change A.ρ (t : G)⁻¹
        (A.ρ (T.schreierFactor t g₁ : G)
          (b (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃))) = _
    rw [← Module.End.mul_apply, ← map_mul,
      T.inv_mul_schreierFactor t g₁]
  rw [hlead]

/-- Degree-two and degree-three chosen-transversal transfers commute with
the inhomogeneous differential `d₂₃`. -/
theorem corestrictionCochainThree_d₂₃ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] (b : H × H → A) :
    corestrictionCochainThree A T
        ((d₂₃ (Rep.res (Subgroup.subtype H) A)).hom b) =
      (d₂₃ A).hom (corestrictionCochainTwo A T b) := by
  funext p
  rcases p with ⟨g₁, g₂, g₃⟩
  rw [corestrictionCochainThree_apply]
  have hterms :
      (∑ t : (T : Set G),
        A.ρ (t : G)⁻¹
          ((d₂₃ (Rep.res (Subgroup.subtype H) A)).hom b
            (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃))) =
        ∑ t : (T : Set G),
          (A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
              (b (T.schreierFactor (T.schreierRep t g₁) g₂,
                T.schreierFactor
                  (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) -
            A.ρ (t : G)⁻¹
              (b (T.schreierFactor t (g₁ * g₂),
                T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃)) +
            A.ρ (t : G)⁻¹
              (b (T.schreierFactor t g₁,
                T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃))) -
            A.ρ (t : G)⁻¹
              (b (T.schreierFactor t g₁,
                T.schreierFactor (T.schreierRep t g₁) g₂))) := by
    apply Finset.sum_congr rfl
    intro t _
    exact corestrictionCochainThree_d₂₃_term A T b t g₁ g₂ g₃
  rw [hterms]
  simp only [d₂₃_hom_apply, corestrictionCochainTwo_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_sub_distrib,
    sum_rho_mul_schreierRep_inv_twoFactor]

/-- Reindexing the leading sum in the transferred three-cocycle equation. -/
theorem sum_rho_mul_schreierRep_inv_threeFactor (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H × H → A) (g₁ g₂ g₃ g₄ : G) :
    (∑ t : (T : Set G),
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
        (f (T.schreierFactor (T.schreierRep t g₁) g₂,
          T.schreierFactor
            (T.schreierRep (T.schreierRep t g₁) g₂) g₃,
          T.schreierFactor
            (T.schreierRep
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃) g₄))) =
      A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₂) g₃) g₄))) := by
  calc
    (∑ t : (T : Set G),
        A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (f (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃,
            T.schreierFactor
              (T.schreierRep
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃) g₄))) =
      ∑ t : (T : Set G),
        A.ρ (g₁ * (t : G)⁻¹)
          (f (T.schreierFactor t g₂,
            T.schreierFactor (T.schreierRep t g₂) g₃,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₂) g₃) g₄)) :=
      (T.schreierRepEquiv g₁).sum_comp
        (fun t : (T : Set G) =>
          A.ρ (g₁ * (t : G)⁻¹)
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₂) g₃) g₄)))
    _ = ∑ t : (T : Set G),
        A.ρ g₁
          (A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₂) g₃) g₄))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [← Module.End.mul_apply, ← map_mul]
    _ = A.ρ g₁
        (∑ t : (T : Set G),
          A.ρ (t : G)⁻¹
            (f (T.schreierFactor t g₂,
              T.schreierFactor (T.schreierRep t g₂) g₃,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₂) g₃) g₄))) := by
      rw [map_sum]

/-- A single summand of the transferred three-cocycle equation. -/
theorem corestrictionCochainThree_cocycle_term (A : Rep k G)
    (T : H.RightTransversal)
    (f : cocycles₃ (Rep.res (Subgroup.subtype H) A))
    (t : (T : Set G)) (g₁ g₂ g₃ g₄ : G) :
    A.ρ (t : G)⁻¹
        (f (T.schreierFactor t (g₁ * g₂),
              T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t (g₁ * g₂)) g₃) g₄) +
          f (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) (g₃ * g₄))) =
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
          (f (T.schreierFactor (T.schreierRep t g₁) g₂,
            T.schreierFactor
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃,
            T.schreierFactor
              (T.schreierRep
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃) g₄)) +
        A.ρ (t : G)⁻¹
          (f (T.schreierFactor t g₁,
                T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃),
                T.schreierFactor
                  (T.schreierRep (T.schreierRep t g₁) (g₂ * g₃)) g₄) +
            f (T.schreierFactor t g₁,
              T.schreierFactor (T.schreierRep t g₁) g₂,
              T.schreierFactor
                (T.schreierRep (T.schreierRep t g₁) g₂) g₃)) := by
  let a₁ : H := T.schreierFactor t g₁
  let r₁ : (T : Set G) := T.schreierRep t g₁
  let a₂ : H := T.schreierFactor r₁ g₂
  let r₂ : (T : Set G) := T.schreierRep r₁ g₂
  let a₃ : H := T.schreierFactor r₂ g₃
  let r₃ : (T : Set G) := T.schreierRep r₂ g₃
  let a₄ : H := T.schreierFactor r₃ g₄
  have hz := (mem_cocycles₃_def f).1 f.2
    (a₁ : H) (a₂ : H) (a₃ : H) (a₄ : H)
  have hz' :
      f (a₁ * a₂, a₃, a₄) + f (a₁, a₂, a₃ * a₄) =
        (Rep.res (Subgroup.subtype H) A).ρ a₁ (f (a₂, a₃, a₄)) +
          f (a₁, a₂ * a₃, a₄) + f (a₁, a₂, a₃) := by
    rw [← sub_eq_zero]
    calc
      f (a₁ * a₂, a₃, a₄) + f (a₁, a₂, a₃ * a₄) -
          ((Rep.res (Subgroup.subtype H) A).ρ a₁ (f (a₂, a₃, a₄)) +
            f (a₁, a₂ * a₃, a₄) + f (a₁, a₂, a₃)) =
        -((Rep.res (Subgroup.subtype H) A).ρ a₁ (f (a₂, a₃, a₄)) -
          f (a₁ * a₂, a₃, a₄) + f (a₁, a₂ * a₃, a₄) -
          f (a₁, a₂, a₃ * a₄) + f (a₁, a₂, a₃)) := by abel
      _ = 0 := by rw [hz, neg_zero]
  have hlead (x : A) :
      A.ρ (t : G)⁻¹
          ((Rep.res (Subgroup.subtype H) A).ρ a₁ x) =
        A.ρ (g₁ * (r₁ : G)⁻¹) x := by
    change A.ρ (t : G)⁻¹ (A.ρ (a₁ : G) x) = _
    rw [← Module.End.mul_apply, ← map_mul]
    change A.ρ ((t : G)⁻¹ * (T.schreierFactor t g₁ : G)) x = _
    rw [T.inv_mul_schreierFactor t g₁]
  rw [T.schreierFactor_mul t g₁ g₂,
    T.schreierFactor_mul r₂ g₃ g₄,
    T.schreierFactor_mul r₁ g₂ g₃,
    T.schreierRep_mul t g₁ g₂,
    T.schreierRep_mul r₁ g₂ g₃]
  change A.ρ (t : G)⁻¹
      (f (a₁ * a₂, a₃, a₄) + f (a₁, a₂, a₃ * a₄)) =
    A.ρ (g₁ * (r₁ : G)⁻¹) (f (a₂, a₃, a₄)) +
      A.ρ (t : G)⁻¹
        (f (a₁, a₂ * a₃, a₄) + f (a₁, a₂, a₃))
  rw [hz', map_add, map_add, hlead]
  rw [map_add]
  abel

/-- Degree-three chosen-transversal cochain transfer sends three-cocycles to
three-cocycles. -/
theorem corestrictionCochainThree_mem_cocycles₃ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionCochainThree A T f ∈ cocycles₃ A := by
  rw [mem_cocycles₃_def]
  intro g₁ g₂ g₃ g₄
  rw [corestrictionCochainThree_apply,
    corestrictionCochainThree_apply,
    corestrictionCochainThree_apply,
    corestrictionCochainThree_apply,
    corestrictionCochainThree_apply]
  let S₀ : A := A.ρ g₁
    (∑ t : (T : Set G), A.ρ (t : G)⁻¹
      (f (T.schreierFactor t g₂,
        T.schreierFactor (T.schreierRep t g₂) g₃,
        T.schreierFactor (T.schreierRep (T.schreierRep t g₂) g₃) g₄)))
  let S₁₂ : A := ∑ t : (T : Set G), A.ρ (t : G)⁻¹
    (f (T.schreierFactor t (g₁ * g₂),
      T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃,
      T.schreierFactor
        (T.schreierRep (T.schreierRep t (g₁ * g₂)) g₃) g₄))
  let S₂₃ : A := ∑ t : (T : Set G), A.ρ (t : G)⁻¹
    (f (T.schreierFactor t g₁,
      T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃),
      T.schreierFactor
        (T.schreierRep (T.schreierRep t g₁) (g₂ * g₃)) g₄))
  let S₃₄ : A := ∑ t : (T : Set G), A.ρ (t : G)⁻¹
    (f (T.schreierFactor t g₁,
      T.schreierFactor (T.schreierRep t g₁) g₂,
      T.schreierFactor
        (T.schreierRep (T.schreierRep t g₁) g₂) (g₃ * g₄)))
  let S₁ : A := ∑ t : (T : Set G), A.ρ (t : G)⁻¹
    (f (T.schreierFactor t g₁,
      T.schreierFactor (T.schreierRep t g₁) g₂,
      T.schreierFactor (T.schreierRep (T.schreierRep t g₁) g₂) g₃))
  let L : A := ∑ t : (T : Set G),
    A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
      (f (T.schreierFactor (T.schreierRep t g₁) g₂,
        T.schreierFactor (T.schreierRep (T.schreierRep t g₁) g₂) g₃,
        T.schreierFactor
          (T.schreierRep
            (T.schreierRep (T.schreierRep t g₁) g₂) g₃) g₄))
  have hL : L = S₀ := by
    exact sum_rho_mul_schreierRep_inv_threeFactor
      A T f g₁ g₂ g₃ g₄
  have hsum : S₁₂ + S₃₄ = L + S₂₃ + S₁ := by
    let q₁₂ : ↥(T : Set G) → A := fun t => A.ρ (t : G)⁻¹
      (f (T.schreierFactor t (g₁ * g₂),
        T.schreierFactor (T.schreierRep t (g₁ * g₂)) g₃,
        T.schreierFactor
          (T.schreierRep (T.schreierRep t (g₁ * g₂)) g₃) g₄))
    let q₃₄ : ↥(T : Set G) → A := fun t => A.ρ (t : G)⁻¹
      (f (T.schreierFactor t g₁,
        T.schreierFactor (T.schreierRep t g₁) g₂,
        T.schreierFactor
          (T.schreierRep (T.schreierRep t g₁) g₂) (g₃ * g₄)))
    let qL : ↥(T : Set G) → A := fun t =>
      A.ρ (g₁ * (T.schreierRep t g₁ : G)⁻¹)
        (f (T.schreierFactor (T.schreierRep t g₁) g₂,
          T.schreierFactor (T.schreierRep (T.schreierRep t g₁) g₂) g₃,
          T.schreierFactor
            (T.schreierRep
              (T.schreierRep (T.schreierRep t g₁) g₂) g₃) g₄))
    let q₂₃ : ↥(T : Set G) → A := fun t => A.ρ (t : G)⁻¹
      (f (T.schreierFactor t g₁,
        T.schreierFactor (T.schreierRep t g₁) (g₂ * g₃),
        T.schreierFactor
          (T.schreierRep (T.schreierRep t g₁) (g₂ * g₃)) g₄))
    let q₁ : ↥(T : Set G) → A := fun t => A.ρ (t : G)⁻¹
      (f (T.schreierFactor t g₁,
        T.schreierFactor (T.schreierRep t g₁) g₂,
        T.schreierFactor (T.schreierRep (T.schreierRep t g₁) g₂) g₃))
    dsimp only [S₁₂, S₃₄, L, S₂₃, S₁]
    change (∑ t, q₁₂ t) + (∑ t, q₃₄ t) =
      (∑ t, qL t) + (∑ t, q₂₃ t) + (∑ t, q₁ t)
    calc
      (∑ t, q₁₂ t) + (∑ t, q₃₄ t) =
          ∑ t, (q₁₂ t + q₃₄ t) := Finset.sum_add_distrib.symm
      _ = ∑ t, (qL t + (q₂₃ t + q₁ t)) := by
        apply Finset.sum_congr rfl
        intro t _
        have ht := corestrictionCochainThree_cocycle_term
          A T f t g₁ g₂ g₃ g₄
        simp only [map_add] at ht
        exact ht
      _ = (∑ t, qL t) + (∑ t, q₂₃ t) + (∑ t, q₁ t) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        abel
  have hbalance : S₁₂ + S₃₄ = S₀ + S₂₃ + S₁ := by
    rw [hsum, hL]
  change S₀ - S₁₂ + S₂₃ - S₃₄ + S₁ = 0
  calc
    S₀ - S₁₂ + S₂₃ - S₃₄ + S₁ =
        (S₀ + S₂₃ + S₁) - (S₁₂ + S₃₄) := by abel
    _ = 0 := by rw [← hbalance]; abel

/-- Degree-three chosen-transversal cochain transfer sends
three-coboundaries to three-coboundaries. -/
theorem corestrictionCochainThree_mem_coboundaries₃ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H × H → A)
    (hf : f ∈ coboundaries₃ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionCochainThree A T f ∈ coboundaries₃ A := by
  rcases hf with ⟨b, rfl⟩
  refine ⟨corestrictionCochainTwo A T b, ?_⟩
  exact (corestrictionCochainThree_d₂₃ A T b).symm

/-- Degree-three cochain transfer restricted to three-cocycles. -/
noncomputable def corestrictionCocyclesThree (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    cocycles₃ (Rep.res (Subgroup.subtype H) A) →ₗ[k] cocycles₃ A where
  toFun f := ⟨corestrictionCochainThree A T f,
    corestrictionCochainThree_mem_cocycles₃ A T f⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    change corestrictionCochainThree A T
        ((f₁ + f₂ : cocycles₃
          (Rep.res (Subgroup.subtype H) A)) : H × H × H → A) = _
    exact map_add (corestrictionCochainThree A T)
      (f₁ : H × H × H → A) (f₂ : H × H × H → A)
  map_smul' r f := by
    apply Subtype.ext
    change corestrictionCochainThree A T
        ((r • f : cocycles₃
          (Rep.res (Subgroup.subtype H) A)) : H × H × H → A) = _
    exact map_smul (corestrictionCochainThree A T) r
      (f : H × H × H → A)

@[simp]
theorem coe_corestrictionCocyclesThree (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    (corestrictionCocyclesThree A T f : G × G × G → A) =
      corestrictionCochainThree A T f :=
  rfl

/-- The `H³` class of a transferred three-cocycle before descending through
the source `H³` quotient. -/
noncomputable def corestrictionCocycleThreeClass (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    cocycles₃ (Rep.res (Subgroup.subtype H) A) →ₗ[k] H3 A :=
  (H3π A).hom.comp (corestrictionCocyclesThree A T)

/-- Transferred three-cocycle classes annihilate source
three-coboundaries. -/
theorem corestrictionCocycleThreeClass_ker (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    LinearMap.ker
        (H3π (Rep.res (Subgroup.subtype H) A)).hom ≤
      LinearMap.ker (corestrictionCocycleThreeClass A T) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  apply (H3π_eq_zero_iff _).2
  have hboundary : (f : H × H × H → A) ∈
      coboundaries₃ (Rep.res (Subgroup.subtype H) A) :=
    (H3π_eq_zero_iff f).1 hf
  exact corestrictionCochainThree_mem_coboundaries₃ A T f hboundary

/-- Degree-three cohomological transfer associated to a chosen finite right
transversal.  Independence of the transversal is not asserted here. -/
noncomputable def corestrictionH3OfRightTransversal (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    H3 (Rep.res (Subgroup.subtype H) A) →ₗ[k] H3 A :=
  let q := (LinearMap.ker
      (H3π (Rep.res (Subgroup.subtype H) A)).hom).liftQ
    (corestrictionCocycleThreeClass A T)
    (corestrictionCocycleThreeClass_ker A T)
  let e :=
    (H3π (Rep.res (Subgroup.subtype H) A)).hom
      |>.quotKerEquivOfSurjective
        ((ModuleCat.epi_iff_surjective
          (H3π (Rep.res (Subgroup.subtype H) A))).1 inferInstance)
  q.comp e.symm.toLinearMap

/-- The chosen-transversal `H³` transfer computes on a presented class by
transferring its three-cocycle representative. -/
@[simp]
theorem corestrictionH3OfRightTransversal_H3π (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionH3OfRightTransversal A T
        (H3π (Rep.res (Subgroup.subtype H) A) f) =
      H3π A (corestrictionCocyclesThree A T f) := by
  change (LinearMap.ker
      (H3π (Rep.res (Subgroup.subtype H) A)).hom).liftQ
        (corestrictionCocycleThreeClass A T)
        (corestrictionCocycleThreeClass_ker A T)
        (((H3π (Rep.res (Subgroup.subtype H) A)).hom
          |>.quotKerEquivOfSurjective
            ((ModuleCat.epi_iff_surjective
              (H3π (Rep.res (Subgroup.subtype H) A))).1 inferInstance)).symm
          (H3π (Rep.res (Subgroup.subtype H) A) f)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end groupCohomology
