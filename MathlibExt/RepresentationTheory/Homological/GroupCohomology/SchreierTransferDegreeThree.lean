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
# Schreier transfer on ternary cochains and degree-three classes

Let H ≤ G have finite index, let T be a right transversal and let A be a k-linear
G-representation over a commutative ring. Starting at t₀ = t, write tᵢgᵢ₊₁ = aᵢtᵢ₊₁ for i =
0,1,2. The ternary transfer is cor_T³(f)(g₁,g₂,g₃) = ∑ₜ ρ(t⁻¹)f(a₀,a₁,a₂).

It commutes with d²b(g₁,g₂,g₃) = ρ(g₁)b(g₂,g₃) − b(g₁g₂,g₃) + b(g₁,g₂g₃) − b(g₁,g₂). The same
factor identities preserve three-cocycles and three-coboundaries, giving a chosen-transversal
map H³(H,A|H) → H³(G,A) computed on cocycle representatives.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- Finite representatives for ternary cochain transfer.

The finite-index hypothesis gives a finite enumeration of T for the degree-three sum. -/
noncomputable local instance corestrictionDegreeThreeRightTransversalFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The degree-three Schreier cochain transfer.

For f : H × H × H → A, sum ρ(t⁻¹)f(a₀,a₁,a₂) over the successive subgroup factors of the scan
of (g₁,g₂,g₃) starting at t. This is a k-linear map of ternary cochains. -/
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

/-- The ternary representative formula for transfer.

At (g₁,g₂,g₃), the transfer is the sum of f evaluated on the three successive Schreier
factors, each weighted by the inverse action ρ(t⁻¹). -/
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

/-- An inverse-weighted degree-two differential term.

Evaluating d²b on the three successive Schreier factors and applying ρ(t⁻¹) gives the leading
translated term and the three remaining terms with signs +,−,+,−. The middle terms correspond
to the products g₁g₂ and g₂g₃. -/
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

/-- Ternary transfer commutes with the degree-two differential.

For b : H × H → A, cor_T³(d²b) = d²(cor_T²b), with the respective restricted H-action and
ambient G-action. -/
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

/-- Reindexing a transfer sum with three remaining factors.

The sum on the tail (g₂,g₃,g₄) starting at r(t,g₁), with weight ρ(g₁r(t,g₁)⁻¹), equals ρ(g₁)
times the ordinary ternary transfer sum on that tail. -/
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

/-- The three-cocycle identity on a Schreier scan.

For successive factors a₀,a₁,a₂,a₃, the H-three-cocycle identity rearranges as f(a₀a₁,a₂,a₃) +
f(a₀,a₁,a₂a₃) = ρ(a₀)f(a₁,a₂,a₃) + f(a₀,a₁a₂,a₃) + f(a₀,a₁,a₂). Weighting by ρ(t⁻¹) gives the
stated scan formula. -/
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

/-- Ternary transfer preserves three-cocycles.

The chosen-transversal transfer sends every H-three-cocycle for A|H to a G-three-cocycle for
A. -/
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

/-- Ternary transfer preserves three-coboundaries.

If a ternary H-cochain is a degree-three coboundary, its transfer is a degree-three
G-coboundary. -/
theorem corestrictionCochainThree_mem_coboundaries₃ (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : H × H × H → A)
    (hf : f ∈ coboundaries₃ (Rep.res (Subgroup.subtype H) A)) :
    corestrictionCochainThree A T f ∈ coboundaries₃ A := by
  rcases hf with ⟨b, rfl⟩
  refine ⟨corestrictionCochainTwo A T b, ?_⟩
  exact (corestrictionCochainThree_d₂₃ A T b).symm

/-- The transfer map on three-cocycles.

Restrict the k-linear ternary transfer to obtain Z³(H,A|H) → Z³(G,A). -/
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

/-- The cochain underlying a transferred three-cocycle.

The ternary G-cochain underlying corestrictionCocyclesThree A T f is corestrictionCochainThree
A T f. -/
@[simp]
theorem coe_corestrictionCocyclesThree (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex]
    (f : cocycles₃ (Rep.res (Subgroup.subtype H) A)) :
    (corestrictionCocyclesThree A T f : G × G × G → A) =
      corestrictionCochainThree A T f :=
  rfl

/-- The class of a transferred three-cocycle.

Transfer an H-three-cocycle and project the resulting G-three-cocycle to H³(G,A). -/
noncomputable def corestrictionCocycleThreeClass (A : Rep k G)
    (T : H.RightTransversal) [H.FiniteIndex] :
    cocycles₃ (Rep.res (Subgroup.subtype H) A) →ₗ[k] H3 A :=
  (H3π A).hom.comp (corestrictionCocyclesThree A T)

/-- Three-coboundaries vanish under the transferred class map.

The kernel of Z³(H,A|H) → H³(H,A|H) is contained in the kernel of the transferred class map to
H³(G,A). -/
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

/-- The degree-three cohomology transfer of a right transversal.

The ternary transfer descends through the source coboundary quotient to a k-linear map
H³(H,A|H) → H³(G,A). -/
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

/-- Degree-three transfer on a ternary cocycle class.

Applying the chosen H³ transfer to the class of an H-three-cocycle gives the class of its
transferred G-three-cocycle. -/
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
