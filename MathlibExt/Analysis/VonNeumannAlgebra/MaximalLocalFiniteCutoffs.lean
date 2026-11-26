/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalProjectionFamily
public import MathlibExt.Algebra.Star.StarProjection.FiniteSum
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite projection cutoffs of a maximal local family

For a positive bounded functional `ψ`, let `S` be the constructed maximal orthogonal family of
locally vector-dominated projections. For finite `t⊆S`, its cutoff is `P_t=Σ_p∈t p`.

Each cutoff is a positive star projection with `P_t≤I` and `‖P_t‖≤1`. Inclusion of finite
subsets makes `P_t` monotone, and the cutoff range is directed and nonempty, containing `P_∅=0`.
No nonempty-family assumption is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped BigOperators

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive finite cutoffs with projection and order bounds.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. Let `S` be the
constructed maximal set of pairwise orthogonal nonzero star projections, each admitting a
vector `ξ` with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`.
`maximalLocalPositiveFiniteCutoffs M ψ` returns `t ↦ P_t`, each a star projection
satisfying `0≤P_t≤I`, `‖P_t‖≤1`; the map is monotone and its range is nonempty and
directed. -/
def maximalLocalPositiveFiniteCutoffs (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) →
      let S := maximalLocalProjectionFamily M ψ
      {P : Finset S.val → PositiveElement M //
        (∀ t, (P t : M) = ∑ p ∈ t, (p.val : M)) ∧
        (∀ t, IsStarProjection (P t : M)) ∧
        (∀ t, @LE.le M (CStarAlgebra.spectralOrder M).toLE (P t : M) 1) ∧
        (∀ t, ‖(P t : M)‖ ≤ 1) ∧
        (@Monotone (Finset S.val) M inferInstance (CStarAlgebra.spectralOrder M).toPreorder
          (fun t => (P t : M))) ∧
        (Set.range P).Nonempty ∧
        DirectedOn (fun a b : PositiveElement M =>
          @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) (b : M)) (Set.range P)} := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder M := sourceOrder
  letI : Preorder M := sourceOrder.toPreorder
  letI : LE M := sourceOrder.toLE
  letI : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  letI : IsOrderedAddMonoid M := StarOrderedRing.toIsOrderedAddMonoid
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  let S := maximalLocalProjectionFamily M ψ
  let sum (t : Finset S.val) : M := ∑ p ∈ t, (p.val : M)
  have hsum (t : Finset S.val) : IsStarProjection (sum t) := by
    apply IsStarProjection.finset_sum_of_pairwise_mul_eq_zero
    · intro p _hp
      exact (S.property.1 p.val p.property).1
    · intro p _hp q _hq hpq
      exact S.property.2.1 p.property q.property
        (fun h => hpq (Subtype.ext h))
  let P (t : Finset S.val) : PositiveElement M := ⟨sum t, (hsum t).nonneg⟩
  have hone (t : Finset S.val) : @LE.le M (CStarAlgebra.spectralOrder M).toLE (P t : M) 1 :=
    (hsum t).le_one
  have hnorm (t : Finset S.val) : ‖(P t : M)‖ ≤ 1 := by
    have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg (hone t) (P t).property
    have hunit : ‖(1 : M)‖ ≤ 1 := by
      change ‖ContinuousLinearMap.id ℂ H‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le
    exact h.trans hunit
  have hmono : @Monotone (Finset S.val) M inferInstance
      (CStarAlgebra.spectralOrder M).toPreorder (fun t => (P t : M)) := by
    intro t v htv
    change sum t ≤ sum v
    apply Finset.sum_le_sum_of_subset_of_nonneg htv
    intro p _hp _hpt
    exact (S.property.1 p.val p.property).1.nonneg
  refine ⟨P, (fun _ => rfl), hsum, hone, hnorm, hmono, ?_, ?_⟩
  · exact ⟨P ∅, Set.mem_range_self ∅⟩
  · intro a ha b hb
    obtain ⟨t, rfl⟩ := ha
    obtain ⟨v, rfl⟩ := hb
    refine ⟨P (t ∪ v), Set.mem_range_self (t ∪ v), ?_, ?_⟩
    · exact hmono Finset.subset_union_left
    · exact hmono Finset.subset_union_right

/-- **Finite sum formula for a maximal-family cutoff.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. for finite `t⊆S`, the
element of `M` underlying its cutoff is `P_t=Σ_p∈t p`. -/
theorem maximalLocalPositiveFiniteCutoffs_value (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M) = ∑ p ∈ t, (p.val : M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.1 t

/-- **Star projection property of each finite cutoff.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. for every finite
`t⊆S`, `P_t²=P_t` and `P_t*=P_t`. -/
theorem maximalLocalPositiveFiniteCutoffs_isStarProjection (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      IsStarProjection ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.1 t

/-- **Finite cutoff bounded by the identity.** Let `H` be a complete complex Hilbert space and
`M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. for every finite
`t⊆S`, `P_t≤I_M` in the spectral order. -/
theorem maximalLocalPositiveFiniteCutoffs_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      @LE.le M (CStarAlgebra.spectralOrder M).toLE
        ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M) 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.1 t

/-- **Operator-norm bound of a finite cutoff.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. for every finite
`t⊆S`, `‖P_t‖≤1`, including the zero cutoff and zero algebra. -/
theorem maximalLocalPositiveFiniteCutoffs_norm_le_one (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ)
      (t : Finset (maximalLocalProjectionFamily M ψ).val),
      ‖((maximalLocalPositiveFiniteCutoffs M ψ).val t : M)‖ ≤ 1 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ t
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.1 t

/-- **Monotonicity of finite cutoff projections.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. if finite subsets
satisfy `t⊆u⊆S`, then `P_t≤P_u`. -/
theorem maximalLocalPositiveFiniteCutoffs_monotone (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      @Monotone (Finset (maximalLocalProjectionFamily M ψ).val) M inferInstance
        (CStarAlgebra.spectralOrder M).toPreorder
        (fun t => ((maximalLocalPositiveFiniteCutoffs M ψ).val t : M)) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.2.1

/-- **Nonempty finite-cutoff range including the empty cutoff.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `S` be the constructed
maximal set of pairwise orthogonal nonzero star projections, each admitting a vector `ξ`
with `Re ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. the cutoff
range `{P_t : t finite in S}` is nonempty, since it contains `P_∅=0`. -/
theorem maximalLocalPositiveFiniteCutoffs_range_nonempty (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      (Set.range (maximalLocalPositiveFiniteCutoffs M ψ).val).Nonempty := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.2.2.1

/-- **Directed order of the finite-cutoff range.** Let `H` be a complete complex Hilbert space
and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive bounded
complex-linear functional for the spectral orders. Let `S` be the constructed maximal set
of pairwise orthogonal nonzero star projections, each admitting a vector `ξ` with `Re
ψ(b)≤Re ⟨ξ,bξ⟩` for `0≤b≤p`. For finite `t ⊆ S`, put `P_t=Σ_p∈t p`. the positive cutoff
range is directed in the spectral order; `P_(t∪u)` is an upper bound for `P_t,P_u`. -/
theorem maximalLocalPositiveFiniteCutoffs_directedOn (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      DirectedOn (fun a b : PositiveElement M =>
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) (b : M))
        (Set.range (maximalLocalPositiveFiniteCutoffs M ψ).val) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ
  exact (maximalLocalPositiveFiniteCutoffs M ψ).property.2.2.2.2.2.2

end

end VonNeumannAlgebra
