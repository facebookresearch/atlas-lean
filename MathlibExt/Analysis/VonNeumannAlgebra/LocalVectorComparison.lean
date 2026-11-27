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

public import MathlibExt.Analysis.CStarAlgebra.Weight
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalFunctional
public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveSupremum
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveLUBLimit
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
public import Mathlib.Order.Zorn

/-!
# Nonzero positive interval with strict vector domination

Let `ψ` be a positive bounded functional and suppose a vector `ξ∈H` has `Re ψ(a)<Re ⟨ξ,aξ⟩` for
a positive `a∈M`. There is a nonzero positive `b≤a` such that `Re ψ(t)<Re ⟨ξ,tξ⟩` for every
nonzero positive `t≤b`.

The vector `ξ` is unchanged. This is a local strict comparison result without a normality
assumption on `ψ`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight Filter Set
open scoped Topology

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Nonzero positive subinterval of strict vector comparison.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a
positive bounded complex-linear functional for the spectral orders. if `a∈M₊` and `ξ∈H`
satisfy `Re ψ(a)<Re ⟨ξ,aξ⟩`, the construction returns `b∈M₊` with `b≤a`, `b≠0`, and `Re
ψ(t)<Re ⟨ξ,tξ⟩` for every nonzero positive `t≤b`. -/
def localVectorComparisonPositiveElement (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    (ψ : PositiveContinuousLinearMap ℂ M ℂ) → (a : PositiveElement M) → (ξ : H) →
      (ψ.toContinuousLinearMap (a : M)).re < (vectorFunctional M ξ ξ (a : M)).re →
      {b : PositiveElement M //
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) (a : M) ∧ (b : M) ≠ 0 ∧
        ∀ t : PositiveElement M, (t : M) ≠ 0 →
          @LE.le M (CStarAlgebra.spectralOrder M).toLE (t : M) (b : M) →
          (ψ.toContinuousLinearMap (t : M)).re < (vectorFunctional M ξ ξ (t : M)).re} := by
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : PartialOrder M := sourceOrder
  letI : Preorder M := sourceOrder.toPreorder
  letI : LE M := sourceOrder.toLE
  letI : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  letI : IsOrderedAddMonoid M := StarOrderedRing.toIsOrderedAddMonoid
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ a ξ hcompare
  let φ : StrongDual ℂ M := ψ.toContinuousLinearMap
  have horders (z w : ℂ) : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE z w ↔
      @LE.le ℂ Complex.partialOrder.toLE z w := by
    have hspectral : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE z w ↔
        ∃ d, d ∈ AddSubmonoid.closure (Set.range fun s : ℂ => star s * s) ∧ w = z + d := by
      let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      let : LE ℂ := (CStarAlgebra.spectralOrder ℂ).toLE
      let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
      exact StarOrderedRing.le_iff z w
    have hstandard : @LE.le ℂ Complex.partialOrder.toLE z w ↔
        ∃ d, d ∈ AddSubmonoid.closure (Set.range fun s : ℂ => star s * s) ∧ w = z + d := by
      let : PartialOrder ℂ := Complex.partialOrder
      let : LE ℂ := Complex.partialOrder.toLE
      let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
      exact StarOrderedRing.le_iff z w
    exact hspectral.trans hstandard.symm
  have hmono (x y : M) (hxy : @LE.le M (CStarAlgebra.spectralOrder M).toLE x y) :
      (φ x).re ≤ (φ y).re := by
    have hspectral : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE (φ x) (φ y) := ψ.monotone' hxy
    exact ((horders (φ x) (φ y)).mp hspectral).1
  let positiveOrder : PartialOrder (PositiveElement M) :=
    @PartialOrder.lift (PositiveElement M) M (CStarAlgebra.spectralOrder M)
      (fun p : PositiveElement M => (p : M)) Subtype.val_injective
  letI : PartialOrder (PositiveElement M) := positiveOrder
  letI : Preorder (PositiveElement M) := positiveOrder.toPreorder
  letI : LE (PositiveElement M) := positiveOrder.toLE
  have positive_le_iff (p q : PositiveElement M) :
      @LE.le (PositiveElement M) positiveOrder.toLE p q ↔
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (p : M) (q : M) := Iff.rfl
  let C : Set (PositiveElement M) :=
    {c | @LE.le M (CStarAlgebra.spectralOrder M).toLE (c : M) (a : M) ∧
      (vectorFunctional M ξ ξ (c : M)).re ≤ (φ (c : M)).re}
  let z : PositiveElement M := ⟨0, @le_refl M (CStarAlgebra.spectralOrder M).toPreorder 0⟩
  have hzC : z ∈ C := by
    change (0 : M) ≤ (a : M) ∧ (vectorFunctional M ξ ξ 0).re ≤ (φ 0).re
    exact ⟨a.property, by simp⟩
  have hchains (S : Set (PositiveElement M)) (hSC : S ⊆ C)
      (hchain : IsChain (fun p q => @LE.le (PositiveElement M) positiveOrder.toLE p q) S) :
      ∃ ub ∈ C, ∀ p ∈ S, @LE.le (PositiveElement M) positiveOrder.toLE p ub := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨z, hzC, by simp⟩
    have hdir : DirectedOn (fun p q : PositiveElement M =>
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (p : M) (q : M)) S := by
      intro p hp q hq
      rcases hchain.total hp hq with hpq | hqp
      · exact ⟨q, hq, (positive_le_iff p q).mp hpq,
          @le_refl M (CStarAlgebra.spectralOrder M).toPreorder (q : M)⟩
      · exact ⟨p, hp, @le_refl M (CStarAlgebra.spectralOrder M).toPreorder (p : M),
          (positive_le_iff q p).mp hqp⟩
    have hbound : ∀ p ∈ S, ‖(p : M)‖ ≤ ‖(a : M)‖ := by
      intro p hp
      exact CStarAlgebra.norm_le_norm_of_le_of_nonneg (hSC hp).1 p.property
    let ub : PositiveElement M :=
      (boundedPositiveSupremum M S hne hdir ‖(a : M)‖ hbound).val
    have hLUB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE
        ((fun p : PositiveElement M => (p : M)) '' S) (ub : M) :=
      boundedPositiveSupremum_isLUB M S hne hdir ‖(a : M)‖ hbound
    have hubA : @LE.le M (CStarAlgebra.spectralOrder M).toLE (ub : M) (a : M) := by
      apply hLUB.2
      rintro _ ⟨p, hp, rfl⟩
      exact (hSC hp).1
    let preS : Preorder S := @Preorder.lift S M (CStarAlgebra.spectralOrder M).toPreorder
      (fun p : S => (p.val : M))
    let : Preorder S := preS
    let : LE S := preS.toLE
    have index_le_iff (p q : S) : @LE.le S preS.toLE p q ↔
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (p.val : M) (q.val : M) := Iff.rfl
    obtain ⟨p₀, hp₀⟩ := hne
    let : Nonempty S := ⟨⟨p₀, hp₀⟩⟩
    let : @IsDirectedOrder S preS.toLE :=
      ⟨fun p q => by
        obtain ⟨r, hr, hpr, hqr⟩ := hdir p.val p.property q.val q.property
        exact ⟨⟨r, hr⟩, (index_le_iff p ⟨r, hr⟩).mpr hpr,
          (index_le_iff q ⟨r, hr⟩).mpr hqr⟩⟩
    have hmonoNet : @Monotone S M preS (CStarAlgebra.spectralOrder M).toPreorder
        (fun p : S => (p.val : M)) := by
      intro p q hpq
      exact (index_le_iff p q).mp hpq
    have hrange : Set.range (fun p : S => (p.val : M)) =
        ((fun p : PositiveElement M => (p : M)) '' S) := by
      ext x
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨p.val, p.property, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp⟩, rfl⟩
    have hnetLUB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE
        (Set.range fun p : S => (p.val : M)) (ub : M) := by
      rw [hrange]
      exact hLUB
    have hlimit := boundedPositiveIsLUB_tendsto_ultraweak M (fun p : S => (p.val : M)) (ub : M)
      hmonoNet (fun p => p.val.property) ⟨‖(a : M)‖, fun p => hbound p.val p.property⟩ hnetLUB
    let v : normalFunctionalSpace M :=
      ⟨vectorFunctional M ξ ξ, vectorFunctional_mem_normalFunctionalSpace M ξ ξ⟩
    have hcontinuous : Continuous fun x : Ultraweak M =>
        ((v : StrongDual ℂ M) (ultraweakLinearEquiv M x)).re :=
      Complex.continuous_re.comp (ultraweak_eval_continuous M v)
    have hvectorLimit : Tendsto (fun p : S => (vectorFunctional M ξ ξ (p.val : M)).re) atTop
        (𝓝 (vectorFunctional M ξ ξ (ub : M)).re) := by
      simpa only [v, Function.comp_def, LinearEquiv.apply_symm_apply] using
        hcontinuous.continuousAt.tendsto.comp hlimit
    have hupper : ∀ p : S, (vectorFunctional M ξ ξ (p.val : M)).re ≤ (φ (ub : M)).re := by
      intro p
      exact (hSC p.property).2.trans (hmono (p.val : M) (ub : M) (hLUB.1 ⟨p.val, p.property, rfl⟩))
    have hubCompare : (vectorFunctional M ξ ξ (ub : M)).re ≤ (φ (ub : M)).re :=
      le_of_tendsto' hvectorLimit hupper
    refine ⟨ub, ⟨hubA, hubCompare⟩, ?_⟩
    intro p hp
    exact (positive_le_iff p ub).mpr (hLUB.1 ⟨p, hp, rfl⟩)
  let maximalExists := @zorn_le₀ (PositiveElement M) positiveOrder.toPreorder C hchains
  let m : PositiveElement M := Classical.choose maximalExists
  have hm := Classical.choose_spec maximalExists
  let b : PositiveElement M := ⟨(a : M) - (m : M), sub_nonneg.mpr hm.1.1⟩
  have hbA : @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) (a : M) :=
    sub_le_self (a : M) m.property
  have hbNonzero : (b : M) ≠ 0 := by
    intro hbzero
    have ham : (a : M) = (m : M) := sub_eq_zero.mp hbzero
    have hstrict : (φ (a : M)).re < (vectorFunctional M ξ ξ (a : M)).re := hcompare
    rw [ham] at hstrict
    exact (not_lt_of_ge hm.1.2) hstrict
  have hbLocal (t : PositiveElement M) (htNonzero : (t : M) ≠ 0)
      (htb : @LE.le M (CStarAlgebra.spectralOrder M).toLE (t : M) (b : M)) :
      (φ (t : M)).re < (vectorFunctional M ξ ξ (t : M)).re := by
    by_contra hnot
    have htCompare : (vectorFunctional M ξ ξ (t : M)).re ≤ (φ (t : M)).re := le_of_not_gt hnot
    have hd0 : @LE.le M (CStarAlgebra.spectralOrder M).toLE 0 ((m : M) + (t : M)) :=
      add_nonneg m.property t.property
    let d : PositiveElement M := ⟨(m : M) + (t : M), hd0⟩
    have hdA : @LE.le M (CStarAlgebra.spectralOrder M).toLE (d : M) (a : M) := by
      have h : @LE.le M (CStarAlgebra.spectralOrder M).toLE
          ((t : M) + (m : M)) (((a : M) - (m : M)) + (m : M)) :=
        add_le_add_left htb (m : M)
      have hrhs : ((a : M) - (m : M)) + (m : M) = (a : M) := sub_add_cancel _ _
      rw [hrhs] at h
      calc
        (m : M) + (t : M) = (t : M) + (m : M) := add_comm _ _
        _ ≤ (a : M) := h
    have hdCompare : (vectorFunctional M ξ ξ (d : M)).re ≤ (φ (d : M)).re := by
      change (vectorFunctional M ξ ξ ((m : M) + (t : M))).re ≤ (φ ((m : M) + (t : M))).re
      simp only [map_add, Complex.add_re]
      exact add_le_add hm.1.2 htCompare
    have hmd : @LE.le (PositiveElement M) positiveOrder.toLE m d := by
      apply (positive_le_iff m d).mpr
      exact le_add_of_nonneg_right t.property
    have hdm : @LE.le (PositiveElement M) positiveOrder.toLE d m := by
      apply hm.2
      · exact ⟨hdA, hdCompare⟩
      · exact hmd
    have hdeq : d = m := @le_antisymm (PositiveElement M) positiveOrder d m hdm hmd
    have hsum : (m : M) + (t : M) = (m : M) := congrArg (fun p : PositiveElement M => (p : M)) hdeq
    have htzero : (t : M) = 0 := by
      have h : (m : M) + (t : M) = (m : M) + 0 := by simpa only [add_zero] using hsum
      exact add_left_cancel h
    exact htNonzero htzero
  exact ⟨b, hbA, hbNonzero, hbLocal⟩

end

end VonNeumannAlgebra
