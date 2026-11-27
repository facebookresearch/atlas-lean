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

public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakOrder
public import MathlibExt.Analysis.CStarAlgebra.Weight
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.ClusterPt

/-!
# Bounded suprema of directed positive operator sets

Let `M ⊆ B(H)` be a concrete von Neumann algebra. A nonempty directed set `S` of positive
elements with `‖a‖≤C` for all `a∈S` has a positive least upper bound `s ∈ M` satisfying `‖s‖≤C`.

The construction returns this supremum with its order and norm properties. The norm bound is any
real `C` satisfying the premise; no supremum element is supplied by the caller.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set CStarAlgebra.ScalarWeight
open scoped Topology

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive supremum with its given operator-norm bound.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `S ⊆ M₊` be nonempty and
directed in the spectral order, and `C : ℝ` satisfy `‖a‖≤C` for all `a∈S`.
`boundedPositiveSupremum M S C` returns `s∈M₊` that is the least upper bound of `S` and
satisfies `‖s‖≤C`. -/
def boundedPositiveSupremum (M : VonNeumannAlgebra H) (S : Set (PositiveElement M))
    (hne : S.Nonempty)
    (hdir : DirectedOn (fun p q : PositiveElement M =>
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (p : M) (q : M)) S)
    (C : ℝ) (hbound : ∀ p ∈ S, ‖(p : M)‖ ≤ C) :
    {s : PositiveElement M //
      @IsLUB M (CStarAlgebra.spectralOrder M).toLE
        ((fun p : PositiveElement M => (p : M)) '' S) (s : M) ∧ ‖(s : M)‖ ≤ C} := by
  classical
  letI : PartialOrder (Ultraweak M) := ultraweakPartialOrder M
  let : OrderClosedTopology (Ultraweak M) := ultraweakOrderClosedTopology M
  let J := {p : PositiveElement M // p ∈ S}
  let preJ : Preorder J := @Preorder.lift J M (CStarAlgebra.spectralOrder M).toPreorder
    (fun j => (j.val : M))
  letI : Preorder J := preJ
  letI : LE J := preJ.toLE
  letI : Nonempty J := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨⟨p, hp⟩⟩
  let : IsDirectedOrder J :=
    ⟨fun i j => by
      obtain ⟨p, hp, hip, hjp⟩ := hdir i.val i.property j.val j.property
      exact ⟨⟨p, hp⟩, hip, hjp⟩⟩
  let f : J → Ultraweak M := fun j => (ultraweakLinearEquiv M).symm (j.val : M)
  have hmono : Monotone f := by
    intro i j hij
    change @LE.le M (CStarAlgebra.spectralOrder M).toLE (i.val : M) (j.val : M) at hij
    apply (ultraweak_le_iff M (f i) (f j)).mpr
    simpa only [f, LinearEquiv.apply_symm_apply] using hij
  let K : Set (Ultraweak M) := Ici (0 : Ultraweak M) ∩
    {x | ‖ultraweakLinearEquiv M x‖ ≤ C}
  have hcompact : IsCompact K := (ultraweakClosedBall_isCompact M C).inter_left isClosed_Ici
  have hmem : ∀ᶠ j in atTop, f j ∈ K := Eventually.of_forall fun j => by
    constructor
    · apply (ultraweak_le_iff M 0 (f j)).mpr
      simpa only [f, map_zero, LinearEquiv.apply_symm_apply] using j.val.property
    · simpa only [f, Set.mem_ofPred_eq, LinearEquiv.apply_symm_apply] using hbound j.val j.property
  have hexists : ∃ s : PositiveElement M,
      @IsLUB M (CStarAlgebra.spectralOrder M).toLE
        ((fun p : PositiveElement M => (p : M)) '' S) (s : M) ∧ ‖(s : M)‖ ≤ C := by
    obtain ⟨y, hy, hycluster⟩ := hcompact.exists_mapClusterPt (f := atTop) (u := f)
      (tendsto_principal.mpr hmem)
    have hcluster : ClusterPt y (Filter.map f atTop) := hycluster
    have hpositive : @LE.le M (CStarAlgebra.spectralOrder M).toLE 0
        (ultraweakLinearEquiv M y) := by
      simpa only [map_zero] using (ultraweak_le_iff M 0 y).mp hy.1
    let s : PositiveElement M := ⟨ultraweakLinearEquiv M y, hpositive⟩
    refine ⟨s, ?_, hy.2⟩
    constructor
    · rintro _ ⟨p, hp, rfl⟩
      let j : J := ⟨p, hp⟩
      have hlower : Ici (f j) ∈ Filter.map f atTop :=
        Filter.mem_map.mpr ((eventually_ge_atTop j).mono fun k hjk => hmono hjk)
      have hj : f j ≤ y := isClosed_Ici.mem_of_nhdsWithin_neBot
        (hcluster.mono (le_principal_iff.mpr hlower))
      simpa only [f, j, s, LinearEquiv.apply_symm_apply] using (ultraweak_le_iff M (f j) y).mp hj
    · intro q hq
      have hupper : Iic ((ultraweakLinearEquiv M).symm q) ∈ Filter.map f atTop :=
        Filter.mem_map.mpr (Eventually.of_forall fun j => by
          apply (ultraweak_le_iff M (f j) ((ultraweakLinearEquiv M).symm q)).mpr
          simpa only [f, LinearEquiv.apply_symm_apply] using hq ⟨j.val, j.property, rfl⟩)
      have hyq : y ≤ (ultraweakLinearEquiv M).symm q := isClosed_Iic.mem_of_nhdsWithin_neBot
        (hcluster.mono (le_principal_iff.mpr hupper))
      simpa only [s, LinearEquiv.apply_symm_apply] using
        (ultraweak_le_iff M y ((ultraweakLinearEquiv M).symm q)).mp hyq
  exact ⟨Classical.choose hexists, Classical.choose_spec hexists⟩

/-- **Least-upper-bound property of the bounded positive supremum.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `S ⊆ M₊` be
nonempty and directed in the spectral order, and `C : ℝ` satisfy `‖a‖≤C` for all `a∈S`.
the positive element returned by `boundedPositiveSupremum M S C` is the least upper bound
of `S` in the operator spectral order. -/
theorem boundedPositiveSupremum_isLUB (M : VonNeumannAlgebra H) (S : Set (PositiveElement M))
    (hne : S.Nonempty)
    (hdir : DirectedOn (fun p q : PositiveElement M =>
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (p : M) (q : M)) S)
    (C : ℝ) (hbound : ∀ p ∈ S, ‖(p : M)‖ ≤ C) :
    @IsLUB M (CStarAlgebra.spectralOrder M).toLE
      ((fun p : PositiveElement M => (p : M)) '' S)
      (boundedPositiveSupremum M S hne hdir C hbound).val :=
  (boundedPositiveSupremum M S hne hdir C hbound).property.1

/-- **Norm estimate for the bounded positive supremum.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `S ⊆ M₊` be nonempty and directed
in the spectral order, and `C : ℝ` satisfy `‖a‖≤C` for all `a∈S`. the supremum
`s=boundedPositiveSupremum M S C` satisfies `‖s‖≤C`. -/
theorem boundedPositiveSupremum_norm_le (M : VonNeumannAlgebra H) (S : Set (PositiveElement M))
    (hne : S.Nonempty)
    (hdir : DirectedOn (fun p q : PositiveElement M =>
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (p : M) (q : M)) S)
    (C : ℝ) (hbound : ∀ p ∈ S, ‖(p : M)‖ ≤ C) :
    ‖((boundedPositiveSupremum M S hne hdir C hbound).val : M)‖ ≤ C :=
  (boundedPositiveSupremum M S hne hdir C hbound).property.2

end

end VonNeumannAlgebra
