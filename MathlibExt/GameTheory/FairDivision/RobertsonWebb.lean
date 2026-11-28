/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.CDF

/-!
# Robertson–Webb valuation queries on the unit interval

Jack Robertson and William Webb, *Cake-Cutting Algorithms: Be Fair If You Can*,
A K Peters, 1998, is the original reference. For interval queries and the leftmost
cut convention, see Caragiannis, Gkatzelis, Psomas and Schoepflin,
[*Beyond Cake Cutting: Allocating Homogeneous Divisible Goods*](https://arxiv.org/abs/2201.04662v1),
§1. For piecewise-constant valuations, see Aziz and Ye,
[*Cake Cutting Algorithms for Piecewise Constant and Piecewise Uniform Valuations*](https://arxiv.org/abs/1307.2908v2),
§2.2. The oracle here is a mathematical function, not an exact-arithmetic implementation.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace MathlibExt.GameTheory.FairDivision.RobertsonWebb

/-- A probability valuation on `[0, 1]`, realized as a measure on `ℝ` with null singletons. -/
structure RWValuation where
  /-- The valuation measure on the real line. -/
  measure : Measure ℝ
  probability : IsProbabilityMeasure measure
  supported : measure (Icc (0 : ℝ) 1)ᶜ = 0
  nullSingleton : NullSingletonClass measure

/-- Value of `(x, y]`. For ordered endpoints in the cake this equals the value of `[x, y]`
because `{x}` is null. Reversed endpoints give zero. -/
noncomputable def RWValuation.eval (V : RWValuation) (x y : ℝ) : ℝ :=
  V.measure.real (Ioc x y)

/-- **Least cut point.** For every start `x ∈ [0, 1]` and every target
`0 ≤ α ≤ V.eval x 1`, the set of endpoints `z ∈ [x, 1]` with `V.eval x z = α`
has a unique least member. Other endpoints can attain the same target; only
the least one is unique. -/
theorem RWValuation.existsUnique_isLeast_cut (V : RWValuation) {x α : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hα : α ∈ Icc (0 : ℝ) (V.eval x 1)) :
    ∃! y : ℝ, IsLeast {z ∈ Icc x 1 | V.eval x z = α} y := by
  have := V.probability
  have := V.nullSingleton
  set F := ⇑(ProbabilityTheory.cdf V.measure)
  have hmono : Monotone F := (ProbabilityTheory.cdf V.measure).mono
  have hcont : Continuous F := by
    refine continuous_iff_continuousAt.mpr fun z => ?_
    have hsing : V.measure {z} = 0 := NullSingletonClass.measure_singleton z
    have hmeas : (ProbabilityTheory.cdf V.measure).measure {z}
        = ENNReal.ofReal (F z - Function.leftLim F z) :=
      StieltjesFunction.measure_singleton _ z
    rw [ProbabilityTheory.measure_cdf, hsing] at hmeas
    have hle : F z - Function.leftLim F z ≤ 0 := ENNReal.ofReal_eq_zero.mp hmeas.symm
    have hge : Function.leftLim F z ≤ F z := hmono.leftLim_le le_rfl
    have hleftLim : Function.leftLim F z = F z := by linarith
    have hleft : ContinuousWithinAt F (Iio z) z :=
      (hmono.continuousWithinAt_Iio_iff_leftLim_eq).mpr hleftLim
    have hright : ContinuousWithinAt F (Ici z) z :=
      (ProbabilityTheory.cdf V.measure).right_continuous z
    exact continuousAt_iff_continuous_left'_right'.mpr
      ⟨hleft, continuousWithinAt_Ioi_iff_Ici.mpr hright⟩
  have hx1 : x ≤ 1 := hx.2
  set g : ℝ → ℝ := fun z => F z - F x
  have hgconst : Continuous (fun _ : ℝ => F x) := continuous_const
  have hgcont : Continuous g := hcont.sub hgconst
  have heval : ∀ z ∈ Icc x 1, V.eval x z = g z := by
    intro z hz
    have hIoc : (ProbabilityTheory.cdf V.measure).measure (Ioc x z)
        = ENNReal.ofReal (F z - F x) :=
      StieltjesFunction.measure_Ioc _ x z
    rw [ProbabilityTheory.measure_cdf] at hIoc
    change (V.measure (Ioc x z)).toReal = F z - F x
    rw [hIoc]
    apply ENNReal.toReal_ofReal
    have hxz : F x ≤ F z := hmono hz.1
    linarith
  have hgx : g x = 0 := sub_self _
  have h1mem : (1 : ℝ) ∈ Icc x 1 := ⟨hx1, le_rfl⟩
  have hg1 : g 1 = V.eval x 1 := (heval 1 h1mem).symm
  have hmem : α ∈ g '' Icc x 1 := by
    have hsub := intermediate_value_Icc hx1 hgcont.continuousOn
    rw [hgx, hg1] at hsub
    exact hsub hα
  obtain ⟨y, hy_mem, hy_eq⟩ := hmem
  have hy_eval : V.eval x y = α := by
    rw [heval y hy_mem]
    exact hy_eq
  have hS_eq : {z ∈ Icc x 1 | V.eval x z = α} = Icc x 1 ∩ g ⁻¹' {α} := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hz, he⟩
      exact ⟨hz, by rw [← heval z hz]; exact he⟩
    · rintro ⟨hz, he⟩
      exact ⟨hz, by rw [heval z hz]; exact he⟩
  have hcompact : IsCompact {z ∈ Icc x 1 | V.eval x z = α} := by
    rw [hS_eq]
    exact isCompact_Icc.inter_right (IsClosed.preimage hgcont isClosed_singleton)
  have hnonempty : {z ∈ Icc x 1 | V.eval x z = α}.Nonempty := ⟨y, hy_mem, hy_eval⟩
  obtain ⟨y0, hy0⟩ := hcompact.exists_isLeast hnonempty
  exact ⟨y0, hy0, fun y' hy' => hy'.unique hy0⟩

/-- The Robertson–Webb cut response: the leftmost endpoint in `[x, 1]` attaining
the target `α`, for a start `x ∈ [0, 1]` and a target `0 ≤ α ≤ V.eval x 1`. -/
noncomputable def RWValuation.cut (V : RWValuation) (x α : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) (hα : α ∈ Icc (0 : ℝ) (V.eval x 1)) : ℝ :=
  Classical.choose (V.existsUnique_isLeast_cut hx hα).exists

/-- The cut response attains the target and is leftmost among endpoints in `[x, 1]`
that do so. -/
theorem RWValuation.cut_spec (V : RWValuation) (x α : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) (hα : α ∈ Icc (0 : ℝ) (V.eval x 1)) :
    IsLeast {z ∈ Icc x 1 | V.eval x z = α} (V.cut x α hx hα) := by
  exact Classical.choose_spec (V.existsUnique_isLeast_cut hx hα).exists

/-- A finite collection of weighted intervals with nonnegative heights. -/
structure PiecewiseConstantDensity (n : ℕ) where
  /-- Left endpoints of the intervals. -/
  lo : Fin n → ℝ
  /-- Right endpoints of the intervals. -/
  hi : Fin n → ℝ
  /-- Nonnegative heights of the intervals. -/
  height : Fin n → ℝ≥0

/-- A finite sum of indicators of the intervals `(lo i, hi i]`, weighted by their
heights. Overlapping terms add. -/
noncomputable def PiecewiseConstantDensity.density {n : ℕ} (D : PiecewiseConstantDensity n)
    (t : ℝ) : ℝ :=
  ∑ i, (Ioc (D.lo i) (D.hi i)).indicator (fun _ => (D.height i : ℝ)) t

/-- Weight Lebesgue measure on the cake by the piecewise-constant density. -/
noncomputable def PiecewiseConstantDensity.measure {n : ℕ} (D : PiecewiseConstantDensity n) :
    Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (D.density t))

/-- A piecewise-constant density of mass one on `[0, 1]` gives a Robertson–Webb
valuation. -/
noncomputable def PiecewiseConstantDensity.toRWValuation {n : ℕ}
    (D : PiecewiseConstantDensity n)
    (hm : (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (D.density t)) = 1) : RWValuation where
  measure := D.measure
  probability := ⟨by simpa [PiecewiseConstantDensity.measure, withDensity_apply] using hm⟩
  supported := by
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply measurableSet_Icc.compl, compl_inter_self, measure_empty]
  nullSingleton := by
    unfold PiecewiseConstantDensity.measure
    infer_instance

/-- **Least cut point for a piecewise constant density.** For a density `D` of mass
one on `[0, 1]`, every start `x ∈ [0, 1]` and every target
`0 ≤ α ≤ (D.toRWValuation hm).eval x 1`, the set of endpoints `z ∈ [x, 1]`
attaining `α` has a unique least member. -/
theorem PiecewiseConstantDensity.existsUnique_isLeast_cut {n : ℕ}
    (D : PiecewiseConstantDensity n)
    (hm : (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (D.density t)) = 1)
    {x α : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hα : α ∈ Icc (0 : ℝ) ((D.toRWValuation hm).eval x 1)) :
    ∃! y : ℝ, IsLeast {z ∈ Icc x 1 | (D.toRWValuation hm).eval x z = α} y := by
  exact (D.toRWValuation hm).existsUnique_isLeast_cut hx hα

end MathlibExt.GameTheory.FairDivision.RobertsonWebb
