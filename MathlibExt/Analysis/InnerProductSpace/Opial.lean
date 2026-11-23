/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Opial's property in Hilbert spaces

A sequence `u : ℕ → E` in a Hilbert space converges **weakly** to `x` when
every continuous linear functional converges on it:
`f (u n) → f x` for all `f : E →L[𝕜] 𝕜`. Opial's property (Z. Opial,
"Weak convergence of the sequence of successive approximations for
nonexpansive mappings", Bull. Amer. Math. Soc. 73 (1967), 591--597) says
that a weakly convergent sequence is asymptotically strictly closer to its
weak limit than to any other point: if `u n ⇀ x` and `y ≠ x`, then

  `liminf ‖u n - x‖ < liminf ‖u n - y‖`.

This is a companion to the Hilbert-space material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/` (Riesz representation,
orthogonal projection, spectral theory); it is not one of the 72 targets,
and it is not in pinned Mathlib or base MathlibExt. The proof goes through
the squared-norm identity

  `‖u n - y‖² = ‖u n - x‖² + ‖x - y‖² + 2 * re ⟪u n - x, x - y⟫`,

whose cross term tends to `0` by weak convergence (via the Fréchet–Riesz
representation), together with boundedness of weakly convergent sequences
(via the Banach–Steinhaus theorem applied to the evaluation maps on the
dual). The norm form follows from the squared form by monotonicity and
continuity of `Real.sqrt`.

Main results:

* `bddAbove_norm_of_weakly_tendsto`: a weakly convergent sequence is
  norm-bounded;
* `tendsto_re_inner_sub_of_weakly_tendsto`: the cross term in the
  squared-norm identity tends to `0`;
* `opial_liminf_sq`: Opial's property for squared norms;
* `opial_liminf`: Opial's property for norms.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.Opial

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A weakly convergent sequence is norm-bounded (Banach–Steinhaus applied
to the evaluation maps on the dual space). -/
theorem bddAbove_norm_of_weakly_tendsto (u : ℕ → E) (x : E)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    BddAbove (Set.range fun n => ‖u n‖) := by
  classical
  let g : ℕ → (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
    fun n => NormedSpace.inclusionInDoubleDual 𝕜 E (u n)
  have hpt : ∀ f : E →L[𝕜] 𝕜, ∃ C, ∀ n, ‖g n f‖ ≤ C := by
    intro f
    have hconv : Tendsto (fun n => ‖g n f‖) atTop (𝓝 ‖f x‖) := by
      have h1 : Tendsto (fun n => g n f) atTop (𝓝 (f x)) := by
        have h := hw f
        refine h.congr (fun n => ?_)
        simp [g, NormedSpace.dual_def]
      exact h1.norm
    obtain ⟨C, hC⟩ := hconv.bddAbove_range
    exact ⟨C, fun n => hC ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ :=
    banach_steinhaus (E := E →L[𝕜] 𝕜) (F := 𝕜) (𝕜 := 𝕜) (𝕜₂ := 𝕜)
      (σ₁₂ := RingHom.id 𝕜) (g := g) hpt
  refine ⟨C', ?_⟩
  rintro y ⟨n, rfl⟩
  show ‖u n‖ ≤ C'
  have hn : ‖g n‖ = ‖u n‖ := by
    show ‖NormedSpace.inclusionInDoubleDual 𝕜 E (u n)‖ = ‖u n‖
    exact (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).norm_map (u n)
  rw [← hn]
  exact hC' n

/-- The cross term in the squared-norm identity tends to `0` under weak
convergence, via the Fréchet–Riesz representation of the functional
`z ↦ ⟪x - y, z⟫`. -/
theorem tendsto_re_inner_sub_of_weakly_tendsto (u : ℕ → E) (x : E)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (u n)) atTop (𝓝 (f x)))
    (y : E) :
    Tendsto (fun n => RCLike.re ⟪u n - x, x - y⟫_𝕜) atTop (𝓝 0) := by
  have hf := hw ((InnerProductSpace.toDual 𝕜 E (x - y) : E →L[𝕜] 𝕜))
  rw [InnerProductSpace.toDual_apply_apply] at hf
  have h2 : Tendsto (fun n => ⟪x - y, u n⟫_𝕜 - ⟪x - y, x⟫_𝕜)
      atTop (𝓝 (⟪x - y, x⟫_𝕜 - ⟪x - y, x⟫_𝕜)) :=
    hf.sub tendsto_const_nhds
  rw [sub_self] at h2
  have h3 : Tendsto (fun n => ⟪x - y, u n - x⟫_𝕜) atTop (𝓝 0) :=
    h2.congr (fun n => by rw [inner_sub_right])
  have h4 : Tendsto (fun n => RCLike.re ⟪x - y, u n - x⟫_𝕜) atTop (𝓝 0) := by
    have hc := (RCLike.continuous_re (K := 𝕜)).tendsto (0 : 𝕜)
    rw [map_zero] at hc
    exact hc.comp h3
  exact h4.congr (fun n => by rw [inner_re_symm])

/-- Abstract `liminf` lemma: if `b n = a n + d + c n` with `c n → 0`,
`a n ≥ 0`, and `a` bounded above, then `liminf b = liminf a + d`. -/
private lemma liminf_eq_of_add_const_add_tendsto_zero (a b c : ℕ → ℝ) (d : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hbdd : BddAbove (Set.range a))
    (hb : ∀ n, b n = a n + d + c n) (hc : Tendsto c atTop (𝓝 0)) :
    liminf b atTop = liminf a atTop + d := by
  have hcl : liminf c atTop = 0 := hc.liminf_eq
  have hcs : limsup c atTop = 0 := hc.limsup_eq
  have ha_above : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) atTop a := by
    obtain ⟨C, hC⟩ := hbdd
    exact isBoundedUnder_of ⟨C, fun n => hC ⟨n, rfl⟩⟩
  have ha_below : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) atTop a :=
    isBoundedUnder_of ⟨0, ha⟩
  have ha_cobelow : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop a :=
    ha_above.isCoboundedUnder_ge
  have h1 : liminf (fun n => a n + d) atTop = liminf a atTop + d :=
    liminf_add_const atTop a d ha_cobelow ha_below
  have hb2 : b = (fun n => a n + d) + c := by
    funext n
    simp only [Pi.add_apply, hb]
  rw [hb2]
  have hu_bdd : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) atTop (fun n => a n + d) := by
    obtain ⟨C, hC⟩ := hbdd
    exact isBoundedUnder_of ⟨C + d, fun n => by have := hC ⟨n, rfl⟩; linarith⟩
  have hu_below : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) atTop (fun n => a n + d) :=
    isBoundedUnder_of ⟨d, fun n => by have := ha n; linarith⟩
  have hc_below : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) atTop c :=
    isBoundedUnder_of_eventually_ge
      ((hc.eventually_const_lt (show (-1 : ℝ) < 0 by norm_num)).mono fun _ hn => hn.le)
  have hc_above : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) atTop c :=
    isBoundedUnder_of_eventually_le
      ((hc.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)).mono fun _ hn => hn.le)
  have hc_cobelow : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop c :=
    hc_above.isCoboundedUnder_ge
  have hu_cobelow : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop (fun n => a n + d) :=
    hu_bdd.isCoboundedUnder_ge
  have hle : liminf (fun n => a n + d) atTop + liminf c atTop ≤
      liminf ((fun n => a n + d) + c) atTop :=
    le_liminf_add hu_below hu_bdd hc_below hc_cobelow
  have hge : liminf (c + (fun n => a n + d)) atTop ≤
      limsup c atTop + liminf (fun n => a n + d) atTop :=
    liminf_add_le hc_below hc_above hu_below hu_cobelow
  have hcomm : (fun n => a n + d) + c = c + (fun n => a n + d) := by
    funext n
    simp [Pi.add_apply, add_comm]
  rw [hcl, add_zero] at hle
  rw [← hcomm, hcs, zero_add] at hge
  rw [← h1]
  exact le_antisymm hge hle

/-- **Opial's property, squared-norm form**: if `u n ⇀ x` weakly and
`y ≠ x`, then `liminf ‖u n - x‖² < liminf ‖u n - y‖²`. -/
theorem opial_liminf_sq (u : ℕ → E) (x y : E) (hxy : x ≠ y)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    liminf (fun n => ‖u n - x‖ ^ 2) atTop < liminf (fun n => ‖u n - y‖ ^ 2) atTop := by
  have ha : ∀ n, 0 ≤ ‖u n - x‖ ^ 2 := fun n => sq_nonneg _
  have hbdd : BddAbove (Set.range fun n => ‖u n - x‖ ^ 2) := by
    obtain ⟨C, hC⟩ := bddAbove_norm_of_weakly_tendsto u x hw
    refine ⟨(C + ‖x‖) ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖u n - x‖ ≤ C + ‖x‖ :=
      le_trans (norm_sub_le _ _) (by have := hC ⟨n, rfl⟩; linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hb : ∀ n, ‖u n - y‖ ^ 2 =
      ‖u n - x‖ ^ 2 + ‖x - y‖ ^ 2 + (2 * RCLike.re ⟪u n - x, x - y⟫_𝕜) := by
    intro n
    have hsplit : u n - y = (u n - x) + (x - y) := by abel
    conv_lhs => rw [hsplit, norm_add_sq (𝕜 := 𝕜)]
    ring
  have hc : Tendsto (fun n => 2 * RCLike.re ⟪u n - x, x - y⟫_𝕜) atTop (𝓝 0) := by
    have hcross := tendsto_re_inner_sub_of_weakly_tendsto u x hw y
    have h2 := hcross.const_mul (2 : ℝ)
    rw [mul_zero] at h2
    exact h2
  have hlim := liminf_eq_of_add_const_add_tendsto_zero
    (fun n => ‖u n - x‖ ^ 2) (fun n => ‖u n - y‖ ^ 2)
    (fun n => 2 * RCLike.re ⟪u n - x, x - y⟫_𝕜) (‖x - y‖ ^ 2) ha hbdd hb hc
  have hdpos : 0 < ‖x - y‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
  rw [hlim]
  exact lt_add_of_pos_right _ hdpos

/-- **Opial's property**: if `u n ⇀ x` weakly and `y ≠ x`, then
`liminf ‖u n - x‖ < liminf ‖u n - y‖`. -/
theorem opial_liminf (u : ℕ → E) (x y : E) (hxy : x ≠ y)
    (hw : ∀ f : E →L[𝕜] 𝕜, Tendsto (fun n => f (u n)) atTop (𝓝 (f x))) :
    liminf (fun n => ‖u n - x‖) atTop < liminf (fun n => ‖u n - y‖) atTop := by
  have hsq := opial_liminf_sq u x y hxy hw
  have hbound : ∀ z : E, BddAbove (Set.range fun n => ‖u n - z‖ ^ 2) := by
    intro z
    obtain ⟨C, hC⟩ := bddAbove_norm_of_weakly_tendsto u x hw
    refine ⟨(C + ‖z‖) ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖u n - z‖ ≤ C + ‖z‖ :=
      le_trans (norm_sub_le _ _) (by have := hC ⟨n, rfl⟩; linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hroot : ∀ z : E,
      Real.sqrt (liminf (fun n => ‖u n - z‖ ^ 2) atTop) =
        liminf (fun n => ‖u n - z‖) atTop := by
    intro z
    obtain ⟨M, hM⟩ := hbound z
    have hbdd' : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) atTop
        (fun n => ‖u n - z‖ ^ 2) :=
      isBoundedUnder_of ⟨M, fun n => hM ⟨n, rfl⟩⟩
    have hcob : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop
        (fun n => ‖u n - z‖ ^ 2) :=
      hbdd'.isCoboundedUnder_ge
    have hbelo : IsBoundedUnder (fun x1 x2 => x1 ≥ x2) atTop
        (fun n => ‖u n - z‖ ^ 2) :=
      isBoundedUnder_of ⟨0, fun n => sq_nonneg _⟩
    have hmap := Real.sqrt_monotone.map_liminf_of_continuousAt
      (fun n => ‖u n - z‖ ^ 2) Real.continuous_sqrt.continuousAt hcob hbelo
    rw [hmap]
    exact Filter.liminf_congr (Filter.Eventually.of_forall fun n => by
      rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)])
  have hsq_nonneg : 0 ≤ liminf (fun n => ‖u n - x‖ ^ 2) atTop := by
    obtain ⟨M, hM⟩ := hbound x
    have hbdd' : IsBoundedUnder (fun x1 x2 => x1 ≤ x2) atTop
        (fun n => ‖u n - x‖ ^ 2) :=
      isBoundedUnder_of ⟨M, fun n => hM ⟨n, rfl⟩⟩
    have hcob : IsCoboundedUnder (fun x1 x2 => x1 ≥ x2) atTop
        (fun n => ‖u n - x‖ ^ 2) :=
      hbdd'.isCoboundedUnder_ge
    exact le_liminf_of_le hcob (Filter.Eventually.of_forall fun n => sq_nonneg _)
  rw [← hroot x, ← hroot y]
  exact Real.sqrt_lt_sqrt hsq_nonneg hsq

end MathlibExt.Analysis.InnerProductSpace.Opial
