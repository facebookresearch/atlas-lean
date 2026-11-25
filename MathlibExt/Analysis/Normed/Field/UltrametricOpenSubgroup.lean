/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_
forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport.lean`
and
`P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_
forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

namespace IsLocallyConstant

/-- A compactly supported locally constant function on the product of a
nonarchimedean normed field with an arbitrary topological space, valued in
any type with a zero, is invariant in its first coordinate under a common
open subgroup of units.

Local constancy makes the function constant near each point of its compact
support, and compactness turns those pointwise neighbourhoods into one
neighbourhood of `1` in the units; the ultrametric then promotes that
neighbourhood to the open subgroup of units within distance `min r 1` of `1`.
The support hypothesis, via invariance under inverses, extends the identity
from the support to all points. No vanishing on the axes is needed. -/
public theorem exists_isOpen_subgroup_forall_apply_mul_eq_of_hasCompactSupport
    {F Y β : Type*} [NormedField F] [IsUltrametricDist F] [ContinuousMul F] [ContinuousInv₀ F] [TopologicalSpace Y] [Zero β]
    (Φ : F × Y → β) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ U : Subgroup Fˣ, IsOpen (U : Set Fˣ) ∧
      ∀ t ∈ U, ∀ b : F, ∀ z : Y, Φ (b * (t : F), z) = Φ (b, z) := by
  classical
  have hS : tsupport Φ = Function.support Φ := by
    rw [tsupport, closure_eq_iff_isClosed]
    have hsupp : Function.support Φ = {x | Φ x = 0}ᶜ := by ext x; simp [Function.mem_support]
    rw [hsupp]
    exact (hΦ.isOpen_fiber 0).isClosed_compl
  have hK : IsCompact (tsupport Φ) := hΦc
  have hV : ∀ᶠ t : Fˣ in nhds 1, ∀ q ∈ tsupport Φ,
      Φ (q.1 * (t : F), q.2) = Φ q := by
    refine hK.eventually_forall_of_forall_eventually fun q _ => ?_
    have hc : Continuous fun w : Fˣ × (F × Y) =>
        ((w.2.1 * (w.1 : F), w.2.2) : F × Y) :=
      ((continuous_fst.comp continuous_snd).mul (Units.continuous_val.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_snd)
    have ht : Filter.Tendsto (fun w : Fˣ × (F × Y) =>
        ((w.2.1 * (w.1 : F), w.2.2) : F × Y)) (nhds (1, q)) (nhds q) := by
      have hlim := hc.tendsto (1, q); simpa using hlim
    have e1 := ht.eventually (((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ) q)
    have e2 : ∀ᶠ w : Fˣ × (F × Y) in nhds (1, q), Φ w.2 = Φ q :=
      (continuous_snd.tendsto (1, q)).eventually (((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ) q)
    filter_upwards [e1, e2] with w h1 h2
    rw [h2]; exact h1
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Units.val_one] at hV
  obtain ⟨W, hW, hWV⟩ := hV
  obtain ⟨r, hr0, hrW⟩ := Metric.mem_nhds_iff.1 hW
  set r' : ℝ := min r 1 with hr'
  have hr'0 : 0 < r' := lt_min hr0 one_pos
  have hr'1 : r' ≤ 1 := min_le_right _ _
  have hr'r : r' ≤ r := min_le_left _ _
  have hnorm1 : ∀ t : F, ‖t - 1‖ < r' → ‖t‖ = 1 := by
    intro t ht
    have h : ‖t - 1‖ < ‖(1 : F)‖ := by rw [norm_one]; exact ht.trans_le hr'1
    have hmax := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := t - 1)
      (y := (1 : F)) h.ne
    rw [sub_add_cancel, max_eq_right h.le, norm_one] at hmax
    exact hmax
  let U : Subgroup Fˣ :=
    { carrier := {t | ‖(t : F) - 1‖ < r'}
      one_mem' := by show ‖((1 : Fˣ) : F) - 1‖ < r'; simpa using hr'0
      mul_mem' := by
        intro s t hs ht
        show ‖((s * t : Fˣ) : F) - 1‖ < r'
        rw [Units.val_mul]
        have e : (s : F) * (t : F) - 1 =
            ((s : F) - 1) * (t : F) + ((t : F) - 1) := by ring
        rw [e]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ht)
        rw [norm_mul, hnorm1 _ ht, mul_one]; exact hs
      inv_mem' := by
        intro s hs
        show ‖((s⁻¹ : Fˣ) : F) - 1‖ < r'
        have h1 : ‖(s : F)‖ = 1 := hnorm1 _ hs
        have e : ((s⁻¹ : Fˣ) : F) - 1 =
            ((s⁻¹ : Fˣ) : F) * (1 - (s : F)) := by
          rw [mul_sub, mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [e, norm_mul, ← norm_neg (1 - (s : F)), neg_sub]
        have h2 : ‖((s⁻¹ : Fˣ) : F)‖ = 1 := by
          have hinv := congrArg (fun x : F => ‖x‖) (s.inv_mul)
          simp only [norm_mul, h1, mul_one, norm_one] at hinv
          exact hinv
        rw [h2, one_mul]; exact hs }
  have hUo : IsOpen (U : Set Fˣ) := by
    show IsOpen {t : Fˣ | ‖(t : F) - 1‖ < r'}
    exact isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const))
      continuous_const
  have hUV : ∀ t ∈ U, ∀ q ∈ tsupport Φ, Φ (q.1 * (t : F), q.2) = Φ q := by
    intro t ht
    apply hWV
    show (t : F) ∈ W
    apply hrW
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le ht hr'r
  refine ⟨U, hUo, fun t ht b z => ?_⟩
  by_cases hq : (b, z) ∈ tsupport Φ
  · exact hUV t ht (b, z) hq
  · have h0 : Φ (b, z) = 0 := image_eq_zero_of_notMem_tsupport hq
    rw [h0]
    by_contra hne
    have hq' : (b * (t : F), z) ∈ tsupport Φ := by rw [hS]; exact hne
    have hinv := hUV t⁻¹ (U.inv_mem ht) _ hq'
    simp only at hinv
    rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, h0] at hinv
    exact hne hinv.symm

end IsLocallyConstant
