/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.LaplaceMeanValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Harnack's inequality for harmonic functions

We compare ball averages at nearby points, then use compactness and connectedness to
bound the number of comparisons needed uniformly over all nonnegative harmonic functions.
-/

public section

namespace MathlibExt.Analysis.PDE.LaplaceMeanValueWanted

open InnerProductSpace Metric MeasureTheory Set Filter
open scoped Topology

/-- A common local multiplicative bound for a family of nonnegative functions on a compact
connected set gives a common global bound. -/
private lemma exists_uniform_comparison {X ι : Type*} [PseudoMetricSpace X] {K : Set X}
    (hK : IsCompact K) (hconn : IsConnected K) {r D : ℝ} (hr : 0 < r) (hD : 1 ≤ D)
    (f : ι → X → ℝ) (hf : ∀ i x, x ∈ K → 0 ≤ f i x)
    (hloc : ∀ i x y, x ∈ K → y ∈ K → dist x y < r → f i x ≤ D * f i y) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x y, x ∈ K → y ∈ K → f i x ≤ C * f i y := by
  classical
  let P (n : ℕ) (x y : X) : Prop :=
    ∀ i, f i x ≤ D ^ n * f i y ∧ f i y ≤ D ^ n * f i x
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hstep {x y : X} (hx : x ∈ K) (hy : y ∈ K) (hxy : dist x y < r) : P 1 x y := by
    intro i
    simp only [pow_one]
    exact ⟨hloc i x y hx hy hxy, hloc i y x hy hx (dist_comm x y ▸ hxy)⟩
  have hsymm {n x y} (h : P n x y) : P n y x := fun i ↦ (h i).symm
  have htrans {m n x y z} (hxy : P m x y) (hyz : P n y z) : P (m + n) x z := by
    intro i
    constructor
    · calc
        f i x ≤ D ^ m * f i y := (hxy i).1
        _ ≤ D ^ m * (D ^ n * f i z) := mul_le_mul_of_nonneg_left (hyz i).1 (pow_nonneg hD₀ _)
        _ = D ^ (m + n) * f i z := by rw [pow_add, mul_assoc]
    · calc
        f i z ≤ D ^ n * f i y := (hyz i).2
        _ ≤ D ^ n * (D ^ m * f i x) := mul_le_mul_of_nonneg_left (hxy i).2 (pow_nonneg hD₀ _)
        _ = D ^ (m + n) * f i x := by rw [Nat.add_comm m n, pow_add, mul_assoc]
  -- Preconnectedness propagates the existence of a finite comparison chain.
  have hchain {x y : X} (hx : x ∈ K) (hy : y ∈ K) : ∃ n, P n x y := by
    refine hconn.isPreconnected.induction₂' (fun a b ↦ ∃ n, P n a b) ?_ ?_ hx hy
    · intro a ha
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)),
        self_mem_nhdsWithin] with b hb hbK
      have h := hstep hbK ha (mem_ball.mp hb)
      exact ⟨⟨1, hsymm h⟩, ⟨1, h⟩⟩
    · rintro a b c _ _ _ ⟨m, hm⟩ ⟨n, hn⟩
      exact ⟨m + n, htrans hm hn⟩
  obtain ⟨a, ha⟩ := hconn.nonempty
  have hcenter (z : K) : ∃ n, P n z a := hchain z.property ha
  choose n hn using hcenter
  -- Take the largest exponent needed by the finitely many centres of a subcover.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K ↦ ball (z : X) r)
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hr⟩)
  let N := t.sup n + 1
  have hbound {x : X} (hx : x ∈ K) : P N x a := by
    have hxcover := ht hx
    simp only [mem_iUnion] at hxcover
    obtain ⟨z, hz, hxz⟩ := hxcover
    have hxa := htrans (hstep hx z.property (mem_ball.mp hxz)) (hn z)
    have hle : 1 + n z ≤ N := by
      rw [Nat.add_comm 1]
      exact Nat.succ_le_succ (Finset.le_sup (f := n) hz)
    have hpow : D ^ (1 + n z) ≤ D ^ N := pow_le_pow_right₀ hD hle
    intro i
    exact ⟨(hxa i).1.trans (mul_le_mul_of_nonneg_right hpow (hf i a ha)),
      (hxa i).2.trans (mul_le_mul_of_nonneg_right hpow (hf i x hx))⟩
  exact ⟨D ^ (N + N), pow_pos (zero_lt_one.trans_le hD) _, fun i _ _ hx hy ↦
    (htrans (hbound hx) (hsymm (hbound hy)) i).1⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

variable [MeasurableSpace E] [BorelSpace E]

private lemma volume_real_closedBall_pos (x : E) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (closedBall x r) :=
  ENNReal.toReal_pos (measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne

/-- Comparison at two nearby centres by inclusion of the small ball in the large ball. -/
private lemma harmonic_le_mul_of_dist_le {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) (hu₀ : ∀ x ∈ U, 0 ≤ u x) {x y : E} {r : ℝ} (hr : 0 < r)
    (hxy : dist x y ≤ r) (hy : closedBall y (r + r) ⊆ U) :
    u x ≤ (volume.real (closedBall (0 : E) (r + r)) / volume.real (closedBall (0 : E) r)) *
      u y := by
  have hsub : closedBall x r ⊆ closedBall y (r + r) :=
    closedBall_subset_closedBall' (add_le_add_right hxy r)
  have hmean := (harmonicOnNhd_iff_forall_average_closedBall hU hu.contDiffOn).mp hu
  have hintegral {z : E} {s : ℝ} (hs : 0 < s) (hz : closedBall z s ⊆ U) :
      ∫ w in closedBall z s, u w = volume.real (closedBall (0 : E) s) * u z := by
    have h := hmean z s hs hz
    rw [setAverage_eq, smul_eq_mul, Measure.addHaar_real_closedBall_center] at h
    rw [← h, ← mul_assoc, mul_inv_cancel₀ (volume_real_closedBall_pos (0 : E) hs).ne', one_mul]
  have hfi : IntegrableOn u (closedBall y (r + r)) volume :=
    (hu.continuousOn.mono hy).integrableOn_compact (isCompact_closedBall _ _)
  have hle : ∫ z in closedBall x r, u z ≤ ∫ z in closedBall y (r + r), u z := by
    apply setIntegral_mono_set hfi
    · filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
      exact hu₀ z (hy hz)
    · exact Filter.Eventually.of_forall fun _ hz ↦ hsub hz
  rw [hintegral hr (hsub.trans hy), hintegral (add_pos hr hr) hy] at hle
  rw [div_mul_eq_mul_div, le_div_iff₀ (volume_real_closedBall_pos (0 : E) hr), mul_comm (u x)]
  exact hle

end

/-- **Harnack's inequality for harmonic functions.** Let `U` be open and let `V` be open and
connected with `closure V` compact and contained in `U`. There is a constant `C > 0`, depending
only on `V` and `U`, such that every nonnegative harmonic function `u` on `U` satisfies
`u x ≤ C u y` for all `x, y ∈ V`; equivalently `sup_V u ≤ C inf_V u`. This is Harnack's
Inequality 3.8 of M. Schmidt, *Partial Differential Equations*, lecture notes, Universität
Mannheim, HWS 2025, Chapter 3 (in its pointwise form "for all `x, y ∈ Ω′`"), and the case
`aⁱʲ = δⁱʲ` of Theorem 3 of Chapter IV.A.3 of L. C. Evans, *Entropy and Partial Differential
Equations*. -/
theorem harnack_inequality {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    (hVconn : IsConnected V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, HarmonicOnNhd u U → (∀ x ∈ U, 0 ≤ u x) →
      ∀ x ∈ V, ∀ y ∈ V, u x ≤ C * u y := by
  -- Keep the named openness hypothesis of the original statement.
  have _ := hV
  -- Use the Borel measure locally rather than adding measure instances to the statement.
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨R, hR, hRU⟩ := hVc.exists_cthickening_subset_open hU hVU
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hball {y : E} (hy : y ∈ closure V) : closedBall y (r + r) ⊆ U := by
    rw [show r + r = R from add_halves R]
    exact (closedBall_subset_cthickening hy R).trans hRU
  -- Translation invariance makes the volume ratio independent of the two centres,
  -- including in dimension zero.
  let D := volume.real (closedBall (0 : E) (r + r)) / volume.real (closedBall (0 : E) r)
  have hD : 1 ≤ D := (one_le_div (volume_real_closedBall_pos (0 : E) hr)).mpr
    (measureReal_mono (closedBall_subset_closedBall (le_add_of_nonneg_right hr.le))
      measure_closedBall_lt_top.ne)
  let F := {u : E → ℝ // HarmonicOnNhd u U ∧ ∀ x ∈ U, 0 ≤ u x}
  obtain ⟨C, hC, h⟩ := exists_uniform_comparison hVc hVconn.closure hr hD
    (fun u : F ↦ u.val) (fun u x hx ↦ u.property.2 x (hVU hx))
    (fun u _ _ _ hy hxy ↦ harmonic_le_mul_of_dist_le hU u.property.1 u.property.2 hr
      hxy.le (hball hy))
  exact ⟨C, hC, fun u hu hu₀ x hx y hy ↦
    h ⟨u, hu, hu₀⟩ x y (subset_closure hx) (subset_closure hy)⟩

end MathlibExt.Analysis.PDE.LaplaceMeanValueWanted
