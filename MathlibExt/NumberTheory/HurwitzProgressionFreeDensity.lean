/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Set.Card
public import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Quaternion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Upper density of progression-free Hurwitz quaternions

A set avoiding three-term geometric progressions has upper density at most `20 / 21`.
We count Hurwitz quaternions as points of a four-dimensional lattice, and pack disjoint
progressions of ratio `1 + i` into successive norm shells.
-/

namespace MetaMathlibExt

set_option quotPrecheck false in
/-- The Hurwitz order: quaternions with all coordinates in `ℤ` or all in `ℤ + 1/2`. -/
local notation "𝐇" => Set.ofPred fun q : Quaternion ℚ =>
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) ∧ q.imI = (b : ℚ) ∧ q.imJ = (c : ℚ) ∧ q.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    q.re = (a : ℚ) + 1 / 2 ∧ q.imI = (b : ℚ) + 1 / 2 ∧
      q.imJ = (c : ℚ) + 1 / 2 ∧ q.imK = (d : ℚ) + 1 / 2)
set_option quotPrecheck false in
/-- `S(N)`: nonzero Hurwitz quaternions of norm at most `N`. -/
local notation "𝐒" N:max => Set.ofPred fun q : Quaternion ℚ =>
  q ∈ 𝐇 ∧ q ≠ 0 ∧ Quaternion.normSq q ≤ ((N : ℕ) : ℚ)
set_option quotPrecheck false in
/-- The density ratio `|A ∩ S(N)| / |S(N)|`. -/
local notation "ρ" A:max N:max =>
  ((Set.ncard (A ∩ 𝐒 N) : ℝ) / (Set.ncard (𝐒 N) : ℝ))
set_option quotPrecheck false in
/-- `A ⊆ Q_Hur` contains no triple `(a, ar, ar²)` with `a, r ≠ 0` and `r` a non-unit. -/
local notation "GPFree" A:max => A ⊆ 𝐇 ∧ ∀ a ∈ 𝐇, ∀ r ∈ 𝐇, a ≠ 0 → r ≠ 0 →
  Quaternion.normSq r ≠ 1 → ¬ (a ∈ A ∧ a * r ∈ A ∧ a * r ^ 2 ∈ A)

namespace upperDensity_le_of_hurwitz_gpFree

open Filter MeasureTheory Metric Set
open scoped Topology

private abbrev E := EuclideanSpace ℝ (Fin 4)

/-- Coordinates in the basis `1, i, j, (1 + i + j + k) / 2`. -/
private def coords (K : Type*) [Field K] [CharZero K] : Quaternion K ≃ₗ[K] (Fin 4 → K) where
  toFun q := ![q.re - q.imK, q.imI - q.imK, q.imJ - q.imK, 2 * q.imK]
  invFun v := ⟨v 0 + v 3 / 2, v 1 + v 3 / 2, v 2 + v 3 / 2, v 3 / 2⟩
  left_inv q := by ext <;> dsimp <;> ring
  right_inv v := by ext i; fin_cases i <;> dsimp <;> ring
  map_add' q r := by ext i; fin_cases i <;> dsimp <;> ring
  map_smul' c q := by ext i; fin_cases i <;> dsimp <;> ring

private lemma mem_hurwitz_iff (q : Quaternion ℚ) :
    q ∈ 𝐇 ↔ ∃ z : Fin 4 → ℤ, coords ℚ q = fun i => (z i : ℚ) := by
  constructor
  · rintro (⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩)
    · refine ⟨![a - d, b - d, c - d, 2 * d], ?_⟩
      ext i; fin_cases i <;> simp [coords, ha, hb, hc, hd]
    · refine ⟨![a - d, b - d, c - d, 2 * d + 1], ?_⟩
      ext i; fin_cases i <;> simp [coords, ha, hb, hc, hd]; ring
  · rintro ⟨z, hz⟩
    have hq := congrArg (coords ℚ).symm hz
    rw [LinearEquiv.symm_apply_apply] at hq
    have h (k : ℤ) (hk : z 3 = 2 * (z 3 / 2) + k) :
        (z 3 : ℚ) / 2 = (↑(z 3 / 2) : ℚ) + (k : ℚ) / 2 := by
      have hk' : (z 3 : ℚ) = 2 * (↑(z 3 / 2) : ℚ) + (k : ℚ) := by exact_mod_cast hk
      linarith
    rw [hq]
    rcases (show z 3 = 2 * (z 3 / 2) + 0 ∨ z 3 = 2 * (z 3 / 2) + 1 by omega) with he | ho
    · refine Or.inl ⟨z 0 + z 3 / 2, z 1 + z 3 / 2, z 2 + z 3 / 2, z 3 / 2, ?_⟩
      simp [coords, h 0 he]
    · refine Or.inr ⟨z 0 + z 3 / 2, z 1 + z 3 / 2, z 2 + z 3 / 2, z 3 / 2, ?_⟩
      simp [coords, h 1 ho, add_assoc]

private noncomputable def basis : Module.Basis (Fin 4) ℝ E :=
  Module.Basis.ofEquivFun (Quaternion.linearIsometryEquivTuple.symm.toLinearEquiv.trans (coords ℝ))

private noncomputable abbrev lattice := Submodule.span ℤ (Set.range basis)

private noncomputable def point (q : Quaternion ℚ) : E :=
  basis.equivFun.symm (fun i => (coords ℚ q i : ℝ))

private lemma point_injective : Function.Injective point := by
  intro q r h
  apply (coords ℚ).injective
  ext i
  exact_mod_cast congrFun (basis.equivFun.symm.injective h) i

private lemma point_image : point '' 𝐇 = (lattice : Set E) := by
  ext x
  rw [SetLike.mem_coe, basis.mem_span_iff_repr_mem ℤ x]
  constructor
  · rintro ⟨q, hq, rfl⟩ i
    obtain ⟨z, hz⟩ := (mem_hurwitz_iff q).1 hq
    refine ⟨z i, ?_⟩
    change (z i : ℝ) = basis.equivFun (point q) i
    rw [point, LinearEquiv.apply_symm_apply, hz]
    simp
  · intro h
    choose z hz using h
    let q := (coords ℚ).symm (fun i => (z i : ℚ))
    refine ⟨q, (mem_hurwitz_iff _).2 ⟨z, (coords ℚ).apply_symm_apply _⟩, ?_⟩
    apply basis.equivFun.injective
    ext i
    rw [point, LinearEquiv.apply_symm_apply, show coords ℚ q = _ from (coords ℚ).apply_symm_apply _]
    rw [Rat.cast_intCast, Module.Basis.equivFun_apply]
    exact hz i

private lemma norm_point_sq (q : Quaternion ℚ) :
    ‖point q‖ ^ 2 = ((Quaternion.normSq q : ℚ) : ℝ) := by
  let r : Quaternion ℝ := ⟨q.re, q.imI, q.imJ, q.imK⟩
  have hr : point q = Quaternion.linearIsometryEquivTuple r := by
    apply basis.equivFun.injective
    rw [point, LinearEquiv.apply_symm_apply]
    ext i
    change _ = ((Module.Basis.ofEquivFun _).equivFun _) i
    rw [Module.Basis.equivFun_ofEquivFun, LinearEquiv.trans_apply]
    simp only [LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply]
    fin_cases i <;> simp [coords, r]
  rw [hr, LinearIsometryEquiv.norm_map, pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp [r, Quaternion.normSq_def']

private def ball (t : ℝ) : Set (Quaternion ℚ) :=
  {q | q ∈ 𝐇 ∧ ((Quaternion.normSq q : ℚ) : ℝ) ≤ t}

private lemma image_ball {t : ℝ} (ht : 0 ≤ t) :
    point '' ball t = {x : E | ‖x‖ ^ 4 ≤ t ^ 2} ∩ lattice := by
  have hnorm (q) : ‖point q‖ ^ 4 ≤ t ^ 2 ↔ ((Quaternion.normSq q : ℚ) : ℝ) ≤ t := by
    rw [show ‖point q‖ ^ 4 = (‖point q‖ ^ 2) ^ 2 by ring, norm_point_sq]
    exact sq_le_sq₀ (by exact_mod_cast Quaternion.normSq_nonneg) ht
  ext x
  rw [← point_image]
  constructor
  · rintro ⟨q, ⟨hq, hqt⟩, rfl⟩
    exact ⟨(hnorm q).2 hqt, q, hq, rfl⟩
  · rintro ⟨hx, q, hq, rfl⟩
    exact ⟨q, ⟨hq, (hnorm q).1 hx⟩, rfl⟩

private lemma finite_ball {t : ℝ} (ht : 0 ≤ t) : (ball t).Finite := by
  apply Set.Finite.of_finite_image (f := point) _ point_injective.injOn
  rw [image_ball ht]
  apply ZSpan.setFinite_inter basis
  apply (isBounded_closedBall (x := (0 : E)) (r := t + 1)).subset
  intro x hx
  rw [mem_closedBall_zero_iff]
  change ‖x‖ ^ 4 ≤ t ^ 2 at hx
  have hs : ‖x‖ ^ 2 ≤ t := (sq_le_sq₀ (sq_nonneg _) ht).1 (by convert hx using 1; ring)
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Counting lattice points with `‖x‖⁴ ≤ t²` gives a positive multiple of `t²` asymptotically. -/
private lemma ball_growth : ∃ C : ℝ, 0 < C ∧
    Tendsto (fun t : ℝ => ((ball t).ncard : ℝ) / t ^ 2) atTop (𝓝 C) := by
  let B := closedBall (0 : E) 1
  have hB : {x ∈ (univ : Set E) | ‖x‖ ^ 4 ≤ 1} = B := by
    ext x
    simp [B, pow_le_one_iff_of_nonneg (norm_nonneg x)]
  have hlim := ZLattice.covolume.tendsto_card_le_div' lattice
    (X := (univ : Set E)) (F := fun x => ‖x‖ ^ 4) (fun _ _ _ _ => mem_univ _)
    (fun x r hr => by simp [norm_smul, abs_of_nonneg hr, mul_pow])
    (by rw [hB]; exact isBounded_closedBall) (by rw [hB]; exact measurableSet_closedBall)
    (by
      rw [hB]
      dsimp [B]
      rw [frontier_closedBall _ one_ne_zero]
      exact Measure.addHaar_sphere _ _ _)
  refine ⟨volume.real B / ZLattice.covolume lattice, div_pos ?_ (ZLattice.covolume_pos _ _), ?_⟩
  · exact ENNReal.toReal_pos (measure_closedBall_pos volume _ zero_lt_one).ne'
      measure_closedBall_lt_top.ne
  rw [hB] at hlim
  apply (hlim.comp (tendsto_pow_atTop (by decide : 2 ≠ 0))).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, mem_univ, true_and]
  rw [← Set.ncard_image_of_injective (ball t) point_injective, image_ball ht]
  rfl

private def points (t : ℝ) := ball t \ {(0 : Quaternion ℚ)}

private lemma points_mono : Monotone points :=
  fun _ _ h _ hq => ⟨⟨hq.1.1, hq.1.2.trans h⟩, hq.2⟩

private lemma points_finite {t : ℝ} (ht : 0 ≤ t) : (points t).Finite :=
  (finite_ball ht).sdiff

private lemma points_growth : ∃ C : ℝ, 0 < C ∧
    Tendsto (fun t : ℝ => ((points t).ncard : ℝ) / t ^ 2) atTop (𝓝 C) := by
  obtain ⟨C, hC, hlim⟩ := ball_growth
  refine ⟨C, hC, ?_⟩
  have hzero : Tendsto (fun t : ℝ => 1 / t ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by decide))
  rw [← sub_zero C]
  apply (hlim.sub hzero).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have h0 : {(0 : Quaternion ℚ)} ⊆ ball t := singleton_subset_iff.mpr
    ⟨Or.inl ⟨0, 0, 0, 0, by simp⟩, by simpa using ht⟩
  rw [points, cast_ncard_sdiff h0 (finite_ball ht), ncard_singleton, Nat.cast_one, sub_div]

private abbrev ratio : Quaternion ℚ := ⟨1, 1, 0, 0⟩

private lemma ratio_norm : Quaternion.normSq ratio = 2 := by
  norm_num [ratio, Quaternion.normSq_def']

private lemma ratio_ne_zero : ratio ≠ 0 := Quaternion.normSq_ne_zero.mp (by norm_num [ratio_norm])

private lemma mul_ratio_mem {q : Quaternion ℚ} (hq : q ∈ 𝐇) : q * ratio ∈ 𝐇 := by
  rcases hq with ⟨a, b, c, d, ha, hb, hc, hd⟩ | ⟨a, b, c, d, ha, hb, hc, hd⟩
  · refine Or.inl ⟨a - b, a + b, c + d, d - c, ?_, ?_, ?_, ?_⟩ <;>
      simp [ratio, ha, hb, hc, hd]
    ring
  · refine Or.inl ⟨a - b, a + b + 1, c + d + 1, d - c, ?_, ?_, ?_, ?_⟩ <;>
      simp [ratio, ha, hb, hc, hd] <;> ring

private lemma mul_ratio_pow_mem {q : Quaternion ℚ} (hq : q ∈ 𝐇) (i : ℕ) :
    q * ratio ^ i ∈ 𝐇 := by
  induction i with
  | zero => simpa using hq
  | succ i ih => simpa [pow_succ, ← mul_assoc] using mul_ratio_mem ih

private abbrev normValue (q : Quaternion ℚ) : ℝ := (Quaternion.normSq q : ℚ)

private lemma norm_mul_ratio (q : Quaternion ℚ) (i : ℕ) :
    normValue (q * ratio ^ i) = normValue q * 2 ^ i := by
  simp [normValue, map_mul, map_pow, ratio_norm]

/-- Starting in the shell `(t/8, t/4]` puts the three terms in distinct consecutive shells.
Each progression therefore supplies a distinct missing point outside the inner ball. -/
private lemma missing_shell (A : Set (Quaternion ℚ)) (hA : GPFree A) {t : ℝ} (ht : 0 < t) :
    ((points (t / 4)).ncard : ℝ) - (points (t / 8)).ncard ≤
      ((points t \ A).ncard : ℝ) - (points (t / 8) \ A).ncard := by
  classical
  let base := points (t / 4) \ points (t / 8)
  let gap := (points t \ A) \ (points (t / 8) \ A)
  have bounds {q} (hq : q ∈ base) : t / 8 < normValue q ∧ normValue q ≤ t / 4 := by
    exact ⟨lt_of_not_ge (fun h => hq.2 ⟨⟨hq.1.1.1, h⟩, hq.1.2⟩), hq.1.1.2⟩
  let index (q : Quaternion ℚ) : Fin 3 := if q ∉ A then 0 else if q * ratio ∉ A then 1 else 2
  have missing {q} (hq : q ∈ base) : q * ratio ^ (index q).val ∉ A := by
    have hfree := hA.2 q hq.1.1.1 ratio (Or.inl ⟨1, 1, 0, 0, by simp⟩)
      hq.1.2 ratio_ne_zero (by norm_num [ratio_norm])
    by_cases h₀ : q ∈ A <;> by_cases h₁ : q * ratio ∈ A <;> simp_all [index]
  let f (q : Quaternion ℚ) := q * ratio ^ (index q).val
  have hmap {q} (hq : q ∈ base) : f q ∈ gap := by
    have hnorm := norm_mul_ratio q (index q).val
    obtain ⟨hlo, hhi⟩ := bounds hq
    have hrange : t / 8 < normValue (f q) ∧ normValue (f q) ≤ t := by
      change _ < normValue (q * _) ∧ normValue (q * _) ≤ _
      rw [hnorm]
      generalize index q = i
      fin_cases i <;> norm_num <;> constructor <;> linarith
    exact ⟨⟨⟨⟨mul_ratio_pow_mem hq.1.1.1 _, hrange.2⟩,
      mul_ne_zero hq.1.2 (pow_ne_zero _ ratio_ne_zero)⟩, missing hq⟩,
      fun h => hrange.1.not_ge h.1.1.2⟩
  have hinj : InjOn f base := by
    intro q hq p hp he
    obtain ⟨hq₀, hq₁⟩ := bounds hq
    obtain ⟨hp₀, hp₁⟩ := bounds hp
    have hn := congrArg normValue he
    change q * ratio ^ (index q).val = p * ratio ^ (index p).val at he
    change normValue (q * _) = normValue (p * _) at hn
    rw [norm_mul_ratio, norm_mul_ratio] at hn
    have hi : index q = index p := by
      generalize index q = i at hn ⊢
      generalize index p = j at hn ⊢
      fin_cases i <;> fin_cases j <;> first | rfl | (norm_num at hn; exfalso; linarith)
    rw [hi] at he
    exact mul_right_cancel₀ (pow_ne_zero _ ratio_ne_zero) he
  have hc : (base.ncard : ℝ) ≤ gap.ncard := by
    exact_mod_cast ncard_le_ncard_of_injOn f (fun _ h => hmap h) hinj
      (points_finite ht.le).sdiff.sdiff
  rw [show (base.ncard : ℝ) = _ from cast_ncard_sdiff (points_mono (by linarith : t / 8 ≤ t / 4))
    (points_finite (by positivity)), show (gap.ncard : ℝ) = _ from
    cast_ncard_sdiff (sdiff_subset_sdiff_left (points_mono (by linarith : t / 8 ≤ t)))
      (points_finite ht.le).sdiff] at hc
  exact hc

private lemma count_pos {t : ℝ} (ht : 1 ≤ t) : 0 < ((points t).ncard : ℝ) := by
  have h : (1 : Quaternion ℚ) ∈ points t :=
    ⟨⟨Or.inl ⟨1, 0, 0, 0, by simp⟩, by simpa using ht⟩, one_ne_zero⟩
  exact_mod_cast (ncard_pos (points_finite (zero_le_one.trans ht))).mpr ⟨_, h⟩

private lemma scaled_count (k : ℝ) (hk : 0 < k) :
    Tendsto (fun t : ℝ => ((points (t / k)).ncard : ℝ) / (points t).ncard)
      atTop (𝓝 (1 / k ^ 2)) := by
  obtain ⟨C, hC, hlim⟩ := points_growth
  have hscale := hlim.comp (tendsto_id.atTop_div_const hk)
  have h := ((hscale.div hlim hC.ne').div_const (k ^ 2))
  rw [div_self hC.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  dsimp
  field_simp [hk.ne', (count_pos ht).ne', (zero_lt_one.trans_le ht).ne']

private noncomputable def deficit (A : Set (Quaternion ℚ)) (t : ℝ) : ℝ :=
  ((points t \ A).ncard : ℝ) / (points t).ncard

/-- The inner ball supplies its own missing points in addition to the outer shell. -/
private lemma deficit_liminf (A : Set (Quaternion ℚ)) (hA : GPFree A) :
    1 / 21 ≤ liminf (deficit A) atTop := by
  let d := liminf (deficit A) atTop
  have lower : IsBoundedUnder (· ≥ ·) atTop (deficit A) :=
    isBoundedUnder_of ⟨0, fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩
  have upper : IsCoboundedUnder (· ≥ ·) atTop (deficit A) := by
    apply isCoboundedUnder_ge_of_eventually_le atTop (x := 1)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    apply (div_le_one (count_pos ht)).2
    exact_mod_cast ncard_le_ncard sdiff_subset (points_finite (zero_le_one.trans ht))
  have step (b : ℝ) (hb : b < d) : b * (1 / 8 ^ 2) + 1 / 4 ^ 2 - 1 / 8 ^ 2 ≤ d := by
    have hlow := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 8)).eventually
      (eventually_lt_of_lt_liminf hb lower)
    have hlim := (((scaled_count 8 (by norm_num)).const_mul b).add
      (scaled_count 4 (by norm_num))).sub (scaled_count 8 (by norm_num))
    rw [← hlim.liminf_eq]
    apply liminf_le_liminf _ hlim.isBoundedUnder_ge upper
    filter_upwards [hlow, eventually_ge_atTop (8 : ℝ)] with t hbt ht
    have ht₁ : 1 ≤ t := by linarith
    have h₈ := count_pos (show 1 ≤ t / 8 by linarith)
    have hbt' : b * (points (t / 8)).ncard ≤ ((points (t / 8) \ A).ncard : ℝ) :=
      ((lt_div_iff₀ h₈).1 hbt).le
    have hs := missing_shell A hA (zero_lt_one.trans_le ht₁)
    dsimp [deficit]
    rw [← mul_div_assoc, ← add_div, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  -- Letting b increase to d gives 64d ≥ d + 3.
  have hd : d ≤ 64 * d - 3 := le_of_forall_lt_imp_le_of_dense fun b hb => by
    linarith [step b hb]
  change 1 / 21 ≤ d
  linarith

private lemma points_nat (N : ℕ) : points (N : ℝ) = 𝐒 N := by
  ext q
  change ((_ ∧ ((Quaternion.normSq q : ℚ) : ℝ) ≤ N) ∧ q ≠ 0) ↔ _
  norm_cast
  exact ⟨fun ⟨⟨h, hn⟩, hz⟩ => ⟨h, hz, hn⟩, fun ⟨h, hz, hn⟩ => ⟨⟨h, hn⟩, hz⟩⟩

end upperDensity_le_of_hurwitz_gpFree

open upperDensity_le_of_hurwitz_gpFree in
/-- **Upper bound for geometric-progression-free Hurwitz sets.** Let $Q_{\mathrm{Hur}}$ be the
set of Hurwitz quaternions, the rational quaternions whose four coordinates are all integers or
all lie in $\mathbb{Z} + \tfrac12$, and let $\mathrm{Nm}(q)$ be the sum of the squares of the
coordinates of $q$. For $N \in \mathbb{N}$ let $S(N)$ be the set of nonzero
$q \in Q_{\mathrm{Hur}}$ with $\mathrm{Nm}(q) \le N$. Let $A \subseteq Q_{\mathrm{Hur}}$ be free
of 3-term geometric progressions: there are no $a, r \in Q_{\mathrm{Hur}}$ with $a \ne 0$,
$r \ne 0$ and $\mathrm{Nm}(r) \ne 1$ such that $a$, $ar$ and $ar^2$ all lie in $A$. Then the
upper density $\limsup_{N \to \infty} |A \cap S(N)| / |S(N)|$ of $A$ is at most $20/21$.

Source: Asada, Fang, Fourakis, Manski, McNew, Miller, Moreland, Yamin, and Zhang, *Avoiding
3-Term Geometric Progressions in Hurwitz Quaternions*, J. Integer Seq. 27 (2024), Article
24.7.7, Lemma 13. -/
public theorem upperDensity_le_of_hurwitz_gpFree (A : Set (Quaternion ℚ))
    (hA : GPFree A) :
    Filter.limsup (fun N : ℕ => ρ A N) Filter.atTop ≤ 20 / 21 := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  apply Filter.limsup_le_of_le (Filter.isCoboundedUnder_le_of_le Filter.atTop
    (x := 0) (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hlow := Filter.eventually_lt_of_lt_liminf
    (lt_of_lt_of_le (show 1 - b < 1 / 21 by linarith) (deficit_liminf A hA))
    (Filter.isBoundedUnder_of ⟨0, fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hlow, Filter.eventually_ge_atTop 1]
    with N hN hN₁
  have htotal := Set.ncard_inter_add_ncard_sdiff_eq_ncard (points (N : ℝ)) A
    (points_finite (Nat.cast_nonneg _))
  have hpos := count_pos (show (1 : ℝ) ≤ N by exact_mod_cast hN₁)
  change ρ A N ≤ b
  rw [← points_nat N, Set.inter_comm]
  apply (div_le_iff₀ hpos).2
  have hsum := congrArg (Nat.cast : ℕ → ℝ) htotal
  push_cast at hsum
  have hlt := (lt_div_iff₀ hpos).1 hN
  linarith

end MetaMathlibExt
