/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported

namespace MathlibExt.Analysis.Convex.ChoquetWanted

open MeasureTheory Set

open scoped Pointwise CompactlySupported ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Separating quadratic form: weighted sum of squared functionals. -/
private noncomputable def cqSepQuad (φ : ℕ → StrongDual ℝ E) (w : E) : ℝ :=
  ∑' n, ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2

/-- Affine majorant values at `x`: reals attained by some continuous affine majorant of `g`. -/
private def cqMajorants (K : Set E) (x : E) (g : C(K, ℝ)) : Set ℝ :=
  { t | ∃ φ : StrongDual ℝ E, ∃ c : ℝ, (∀ y : K, g y ≤ φ y + c) ∧ t = φ x + c }

/-- Upper envelope value: infimum of affine majorant values at `x`. -/
private noncomputable def cqEnv (K : Set E) (x : E) (g : C(K, ℝ)) : ℝ :=
  sInf (cqMajorants K x g)

/-- Continuous affine function on `K` from a functional and constant. -/
private noncomputable def cqAffine (K : Set E) (φ : StrongDual ℝ E) (c : ℝ) :
    C(K, ℝ) :=
  ⟨fun y => φ y + c, by fun_prop⟩

/-- Pointwise bound on each functional value. -/
private theorem cqSepQuad_abs_le (φ : ℕ → StrongDual ℝ E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (w : E) (n : ℕ) : |φ n w| ≤ ‖w‖ := by
  have h2 := (φ n).le_opNorm w
  have h3 := mul_le_mul_of_nonneg_right (hφ n) (norm_nonneg w)
  rw [one_mul] at h3
  calc |φ n w| = ‖φ n w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖w‖ := le_trans h2 h3

/-- Each summand is nonnegative and dominated. -/
private theorem cqSepQuad_term (φ : ℕ → StrongDual ℝ E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (w : E) (n : ℕ) :
    0 ≤ ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2 ∧
      ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2 ≤ ((1 / 2 : ℝ) ^ n) * ‖w‖ ^ 2 := by
  have hsq : (φ n w) ^ 2 ≤ ‖w‖ ^ 2 := by
    have h := abs_le.mp (cqSepQuad_abs_le φ hφ w n)
    exact sq_le_sq' h.1 h.2
  refine ⟨by positivity, ?_⟩
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- The defining series is summable. -/
private theorem cqSepQuad_summable (φ : ℕ → StrongDual ℝ E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (w : E) : Summable (fun n => ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2) := by
  have hcomp : Summable (fun n => ((1 / 2 : ℝ) ^ n) * ‖w‖ ^ 2) :=
    summable_geometric_two.mul_right _
  exact Summable.of_nonneg_of_le (fun n => (cqSepQuad_term φ hφ w n).1)
    (fun n => (cqSepQuad_term φ hφ w n).2) hcomp

/-- Scalar parallelogram identity for weights summing to one. -/
private theorem cq_scalar_combo (a b : ℝ) (hab : a + b = 1) (s t : ℝ) :
    a * s ^ 2 + b * t ^ 2 = (a * s + b * t) ^ 2 + a * b * (s - t) ^ 2 := by
  have ha : a = 1 - b := by linarith
  rw [ha]
  ring

/-- The quadratic form satisfies the strict-convexity identity. -/
private theorem cqSepQuad_combo (φ : ℕ → StrongDual ℝ E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (u v : E) (a b : ℝ) (hab : a + b = 1) :
    a * cqSepQuad φ u + b * cqSepQuad φ v = cqSepQuad φ (a • u + b • v)
      + a * b * cqSepQuad φ (u - v) := by
  have hlin : ∀ n, φ n (a • u + b • v) = a * φ n u + b * φ n v := by
    intro n
    rw [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
      smul_eq_mul, smul_eq_mul]
  have hsub : ∀ n, φ n (u - v) = φ n u - φ n v := fun n => map_sub _ _ _
  have hsu := cqSepQuad_summable φ hφ u
  have hsv := cqSepQuad_summable φ hφ v
  have hsm := cqSepQuad_summable φ hφ (a • u + b • v)
  have hsd := cqSepQuad_summable φ hφ (u - v)
  have hterm : ∀ n, a * (((1 / 2 : ℝ) ^ n) * (φ n u) ^ 2)
        + b * (((1 / 2 : ℝ) ^ n) * (φ n v) ^ 2)
      = ((1 / 2 : ℝ) ^ n) * (φ n (a • u + b • v)) ^ 2
        + a * b * (((1 / 2 : ℝ) ^ n) * (φ n (u - v)) ^ 2) := by
    intro n
    have k := cq_scalar_combo a b hab (φ n u) (φ n v)
    calc a * ((1 / 2 : ℝ) ^ n * (φ n u) ^ 2) + b * ((1 / 2 : ℝ) ^ n * (φ n v) ^ 2)
        = ((1 / 2 : ℝ) ^ n) * (a * (φ n u) ^ 2 + b * (φ n v) ^ 2) := by ring
      _ = ((1 / 2 : ℝ) ^ n)
          * ((a * φ n u + b * φ n v) ^ 2 + a * b * (φ n u - φ n v) ^ 2) := by
        rw [k]
      _ = ((1 / 2 : ℝ) ^ n) * (φ n (a • u + b • v)) ^ 2
          + a * b * (((1 / 2 : ℝ) ^ n) * (φ n (u - v)) ^ 2) := by
        rw [← hlin n, ← hsub n]
        ring
  have hsum := tsum_congr (L := SummationFilter.unconditional ℕ) hterm
  have eL : (∑' n, (a * (((1 / 2 : ℝ) ^ n) * (φ n u) ^ 2)
        + b * (((1 / 2 : ℝ) ^ n) * (φ n v) ^ 2)))
      = a * cqSepQuad φ u + b * cqSepQuad φ v := by
    unfold cqSepQuad
    rw [Summable.tsum_add (hsu.mul_left a) (hsv.mul_left b)]
    rw [Summable.tsum_mul_left _ hsu, Summable.tsum_mul_left _ hsv]
  have eR : (∑' n, (((1 / 2 : ℝ) ^ n) * (φ n (a • u + b • v)) ^ 2
        + a * b * (((1 / 2 : ℝ) ^ n) * (φ n (u - v)) ^ 2)))
      = cqSepQuad φ (a • u + b • v) + a * b * cqSepQuad φ (u - v) := by
    unfold cqSepQuad
    rw [Summable.tsum_add hsm (hsd.mul_left (a * b))]
    rw [Summable.tsum_mul_left _ hsd]
  rw [← eL, ← eR]
  exact hsum

/-- The quadratic form is strictly positive away from zero. -/
private theorem cqSepQuad_pos (φ : ℕ → StrongDual ℝ E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hsep : ∀ w : E, w ≠ 0 → ∃ n, φ n w ≠ 0) (w : E) (hw : w ≠ 0) :
    0 < cqSepQuad φ w := by
  obtain ⟨n, hn⟩ := hsep w hw
  have hsum := cqSepQuad_summable φ hφ w
  have hnn : ∀ m, 0 ≤ ((1 / 2 : ℝ) ^ m) * (φ m w) ^ 2 :=
    fun m => (cqSepQuad_term φ hφ w m).1
  have hpos : 0 < ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2 :=
    mul_pos (pow_pos (by norm_num) n) (pow_two_pos_of_ne_zero hn)
  have h := hsum.tsum_pos hnn n hpos
  simpa [cqSepQuad] using h

/-- The quadratic form is continuous on bounded sets. -/
private theorem cqSepQuad_continuousOn (φ : ℕ → StrongDual ℝ E)
    (hφ : ∀ n, ‖φ n‖ ≤ 1) {s : Set E} (hs : Bornology.IsBounded s) :
    ContinuousOn (cqSepQuad φ) s := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  set S : ℝ := max R 0 with hSdef
  have hS0 : 0 ≤ S := le_max_right _ _
  have hRS : s ⊆ Metric.closedBall 0 S := by
    intro w hw
    have h1 := hR hw
    rw [Metric.mem_closedBall] at h1 ⊢
    exact le_trans h1 (le_max_left _ _)
  have hcont : ∀ n, ContinuousOn (fun w => ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2) s := by
    intro n
    exact continuousOn_const.mul (((φ n).continuous.pow 2).continuousOn)
  have hsum : Summable (fun n => ((1 / 2 : ℝ) ^ n) * S ^ 2) :=
    summable_geometric_two.mul_right _
  have hbound : ∀ n w, w ∈ s → ‖((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2‖
      ≤ ((1 / 2 : ℝ) ^ n) * S ^ 2 := by
    intro n w hw
    have hmem := hRS hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    have hwnorm : ‖w‖ ≤ S := by simpa using hmem
    have hsq : (φ n w) ^ 2 ≤ S ^ 2 := by
      have h1 := abs_le.mp (cqSepQuad_abs_le φ hφ w n)
      have h2 : (φ n w) ^ 2 ≤ ‖w‖ ^ 2 := sq_le_sq' h1.1 h1.2
      exact le_trans h2 (pow_le_pow_left₀ (norm_nonneg w) hwnorm 2)
    rw [norm_mul, Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  change ContinuousOn (fun w => ∑' n, ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2) s
  exact continuousOn_tsum hcont hsum hbound

/-- Membership constructor for the majorant set. -/
private theorem cqMajorants_mk {K : Set E} {x : E} {g : C(K, ℝ)} {t : ℝ}
    {φ : StrongDual ℝ E} {c : ℝ}
    (hbound : ∀ y : K, g y ≤ φ y + c) (heq : t = φ x + c) :
    t ∈ cqMajorants K x g :=
  ⟨φ, c, hbound, heq⟩

/-- Membership destructor for the majorant set. -/
private theorem cqMajorants_get {K : Set E} {x : E} {g : C(K, ℝ)} {t : ℝ}
    (ht : t ∈ cqMajorants K x g) :
    ∃ φ : StrongDual ℝ E, ∃ c : ℝ, (∀ y : K, g y ≤ φ y + c) ∧ t = φ x + c := ht

/-- The majorant set is nonempty over a compact space. -/
private theorem cqMajorants_nonempty (K : Set E) (x : E) (g : C(K, ℝ))
    [CompactSpace K] : (cqMajorants K x g).Nonempty := by
  refine ⟨‖g‖, cqMajorants_mk (φ := 0) (c := ‖g‖) ?_ ?_⟩
  · intro y
    have h := ContinuousMap.norm_coe_le_norm g y
    rw [Real.norm_eq_abs] at h
    simp only [zero_apply, zero_add]
    exact le_trans (le_abs_self _) h
  · simp

/-- The majorant set is bounded below. -/
private theorem cqMajorants_bddBelow (K : Set E) (x : E) (hx : x ∈ K)
    (g : C(K, ℝ)) : BddBelow (cqMajorants K x g) := by
  refine ⟨g ⟨x, hx⟩, ?_⟩
  intro t ht
  obtain ⟨φ, c, hbound, rfl⟩ := cqMajorants_get ht
  exact hbound ⟨x, hx⟩

/-- The envelope dominates the value at `x`. -/
private theorem cqEnv_lower (K : Set E) (x : E) (hx : x ∈ K) (g : C(K, ℝ))
    [CompactSpace K] : g ⟨x, hx⟩ ≤ cqEnv K x g := by
  unfold cqEnv
  apply le_csInf (cqMajorants_nonempty K x g)
  intro t ht
  obtain ⟨φ, c, hbound, rfl⟩ := cqMajorants_get ht
  exact hbound ⟨x, hx⟩

/-- The envelope is bounded by any majorant value. -/
private theorem cqEnv_le (K : Set E) (x : E) (hx : x ∈ K) (g : C(K, ℝ))
    [CompactSpace K] (φ : StrongDual ℝ E) (c : ℝ)
    (hbound : ∀ y : K, g y ≤ φ y + c) : cqEnv K x g ≤ φ x + c := by
  unfold cqEnv
  exact csInf_le (cqMajorants_bddBelow K x hx g) (cqMajorants_mk hbound rfl)

/-- The envelope of zero is zero. -/
private theorem cqEnv_zero (K : Set E) (x : E) (hx : x ∈ K) [CompactSpace K] :
    cqEnv K x 0 = 0 := by
  apply le_antisymm
  · have hle : cqEnv K x 0 ≤ (0 : StrongDual ℝ E) x + 0 :=
      cqEnv_le K x hx 0 0 0 (by intro y; simp)
    simpa using hle
  · have h := cqEnv_lower K x hx (0 : C(K, ℝ))
    simpa using h

/-- Epsilon squeeze for real inequalities. -/
private theorem cq_le_of_forall_pos_le_add {a b : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → a ≤ b + δ) : a ≤ b := by
  by_contra hne
  have hlt : b < a := lt_of_not_ge hne
  have h2 := h ((a - b) / 2) (by linarith)
  linarith

/-- Sums of majorants majorize the sum. -/
private theorem cqMajorants_add_subset (K : Set E) (x : E) (g h : C(K, ℝ)) :
    cqMajorants K x g + cqMajorants K x h ⊆ cqMajorants K x (g + h) := by
  intro t ht
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp ht
  obtain ⟨φ₁, c₁, hb₁, e₁⟩ := cqMajorants_get ha
  obtain ⟨φ₂, c₂, hb₂, e₂⟩ := cqMajorants_get hb
  refine cqMajorants_mk (φ := φ₁ + φ₂) (c := c₁ + c₂) ?_ ?_
  · intro y
    have hle := add_le_add (hb₁ y) (hb₂ y)
    simp only [ContinuousMap.add_apply, add_apply]
    linarith
  · rw [e₁, e₂, add_apply]
    ring

/-- The envelope is subadditive. -/
private theorem cqEnv_add_le (K : Set E) (x : E) (hx : x ∈ K) (g h : C(K, ℝ))
    [CompactSpace K] : cqEnv K x (g + h) ≤ cqEnv K x g + cqEnv K x h := by
  unfold cqEnv
  apply cq_le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨u, huM, hu⟩ := exists_lt_of_csInf_lt (cqMajorants_nonempty K x g)
    (lt_add_of_pos_right _ (half_pos hδ))
  obtain ⟨v, hvM, hv⟩ := exists_lt_of_csInf_lt (cqMajorants_nonempty K x h)
    (lt_add_of_pos_right _ (half_pos hδ))
  have hmem : u + v ∈ cqMajorants K x (g + h) :=
    cqMajorants_add_subset K x g h (Set.add_mem_add huM hvM)
  have hle := csInf_le (cqMajorants_bddBelow K x hx (g + h)) hmem
  linarith

/-- Scaling majorants by a positive constant. -/
private theorem cqMajorants_smul (K : Set E) (x : E) (g : C(K, ℝ)) {c : ℝ}
    (hc : 0 < c) : cqMajorants K x (c • g) = c • cqMajorants K x g := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  ext t
  rw [Set.mem_smul_set]
  constructor
  · intro ht
    obtain ⟨φ, c', hbound, rfl⟩ := cqMajorants_get ht
    refine ⟨(c⁻¹ • φ) x + c⁻¹ * c', cqMajorants_mk ?_ rfl, ?_⟩
    · intro y
      have h := hbound y
      simp only [ContinuousMap.smul_apply, smul_eq_mul] at h
      have hnn : (0 : ℝ) ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
      have h2 := mul_le_mul_of_nonneg_left h hnn
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at h2
      have e : (c⁻¹ • φ) (↑y : E) + c⁻¹ * c' = c⁻¹ * (φ ↑y + c') := by
        have r : (c⁻¹ • φ) (↑y : E) = c⁻¹ • φ ↑y := rfl
        rw [r, smul_eq_mul]
        ring
      rw [e]
      exact h2
    · have r : (c⁻¹ • φ) (x : E) = c⁻¹ * φ x := by
        have r0 : (c⁻¹ • φ) (x : E) = c⁻¹ • φ x := rfl
        rwa [smul_eq_mul] at r0
      have e1 : c * (c⁻¹ * φ x) = φ x := by
        rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      have e2 : c * (c⁻¹ * c') = c' := by
        rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      rw [smul_eq_mul, r, mul_add, e1, e2]
  · intro ht
    obtain ⟨s, hsM, hcs⟩ := ht
    obtain ⟨ψ, d, hbound, rfl⟩ := cqMajorants_get hsM
    refine cqMajorants_mk (φ := c • ψ) (c := c * d) ?_ ?_
    · intro y
      have h := hbound y
      have h2 := mul_le_mul_of_nonneg_left h hc.le
      have e : (c • ψ) (↑y : E) + c * d = c * (ψ ↑y + d) := by
        have r : (c • ψ) (↑y : E) = c • ψ ↑y := rfl
        rw [r, smul_eq_mul]
        ring
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      rw [e]
      exact h2
    · rw [← hcs]
      have r : (c • ψ) (x : E) = c * ψ x := by
        have r0 : (c • ψ) (x : E) = c • ψ x := rfl
        rwa [smul_eq_mul] at r0
      rw [smul_eq_mul, r, mul_add]

/-- The envelope is positively homogeneous. -/
private theorem cqEnv_smul_of_pos (K : Set E) (x : E) (g : C(K, ℝ)) {c : ℝ}
    (hc : 0 < c) [CompactSpace K] :
    cqEnv K x (c • g) = c * cqEnv K x g := by
  have h := Real.sInf_smul_of_nonneg hc.le (cqMajorants K x g)
  unfold cqEnv
  rw [cqMajorants_smul K x g hc, h, smul_eq_mul]

/-- Scaling inequality for arbitrary real scalars. -/
private theorem cqEnv_smul_le (K : Set E) (x : E) (hx : x ∈ K) (g : C(K, ℝ))
    [CompactSpace K] (c : ℝ) : c * cqEnv K x g ≤ cqEnv K x (c • g) := by
  rcases lt_trichotomy c 0 with hneg | rfl | hpos
  · have h1 := cqEnv_add_le K x hx (c • g) ((-c) • g)
    have h2 := cqEnv_smul_of_pos K x g (by linarith : (0 : ℝ) < -c)
    have h3 : (c • g + (-c) • g : C(K, ℝ)) = 0 := by
      ext y
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
        ContinuousMap.zero_apply]
      ring
    rw [h3, cqEnv_zero K x hx, h2] at h1
    linarith
  · rw [zero_mul]
    have h0 : ((0 : ℝ) • g : C(K, ℝ)) = 0 := by simp
    rw [h0, cqEnv_zero K x hx]
  · rw [cqEnv_smul_of_pos K x g hpos]

/-- Hahn-Banach extension dominated by the envelope. -/
private theorem cq_exists_linear_le_cqEnv (K : Set E) (x : E) (hx : x ∈ K)
    (f : C(K, ℝ)) [CompactSpace K] :
    ∃ L : C(K, ℝ) →ₗ[ℝ] ℝ, (∀ g, L g ≤ cqEnv K x g) ∧ L f = cqEnv K x f := by
  have H : ∀ c : ℝ, c • f = 0 → (RingHom.id ℝ) c • cqEnv K x f = 0 := by
    intro c hc
    simp only [RingHom.id_apply]
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have h1 : f = 0 := by
        have h1 : c⁻¹ • (c • f) = c⁻¹ • (0 : C(K, ℝ)) := by rw [hc]
        rwa [← mul_smul, inv_mul_cancel₀ hc0, one_smul, smul_zero] at h1
      rw [h1, cqEnv_zero K x hx]
      exact smul_zero c
  have hdom : ∀ z : (LinearPMap.mkSpanSingleton' f (cqEnv K x f) H).domain,
      (LinearPMap.mkSpanSingleton' f (cqEnv K x f) H) z ≤ cqEnv K x ↑z := by
    intro z
    obtain ⟨w, hw⟩ := z
    rw [LinearPMap.domain_mkSpanSingleton] at hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [LinearPMap.mkSpanSingleton'_apply]
    exact cqEnv_smul_le K x hx f c
  obtain ⟨L, hLext, hLle⟩ := exists_extension_of_le_sublinear
    (LinearPMap.mkSpanSingleton' f (cqEnv K x f) H)
    (fun g => cqEnv K x g)
    (fun c hc g => cqEnv_smul_of_pos K x g hc)
    (fun g h => cqEnv_add_le K x hx g h)
    hdom
  have hfmem : f ∈ (LinearPMap.mkSpanSingleton' f (cqEnv K x f) H).domain := by
    rw [LinearPMap.domain_mkSpanSingleton]
    exact Submodule.mem_span_singleton_self f
  have hLf : L f = cqEnv K x f := by
    have heq := hLext ⟨f, hfmem⟩
    have hself := LinearPMap.mkSpanSingleton'_apply_self f (cqEnv K x f) H hfmem
    exact heq.trans hself
  exact ⟨L, fun g => hLle g, hLf⟩

/-- Pointwise values of the affine function. -/
private theorem cqAffine_apply (K : Set E) (φ : StrongDual ℝ E) (c : ℝ) (y : K) :
    cqAffine K φ c y = φ y + c := rfl

/-- The functional agrees with every affine function at `x`. -/
private theorem cqFunctional_affine (K : Set E) (x : E) (hx : x ∈ K)
    (L : C(K, ℝ) →ₗ[ℝ] ℝ) (hL : ∀ g, L g ≤ cqEnv K x g)
    (φ : StrongDual ℝ E) (c : ℝ) [CompactSpace K] :
    L (cqAffine K φ c) = φ x + c := by
  apply le_antisymm
  · exact le_trans (hL _) (cqEnv_le K x hx _ φ c (fun y => by rw [cqAffine_apply]))
  · have h1 := hL (-(cqAffine K φ c))
    have h2 : cqEnv K x (-(cqAffine K φ c)) ≤ -φ x + -c := by
      apply cqEnv_le K x hx _ (-φ) (-c)
      intro y
      rw [ContinuousMap.neg_apply, cqAffine_apply, neg_apply, neg_add]
    have h3 : L (-(cqAffine K φ c)) = -L (cqAffine K φ c) := map_neg L _
    linarith

/-- The functional is monotone. -/
private theorem cqFunctional_mono (K : Set E) (x : E) (hx : x ∈ K)
    (L : C(K, ℝ) →ₗ[ℝ] ℝ) (hL : ∀ g, L g ≤ cqEnv K x g)
    (g h : C(K, ℝ)) (hle : ∀ y, g y ≤ h y) [CompactSpace K] :
    L g ≤ L h := by
  have hsub : L (g - h) = L g - L h := map_sub L g h
  have hle2 : L (g - h) ≤ 0 := by
    have h1 := hL (g - h)
    have h2 : cqEnv K x (g - h) ≤ 0 := by
      have h0 : cqEnv K x (g - h) ≤ (0 : StrongDual ℝ E) x + 0 :=
        cqEnv_le K x hx _ 0 0 (by
          intro y
          have hy := hle y
          simp only [ContinuousMap.sub_apply, zero_apply, zero_add]
          exact sub_nonpos.mpr hy)
      simpa using h0
    linarith
  linarith

/-- The functional sends one to one. -/
private theorem cqFunctional_one (K : Set E) (x : E) (hx : x ∈ K)
    (L : C(K, ℝ) →ₗ[ℝ] ℝ) (hL : ∀ g, L g ≤ cqEnv K x g)
    [CompactSpace K] : L 1 = 1 := by
  have h : (1 : C(K, ℝ)) = cqAffine K 0 1 := by
    apply ContinuousMap.ext
    intro y
    simp [cqAffine_apply]
  rw [h]
  have hval := cqFunctional_affine K x hx L hL 0 1
  simpa using hval

/-- Riesz-Markov-Kakutani for a monotone unital functional on a compact space. -/
private theorem cq_exists_measure_of_monotone
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (L : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hmono : ∀ g h : C(X, ℝ), (∀ x, g x ≤ h x) → L g ≤ L h)
    (hone : L 1 = 1) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      ∀ g : C(X, ℝ), ∫ x, g x ∂μ = L g := by
  have eadd : ∀ g h : C_c(X, ℝ), (g + h).toContinuousMap
      = g.toContinuousMap + h.toContinuousMap := by
    intro g h
    apply ContinuousMap.ext
    intro z
    rfl
  have esmul : ∀ (a : ℝ) (g : C_c(X, ℝ)), (a • g).toContinuousMap
      = a • g.toContinuousMap := by
    intro a g
    apply ContinuousMap.ext
    intro z
    rfl
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun g => L g.toContinuousMap
      map_add' := fun g h => by
        change L ((g + h).toContinuousMap) = L g.toContinuousMap + L h.toContinuousMap
        rw [eadd, map_add]
      map_smul' := fun a g => by
        change L ((a • g).toContinuousMap) = a • L g.toContinuousMap
        rw [esmul, map_smulₛₗ, RingHom.id_apply]
      monotone' := fun g h hgh => by
        change L g.toContinuousMap ≤ L h.toContinuousMap
        refine hmono _ _ fun z => ?_
        exact CompactlySupportedContinuousMap.le_def.mp hgh z }
  have hΛ : ∀ g : C_c(X, ℝ), Λ g = L g.toContinuousMap := fun g => rfl
  have hint : ∀ g : C(X, ℝ), ∫ x, g x ∂(RealRMK.rieszMeasure Λ) = L g := by
    intro g
    let g' : C_c(X, ℝ) :=
      { toFun := g
        hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
    have h := RealRMK.integral_rieszMeasure Λ g'
    rw [hΛ] at h
    have egt : g'.toContinuousMap = g := by
      apply ContinuousMap.ext
      intro z
      rfl
    rw [egt] at h
    exact h
  refine ⟨RealRMK.rieszMeasure Λ, ?_, hint⟩
  rw [MeasureTheory.isProbabilityMeasure_iff_real]
  have h1 := hint 1
  simp only [ContinuousMap.one_apply] at h1
  rw [MeasureTheory.integral_const, smul_eq_mul, mul_one, hone] at h1
  exact h1

/-- Representing probability measure on the subtype. -/
private theorem cq_exists_measure_subtype (K : Set E) (x : E) (hx : x ∈ K)
    (f : C(K, ℝ)) [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] :
    ∃ μK : Measure K, IsProbabilityMeasure μK ∧
      (∀ φ : StrongDual ℝ E, ∀ c : ℝ, ∫ y, cqAffine K φ c y ∂μK = φ x + c) ∧
        ∫ y, f y ∂μK = cqEnv K x f := by
  obtain ⟨L, hLle, hLf⟩ := cq_exists_linear_le_cqEnv K x hx f
  have hmono : ∀ g h : C(K, ℝ), (∀ y, g y ≤ h y) → L g ≤ L h :=
    fun g h hgh => cqFunctional_mono K x hx L hLle g h hgh
  have hone : L 1 = 1 := cqFunctional_one K x hx L hLle
  obtain ⟨μK, hprob, hint⟩ := cq_exists_measure_of_monotone L hmono hone
  refine ⟨μK, hprob, ?_, ?_⟩
  · intro φ c
    calc ∫ y, cqAffine K φ c y ∂μK = L (cqAffine K φ c) := hint _
      _ = φ x + c := cqFunctional_affine K x hx L hLle φ c
  · calc ∫ y, f y ∂μK = L f := hint _
      _ = cqEnv K x f := hLf

/-- Uniform gap at a non-extreme point. -/
private theorem cq_gap_of_not_mem_extremePoints
    (q : E → ℝ)
    (hqcombo : ∀ u v : E, ∀ a b : ℝ, a + b = 1 →
      a * q u + b * q v = q (a • u + b • v) + a * b * q (u - v))
    (hqpos : ∀ w : E, w ≠ 0 → 0 < q w)
    {K : Set E} {y : E} (hy : y ∈ K) (hyext : y ∉ extremePoints ℝ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : StrongDual ℝ E, ∀ c : ℝ,
      (∀ z ∈ K, q z ≤ φ z + c) → q y + δ ≤ φ y + c := by
  rw [mem_extremePoints] at hyext
  push Not at hyext
  obtain ⟨x₁, hx₁, x₂, hx₂, hseg, hne⟩ := hyext hy
  obtain ⟨a, b, ha, hb, hab, hyeq⟩ := hseg
  have h12 : x₁ ≠ x₂ := by
    rintro rfl
    have e : (a + b) • x₁ = y := by
      rw [add_smul]
      exact hyeq
    rw [hab, one_smul] at e
    exact (hne e) e
  have hδpos : (0 : ℝ) < a * b * q (x₁ - x₂) :=
    mul_pos (mul_pos ha hb) (hqpos _ (sub_ne_zero.mpr h12))
  refine ⟨a * b * q (x₁ - x₂), hδpos, fun φ c hbound => ?_⟩
  have h1 := hbound x₁ hx₁
  have h2 := hbound x₂ hx₂
  have hcombo := hqcombo x₁ x₂ a b hab
  rw [hyeq] at hcombo
  have hφy : φ y = a * φ x₁ + b * φ x₂ := by
    conv_lhs => rw [← hyeq]
    rw [map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
      smul_eq_mul, smul_eq_mul]
  have hle : a * q x₁ + b * q x₂ ≤ a * (φ x₁ + c) + b * (φ x₂ + c) :=
    add_le_add (mul_le_mul_of_nonneg_left h1 ha.le)
      (mul_le_mul_of_nonneg_left h2 hb.le)
  have heq2 : a * (φ x₁ + c) + b * (φ x₂ + c) = φ y + c := by
    have hcc : a * c + b * c = c := by
      rw [← add_mul, hab, one_mul]
    rw [hφy]
    linear_combination hcc
  linarith

/-- A null set for a uniform positive gap. -/
private theorem cq_measure_uniform_gap_eq_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {g : ℕ → X → ℝ}
    (hint : ∀ k, Integrable (g k) μ)
    (hnn : ∀ k y, 0 ≤ g k y)
    (hsmall : ∀ k, ∫ y, g k y ∂μ ≤ 1 / ((k : ℝ) + 1)) :
    μ {y | ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ g k y} = 0 := by
  have key : ∀ m : ℕ, μ {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y} = 0 := by
    intro m
    have hR0 : μ.real {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y} ≤ 0 := by
      by_contra hcon
      have hpos : 0 < μ.real {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y} :=
        lt_of_not_ge hcon
      have hP : (0 : ℝ) < (1 / ((m : ℝ) + 1))
          * μ.real {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y} :=
        mul_pos (by positivity) hpos
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hP
      have hsub : {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y}
          ⊆ {y | (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y} := fun y hy => hy k
      have hmonoR := MeasureTheory.measureReal_mono hsub
        (MeasureTheory.measure_ne_top μ _)
      have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall (hnn k)) (hint k) (1 / ((m : ℝ) + 1))
      have hle : (1 / ((m : ℝ) + 1))
          * μ.real {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y}
          ≤ 1 / ((k : ℝ) + 1) :=
        le_trans (mul_le_mul_of_nonneg_left hmonoR (by positivity))
          (le_trans hmarkov (hsmall k))
      linarith
    exact (MeasureTheory.measureReal_eq_zero_iff
      (MeasureTheory.measure_ne_top μ _)).mp (le_antisymm hR0 measureReal_nonneg)
  have hsubU : {y | ∃ δ : ℝ, 0 < δ ∧ ∀ k, δ ≤ g k y}
      ⊆ ⋃ (m : ℕ), {y | ∀ k, (1 : ℝ) / ((m : ℝ) + 1) ≤ g k y} := by
    intro y hy
    obtain ⟨δ, hδ, hδk⟩ := hy
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    exact Set.mem_iUnion.mpr ⟨m, fun k => le_trans hm.le (hδk k)⟩
  exact MeasureTheory.measure_mono_null hsubU
    (MeasureTheory.measure_iUnion_null key)

/-- A countable norm-bounded separating family of functionals. -/
private theorem cq_exists_seq_strongDual_separating [TopologicalSpace.SeparableSpace E]
    [Nonempty E] :
    ∃ φ : ℕ → StrongDual ℝ E, (∀ n, ‖φ n‖ ≤ 1) ∧
      ∀ w : E, w ≠ 0 → ∃ n, φ n w ≠ 0 := by
  choose g hg_norm hg_val using
    fun n => exists_dual_vector'' ℝ (TopologicalSpace.denseSeq E n)
  refine ⟨g, hg_norm, fun w hw => ?_⟩
  have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨n, hn⟩ :=
    DenseRange.exists_dist_lt (TopologicalSpace.denseRange_denseSeq E) w (half_pos hwpos)
  refine ⟨n, ?_⟩
  rw [dist_eq_norm] at hn
  have hle : ‖g n (TopologicalSpace.denseSeq E n - w)‖
      ≤ ‖TopologicalSpace.denseSeq E n - w‖ := by
    have h2 := (g n).le_opNorm (TopologicalSpace.denseSeq E n - w)
    have h3 := mul_le_mul_of_nonneg_right (hg_norm n)
      (norm_nonneg (TopologicalSpace.denseSeq E n - w))
    rw [one_mul] at h3
    exact le_trans h2 h3
  have habs : |g n (TopologicalSpace.denseSeq E n - w)|
      ≤ ‖TopologicalSpace.denseSeq E n - w‖ := by
    rwa [Real.norm_eq_abs] at hle
  have hval : g n (TopologicalSpace.denseSeq E n) = ‖TopologicalSpace.denseSeq E n‖ := by
    simpa using hg_val n
  have hdecomp : g n w = g n (TopologicalSpace.denseSeq E n)
      - g n (TopologicalSpace.denseSeq E n - w) := by
    rw [← map_sub]
    congr 1
    abel
  have hgap : (0 : ℝ) < ‖TopologicalSpace.denseSeq E n‖
      - ‖TopologicalSpace.denseSeq E n - w‖ := by
    have h := norm_sub_norm_le w (TopologicalSpace.denseSeq E n)
    rw [norm_sub_rev] at h
    rw [norm_sub_rev] at hn
    linarith
  have hpos : (0 : ℝ) < g n w := by
    rw [hdecomp, hval]
    linarith [le_trans (le_abs_self _) habs]
  exact ne_of_gt hpos

/-- Non-extreme points of `K` form a null set for the representing measure. -/
private theorem cq_measure_nonextreme_null (K : Set E) (x : E)
    (φ : ℕ → StrongDual ℝ E) (hφ : ∀ n, ‖φ n‖ ≤ 1)
    (hsep : ∀ w : E, w ≠ 0 → ∃ n, φ n w ≠ 0)
    (f : C(K, ℝ)) (hf : ∀ y : K, f y = cqSepQuad φ y)
    [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μK : Measure K) [IsProbabilityMeasure μK]
    (haff : ∀ ψ : StrongDual ℝ E, ∀ c : ℝ, ∫ y, cqAffine K ψ c y ∂μK = ψ x + c)
    (henv : ∫ y, f y ∂μK = cqEnv K x f) :
    μK {y : K | (y : E) ∉ extremePoints ℝ K} = 0 := by
  have hseq : ∀ k : ℕ, ∃ ψ : StrongDual ℝ E, ∃ c : ℝ,
      (∀ y : K, f y ≤ ψ y + c) ∧ ψ x + c < cqEnv K x f + 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨t, htM, hlt⟩ := exists_lt_of_csInf_lt (cqMajorants_nonempty K x f)
      (lt_add_of_pos_right _ hpos)
    obtain ⟨ψ, c, hbound, rfl⟩ := cqMajorants_get htM
    exact ⟨ψ, c, hbound, hlt⟩
  choose ψ c hbound hval using hseq
  have hnn : ∀ k (y : K), 0 ≤ (cqAffine K (ψ k) (c k) - f) y := by
    intro k y
    have h := hbound k y
    simp only [ContinuousMap.sub_apply, cqAffine_apply]
    linarith
  have hint : ∀ k, Integrable (fun y => (cqAffine K (ψ k) (c k) - f) y) μK := by
    intro k
    exact (BoundedContinuousFunction.mkOfCompact (cqAffine K (ψ k) (c k) - f)).integrable μK
  have hsmall : ∀ k, ∫ y, (cqAffine K (ψ k) (c k) - f) y ∂μK
      ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have h1 : Integrable (fun y => cqAffine K (ψ k) (c k) y) μK :=
      (BoundedContinuousFunction.mkOfCompact _).integrable μK
    have h2 : Integrable (fun y => f y) μK :=
      (BoundedContinuousFunction.mkOfCompact _).integrable μK
    have heq : ∫ y, (cqAffine K (ψ k) (c k) - f) y ∂μK
        = ψ k x + c k - cqEnv K x f := by
      simp only [ContinuousMap.sub_apply]
      rw [integral_sub h1 h2, haff, henv]
    rw [heq]
    have h := hval k
    linarith
  have hnull : μK {y | ∃ δ : ℝ, 0 < δ
      ∧ ∀ k, δ ≤ (cqAffine K (ψ k) (c k) - f) y} = 0 :=
    cq_measure_uniform_gap_eq_zero
      (g := fun k y => (cqAffine K (ψ k) (c k) - f) y) hint hnn hsmall
  refine MeasureTheory.measure_mono_null ?_ hnull
  intro y hy
  obtain ⟨δ, hδ, hgap⟩ := cq_gap_of_not_mem_extremePoints (cqSepQuad φ)
    (fun u v a b hab => cqSepQuad_combo φ hφ u v a b hab)
    (fun w hw => cqSepQuad_pos φ hφ hsep w hw)
    y.property hy
  refine ⟨δ, hδ, fun k => ?_⟩
  have hcond : ∀ z ∈ K, cqSepQuad φ z ≤ (ψ k) z + c k := by
    intro z hz
    have h1 := hbound k ⟨z, hz⟩
    rwa [hf ⟨z, hz⟩] at h1
  have hle := hgap (ψ k) (c k) hcond
  rw [← hf y] at hle
  simp only [ContinuousMap.sub_apply, cqAffine_apply]
  linarith

/-- Weak characterization of the Bochner barycenter. -/
private theorem cq_integral_eq_of_forall_dual
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {v : X → E} [CompleteSpace E] (hv : Integrable v ν) (x : E)
    (h : ∀ φ : StrongDual ℝ E, ∫ y, φ (v y) ∂ν = φ x) :
    ∫ y, v y ∂ν = x := by
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  rw [← h φ]
  exact (φ.integral_comp_comm hv).symm

end MathlibExt.Analysis.Convex.ChoquetWanted

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Analysis.Convex.ChoquetWanted

/--
**Choquet representation for compact sets.** Let $E$ be a second-countable real Banach space
with its Borel σ-algebra and let $K \subseteq E$ be compact. For every $x \in K$ there is a
probability measure $\mu$ on $E$ such that the set $\operatorname{ext} K$ of extreme points of
$K$ has $\mu(\operatorname{ext} K) = 1$, the identity map $y \mapsto y$ is Bochner integrable
for $\mu$, and $\int_E y \, d\mu(y) = x$.

Neither convexity nor nonemptiness of $K$ is assumed; Choquet's theorem for nonempty compact
convex sets is the special case.
-/
public theorem choquet_representation_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {K : Set E} (hKCompact : IsCompact K) {x : E} (hx : x ∈ K) :
    ∃ (μ : ProbabilityMeasure E),
      (μ : Measure E) (Set.extremePoints ℝ K) = 1 ∧
        Integrable (fun y : E => y) (μ : Measure E) ∧
          MeasureTheory.integral (μ : Measure E) (fun y : E => y) = x := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKCompact
  have : Nonempty E := ⟨x⟩
  obtain ⟨φ, hφ, hsep⟩ := cq_exists_seq_strongDual_separating (E := E)
  have hcont : ContinuousOn (cqSepQuad φ) K :=
    cqSepQuad_continuousOn φ hφ hKCompact.isBounded
  have hfbund : ∃ f : C(K, ℝ), ∀ y : K, f y = cqSepQuad φ y :=
    ⟨⟨K.domRestrict (cqSepQuad φ), hcont.domRestrict⟩, fun y => rfl⟩
  obtain ⟨f, hfq⟩ := hfbund
  obtain ⟨μK, hprob, haff, henv⟩ := cq_exists_measure_subtype K x hx f
  have hnull : μK {y : K | (y : E) ∉ extremePoints ℝ K} = 0 :=
    cq_measure_nonextreme_null K x φ hφ hsep f hfq μK haff henv
  have hvint : Integrable (fun y : K => (y : E)) μK :=
    (BoundedContinuousFunction.mkOfCompact
      (⟨Subtype.val, continuous_subtype_val⟩ : C(K, E))).integrable μK
  have hbary : ∫ y : K, (y : E) ∂μK = x := by
    apply cq_integral_eq_of_forall_dual hvint x
    intro ψ
    show ∫ y : K, ψ (y : E) ∂μK = ψ x
    have e : (fun y : K => ψ (y : E)) = fun y => cqAffine K ψ 0 y := by
      funext y
      simp [cqAffine_apply]
    rw [e, haff ψ 0, add_zero]
  have hKmeas : MeasurableSet K := hKCompact.isClosed.measurableSet
  have emb : MeasurableEmbedding ((↑) : K → E) :=
    MeasurableEmbedding.subtype_coe hKmeas
  have hcompl : ((((↑) : K → E) ⁻¹' extremePoints ℝ K))ᶜ
      = {y : K | (y : E) ∉ extremePoints ℝ K} := by
    ext y
    simp
  refine ⟨⟨μK.map ((↑) : K → E), inferInstance⟩, ?_, ?_, ?_⟩
  · rw [MeasureTheory.ProbabilityMeasure.coe_mk, emb.map_apply]
    have h1 : μK univ = 1 := IsProbabilityMeasure.measure_univ
    have hA : μK ((((↑) : K → E) ⁻¹' extremePoints ℝ K))ᶜ = 0 := by
      rw [hcompl]
      exact hnull
    have hle1 : (1 : ENNReal) ≤ μK ((↑) ⁻¹' extremePoints ℝ K) := by
      calc (1 : ENNReal) = μK univ := h1.symm
        _ = μK (((↑) : K → E) ⁻¹' extremePoints ℝ K ∪
            ((((↑) : K → E) ⁻¹' extremePoints ℝ K))ᶜ) := by
          rw [Set.union_compl_self]
        _ ≤ μK ((↑) ⁻¹' extremePoints ℝ K) +
            μK ((((↑) : K → E) ⁻¹' extremePoints ℝ K))ᶜ :=
          MeasureTheory.measure_union_le _ _
        _ = μK ((↑) ⁻¹' extremePoints ℝ K) := by rw [hA, add_zero]
    exact le_antisymm MeasureTheory.prob_le_one hle1
  · rw [MeasureTheory.ProbabilityMeasure.coe_mk, emb.integrable_map_iff]
    exact hvint
  · rw [MeasureTheory.ProbabilityMeasure.coe_mk, emb.integral_map]
    exact hbary

/--
**Choquet's theorem.** Let $E$ be a second-countable real Banach space with its Borel σ-algebra
and let $K \subseteq E$ be a nonempty compact convex set. For every $x \in K$ there is a
probability measure $\mu$ on $E$ such that the set $\operatorname{ext} K$ of extreme points of
$K$ has $\mu(\operatorname{ext} K) = 1$, the identity map $y \mapsto y$ is Bochner integrable
for $\mu$, and $\int_E y \, d\mu(y) = x$.

Proves `Wanted` entry `choquet_representation`.

Source: G. Choquet,
Seminaire Bourbaki 1956 and Lectures 1962; Bishop-de Leeuw and Choquet-Bishop-de Leeuw integral
representation; Phelps, Lectures on Choquet's Theorem, 1966; Lean states compact-source
specialization in second-countable real Banach space with `ProbabilityMeasure` carried by
`extremePoints` and Bochner integral barycenter.
-/
public theorem choquet_representation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {K : Set E} (hKCompact : IsCompact K) (hKConvex : Convex ℝ K)
    (hKNonempty : K.Nonempty)
    {x : E} (hx : x ∈ K) :
    ∃ (μ : ProbabilityMeasure E),
      (μ : Measure E) (Set.extremePoints ℝ K) = 1 ∧
        Integrable (fun y : E => y) (μ : Measure E) ∧
          MeasureTheory.integral (μ : Measure E) (fun y : E => y) = x :=
    choquet_representation_of_isCompact hKCompact hx

end MathlibExt.Analysis.Convex.ChoquetWanted
