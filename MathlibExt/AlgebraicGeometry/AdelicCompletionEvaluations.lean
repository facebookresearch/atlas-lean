/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RationalAdelicModelMetrics
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Native pointwise evaluation of the boundary Cauchy quotient

The logarithmic value is the actual real limit of a representative's
fibre norms. Boundary-null representatives have the same limit, so this
is a computed function on the original quotient. Its fibre norm is zero
at the zero vector and the exponential of that limit elsewhere.

Continuity and construction of a metrized line with these exact norms
are recorded separately. No second completion or unrelated metric
carrier is introduced.
Modelled on Yuan--Zhang, arXiv:2105.13587v9, Sections 2.5 and 3.4.
The completion is the fixed-gauge completion of `BoundaryMetricCompletionModels`, not
Yuan--Zhang's boundary topology: their adelic line bundles and positivity notions are not
claimed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations

open CategoryTheory _root_.AlgebraicGeometry Filter
open PlacewiseMetrizedLineModels BoundaryMetricCompletionModels
open scoped Topology

variable {K : Type} [Field K] {A : AdelicField K} {X : Over (Spec (.of K))}
  {L : X.left.Modules} (B : EffectiveBoundary A X)

abbrev Point (v : A.places) :=
  ValuedLineFibres.Point (A.completion v) (placeScheme A X v)

abbrev Vector (v : A.places) (p : Point (A := A) (X := X) v) :=
  ValuedLineFibres.Fibre (A.completion v) (placeScheme A X v) (placeLine A X L v) p

def sequenceLog (f : CauchySequence (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) : ℕ → ℝ :=
  fun n ↦ Real.log (norm (f.val n) v p z)

private theorem gauge_small {ε G : ℝ} (hε : 0 < ε) (hG : 0 ≤ G) :
    0 < ε / (G + 1) ∧ ε / (G + 1) * G < ε := by
  have h : 0 < G + 1 := by linarith
  refine ⟨div_pos hε h, ?_⟩
  calc
    ε / (G + 1) * G < ε / (G + 1) * (G + 1) :=
      mul_lt_mul_of_pos_left (by linarith) (div_pos hε h)
    _ = ε := div_mul_cancel₀ ε (ne_of_gt h)

theorem sequenceLog_cauchy (f : CauchySequence (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    CauchySeq (sequenceLog B f v p z) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  by_cases hz : z = 0
  · refine ⟨0, ?_⟩
    intro m hm n hn
    have h0 (i : ℕ) : norm (f.val i) v p z = 0 :=
      (norm_zero_iff _ _ _ _).mpr hz
    simpa [sequenceLog, h0] using hε
  · obtain ⟨hδ, hsmall⟩ := gauge_small hε (B.nonnegative v p)
    obtain ⟨N, hN⟩ := f.property _ hδ
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    exact (hN m n hm hn v p z hz).trans_lt hsmall

theorem equivalent_difference_tendsto (f g : CauchySequence (L := L) B)
    (h : Equivalent B f g) (v : A.places) (p : Point (A := A) (X := X) v)
    (z : Vector (L := L) v p) :
    Tendsto (fun n ↦ sequenceLog B f v p z n - sequenceLog B g v p z n)
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_cases hz : z = 0
  · refine ⟨0, ?_⟩
    intro n hn
    have hf : norm (f.val n) v p z = 0 := (norm_zero_iff _ _ _ _).mpr hz
    have hg : norm (g.val n) v p z = 0 := (norm_zero_iff _ _ _ _).mpr hz
    simpa [sequenceLog, hf, hg] using hε
  · obtain ⟨hδ, hsmall⟩ := gauge_small hε (B.nonnegative v p)
    obtain ⟨N, hN⟩ := h _ hδ
    refine ⟨N, ?_⟩
    intro n hn
    rw [Real.dist_eq, sub_zero]
    exact (hN n hn v p z hz).trans_lt hsmall

def representativeLog (f : CauchySequence (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) : ℝ :=
  limUnder atTop (sequenceLog B f v p z)

theorem representativeLog_congr (f g : CauchySequence (L := L) B)
    (h : Equivalent B f g) (v : A.places) (p : Point (A := A) (X := X) v)
    (z : Vector (L := L) v p) : representativeLog B f v p z =
      representativeLog B g v p z := by
  have hf := (sequenceLog_cauchy B f v p z).tendsto_limUnder
  have hg := (sequenceLog_cauchy B g v p z).tendsto_limUnder
  exact sub_eq_zero.mp (tendsto_nhds_unique (hf.sub hg)
    (equivalent_difference_tendsto B f g h v p z))

/-- Evaluation is on the exact quotient used by rational adelic model sequences. -/
def logNorm (m : BoundaryMetricCompletion (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) : ℝ :=
  Quotient.lift (fun f ↦ representativeLog B f v p z)
    (fun f g h ↦ representativeLog_congr B f g h v p z) m

/-- A representative converges to this same quotient evaluation. -/
theorem logNorm_tendsto (f : CauchySequence (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    Tendsto (sequenceLog B f v p z) atTop
      (𝓝 (logNorm B (Quotient.mk _ f) v p z)) :=
  (sequenceLog_cauchy B f v p z).tendsto_limUnder

/-- Scalar normalization survives the native Cauchy quotient. -/
theorem logNorm_smul (m : BoundaryMetricCompletion (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v)
    (a : ValuedLineFibres.CompletedResidue (A.completion v) (placeScheme A X v) p)
    (ha : a ≠ 0) (z : Vector (L := L) v p) (hz : z ≠ 0) :
    logNorm B m v p (a • z) = Real.log ‖a‖ + logNorm B m v p z := by
  refine Quotient.inductionOn m ?_
  intro f
  have heq : sequenceLog B f v p (a • z) =
      fun n ↦ Real.log ‖a‖ + sequenceLog B f v p z n := by
    funext n
    unfold sequenceLog
    change Real.log (((f.val n).metric v).fibreNorm p |>.norm (a • z)) = _
    rw [ValuedLineFibres.FibreNorm.homogeneous]
    exact Real.log_mul (norm_ne_zero_iff.mpr ha)
      (fun h ↦ hz ((norm_zero_iff _ _ _ _).mp h))
  have ht : Tendsto (sequenceLog B f v p (a • z)) atTop
      (𝓝 (Real.log ‖a‖ + logNorm B (Quotient.mk _ f) v p z)) := by
    rw [heq]
    exact tendsto_const_nhds.add (logNorm_tendsto B f v p z)
  exact tendsto_nhds_unique (logNorm_tendsto B f v p (a • z)) ht

def fibreNorm (m : BoundaryMetricCompletion (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) : ℝ := by
  classical
  exact if z = 0 then 0 else Real.exp (logNorm B m v p z)

theorem fibreNorm_nonnegative (m : BoundaryMetricCompletion (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    0 ≤ fibreNorm B m v p z := by
  unfold fibreNorm
  split_ifs
  · exact le_rfl
  · exact le_of_lt (Real.exp_pos _)

theorem fibreNorm_zero_iff (m : BoundaryMetricCompletion (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    fibreNorm B m v p z = 0 ↔ z = 0 := by
  unfold fibreNorm
  split_ifs with hz
  · simp [hz]
  · simp [hz, Real.exp_ne_zero]

/-- Actual representative norms converge to the same computed quotient norm. -/
theorem fibreNorm_tendsto (f : CauchySequence (L := L) B) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    Tendsto (fun n ↦ norm (f.val n) v p z) atTop
      (𝓝 (fibreNorm B (Quotient.mk _ f) v p z)) := by
  by_cases hz : z = 0
  · have hzero : (fun n ↦ norm (f.val n) v p z) = fun _ ↦ (0 : ℝ) := by
      funext n
      exact (norm_zero_iff _ _ _ _).mpr hz
    rw [hzero]
    simp [fibreNorm, hz]
  · have hpos (n : ℕ) : 0 < norm (f.val n) v p z := by
      exact lt_of_le_of_ne (((f.val n).metric v).fibreNorm p |>.nonnegative z)
        (fun h ↦ hz ((norm_zero_iff _ _ _ _).mp h.symm))
    have heq : (fun n ↦ Real.exp (sequenceLog B f v p z n)) =
        fun n ↦ norm (f.val n) v p z := by
      funext n
      exact Real.exp_log (hpos n)
    have ht := (logNorm_tendsto B f v p z).rexp
    rw [heq] at ht
    simpa [fibreNorm, hz] using ht

/-- Continuity is a construction result with every norm fixed to the computed limit. -/
structure Realization (m : BoundaryMetricCompletion (L := L) B) where
  metric : MetrizedLine A X L
  normalized : ∀ v p z, norm metric v p z = fibreNorm B m v p z

/-- The original metric has its literal constant Cauchy representative. -/
def constantSequence (N : MetrizedLine A X L) : CauchySequence (L := L) B :=
  ⟨fun _ ↦ N, by
    intro ε hε
    refine ⟨0, ?_⟩
    intro m n hm hn v p z hz
    simpa only [sub_self, abs_zero] using mul_nonneg (le_of_lt hε) (B.nonnegative v p)⟩

def constantClass (N : MetrizedLine A X L) : BoundaryMetricCompletion (L := L) B :=
  Quotient.mk _ (constantSequence B N)

theorem logNorm_constant (N : MetrizedLine A X L) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    logNorm B (constantClass B N) v p z = Real.log (norm N v p z) :=
  tendsto_nhds_unique (logNorm_tendsto B (constantSequence B N) v p z) tendsto_const_nhds

theorem fibreNorm_constant (N : MetrizedLine A X L) (v : A.places)
    (p : Point (A := A) (X := X) v) (z : Vector (L := L) v p) :
    fibreNorm B (constantClass B N) v p z = norm N v p z := by
  by_cases hz : z = 0
  · simpa only [fibreNorm, ite_eq_left hz] using ((norm_zero_iff N v p z).mpr hz).symm
  · rw [fibreNorm, ite_eq_right hz, logNorm_constant]
    exact Real.exp_log (lt_of_le_of_ne (((N.metric v).fibreNorm p).nonnegative z)
      (fun h ↦ hz ((norm_zero_iff N v p z).mp h.symm)))

end MathlibExt.AlgebraicGeometry.AdelicCompletionEvaluations
