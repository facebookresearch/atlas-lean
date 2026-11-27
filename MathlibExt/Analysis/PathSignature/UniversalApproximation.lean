/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PathSignature.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import MathlibExt.Analysis.PathSignature.Shuffle
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Universal approximation by linear functionals of the signature

`exists_signature_linear_approx` proves uniform approximation of continuous real-valued
functions on compact sets of time-augmented velocities by finite linear combinations of
signature coordinates. The shuffle identity makes these combinations an algebra, and
moments against the time coordinate distinguish velocities.
-/

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ENNReal Topology

namespace MathlibExt.Analysis.PathSignature.UniversalApproximationWanted

noncomputable section

private abbrev Velocity (d : ℕ) (a b : ℝ) :=
  Lp (Fin (d + 1) → ℝ) 1 (volume.restrict (Icc a b))

private theorem norm_primitive_le {μ : Measure ℝ} (f : Lp ℝ 1 μ) (a t : ℝ) :
    ‖∫ x in a..t, f x ∂μ‖ ≤ ‖f‖ := by
  rw [L1.norm_eq_integral_norm]
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (integral_mono_measure Measure.restrict_le_self
      (.of_forall fun _ => norm_nonneg _) (L1.integrable_coeFn f).norm)

private def primitive {μ : Measure ℝ} [NullSingletonClass μ] (a : ℝ) :
    Lp ℝ 1 μ →L[ℝ] (ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => BoundedContinuousFunction.ofNormedAddCommGroup
        (fun t => ∫ x in a..t, f x ∂μ)
        (intervalIntegral.continuous_primitive
          (fun _ _ => (L1.integrable_coeFn f).intervalIntegrable) a)
        ‖f‖ (norm_primitive_le f a)
      map_add' := by
        intro f g
        ext t
        change (∫ x in a..t, (f + g) x ∂μ) = _
        rw [intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae (Lp.coeFn_add f g))]
        exact intervalIntegral.integral_add (L1.integrable_coeFn f).intervalIntegrable
          (L1.integrable_coeFn g).intervalIntegrable
      map_smul' := by
        intro c f
        ext t
        change (∫ x in a..t, (c • f) x ∂μ) = _
        rw [intervalIntegral.integral_congr_ae_restrict (ae_restrict_of_ae (Lp.coeFn_smul c f))]
        exact intervalIntegral.integral_smul c _ }
    1 fun f => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 (norm_primitive_le f a)

variable {d : ℕ} {a b : ℝ}

-- Construct the whole indefinite integral as a bounded continuous function. Multiplication of
-- the prefix by the next velocity is continuous from L∞ × L¹ to L¹ by Hölder's inequality.
private theorem continuous_signature_family (w : List (Fin (d + 1))) :
    ∃ F : C(Velocity d a b, ℝ →ᵇ ℝ), ∀ (f : Velocity d a b) (v : ℝ → Fin (d + 1) → ℝ),
      (⇑f =ᵐ[volume.restrict (Icc a b)] v) → ∀ t ∈ Icc a b,
        F f t = signature (fun i u => v u i) a t w := by
  let μ := volume.restrict (Icc a b)
  induction w using List.reverseRecOn with
  | nil => exact ⟨ContinuousMap.const _ 1, by simp⟩
  | append_singleton w i ih =>
    obtain ⟨F, hF⟩ := ih
    let proj : (Fin (d + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    let product := (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 1 1
    let pre : C(Velocity d a b, Lp ℝ ∞ μ) :=
      ⟨fun f => BoundedContinuousFunction.toLp ∞ μ ℝ (F f),
        (BoundedContinuousFunction.toLp ∞ μ ℝ).continuous.comp F.continuous⟩
    let coord := proj.compLpL 1 μ
    have hprod : Continuous fun f => product (pre f) (coord f) :=
      (product.continuous.comp pre.continuous).clm_apply coord.continuous
    refine ⟨⟨fun f => primitive (μ := μ) a (product (pre f) (coord f)),
      (primitive (μ := μ) a).continuous.comp hprod⟩, ?_⟩
    intro f v hv t ht
    change (∫ u in a..t, (product (pre f) (coord f)) u ∂μ) = _
    rw [signature_concat, intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_of_le ht.1]
    have hsub : Ioc a t ⊆ Icc a b := fun u hu => ⟨hu.1.le, hu.2.trans ht.2⟩
    change (∫ u, _ ∂(volume.restrict (Icc a b)).restrict (Ioc a t)) = _
    rw [Measure.restrict_restrict_of_subset hsub]
    apply integral_congr_ae
    have heq : ∀ᵐ u ∂μ, (product (pre f) (coord f)) u = F f u * v u i := by
      filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) (pre f) (coord f),
        BoundedContinuousFunction.coeFn_toLp ∞ μ ℝ (F f), proj.coeFn_compLp f, hv]
        with u hmul hFv hi hfv
      exact hmul.trans (congrArg₂ (· * ·) hFv (hi.trans (congrFun hfv i)))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub heq,
      ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu hmem
    rw [hu, hF f v hv u (hsub hmem)]

private abbrev coordSig (f : Velocity d a b) (w : List (Fin (d + 1))) :=
  signature (fun i u => f u i) a b w

private theorem continuous_coordSig (hab : a ≤ b) (w : List (Fin (d + 1))) :
    Continuous fun f : Velocity d a b => coordSig f w := by
  obtain ⟨F, hF⟩ := continuous_signature_family (a := a) (b := b) w
  exact ((continuous_eval_const b).comp F.continuous).congr fun f =>
    hF f f .rfl b ⟨hab, le_rfl⟩

private theorem coordSig_congr (hab : a ≤ b) (f : Velocity d a b)
    {v : ℝ → Fin (d + 1) → ℝ} (hv : ⇑f =ᵐ[volume.restrict (Icc a b)] v)
    (w : List (Fin (d + 1))) : coordSig f w = signature (fun i u => v u i) a b w := by
  obtain ⟨F, hF⟩ := continuous_signature_family (a := a) (b := b) w
  exact (hF f f .rfl b ⟨hab, le_rfl⟩).symm.trans (hF f v hv b ⟨hab, le_rfl⟩)

private theorem coordSig_shuffle (hab : a ≤ b) (f : Velocity d a b) (I J : List (Fin (d + 1))) :
    coordSig f I * coordSig f J = ((shuffle I J).map (coordSig f)).sum := by
  let μ := volume.restrict (Icc a b)
  refine (BoundedContinuousFunction.toLp_denseRange (E := Fin (d + 1) → ℝ) μ ℝ
    (p := 1) (by simp)).induction_on f ?_ ?_
  · exact isClosed_eq ((continuous_coordSig hab I).mul (continuous_coordSig hab J))
      (continuous_list_sum _ fun w _ => continuous_coordSig hab w)
  · intro g
    have h := coordSig_congr hab _ (BoundedContinuousFunction.coeFn_toLp 1 μ ℝ g)
    rw [funext h]
    exact signature_mul_signature (v := fun i u => g u i)
      (fun i => (continuous_apply i).comp g.continuous) a b I J

-- A word with k time letters followed by i measures the kth shifted moment of velocity i.
private theorem moment_eq (hab : a ≤ b) (f : Velocity d a b)
    (ht : ∀ᵐ u ∂volume.restrict (Icc a b), f u 0 = 1) (i : Fin (d + 1)) (k : ℕ) :
    (∫ u in Icc a b, (u - a) ^ k * f u i) =
      k.factorial * coordSig f (List.replicate k 0 ++ [i]) := by
  let v := fun u => Function.update (f u) 0 1
  have hv : ⇑f =ᵐ[volume.restrict (Icc a b)] v := by
    filter_upwards [ht] with u hu
    simp [v, ← hu]
  rw [coordSig_congr hab f hv, signature_concat, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [hv] with u hu
  have htime : (fun t => v t 0) = fun _ => 1 := by funext t; simp [v]
  rw [signature_replicate (show Continuous (fun t => v t 0) by rw [htime]; exact continuous_const),
    htime, intervalIntegral.integral_const, ← hu]
  simp only [smul_eq_mul, mul_one]
  field_simp

-- Polynomials in t - a approximate each smooth test function uniformly on [a,b].
-- Testing against these polynomials therefore detects any integrable density on the interval.
private theorem ae_zero_of_moments {v : ℝ → ℝ} (hv : IntegrableOn v (Icc a b))
    (hm : ∀ k : ℕ, ∫ u in Icc a b, (u - a) ^ k * v u = 0) :
    ∀ᵐ u ∂volume.restrict (Icc a b), v u = 0 := by
  have hint (p : Polynomial ℝ) : IntegrableOn (fun u => p.eval (u - a) * v u) (Icc a b) :=
    IntegrableOn.continuousOn_mul (by fun_prop) hv isCompact_Icc
  have hpoly (p : Polynomial ℝ) : ∫ u in Icc a b, p.eval (u - a) * v u = 0 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval_add, add_mul, integral_add (hint p) (hint q),
        hp, hq, add_zero]
    | monomial k c => simp only [Polynomial.eval_monomial, mul_assoc, integral_const_mul, hm,
        mul_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hv.locallyIntegrable
  intro g hg _
  simp only [smul_eq_mul]
  have hbound (δ : ℝ) (hδ : 0 < δ) :
      |∫ u in Icc a b, g u * v u| ≤ δ * ∫ u in Icc a b, ‖v u‖ := by
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 (b - a)
      (fun t => g (t + a)) (hg.continuous.comp (continuous_id.add_const a)).continuousOn δ hδ
    have hgi := IntegrableOn.continuousOn_mul hg.continuous.continuousOn hv isCompact_Icc
    rw [← sub_zero (∫ u in Icc a b, g u * v u), ← hpoly p, ← integral_sub hgi (hint p),
      ← integral_const_mul, ← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (hv.norm.const_mul δ)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with u hu
    rw [← sub_mul, norm_mul, Real.norm_eq_abs (g u - _), abs_sub_comm]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [sub_add_cancel] using (hp (u - a) ⟨sub_nonneg.mpr hu.1, by linarith [hu.2]⟩).le
  have hlim : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_right nhdsWithin_le_nhds
  have hz := ge_of_tendsto (hlim.mul_const (∫ u in Icc a b, ‖v u‖))
    (mem_of_superset self_mem_nhdsWithin fun δ hδ => hbound δ hδ)
  simpa using hz

private theorem eq_of_coordSig_eq (hab : a ≤ b) {f g : Velocity d a b}
    (hf : ∀ᵐ u ∂volume.restrict (Icc a b), f u 0 = 1)
    (hg : ∀ᵐ u ∂volume.restrict (Icc a b), g u 0 = 1) (heq : coordSig f = coordSig g) :
    f = g := by
  apply Lp.ext
  suffices h : ∀ i, ∀ᵐ u ∂volume.restrict (Icc a b), f u i = g u i by
    filter_upwards [ae_all_iff.2 h] with u hu
    exact funext hu
  intro i
  let proj : (Fin (d + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hint (z : Velocity d a b) : IntegrableOn (fun u => z u i) (Icc a b) :=
    proj.integrable_comp (L1.integrable_coeFn z)
  have hw (z : Velocity d a b) (k : ℕ) :
      IntegrableOn (fun u => (u - a) ^ k * z u i) (Icc a b) :=
    IntegrableOn.continuousOn_mul (by fun_prop) (hint z) isCompact_Icc
  refine (ae_zero_of_moments (v := fun u => f u i - g u i) ((hint f).sub (hint g)) ?_).mono
    fun _ hu => sub_eq_zero.mp hu
  intro k
  simp_rw [mul_sub]
  rw [integral_sub (hw f k) (hw g k), moment_eq hab f hf, moment_eq hab g hg, heq, sub_self]

private abbrev Terms (d : ℕ) := List (ℝ × List (Fin (d + 1)))

private def evaluate (f : Velocity d a b) (L : Terms d) : ℝ :=
  (L.map fun p => p.1 * coordSig f p.2).sum

private theorem evaluate_append (f : Velocity d a b) (L M : Terms d) :
    evaluate f (L ++ M) = evaluate f L + evaluate f M := by
  simp [evaluate]

private theorem evaluate_product (hab : a ≤ b) (L M : Terms d) :
    ∃ N : Terms d, ∀ f : Velocity d a b, evaluate f N = evaluate f L * evaluate f M := by
  have single (p : ℝ × List (Fin (d + 1))) :
      ∃ N : Terms d, ∀ f : Velocity d a b,
        evaluate f N = (p.1 * coordSig f p.2) * evaluate f M := by
    induction M with
    | nil => exact ⟨[], by simp [evaluate]⟩
    | cons q M ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨((shuffle p.2 q.2).map fun w => (p.1 * q.1, w)) ++ N, fun f => ?_⟩
      rw [evaluate_append, hN]
      simp only [evaluate, List.map_map, Function.comp_def, List.sum_map_mul_left,
        ← coordSig_shuffle hab, List.map_cons, List.sum_cons]
      ring
  induction L with
  | nil => exact ⟨[], by simp [evaluate]⟩
  | cons p L ih =>
    obtain ⟨N, hN⟩ := single p
    obtain ⟨P, hP⟩ := ih
    refine ⟨N ++ P, fun f => ?_⟩
    rw [evaluate_append, hN, hP]
    simp [evaluate, add_mul]

private def signatureAlgebra (hab : a ≤ b) (K : Set (Velocity d a b)) :
    Subalgebra ℝ C(K, ℝ) where
  carrier := {h | ∃ L : Terms d, ∀ f : K, h f = evaluate f.1 L}
  zero_mem' := ⟨[], by simp [evaluate]⟩
  one_mem' := ⟨[(1, [])], by simp [evaluate, coordSig]⟩
  add_mem' := by
    rintro h g ⟨L, hL⟩ ⟨M, hM⟩
    exact ⟨L ++ M, fun f => by simp [evaluate_append, hL, hM]⟩
  mul_mem' := by
    rintro h g ⟨L, hL⟩ ⟨M, hM⟩
    obtain ⟨N, hN⟩ := evaluate_product (d := d) hab L M
    exact ⟨N, fun f => by simp [hL, hM, hN]⟩
  algebraMap_mem' := fun r => ⟨[(r, [])], by simp [evaluate, coordSig]⟩

/-- **Universal approximation by linear functionals of the signature.** Fix `a < b`. Describe an
absolutely continuous path `X : [a, b] → ℝ^{d+1}` with a fixed starting point by its velocity
`f ∈ L¹([a, b]; ℝ^{d+1})`, so that `‖f − f'‖_{L¹}` is the bounded-variation distance of the two
paths, and suppose the coordinate `0` is time (`f₀ = 1` almost everywhere, so `X⁰_t = t` up to
the fixed start). Let `K` be a compact set of such velocities and `g` a real function continuous
on `K`. Then for every `ε > 0` there are finitely many reals `λ_k` and words `I_k` with
`|g(X) − ∑_k λ_k S(X)^{I_k}_{a,b}| < ε` for every `X ∈ K` (Chevyrev and Kormilitzin, *A primer
on the signature method in machine learning*, arXiv:1603.03788v2, Proposition 1.35, stated there
for paths with the bounded-variation norm `|X_a| + ∫_a^b |Ẋ_t| dt`). -/
public theorem exists_signature_linear_approx {d : ℕ} {a b : ℝ} (hab : a < b)
    (K : Set (Lp (Fin (d + 1) → ℝ) 1 (volume.restrict (Set.Icc a b)))) (hK : IsCompact K)
    (htime : ∀ f ∈ K, ∀ᵐ u ∂(volume.restrict (Set.Icc a b)), f u 0 = 1)
    (g : Lp (Fin (d + 1) → ℝ) 1 (volume.restrict (Set.Icc a b)) → ℝ) (hg : ContinuousOn g K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : List (ℝ × List (Fin (d + 1))), ∀ f ∈ K,
      |g f - (L.map fun p => p.1 * signature (fun i u => f u i) a b p.2).sum| < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A := signatureAlgebra hab.le K
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have hne : coordSig x.1 ≠ coordSig y.1 := fun heq =>
      hxy (Subtype.ext (eq_of_coordSig_eq hab.le (htime _ x.2) (htime _ y.2) heq))
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hne
    let h : C(K, ℝ) :=
      ⟨fun f => coordSig f.1 w, (continuous_coordSig hab.le w).comp continuous_subtype_val⟩
    have hmem : h ∈ A := ⟨[(1, w)], fun f => by simp [evaluate, h]⟩
    exact ⟨_, ⟨h, hmem, rfl⟩, hw⟩
  obtain ⟨h, hh⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    A hsep (fun f : K => g f.1) hg.domRestrict ε hε
  obtain ⟨L, hL⟩ := h.property
  refine ⟨L, fun f hf => ?_⟩
  rw [abs_sub_comm]
  change |evaluate f L - g f| < ε
  rw [← hL ⟨f, hf⟩]
  exact hh ⟨f, hf⟩

end

end MathlibExt.Analysis.PathSignature.UniversalApproximationWanted
