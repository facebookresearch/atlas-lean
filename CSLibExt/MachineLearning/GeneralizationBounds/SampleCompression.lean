/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass
public import MathlibExt.Probability.Concentration.Bernstein
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Relative generalization bound for bounded-loss sample compression -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CSLibExt.MachineLearning.GeneralizationBounds

private noncomputable def meanLoss {ι Z : Type*} [Fintype ι] (g : Z → ℝ) (S : ι → Z) : ℝ :=
  (∑ i, g (S i)) / Fintype.card ι

/-- The average loss on the indices not selected by the compression tuple `I`. Repeated
entries in `I` remove the corresponding sample index only once. The value is `0` if no
unkept indices remain. -/
noncomputable def compressionValidationRisk {Z H : Type*} {m k : ℕ} (L : H → Z → ℝ)
    (I : Fin k → Fin m) (S : Fin m → Z) (h : H) : ℝ :=
  let V := {i : Fin m // i ∉ Finset.univ.image I}
  (∑ i : V, L h (S i)) / Fintype.card V

private theorem meanLoss_nonneg {ι Z : Type*} [Fintype ι] (g : Z → ℝ)
    (hg : ∀ z, 0 ≤ g z) (S : ι → Z) : 0 ≤ meanLoss g S :=
  div_nonneg (Finset.sum_nonneg fun i _ => hg (S i)) (Nat.cast_nonneg _)

private theorem boundedLoss_lowerTail {ι Z : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (g : Z → ℝ) (hg : Measurable g) (h01 : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    {x : ℝ} (hx : 0 < x) :
    (Measure.pi fun _ : ι => D).real
        {S | meanLoss g S + Real.sqrt (2 * meanLoss g S * x) + 4 * x < ∫ z, g z ∂D} ≤
      Real.exp (-((Fintype.card ι : ℝ) * x)) := by
  let P : Measure (ι → Z) := Measure.pi fun _ => D
  let p := ∫ z, g z ∂D
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hint : Integrable g D := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by simpa [Real.norm_eq_abs, abs_of_nonneg (h01 z).1] using (h01 z).2
  have hp0 : 0 ≤ p := integral_nonneg fun z => (h01 z).1
  have hp1 : p ≤ 1 := by
    change (∫ z, g z ∂D) ≤ 1
    have h := integral_mono hint (integrable_const (1 : ℝ)) (fun z => (h01 z).2)
    simpa using h
  rcases eq_or_lt_of_le hp0 with hp | hp
  · have hempty : {S : ι → Z | meanLoss g S + Real.sqrt (2 * meanLoss g S * x) + 4 * x < p} =
        ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro S hS
      change meanLoss g S + Real.sqrt (2 * meanLoss g S * x) + 4 * x < p at hS
      have hq := meanLoss_nonneg g (fun z => (h01 z).1) S
      linarith [Real.sqrt_nonneg (2 * meanLoss g S * x)]
    change P.real _ ≤ _
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  let e := Fintype.equivFin ι
  let X : Fin (Fintype.card ι) → (ι → Z) → ℝ := fun i S => p - g (S (e.symm i))
  have hXmeas (i : Fin (Fintype.card ι)) : Measurable (X i) :=
    measurable_const.sub (hg.comp (measurable_pi_apply _))
  have hXi : iIndepFun X P := by
    have h : iIndepFun (fun i (S : ι → Z) => p - g (S i)) P :=
      iIndepFun_pi (X := fun _ : ι => fun z => p - g z)
        (fun _ => (measurable_const.sub hg).aemeasurable)
    exact h.precomp e.symm.injective
  have int_eval (j : ι) (f : Z → ℝ) (hf : Measurable f) :
      (∫ S, f (S j) ∂P) = ∫ z, f z ∂D := by
    let ev : (ι → Z) → Z := Function.eval j
    have hmp : MeasurePreserving ev P D := measurePreserving_eval (fun _ : ι => D) j
    calc
      _ = ∫ z, f z ∂(P.map ev) :=
        (integral_map (measurable_pi_apply j).aemeasurable hf.aestronglyMeasurable).symm
      _ = _ := by rw [hmp.map_eq]
  have hXmean (i : Fin (Fintype.card ι)) : ∫ S, X i S ∂P = 0 := by
    change (∫ S, p - g (S (e.symm i)) ∂P) = 0
    rw [int_eval (e.symm i) (fun z => p - g z) (measurable_const.sub hg),
      integral_sub (integrable_const p) hint]
    simp [p]
  have hXbdd (i : Fin (Fintype.card ι)) : ∀ᵐ S ∂P, |X i S| ≤ 1 := by
    refine ae_of_all _ fun S => abs_le.mpr ?_
    change -1 ≤ p - g (S (e.symm i)) ∧ p - g (S (e.symm i)) ≤ 1
    exact ⟨by linarith [(h01 (S (e.symm i))).2], by linarith [(h01 (S (e.symm i))).1]⟩
  have hvar1 : (∫ z, (p - g z) ^ 2 ∂D) ≤ p := by
    have hsq : Integrable (fun z => (p - g z) ^ 2) D := by
      refine Integrable.of_bound ((measurable_const.sub hg).pow_const 2).aestronglyMeasurable 1 ?_
      refine ae_of_all _ fun z => ?_
      have hpz : |p - g z| ≤ 1 := abs_le.mpr
        ⟨by linarith [(h01 z).2], by linarith [(h01 z).1]⟩
      rw [Real.norm_eq_abs, abs_pow]
      simpa using pow_le_pow_left₀ (abs_nonneg _) hpz 2
    have hpt : ∀ z, (p - g z) ^ 2 ≤ p ^ 2 + (1 - 2 * p) * g z := by
      intro z
      nlinarith [mul_nonneg (h01 z).1 (sub_nonneg.mpr (h01 z).2)]
    calc _ ≤ ∫ z, p ^ 2 + (1 - 2 * p) * g z ∂D :=
          integral_mono hsq ((integrable_const (p ^ 2)).add (hint.const_mul _)) hpt
      _ = p ^ 2 + (1 - 2 * p) * p := by
        rw [integral_add (integrable_const (p ^ 2)) (hint.const_mul _), integral_const_mul]
        simp [p]
      _ ≤ p := by nlinarith [sq_nonneg p]
  have hvar : (∑ i, ∫ S, (X i S) ^ 2 ∂P) ≤ n * p := by
    calc _ ≤ ∑ _i : Fin (Fintype.card ι), p := by
          apply Finset.sum_le_sum
          intro i _
          change (∫ S, (p - g (S (e.symm i))) ^ 2 ∂P) ≤ p
          rw [int_eval (e.symm i) (fun z => (p - g z) ^ 2)
            ((measurable_const.sub hg).pow_const 2)]
          exact hvar1
      _ = _ := by simp [n, nsmul_eq_mul]
  let a := x / 3 + Real.sqrt ((x / 3) ^ 2 + 2 * p * x)
  have hrad : 0 ≤ (x / 3) ^ 2 + 2 * p * x := by positivity
  have hasqrt : a - x / 3 = Real.sqrt ((x / 3) ^ 2 + 2 * p * x) := by dsimp [a]; ring
  have ha : 0 < a := by dsimp [a]; positivity
  have haeq : a ^ 2 = 2 * x * (p + a / 3) := by
    have h := Real.sq_sqrt hrad
    rw [← hasqrt] at h
    nlinarith
  have hsum (S : ι → Z) : ∑ i, X i S = n * (p - meanLoss g S) := by
    have h : (∑ i : Fin (Fintype.card ι), g (S (e.symm i))) = ∑ i : ι, g (S i) :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, h, meanLoss]
    change n * p - (∑ i, g (S i)) = n * (p - (∑ i, g (S i)) / n)
    field_simp
  have hsub : {S : ι → Z | meanLoss g S + Real.sqrt (2 * meanLoss g S * x) + 4 * x < p} ⊆
      {S | n * a ≤ ∑ i, X i S} := by
    intro S hS
    let q := meanLoss g S
    let d := p - q
    let s := Real.sqrt (2 * q * x)
    have hq : 0 ≤ q := meanLoss_nonneg g (fun z => (h01 z).1) S
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = 2 * q * x := Real.sq_sqrt (by positivity)
    change q + s + 4 * x < p at hS
    have hd : s + 4 * x < d := by dsimp [d]; linarith
    have hds : 0 < d - s := by linarith
    have hdx : 0 < d := by linarith
    have hsq : (8 / 3 : ℝ) * x * d < d ^ 2 - s ^ 2 := by
      have hmul := mul_lt_mul_of_pos_right (show (8 / 3 : ℝ) * x < d - s by linarith) hdx
      nlinarith [mul_nonneg hds.le hs]
    have hbad : 0 < d ^ 2 - 2 * x * (p + d / 3) := by dsimp [d] at *; nlinarith
    have had : a ≤ d := by
      by_contra! hh
      have hprod := mul_pos (sub_pos.mpr hh) (show 0 < a + d - 2 * x / 3 by linarith)
      nlinarith
    change n * a ≤ ∑ i, X i S
    rw [hsum]
    exact mul_le_mul_of_nonneg_left had hn.le
  have hb := bernstein_one_sided (P := P) (M := 1) (V := n * p) (t := n * a)
    (by norm_num) (mul_pos hn hp) (mul_pos hn ha) hXi hXmeas hXmean hXbdd hvar
  have hexp : (n * a) ^ 2 / (2 * (n * p + 1 * (n * a) / 3)) = n * x := by
    have hpa : 0 < p + a / 3 := by positivity
    apply (div_eq_iff (by positivity)).mpr
    calc (n * a) ^ 2 = n ^ 2 * a ^ 2 := by ring
      _ = _ := by rw [haeq]; ring
  rw [hexp] at hb
  exact (measureReal_mono hsub).trans hb

private theorem card_validation_ge {m k : ℕ} (I : Fin k → Fin m) :
    m - k ≤ Fintype.card {i : Fin m // i ∉ Finset.univ.image I} := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]
  apply Nat.sub_le_sub_left
  calc (Finset.univ.filter fun i => i ∈ Finset.univ.image I).card
      ≤ (Finset.univ.image I).card :=
        Finset.card_le_card fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = k := by simp

private def compressionBad {Z H : Type*} [MeasurableSpace Z]
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (L : H → Z → ℝ)
    (R : (Fin k → Z) → H) (x : ℝ) (I : Fin k → Fin m) : Set (Fin m → Z) :=
  {S | let q := compressionValidationRisk L I S (R (S ∘ I))
       q + Real.sqrt (2 * q * x) + 4 * x < risk L D (R (S ∘ I))}

private theorem compressionBad_fixed {Z H : Type*} [MeasurableSpace Z] [MeasurableSpace H]
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hm : k < m)
    (L : H → Z → ℝ) (hL : Measurable fun hz : H × Z => L hz.1 hz.2)
    (h01 : ∀ h z, L h z ∈ Icc (0 : ℝ) 1)
    (R : (Fin k → Z) → H) (hR : Measurable R) {x : ℝ} (hx : 0 < x) (I : Fin k → Fin m) :
    MeasurableSet (compressionBad D L R x I) ∧
      (Measure.pi fun _ : Fin m => D).real (compressionBad D L R x I) ≤
        Real.exp (-((m - k : ℕ) : ℝ) * x) := by
  let p : Fin m → Prop := fun i => i ∈ Finset.univ.image I
  let K := {i : Fin m // p i}
  let V := {i : Fin m // ¬p i}
  have hcard : m - k ≤ Fintype.card V := card_validation_ge I
  have : Nonempty V := Fintype.card_pos_iff.mp ((Nat.sub_pos_of_lt hm).trans_le hcard)
  let keep (j : Fin k) : K := ⟨I j, Finset.mem_image_of_mem I (Finset.mem_univ j)⟩
  let r : (K → Z) → H := fun a => R (fun j => a (keep j))
  have hr : Measurable r := hR.comp (Measurable.of_eval fun j => measurable_pi_apply (keep j))
  let A : Measure (K → Z) := Measure.pi fun _ => D
  let B : Measure (V → Z) := Measure.pi fun _ => D
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => Z) p
  have he : MeasurePreserving e (Measure.pi fun _ : Fin m => D) (A.prod B) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => D) p
  let q : ((K → Z) × (V → Z)) → ℝ := fun ab => meanLoss (L (r ab.1)) ab.2
  have hq : Measurable q := by
    have hterm (i : V) : Measurable (fun ab : (K → Z) × (V → Z) => L (r ab.1) (ab.2 i)) :=
      hL.comp ((hr.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact (Finset.measurable_sum Finset.univ fun i _ => hterm i).div_const _
  have hpop : Measurable fun a : K → Z => risk L D (r a) := by
    have h : Measurable fun az : (K → Z) × Z => L (r az.1) az.2 :=
      hL.comp ((hr.comp measurable_fst).prodMk measurable_snd)
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  let F : Set ((K → Z) × (V → Z)) :=
    {ab | q ab + Real.sqrt (2 * q ab * x) + 4 * x < risk L D (r ab.1)}
  have hF : MeasurableSet F := measurableSet_lt
    ((hq.add (((hq.const_mul 2).mul_const x).sqrt)).add_const (4 * x))
    (hpop.comp measurable_fst)
  have hE : compressionBad D L R x I = e ⁻¹' F := by
    ext S
    rfl
  refine ⟨hE ▸ e.measurable hF, ?_⟩
  have hslice (a : K → Z) : B (Prod.mk a ⁻¹' F) ≤
      ENNReal.ofReal (Real.exp (-(Fintype.card V : ℝ) * x)) := by
    have hmeas : Measurable (L (r a)) := hL.comp (measurable_const.prodMk measurable_id)
    have h := boundedLoss_lowerTail D (L (r a)) hmeas (h01 (r a)) hx (ι := V)
    have hset : Prod.mk a ⁻¹' F =
        {S : V → Z | meanLoss (L (r a)) S + Real.sqrt (2 * meanLoss (L (r a)) S * x)
          + 4 * x < ∫ z, L (r a) z ∂D} := rfl
    rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top B _)]
    apply ENNReal.ofReal_le_ofReal
    change (Measure.pi fun _ : V => D).real _ ≤ _
    simpa only [neg_mul] using h
  have hprod : (A.prod B) F ≤ ENNReal.ofReal (Real.exp (-(Fintype.card V : ℝ) * x)) := by
    rw [Measure.prod_apply hF]
    calc _ ≤ ∫⁻ _a, ENNReal.ofReal (Real.exp (-(Fintype.card V : ℝ) * x)) ∂A :=
          lintegral_mono hslice
      _ = _ := by simp
  rw [hE, measureReal_def, he.measure_preimage hF.nullMeasurableSet]
  apply (ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hprod).trans
  apply Real.exp_le_exp.mpr
  have hc : ((m - k : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hx.le]

/-- **Bounded-loss sample compression** (Shalev-Shwartz and Ben-David, Theorem 30.2 and
Corollary 30.3). Let `S` consist of `m` independent draws from the probability law `D`, let
`L` be a jointly measurable loss taking values in `[0, 1]`, and let `R` be a measurable
reconstruction rule. Assume `1 ≤ k`, `2 * k ≤ m`, and `0 < δ < 1`. Set
`c = k * log (m / δ) / m`, where `log` is the natural logarithm.

With probability at least `1 - δ`, simultaneously for every ordered tuple `I` of `k`
kept indices, the hypothesis `h = R (S ∘ I)` has expected loss `r` under `D` satisfying
`r ≤ q + sqrt (4 * c * q) + 8 * c`, where `q` is its mean loss on the unkept indices.
Repetition in `I` does not remove extra indices. In particular, `r ≤ 8 * c` when `q = 0`. -/
theorem sampleCompression_generalization {Z H : Type*} [MeasurableSpace Z] [MeasurableSpace H]
    (D : Measure Z) [IsProbabilityMeasure D] {m k : ℕ} (hk : 1 ≤ k) (hm : 2 * k ≤ m)
    (L : H → Z → ℝ) (hL : Measurable fun hz : H × Z => L hz.1 hz.2)
    (h01 : ∀ h z, L h z ∈ Icc (0 : ℝ) 1)
    (R : (Fin k → Z) → H) (hR : Measurable R) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ G : Set (Fin m → Z), MeasurableSet G ∧ (1 - δ ≤ (Measure.pi fun _ : Fin m => D).real G) ∧
      ∀ S ∈ G, ∀ I : Fin k → Fin m,
        let h := R (S ∘ I)
        let q := compressionValidationRisk L I S h
        let c := (k : ℝ) * Real.log ((m : ℝ) / δ) / (m : ℝ)
        risk L D h ≤ q + Real.sqrt (q * (4 * c)) + 8 * c ∧
          (q = 0 → risk L D h ≤ 8 * c) := by
  let P : Measure (Fin m → Z) := Measure.pi fun _ => D
  let c := (k : ℝ) * Real.log ((m : ℝ) / δ) / (m : ℝ)
  let x := 2 * c
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hratio : 1 < (m : ℝ) / δ := by
    apply (lt_div_iff₀ hδ).mpr
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
    linarith
  have hcpos : 0 < c := div_pos (mul_pos hkR (Real.log_pos hratio)) hmR
  have hx : 0 < x := mul_pos (by norm_num) hcpos
  let B := fun I : Fin k → Fin m => compressionBad D L R x I
  have hB (I : Fin k → Fin m) := compressionBad_fixed D (by omega : k < m) L hL h01 R hR hx I
  have hBmeas : MeasurableSet (⋃ I, B I) := MeasurableSet.iUnion fun I => (hB I).1
  have hscale : (k : ℝ) * Real.log ((m : ℝ) / δ) ≤ ((m - k : ℕ) : ℝ) * x := by
    have hmk : (m : ℝ) ≤ 2 * ((m - k : ℕ) : ℝ) := by
      exact_mod_cast (show m ≤ 2 * (m - k) by omega)
    have hcEq : c * (m : ℝ) = (k : ℝ) * Real.log ((m : ℝ) / δ) := by
      dsimp [c]
      field_simp
    rw [← hcEq]
    dsimp [x]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmk) hcpos.le]
  have htail : Real.exp (-((m - k : ℕ) : ℝ) * x) ≤ (δ / (m : ℝ)) ^ k := by
    calc _ ≤ Real.exp (-((k : ℝ) * Real.log ((m : ℝ) / δ))) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = _ := by
        rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (div_pos hmR hδ), ← inv_pow, inv_div]
  have hsum : P.real (⋃ I, B I) ≤ δ := by
    calc _ ≤ ∑ I, P.real (B I) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _I : Fin k → Fin m, (δ / (m : ℝ)) ^ k :=
        Finset.sum_le_sum fun I _ => (hB I).2.trans htail
      _ = δ ^ k := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow, div_pow]
        field_simp
      _ ≤ δ := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        rw [pow_succ]
        exact mul_le_of_le_one_left hδ.le (pow_le_one₀ hδ.le hδ1.le)
  refine ⟨(⋃ I, B I)ᶜ, hBmeas.compl, ?_, ?_⟩
  · rw [probReal_compl_eq_one_sub hBmeas]
    linarith
  · intro S hS I
    have hnB : S ∉ B I := fun hb => hS (mem_iUnion.mpr ⟨I, hb⟩)
    change ¬ compressionValidationRisk L I S (R (S ∘ I)) +
      Real.sqrt (2 * compressionValidationRisk L I S (R (S ∘ I)) * x) + 4 * x <
        risk L D (R (S ∘ I)) at hnB
    intro h q c'
    change risk L D h ≤ q + Real.sqrt (q * (4 * c)) + 8 * c ∧ _
    have hr : risk L D h ≤ q + Real.sqrt (q * (4 * c)) + 8 * c := by
      have he : 2 * q * x = q * (4 * c) := by dsimp [x]; ring
      have hx' : 4 * x = 8 * c := by dsimp [x]; ring
      rw [← he, ← hx']
      exact le_of_not_gt hnB
    exact ⟨hr, fun hq => by simpa [hq] using hr⟩

end CSLibExt.MachineLearning.GeneralizationBounds
