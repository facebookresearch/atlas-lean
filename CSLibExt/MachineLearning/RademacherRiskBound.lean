/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.RademacherComplexity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Pi
import MathlibExt.Probability.Concentration.McDiarmidPi

/-!
# The Rademacher risk bound

Bartlett and Mendelson, *Rademacher and Gaussian complexities: risk bounds and structural
results*, JMLR 3 (2002), Theorem 8: for a loss `L` and a dominating cost `φ ≥ L`, both with
values in `[0, 1]`, with probability at least `1 - δ` over an i.i.d. sample of size `n`, every
`f` in the class satisfies

`𝔼 L(Y, f(X)) ≤ (1/n) ∑ᵢ φ(Yᵢ, f(Xᵢ)) + (complexity term) + √(8 log (2/δ) / n)`.

The theorem `risk_le_empirical_add_rademacher` uses the convention of
`Cslib.MachineLearning.Rademacher.rademacherComplexity` (no absolute value, normalization
`1/n`): it is `2 𝔼_S R(φ ∘ F|_S)`, the expected empirical Rademacher complexity of the cost
vectors `(φ(Yᵢ, f(Xᵢ)))ᵢ`. This is the quantity reached in the last display of Bartlett and
Mendelson's proof (`2 𝔼 sup_h (1/n) ∑ σᵢ h(Xᵢ, Yᵢ)`, page 468), and it is at most their
`R_n(φ̃ ∘ F)`; their recentring `φ̃ = φ(·, ·) - φ(·, 0)` is not needed because this
complexity is translation invariant (`rademacherComplexity_add_singleton`). The statement is
restricted to a finite class `F`, for which every quantity involved is measurable.
Shalev-Shwartz and Ben-David (*Understanding Machine Learning*, CUP 2014, Theorem 26.5, part 1)
state the case `φ = L` with the sharper deviation term `√(2 log (2/δ) / n)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Rademacher

open MeasureTheory

/-- The cost vectors `(φ(yᵢ, f(xᵢ)))ᵢ` of the functions `f ∈ F` on a sample
`S = ((x₁, y₁), …, (xₙ, yₙ))`. -/
def costVectors {X Y A : Type*} (φ : Y → A → ℝ) (F : Set (X → A)) {n : ℕ}
    (S : Fin n → X × Y) : Set (Fin n → ℝ) :=
  (fun f i => φ (S i).2 (f (S i).1)) '' F

open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype
  (rademacherSign)

section Symmetrization

variable {Z ι : Type*} [MeasurableSpace Z] [Finite ι] [Nonempty ι] {n : ℕ}

/-- The maximum of finitely many integrable functions is dominated in norm by the sum of
their norms. -/
private lemma integrable_maximum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : ι → Ω → ℝ} (hu : ∀ j, Integrable (u j) μ) :
    Integrable (fun x => ⨆ j, u j x) μ := by
  let := Fintype.ofFinite ι
  refine (integrable_finsetSum Finset.univ fun j _ => (hu j).norm).mono'
    (AEMeasurable.iSup fun j => (hu j).aemeasurable).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro x
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j => u j x)
  rw [← hj]
  exact Finset.single_le_sum (fun k _ => norm_nonneg (u k x)) (Finset.mem_univ j)

private def sampleSum (g : ι → Z → ℝ) (j : ι) (x : Fin n → Z) : ℝ :=
  ∑ k, g j (x k)

private noncomputable def signedMax (g : ι → Z → ℝ) (s : Fin n → Bool) (x : Fin n → Z) : ℝ :=
  ⨆ j, signCorr s (fun k => g j (x k))

private noncomputable def deviation (P : Measure Z) (g : ι → Z → ℝ) (x : Fin n → Z) : ℝ :=
  ⨆ j, (n : ℝ) * (∫ z, g j z ∂P) - sampleSum g j x

private noncomputable def pairedDeviation (g : ι → Z → ℝ) (p : (Fin n → Z) × (Fin n → Z)) : ℝ :=
  ⨆ j, sampleSum g j p.2 - sampleSum g j p.1

variable (P : Measure Z) [IsProbabilityMeasure P] {g : ι → Z → ℝ}
  (hg : ∀ j : ι, Integrable (g j) P)

include hg

omit [Finite ι] [Nonempty ι] in
private lemma integrable_sampleSum (j : ι) :
    Integrable (sampleSum (n := n) g j) (Measure.pi fun _ => P) :=
  integrable_finsetSum _ fun k _ =>
    (measurePreserving_eval (fun _ => P) k).integrable_comp_of_integrable (hg j)

private lemma integrable_signedMax (s : Fin n → Bool) :
    Integrable (signedMax g s) (Measure.pi fun _ => P) := by
  apply integrable_maximum
  intro j
  exact integrable_finsetSum _ fun k _ =>
    ((measurePreserving_eval (fun _ => P) k).integrable_comp_of_integrable (hg j)).const_mul _

/-- The expected one-sided deviation is at most the expected deviation between two independent
samples. The second sample integrates to the population cost for each fixed class member. -/
private lemma integral_deviation_le_paired :
    let μ := Measure.pi fun _ : Fin n => P
    ∫ x, deviation P g x ∂μ ≤ ∫ p, pairedDeviation g p ∂(μ.prod μ) := by
  intro μ
  have hsum := integrable_sampleSum (n := n) P hg
  have hp : Integrable (pairedDeviation g) (μ.prod μ) :=
    integrable_maximum fun j => ((hsum j).comp_snd μ).sub ((hsum j).comp_fst μ)
  rw [integral_prod _ hp]
  refine integral_mono (integrable_maximum fun j => (integrable_const _).sub (hsum j))
    hp.integral_prod_left fun x => ciSup_le fun j => ?_
  have heval (k : Fin n) : ∫ y, g j (y k) ∂μ = ∫ z, g j z ∂P :=
    integral_comp_eval (μ := fun _ => P) (hg j).aestronglyMeasurable
  calc (n : ℝ) * (∫ z, g j z ∂P) - sampleSum g j x =
      ∫ y, sampleSum g j y - sampleSum g j x ∂μ := by
        rw [integral_sub (hsum j) (integrable_const _), integral_const, probReal_univ, one_smul]
        congr 1
        unfold sampleSum
        rw [integral_finsetSum (f := fun k (y : Fin n → Z) => g j (y k)) _ fun k _ =>
          (measurePreserving_eval (fun _ : Fin n => P) k).integrable_comp_of_integrable (hg j)]
        change (n : ℝ) * _ = ∑ k : Fin n, ∫ y, g j (y k) ∂μ
        simp [heval]
    _ ≤ ∫ y, pairedDeviation g (x, y) ∂μ :=
      integral_mono ((hsum j).sub (integrable_const _))
        (integrable_maximum fun l => (hsum l).sub (integrable_const (sampleSum g l x)))
        fun y => Finite.le_ciSup (fun l => sampleSum g l y - sampleSum g l x) j

/-- Swapping the two observations at each negative sign preserves the joint sample law.
The resulting signed difference is bounded by a signed maximum on each sample. -/
private lemma integral_paired_le_signed (s : Fin n → Bool) :
    let μ := Measure.pi fun _ : Fin n => P
    ∫ p, pairedDeviation g p ∂(μ.prod μ) ≤
      (∫ x, signedMax g (flipSigns s) x ∂μ) + ∫ y, signedMax g s y ∂μ := by
  intro μ
  let swapAt (k : Fin n) (q : Z × Z) := if s k then q else q.swap
  have hswap (k : Fin n) : MeasurePreserving (swapAt k) (P.prod P) (P.prod P) := by
    cases hk : s k
    · simpa [swapAt, hk] using (Measure.measurePreserving_swap (μ := P) (ν := P))
    · rw [show swapAt k = id from funext fun q => by simp [swapAt, hk]]
      exact MeasurePreserving.id _
  let e := MeasurableEquiv.arrowProdEquivProdArrow Z Z (Fin n)
  have he : MeasurePreserving e (Measure.pi fun _ => P.prod P) (μ.prod μ) :=
    measurePreserving_arrowProdEquivProdArrow Z Z (Fin n) (fun _ => P) (fun _ => P)
  let T (p : (Fin n → Z) × (Fin n → Z)) := e (fun k => swapAt k (e.symm p k))
  have hT : MeasurePreserving T (μ.prod μ) (μ.prod μ) :=
    he.comp ((measurePreserving_pi _ _ hswap).comp he.symm)
  have hsum := integrable_sampleSum (n := n) P hg
  have hp : Integrable (pairedDeviation g) (μ.prod μ) :=
    integrable_maximum fun j => ((hsum j).comp_snd μ).sub ((hsum j).comp_fst μ)
  have hleft := (integrable_signedMax P hg (flipSigns s)).comp_fst μ
  have hright := (integrable_signedMax P hg s).comp_snd μ
  calc ∫ p, pairedDeviation g p ∂(μ.prod μ) = ∫ p, pairedDeviation g (T p) ∂(μ.prod μ) := by
        conv_lhs => rw [← hT.map_eq]
        exact integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hp.1)
    _ ≤ ∫ p, signedMax g (flipSigns s) p.1 + signedMax g s p.2 ∂(μ.prod μ) := by
        refine integral_mono (hT.integrable_comp_of_integrable hp) (hleft.add hright) fun p =>
          ciSup_le fun j => ?_
        refine le_trans ?_ (add_le_add (Finite.le_ciSup _ j) (Finite.le_ciSup _ j))
        apply le_of_eq
        unfold sampleSum signCorr
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        cases hk : s k <;>
          simp [T, swapAt, e, MeasurableEquiv.arrowProdEquivProdArrow, rademacherSign,
            flipSigns, hk] <;> ring
    _ = _ := by rw [integral_add hleft hright, integral_fun_fst, integral_fun_snd]; simp [μ]

/-- Averaging the two signed maxima over signs gives twice the one-sided complexity. -/
private lemma symmetrization :
    let μ := Measure.pi fun _ : Fin n => P
    ∫ x, deviation P g x ∂μ ≤
      2 * ∫ x, ((2 : ℝ) ^ n)⁻¹ * ∑ s, signedMax g s x ∂μ := by
  intro μ
  let m := ∫ p, pairedDeviation g p ∂(μ.prod μ)
  have hcard : ((2 : ℝ) ^ n)⁻¹ * ∑ _s : Fin n → Bool, m = m := by
    simp [nsmul_eq_mul]
  refine (integral_deviation_le_paired P hg).trans ?_
  change m ≤ _
  rw [← hcard, integral_const_mul, integral_finsetSum _ fun s _ => integrable_signedMax P hg s]
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ _s : Fin n → Bool, m ≤
      ((2 : ℝ) ^ n)⁻¹ * ∑ s, ((∫ x, signedMax g (flipSigns s) x ∂μ) +
        ∫ y, signedMax g s y ∂μ) := by
          gcongr with s
          exact integral_paired_le_signed P hg s
    _ = _ := by rw [Finset.sum_add_distrib, sum_flipSigns (fun s => ∫ x, signedMax g s x ∂μ)]; ring

end Symmetrization

section Concentration

variable {Z ι : Type*} [MeasurableSpace Z] [Finite ι] [Nonempty ι] {n : ℕ}
  (P : Measure Z) {g : ι → Z → ℝ}

private lemma deviation_update (hb : ∀ j z, g j z ∈ Set.Icc 0 1)
    (x : Fin n → Z) (k : Fin n) (z : Z) :
    |deviation P g (Function.update x k z) - deviation P g x| ≤ 1 := by
  have hdiff (j : ι) : sampleSum g j (Function.update x k z) - sampleSum g j x =
      g j z - g j (x k) := by
    unfold sampleSum
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [Function.update_of_ne hik]
    · simp
  let d (x : Fin n → Z) (j : ι) := (n : ℝ) * (∫ z, g j z ∂P) - sampleSum g j x
  have hle (j : ι) (y : Fin n → Z) : d y j ≤ deviation P g y := Finite.le_ciSup _ j
  rw [abs_sub_le_iff, sub_le_iff_le_add, sub_le_iff_le_add]
  constructor <;> refine ciSup_le fun j => ?_
  · have := hle j x
    dsimp only [d] at this
    linarith [hdiff j, (hb j z).1, (hb j (x k)).2]
  · have := hle j (Function.update x k z)
    dsimp only [d] at this
    linarith [hdiff j, (hb j z).2, (hb j (x k)).1]

private lemma deviation_concentration [IsProbabilityMeasure P] (hm : ∀ j, Measurable (g j))
    (hb : ∀ j z, g j z ∈ Set.Icc 0 1) (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let μ := Measure.pi fun _ : Fin n => P
    let t := (n : ℝ) * Real.sqrt (8 * Real.log (2 / δ) / n)
    1 - δ ≤ μ.real {x | deviation P g x ≤ (∫ y, deviation P g y ∂μ) + t} := by
  intro μ t
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 ≤ t := mul_nonneg hn'.le (Real.sqrt_nonneg _)
  have hlog := Real.log_nonneg (show 1 ≤ 2 / δ by rw [le_div_iff₀ hδ0]; linarith)
  have hD : Measurable (deviation (n := n) P g) := by
    unfold deviation sampleSum
    exact Measurable.iSup fun j => by fun_prop
  let m := ∫ y, deviation P g y ∂μ
  have htail := ProbabilityTheory.measureReal_sub_integral_ge_le_of_bounded_differences
    (μ := fun _ : Fin n => P) (c := fun _ => 1) hD (deviation_update P hb) ht
  have hprob : μ.real {x | t ≤ deviation P g x - m} ≤ δ := by
    refine htail.trans ?_
    simp only [NNReal.coe_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    calc Real.exp (-2 * t ^ 2 / n) ≤ Real.exp (-Real.log (2 / δ)) := by
          apply Real.exp_le_exp.mpr
          dsimp [t]
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          field_simp
          nlinarith
      _ ≤ δ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp; linarith
  have hmset : MeasurableSet {x | t ≤ deviation P g x - m} :=
    measurableSet_le measurable_const (hD.sub_const m)
  calc 1 - δ ≤ 1 - μ.real {x | t ≤ deviation P g x - m} := by linarith
    _ = μ.real {x | t ≤ deviation P g x - m}ᶜ := by rw [measureReal_compl hmset, probReal_univ]
    _ ≤ _ := measureReal_mono fun x hx => by
      change ¬ t ≤ deviation P g x - m at hx
      change deviation P g x ≤ m + t
      linarith

end Concentration

/-- **The Rademacher risk bound** (Bartlett and Mendelson, *Rademacher and Gaussian
complexities: risk bounds and structural results*, JMLR 3, 2002, Theorem 8, in the
no-absolute-value convention and for a finite class): let `P` be a probability measure on
`X × Y`, let `L ≤ φ` be measurable along every `f ∈ F` with `0 ≤ L` and `φ ≤ 1`, and let
`0 < δ < 1`. Then with probability at least `1 - δ` over an i.i.d. sample `S ∼ Pⁿ`, every
`f ∈ F` satisfies
`𝔼_P L(Y, f(X)) ≤ (1/n) ∑ᵢ φ(Yᵢ, f(Xᵢ)) + 2 𝔼_{S'} R(φ ∘ F|_{S'}) + √(8 log (2/δ) / n)`
(for `φ = L` this is also Shalev-Shwartz and Ben-David, Theorem 26.5, part 1, with a weaker
constant). -/
theorem risk_le_empirical_add_rademacher {X Y A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (P : Measure (X × Y)) [IsProbabilityMeasure P]
    (L φ : Y → A → ℝ) (hL : ∀ y a, 0 ≤ L y a) (hφ : ∀ y a, φ y a ≤ 1)
    (hdom : ∀ y a, L y a ≤ φ y a) (F : Set (X → A)) (hF : F.Finite)
    (hmeasL : ∀ f ∈ F, Measurable fun z : X × Y => L z.2 (f z.1))
    (hmeasφ : ∀ f ∈ F, Measurable fun z : X × Y => φ z.2 (f z.1))
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => P)
      {S | ∀ f ∈ F, ∫ z, L z.2 (f z.1) ∂P ≤
        (n : ℝ)⁻¹ * ∑ i, φ (S i).2 (f (S i).1) +
          2 * ∫ S', rademacherComplexity (costVectors φ F S') ∂(Measure.pi fun _ : Fin n => P) +
          Real.sqrt (8 * Real.log (2 / δ) / n)} := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | hne
  · simp
  have := hF.to_subtype
  have := hne.to_subtype
  let g (j : F) (z : X × Y) := φ z.2 (j.val z.1)
  have hm (j : F) : Measurable (g j) := hmeasφ j j.property
  have hb (j : F) (z : X × Y) : g j z ∈ Set.Icc 0 1 :=
    ⟨(hL ..).trans (hdom ..), hφ ..⟩
  have hg (j : F) : Integrable (g j) P :=
    Integrable.of_mem_Icc 0 1 (hm j).aemeasurable (Filter.Eventually.of_forall (hb j))
  let μ := Measure.pi fun _ : Fin n => P
  have hcorr (x : Fin n → X × Y) (s : Fin n → Bool) :
      supCorr (costVectors φ F x) s = signedMax g s x := by
    unfold supCorr costVectors signedMax iSup
    rw [Set.image_image, Set.image_eq_range]
  have hcomplex :
      (∫ x, rademacherComplexity (costVectors φ F x) ∂μ) =
        (n : ℝ)⁻¹ * ∫ x, ((2 : ℝ) ^ n)⁻¹ * ∑ s, signedMax g s x ∂μ := by
    simp only [rademacherComplexity, hcorr, integral_const_mul]
  have hsym := symmetrization (n := n) P hg
  have hcon := deviation_concentration P hm hb hn hδ0 hδ1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hδ0.le, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine hcon.trans (measureReal_mono fun x hx f hf => ?_)
  let j : F := ⟨f, hf⟩
  have hintL : Integrable (fun z : X × Y => L z.2 (f z.1)) P :=
    Integrable.of_mem_Icc 0 1 (hmeasL f hf).aemeasurable <|
      Filter.Eventually.of_forall fun z => ⟨hL .., (hdom ..).trans (hφ ..)⟩
  refine (integral_mono hintL (hg j) fun z => hdom z.2 (f z.1)).trans ?_
  have hdev : (n : ℝ) * (∫ z, g j z ∂P) - sampleSum g j x ≤ deviation P g x :=
    Finite.le_ciSup (fun l => (n : ℝ) * (∫ z, g l z ∂P) - sampleSum g l x) j
  change deviation P g x ≤ (∫ y, deviation P g y ∂μ) + _ at hx
  change (∫ z, g j z ∂P) ≤ (n : ℝ)⁻¹ * sampleSum g j x +
    2 * (∫ x, rademacherComplexity (costVectors φ F x) ∂μ) + _
  rw [hcomplex]
  let R := ∫ x, ((2 : ℝ) ^ n)⁻¹ * ∑ s, signedMax g s x ∂μ
  change (∫ y, deviation P g y ∂μ) ≤ 2 * R at hsym
  change _ ≤ (n : ℝ)⁻¹ * sampleSum g j x + 2 * ((n : ℝ)⁻¹ * R) + _
  field_simp
  linarith only [hdev, hx, hsym]

end Cslib.MachineLearning.Rademacher
