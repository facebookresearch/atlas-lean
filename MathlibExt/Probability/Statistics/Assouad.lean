/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.MeasurePinsker
public import MathlibExt.InformationTheory.DobrushinContraction
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.Decision.Risk.Defs

/-!
# Assouad's lemma

Let `P : Kernel Θ Ω` be a statistical model and `ℓ : Θ → Θ → [0, ∞]` a loss with the
`α`-triangle inequality `ℓ(θ₀, θ₁) ≤ α (ℓ(θ₀, t) + ℓ(θ₁, t))`. If parameters `θ_b` indexed by the
hypercube `b ∈ {0, 1}^d` satisfy `ℓ(θ_b, θ_{b'}) ≥ β d_H(b, b')` and neighbouring hypotheses are
within total variation `τ`, then the minimax risk over randomised estimators (Mathlib's
`minimaxRisk`) is at least `β d (1 - τ) / (4α)`.

The proof follows Polyanskiy and Wu: an estimator `T` is projected to the cube by a measurable
nearest point `b̂` (so `β d_H(b̂, b) ≤ 2α ℓ(θ_b, T)`), the Hamming distance splits over
coordinates, and for each coordinate `i` the pairs `b, b ⊕ e_i` are compared by the two-point
testing bound `P(A) + Q(Aᶜ) ≥ 1 - TV(P, Q)`. A randomised estimator `κ` is handled by applying
the deterministic bound to the identity estimator on the output laws `κ ∘ P θ`, which are still
within `τ` of their neighbours by the data-processing inequality for total variation
(`DobrushinContraction.totalVariationDist_comp_le_self`).

## Main results

* `exists_measurable_argmin`: a measurable selection of a minimiser of finitely many measurable
  functions.
* `mul_one_sub_le_four_mul_iSup`: the bound for one deterministic estimator.
* `mul_one_sub_le_minimax`: Assouad's lemma for `minimaxRisk`.

## References

* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Section 28.3.2 (minimax risk over randomised estimators) and Theorem 31.2
  (Assouad's lemma, eq. (31.5)).
* P. Assouad, Deux remarques sur l'estimation, C. R. Acad. Sci. Paris Sér. I 296 (1983),
  1021-1024.
* B. Yu, Assouad, Fano, and Le Cam, in *Festschrift for Lucien Le Cam*, Springer, 1997, 423-435.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ENNReal
open MathlibExt.Probability.TotalVariationDistance MathlibExt.InformationTheory.MeasurePinsker
open MathlibExt.InformationTheory.DobrushinContraction

namespace MathlibExt.Probability.Statistics.Assouad

variable {Ω Θ : Type*} [MeasurableSpace Ω]

/-- A measurable selection of a minimiser: for finitely many measurable functions
`L i : Ω → [0, ∞]`, some `g : Ω → ι` with measurable fibres satisfies `L (g ω) ω ≤ L i ω` for
all `ω` and `i` (the first minimiser for a fixed enumeration of `ι`).
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), proof of Theorem 31.2 (the projection `b̂ ∈ argmin ℓ(θ̂, θ_b)`). -/
theorem exists_measurable_argmin {ι : Type*} [Finite ι] [Nonempty ι] (L : ι → Ω → ℝ≥0∞)
    (hL : ∀ i, Measurable (L i)) :
    ∃ g : Ω → ι, (∀ i, MeasurableSet (g ⁻¹' {i})) ∧ ∀ ω i, L (g ω) ω ≤ L i ω := by
  classical
  have := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have hS : ∀ ω, (Finset.univ.filter fun k : ι => ∀ j, L k ω ≤ L j ω).Nonempty := by
    intro ω
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun k => L k ω) Finset.univ_nonempty
    exact ⟨k, by simpa using fun j => hk j (Finset.mem_univ j)⟩
  have hmeas : ∀ k, MeasurableSet {ω | ∀ j, L k ω ≤ L j ω} := fun k => by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (hL k) (hL j)
  refine ⟨fun ω => (Finset.univ.filter fun k : ι => ∀ j, L k ω ≤ L j ω).min' (hS ω), ?_, ?_⟩
  · intro i
    have : (fun ω => (Finset.univ.filter fun k : ι => ∀ j, L k ω ≤ L j ω).min' (hS ω)) ⁻¹' {i}
        = {ω | ∀ j, L i ω ≤ L j ω} ∩ ⋂ k ∈ {k | k < i}, {ω | ∀ j, L k ω ≤ L j ω}ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · rintro rfl
        refine ⟨?_, fun k hk hkmin => ?_⟩
        · have := Finset.min'_mem _ (hS ω)
          simpa using this
        · exact absurd (Finset.min'_le _ k (by simpa using hkmin)) (not_le.mpr hk)
      · rintro ⟨hi, hlt⟩
        apply le_antisymm
        · exact Finset.min'_le _ i (by simpa using hi)
        · apply Finset.le_min'
          intro k hk
          by_contra h
          exact hlt k (not_le.mp h) (by simpa using hk)
    rw [this]
    exact (hmeas i).inter (MeasurableSet.biInter (Set.to_countable _) fun k _ => (hmeas k).compl)
  · intro ω i
    have := Finset.min'_mem _ (hS ω)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this i

/-- Flipping coordinate `i` of a point of the hypercube. -/
private def flip {d : ℕ} (i : Fin d) (b : Fin d → Bool) : Fin d → Bool :=
  Function.update b i (!b i)

private lemma flip_involutive {d : ℕ} (i : Fin d) : Function.Involutive (flip i) := by
  intro b
  ext j
  by_cases h : j = i
  · subst h; simp [flip]
  · simp [flip, Function.update_of_ne h]

private lemma hammingDist_flip {d : ℕ} (i : Fin d) (b : Fin d → Bool) :
    hammingDist b (flip i b) = 1 := by
  classical
  unfold hammingDist
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases h : j = i
  · subst h; simp [flip]
  · simp [flip, h]

private lemma hammingDist_eq_sum {d : ℕ} (x y : Fin d → Bool) :
    (hammingDist x y : ℝ≥0∞) = ∑ i, if x i ≠ y i then 1 else 0 := by
  classical
  unfold hammingDist
  rw [Finset.card_filter]
  push_cast
  rfl

/-- **Assouad's lemma for one deterministic estimator.** For probability measures `P θ` and the
hypotheses of `mul_one_sub_le_minimax` (any `α ∈ [0, ∞]`), every deterministic estimator `T` with
measurable losses satisfies `β d (1 - τ) ≤ 4α sup_θ E_θ ℓ(θ, T)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 31.2, eq. (31.5), and its proof. -/
theorem mul_one_sub_le_four_mul_iSup (P : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (P θ)]
    (ℓ : Θ → Θ → ℝ≥0∞) (α : ℝ≥0∞) (htri : ∀ θ₀ θ₁ t, ℓ θ₀ θ₁ ≤ α * (ℓ θ₀ t + ℓ θ₁ t)) (d : ℕ)
    (θ : (Fin d → Bool) → Θ) (β : ℝ≥0∞)
    (hβ : ∀ b b', β * (hammingDist b b' : ℝ≥0∞) ≤ ℓ (θ b) (θ b')) (τ : ℝ)
    (hτ : ∀ b b', hammingDist b b' = 1 → totalVariationDist (P (θ b)) (P (θ b')) ≤ τ)
    (T : Ω → Θ) (hT : ∀ θ', Measurable fun ω => ℓ θ' (T ω)) :
    β * d * ENNReal.ofReal (1 - τ) ≤ 4 * α * ⨆ θ', ∫⁻ ω, ℓ θ' (T ω) ∂(P θ') := by
  classical
  set R := ⨆ θ', ∫⁻ ω, ℓ θ' (T ω) ∂(P θ')
  set L : (Fin d → Bool) → Ω → ℝ≥0∞ := fun b ω => ℓ (θ b) (T ω)
  obtain ⟨g, hg, hgmin⟩ := exists_measurable_argmin L fun b => hT (θ b)
  -- the coordinate events `A b i = {ĝ_i ≠ b_i}`
  set A : (Fin d → Bool) → Fin d → Set Ω := fun b i => {ω | g ω i ≠ b i}
  have hA : ∀ b i, MeasurableSet (A b i) := by
    intro b i
    have : A b i = ⋃ c ∈ {c : Fin d → Bool | c i ≠ b i}, g ⁻¹' {c} := by
      ext ω; simp [A]
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun c _ => hg c
  have hAflip : ∀ b i, A (flip i b) i = (A b i)ᶜ := by
    intro b i; ext ω; simp [A, flip]
  -- pointwise: `β d_H(ĝ, b) ≤ 2α ℓ(θ_b, T)`
  have hpt : ∀ b ω, β * (hammingDist (g ω) b : ℝ≥0∞) ≤ 2 * α * L b ω := by
    intro b ω
    calc β * (hammingDist (g ω) b : ℝ≥0∞) ≤ ℓ (θ (g ω)) (θ b) := hβ _ _
      _ ≤ α * (ℓ (θ (g ω)) (T ω) + ℓ (θ b) (T ω)) := htri _ _ _
      _ ≤ α * (L b ω + L b ω) := by gcongr; exact hgmin ω b
      _ = 2 * α * L b ω := by ring
  -- two-point testing bound for each coordinate and each pair `b, b ⊕ e_i`
  have htest : ∀ b i, ENNReal.ofReal (1 - τ) ≤ P (θ b) (A b i) + P (θ (flip i b)) (A b i)ᶜ := by
    intro b i
    have h1 := one_sub_totalVariationDist_le_add_compl (μ := P (θ b)) (ν := P (θ (flip i b)))
      (hA b i)
    have h2 := hτ b (flip i b) (hammingDist_flip i b)
    calc ENNReal.ofReal (1 - τ)
        ≤ ENNReal.ofReal ((P (θ b)).real (A b i) + (P (θ (flip i b))).real (A b i)ᶜ) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = P (θ b) (A b i) + P (θ (flip i b)) (A b i)ᶜ := by
          rw [ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg, measureReal_def,
            measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
            ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- summing over the cube, for each coordinate
  have hcoord : ∀ i, 2 ^ d * ENNReal.ofReal (1 - τ) ≤ 2 * ∑ b, P (θ b) (A b i) := by
    intro i
    have hperm : ∑ b, P (θ (flip i b)) (A (flip i b) i) = ∑ b, P (θ b) (A b i) :=
      Equiv.sum_comp ((flip_involutive i).toPerm (flip i)) (fun b => P (θ b) (A b i))
    calc 2 ^ d * ENNReal.ofReal (1 - τ) = ∑ _b : Fin d → Bool, ENNReal.ofReal (1 - τ) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
            nsmul_eq_mul]
      _ ≤ ∑ b, (P (θ b) (A b i) + P (θ (flip i b)) (A (flip i b) i)) := by
          gcongr with b
          rw [hAflip]
          exact htest b i
      _ = 2 * ∑ b, P (θ b) (A b i) := by
          rw [Finset.sum_add_distrib, hperm]; ring
  -- the Bayes risk under the uniform prior on the cube
  have hrisk : ∀ b, β * ∑ i, P (θ b) (A b i) ≤ 2 * α * ∫⁻ ω, L b ω ∂(P (θ b)) := by
    intro b
    have hind : ∀ i, Measurable fun ω => (if g ω i ≠ b i then (1 : ℝ≥0∞) else 0) := by
      intro i
      have : (fun ω => (if g ω i ≠ b i then (1 : ℝ≥0∞) else 0)) = (A b i).indicator 1 := by
        ext ω; by_cases h : g ω i ≠ b i <;> simp [A, h]
      rw [this]; exact measurable_one.indicator (hA b i)
    calc β * ∑ i, P (θ b) (A b i)
        = ∫⁻ ω, β * (hammingDist (g ω) b : ℝ≥0∞) ∂(P (θ b)) := by
          simp_rw [hammingDist_eq_sum]
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hind i),
            lintegral_finsetSum _ fun i _ => hind i]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          have : (fun ω => (if g ω i ≠ b i then (1 : ℝ≥0∞) else 0)) = (A b i).indicator 1 := by
            ext ω; by_cases h : g ω i ≠ b i <;> simp [A, h]
          rw [this, lintegral_indicator_one (hA b i)]
      _ ≤ ∫⁻ ω, 2 * α * L b ω ∂(P (θ b)) := lintegral_mono fun ω => hpt b ω
      _ = 2 * α * ∫⁻ ω, L b ω ∂(P (θ b)) := lintegral_const_mul _ (hT (θ b))
  have hsup : ∀ b, ∫⁻ ω, L b ω ∂(P (θ b)) ≤ R := fun b =>
    le_iSup (fun θ' => ∫⁻ ω, ℓ θ' (T ω) ∂(P θ')) (θ b)
  -- assemble
  have hcard : (∑ _b : Fin d → Bool, R) = 2 ^ d * R := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  have key : 2 ^ d * (β * d * ENNReal.ofReal (1 - τ)) ≤ 2 ^ d * (4 * α * R) := by
    calc 2 ^ d * (β * d * ENNReal.ofReal (1 - τ))
        = β * ∑ _i : Fin d, 2 ^ d * ENNReal.ofReal (1 - τ) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ β * ∑ i, 2 * ∑ b, P (θ b) (A b i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) zero_le
      _ = 2 * ∑ b, β * ∑ i, P (θ b) (A b i) := by
          rw [← Finset.mul_sum, Finset.sum_comm, ← Finset.mul_sum]
          simp_rw [Finset.mul_sum]; ring_nf
      _ ≤ 2 * ∑ b, 2 * α * ∫⁻ ω, L b ω ∂(P (θ b)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => hrisk b) zero_le
      _ ≤ 2 * ∑ _b : Fin d → Bool, 2 * α * R :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hsup b) zero_le) zero_le
      _ = 2 ^ d * (4 * α * R) := by rw [← Finset.mul_sum, hcard]; ring
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).mp key

/-- **Assouad's lemma.** Let `P : Kernel Θ Ω` be a statistical model of probability measures and
`ℓ : Θ → Θ → [0, ∞]` a loss, measurable in its second argument, satisfying the `α`-triangle
inequality `ℓ(θ₀, θ₁) ≤ α (ℓ(θ₀, t) + ℓ(θ₁, t))` with `α < ∞`. Suppose the parameters `θ_b`, indexed
by the hypercube `b ∈ {0, 1}^d`, satisfy `ℓ(θ_b, θ_{b'}) ≥ β d_H(b, b')`, and that neighbouring
hypotheses are within total variation `τ`: `TV(P θ_b, P θ_{b'}) ≤ τ` when `d_H(b, b') = 1`.
Then `β d (1 - τ) ≤ 4α · minimaxRisk ℓ P`, where `minimaxRisk ℓ P` is the infimum over all
randomised estimators (Markov kernels `κ : Ω → Θ`) of `sup_θ E_{(κ ∘ P)(θ)} ℓ(θ, ·)`; for
`0 < α < ∞` the minimax risk is at least `β d (1 - τ) / (4α)`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 31.2, eq. (31.5), with `τ` bounding the maximum there and the
minimax risk of Section 28.3.2. -/
theorem mul_one_sub_le_minimax [MeasurableSpace Θ] (P : Kernel Θ Ω) [IsMarkovKernel P]
    (ℓ : Θ → Θ → ℝ≥0∞) (hℓ : ∀ θ, Measurable (ℓ θ)) (α : ℝ≥0∞) (hα : α ≠ ⊤)
    (htri : ∀ θ₀ θ₁ t, ℓ θ₀ θ₁ ≤ α * (ℓ θ₀ t + ℓ θ₁ t)) (d : ℕ) (θ : (Fin d → Bool) → Θ)
    (β : ℝ≥0∞) (hβ : ∀ b b', β * (hammingDist b b' : ℝ≥0∞) ≤ ℓ (θ b) (θ b')) (τ : ℝ)
    (hτ : ∀ b b', hammingDist b b' = 1 → totalVariationDist (P (θ b)) (P (θ b')) ≤ τ) :
    β * d * ENNReal.ofReal (1 - τ) ≤ 4 * α * minimaxRisk ℓ P := by
  rcases eq_or_ne α 0 with rfl | hα₀
  · -- `α = 0`: test the bound on a constant estimator
    have h := mul_one_sub_le_four_mul_iSup (fun θ' => P θ') ℓ 0 htri d θ β hβ τ hτ
      (fun _ => θ fun _ => false) (fun _ => measurable_const)
    simpa using h
  have h4 : 4 * α ≠ 0 := mul_ne_zero (by norm_num) hα₀
  have h4' : 4 * α ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hα
  unfold minimaxRisk
  rw [ENNReal.mul_iInf_of_ne h4 h4']
  refine le_iInf fun κ => ?_
  rw [ENNReal.mul_iInf_of_ne h4 h4']
  refine le_iInf fun hκ => ?_
  have hτ' : ∀ b b', hammingDist b b' = 1 →
      totalVariationDist (κ ∘ₘ P (θ b)) (κ ∘ₘ P (θ b')) ≤ τ := fun b b' h =>
    (totalVariationDist_comp_le_self κ _ _).trans (hτ b b' h)
  have h := mul_one_sub_le_four_mul_iSup (fun θ' => κ ∘ₘ P θ') ℓ α htri d θ β hβ τ hτ' id hℓ
  refine h.trans (le_of_eq ?_)
  congr 1

end MathlibExt.Probability.Statistics.Assouad
