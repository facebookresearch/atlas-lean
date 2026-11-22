/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.RandomCodingBound
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Order.Filter.AtTopBot.Archimedean

@[expose] public section

/-!
# Shannon's channel coding theorem, achievability, by Gallager's random coding bound

For a discrete memoryless channel on finite alphabets, every rate below capacity is achievable
with vanishing maximal error probability. The proof is Gallager's (1965): the expurgated random
coding bound (`RandomCodingBound.exists_code_mlErrorProb_le`, Corollary 2) bounds every code
word's error by `4 M^ρ exp(-N E₀(ρ, p))`, and the exponent `E₀(ρ, p) - ρ R` is positive for a
suitable `ρ` when `R < I(p; W)` (`GallagerExponent.exists_gallagerE0_sub_pos`). A
maximum-likelihood decoder with any tie-breaking rule then has maximal error at most
`4 exp(-N (E₀ - ρ R))`, which tends to `0`.

The statement was first recorded as wanted in `WantedExt.InformationTheory.ChannelCodingWanted`,
which keeps the two converses.

* `measureReal_pi_le_mlErrorProb`: for a maximum-likelihood decoder `g`, the product-measure
  probability that `g` errs on message `m` is at most `mlErrorProb W C m`.
* `channelCoding_achievability`: Shannon's achievability with maximal error.

## References

* R. G. Gallager, A simple derivation of the coding theorem and some applications, IEEE Trans.
  Inform. Theory IT-11 (1965), 3–18: Theorem 1, Corollary 2, Theorems 2 and 3.
* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Theorem 19.9 with Corollary 19.5 (the statement as recorded).
-/

namespace MathlibExt.InformationTheory.ChannelCodingAchievability

open MeasureTheory Filter Topology _root_.InformationTheory
  MathlibExt.InformationTheory.GallagerExponent MathlibExt.InformationTheory.RandomCodingBound

variable {α β : Type*}

/-- **Maximum-likelihood decoding errs only on ties or worse.** If the decoder `g` picks, for
every output `y`, a message maximising `W^N(y | x_m)`, then the probability under the product law
`W^N(· | x_m)` that `g` does not return `m` is at most `mlErrorProb W C m`, the probability that
some other code word is at least as likely. -/
theorem measureReal_pi_le_mlErrorProb [Fintype β] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (W : α → PMF β) {N M : ℕ} (C : Fin M → Fin N → α) (g : (Fin N → β) → Fin M)
    (hg : ∀ y m, blockTransition W (C m) y ≤ blockTransition W (C (g y)) y) (m : Fin M) :
    (Measure.pi fun i => (W (C m i)).toMeasure).real {y | g y ≠ m} ≤ mlErrorProb W C m := by
  classical
  set μ := Measure.pi fun i => (W (C m i)).toMeasure
  set bad : Finset (Fin N → β) := Finset.univ.filter fun y =>
    ∃ m', m' ≠ m ∧ blockTransition W (C m) y ≤ blockTransition W (C m') y
  have hsub : {y | g y ≠ m} ⊆ (bad : Set (Fin N → β)) := by
    intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, bad] at hy ⊢
    exact ⟨g y, hy, hg y m⟩
  have hsing : ∀ y, μ.real {y} = blockTransition W (C m) y := by
    intro y
    rw [measureReal_def, ← Set.univ_pi_singleton, Measure.pi_pi]
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete)]
  calc μ.real {y | g y ≠ m} ≤ μ.real (bad : Set (Fin N → β)) := measureReal_mono hsub
    _ = ∑ y ∈ bad, μ.real {y} := (sum_measureReal_singleton bad).symm
    _ = mlErrorProb W C m := by
        simp_rw [hsing]
        unfold mlErrorProb
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp

/-- **A maximum-likelihood decoder exists.** For a code with at least one word there is a
decoder that returns, for every output, a most likely message. -/
theorem exists_mlDecoder (W : α → PMF β) {N M : ℕ} (hM : 0 < M) (C : Fin M → Fin N → α) :
    ∃ g : (Fin N → β) → Fin M,
      ∀ y m, blockTransition W (C m) y ≤ blockTransition W (C (g y)) y := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  refine ⟨fun y => (Finset.univ.exists_max_image (fun m => blockTransition W (C m) y)
    Finset.univ_nonempty).choose, fun y m => ?_⟩
  exact (Finset.univ.exists_max_image (fun m => blockTransition W (C m) y)
    Finset.univ_nonempty).choose_spec.2 m (Finset.mem_univ m)

set_option linter.unusedFintypeInType false in
/-- **Shannon's channel coding theorem, achievability.** For a discrete memoryless channel
`W : α → PMF β` on finite alphabets (`α` nonempty), every rate `R < C(W)` (bits per channel use)
is achievable with maximal error probability at most `ε`, for every `ε > 0` and all large
blocklengths `n`: there is a code with `M ≥ 2^{nR}` codewords of length `n` whose every message
is decoded wrongly with probability at most `ε`.
Source: Y. Polyanskiy and Y. Wu, Information Theory: From Coding to Learning (Cambridge
University Press, 2025), Theorem 19.9 with Corollary 19.5 (in particular `C^(max) = C`);
C. E. Shannon (1948), Theorem 11. Proved here by Gallager's route (R. G. Gallager, A simple
derivation of the coding theorem and some applications, IEEE Trans. Inform. Theory IT-11 (1965),
Theorem 1 and Corollary 2), with a maximum-likelihood decoder. -/
public theorem channelCoding_achievability {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [MeasurableSpace β] [DiscreteMeasurableSpace β] (W : α → PMF β) {R : ℝ}
    (hR : R < ⨆ p : PMF α, finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, ∃ (M : ℕ) (f : Fin M → Fin n → α) (g : (Fin n → β) → Fin M),
      (2 : ℝ) ^ ((n : ℝ) * R) ≤ M ∧
        ∀ m, (Measure.pi fun i => (W (f m i)).toMeasure).real {y | g y ≠ m} ≤ ε := by
  classical
  -- Rates `R ≤ 0`: one code word, never in error.
  rcases le_or_gt R 0 with hR0 | hR0
  · refine Filter.Eventually.of_forall fun n => ?_
    obtain ⟨a⟩ := ‹Nonempty α›
    refine ⟨1, fun _ _ => a, fun _ => 0, ?_, fun m => ?_⟩
    · have : (2 : ℝ) ^ ((n : ℝ) * R) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR0)
      simpa using this
    · have : m = 0 := Subsingleton.elim _ _
      subst this
      simp [hε.le]
  -- Rates `0 < R < C`: pick an input law with `R < I(p; W)` and a rate `R'` in nats in between.
  have : Nonempty (PMF α) := ⟨PMF.pure (Classical.arbitrary α)⟩
  obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hR
  set I := finiteMutualInformation (p.bind fun a => (W a).map (Prod.mk a))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set R' := (R + I) / 2 * Real.log 2
  have hR'I : R' < I * Real.log 2 := by simp only [R']; nlinarith
  have hRR' : R * Real.log 2 < R' := by simp only [R']; nlinarith
  obtain ⟨ρ, ⟨hρ0, hρ1⟩, hE⟩ := exists_gallagerE0_sub_pos p W hR'I
  set E := gallagerE0 p W ρ - ρ * R'
  -- Eventually `2 · 2^{nR} ≤ e^{nR'}` and `4 e^{-nE} ≤ ε`.
  have hev1 : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ n * (R' - R * Real.log 2) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)).eventually_ge_atTop _
  have hev2 : ∀ᶠ n : ℕ in atTop, 4 * Real.exp (-(n * E)) ≤ ε := by
    have ht : Tendsto (fun n : ℕ => 4 * Real.exp (-(n * E))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hE)).const_mul 4
      simpa [Function.comp_def] using this
    exact ht.eventually (ge_mem_nhds hε)
  filter_upwards [hev1, hev2] with n hn1 hn2
  set x : ℝ := (2 : ℝ) ^ ((n : ℝ) * R)
  have hx1 : 1 ≤ x := Real.one_le_rpow (by norm_num) (by positivity)
  set M : ℕ := ⌈x⌉₊
  have hMpos : 0 < M := Nat.ceil_pos.2 (by linarith)
  have hxM : x ≤ M := Nat.le_ceil x
  have hMR : (M : ℝ) ≤ Real.exp (n * R') := by
    have hceil : (M : ℝ) ≤ 2 * x := by
      have := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
      linarith
    have hxexp : x = Real.exp (n * R * Real.log 2) := by
      simp only [x]
      rw [Real.rpow_def_of_pos (by norm_num)]
      ring_nf
    calc (M : ℝ) ≤ 2 * x := hceil
      _ = Real.exp (Real.log 2 + n * R * Real.log 2) := by
          rw [hxexp, Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (n * R') := Real.exp_le_exp.2 (by nlinarith)
  obtain ⟨C, hC⟩ := exists_code_mlErrorProb_le p W n M hMpos hρ0.le hρ1
  obtain ⟨g, hg⟩ := exists_mlDecoder W hMpos C
  refine ⟨M, C, g, hxM, fun m => (measureReal_pi_le_mlErrorProb W C g hg m).trans
    ((hC m).trans ?_)⟩
  calc 4 * (M : ℝ) ^ ρ * Real.exp (-(n * gallagerE0 p W ρ))
      ≤ 4 * Real.exp (n * R') ^ ρ * Real.exp (-(n * gallagerE0 p W ρ)) := by
        gcongr
    _ = 4 * Real.exp (-(n * E)) := by
        rw [← Real.exp_mul, mul_assoc, ← Real.exp_add]
        simp only [E]
        ring_nf
    _ ≤ ε := hn2

end MathlibExt.InformationTheory.ChannelCodingAchievability
