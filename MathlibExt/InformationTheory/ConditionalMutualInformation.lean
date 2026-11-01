/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ConditionalEntropy

/-!
# Conditional mutual information of finite laws and its chain rule

For a finite joint law `p` of `(X, Y, Z)` (a `PMF (α × β × γ)`), the conditional mutual
information is, in bits,
`I(X; Y | Z) = ∑ p(x, y, z) log₂ (p(x, y, z) p(z) / (p(x, z) p(y, z)))`.
Zero-probability atoms contribute zero; on atoms with `p(x, y, z) > 0` every marginal in the
quotient is positive, so no logarithm of zero or division by zero is used there.

Mutual information is the repository's `measureMutualInformation` (divergence of the joint law
from the product of its marginals), read on finite laws through `finiteMutualInformation`, its
real value.

## Main results

* `finiteConditionalMutualInformation_eq`: `I(X; Y | Z) = H(X, Z) + H(Y, Z) - H(X, Y, Z) - H(Z)`.
* `finiteConditionalMutualInformation_nonneg`: `0 ≤ I(X; Y | Z)`.
* `finiteConditionalMutualInformation_eq_zero_iff`: `I(X; Y | Z) = 0` iff `X` and `Y` are
  conditionally independent given `Z`, i.e. `p(x, y, z) p(z) = p(x, z) p(y, z)` for all atoms.
* `finiteMutualInformation_chain_rule` (**chain rule**): `I(X; (Y, Z)) = I(X; Z) + I(X; Y | Z)`.
* `finiteMutualInformation_le_left_of_markov` and `finiteMutualInformation_le_right_of_markov`
  (**data-processing inequality**): if `X` and `Z` are conditionally independent given `Y`
  (a Markov chain `X - Y - Z`), then `I(X; Z) ≤ I(X; Y)` and `I(X; Z) ≤ I(Y; Z)`.
  This is the inequality behind ARACNE's pruning of indirect interactions
  (`Cslib.Bioinformatics.GeneNetworks.Aracne`).

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  §2.5 (chain rule for information) and §2.8 (data-processing inequality).
-/

@[expose] public section

namespace InformationTheory

open MeasureTheory Real
open scoped ENNReal

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Summing a function of `f t` against `p` is summing against the pushforward `p.map f`. -/
theorem sum_toReal_mul_comp {τ δ : Type*} [Fintype τ] [Fintype δ] (p : PMF τ) (f : τ → δ)
    (φ : δ → ℝ) : ∑ t, (p t).toReal * φ (f t) = ∑ d, ((p.map f) d).toReal * φ d := by
  classical
  have hmap : ∀ d, ((p.map f) d).toReal = ∑ t with f t = d, (p t).toReal := by
    intro d
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun t _ ↦ by
      split_ifs <;> simp [PMF.apply_ne_top], Finset.sum_filter]
    exact Finset.sum_congr rfl fun t _ ↦ by split_ifs with h1 h2 h2 <;> simp_all [eq_comm]
  simp_rw [hmap, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun t ht ↦ ?_
  rw [(Finset.mem_filter.mp ht).2]

/-- An atom's mass is at most the mass of its image. -/
theorem le_map_apply {τ δ : Type*} (p : PMF τ) (f : τ → δ) (t : τ) :
    p t ≤ (p.map f) (f t) := by
  classical
  rw [PMF.map_apply]
  exact le_trans (by simp) (ENNReal.le_tsum t)

/-- An atom's mass is at most the mass of its image, as real numbers. -/
theorem toReal_le_map_apply {τ δ : Type*} (p : PMF τ) (f : τ → δ) (t : τ) :
    (p t).toReal ≤ ((p.map f) (f t)).toReal :=
  ENNReal.toReal_mono (PMF.apply_ne_top _ _) (le_map_apply p f t)

/-- Entropy times `log 2` as a `p log p` sum. -/
theorem shannonEntropy_mul_log_two {δ : Type*} [Fintype δ] (q : PMF δ) :
    shannonEntropy q * log 2 = -∑ d, (q d).toReal * log (q d).toReal := by
  rw [shannonEntropy, div_mul_cancel₀ _ (log_pos one_lt_two).ne', ← Finset.sum_neg_distrib]
  simp [negMulLog]

/-- `∑ p(t) log (p.map f)(f t) = -H(p.map f) log 2`. -/
theorem sum_mul_log_map {τ δ : Type*} [Fintype τ] [Fintype δ] (p : PMF τ) (f : τ → δ) :
    ∑ t, (p t).toReal * log ((p.map f) (f t)).toReal = -(shannonEntropy (p.map f) * log 2) := by
  rw [sum_toReal_mul_comp p f (fun d ↦ log ((p.map f) d).toReal), shannonEntropy_mul_log_two,
    neg_neg]


/-- Relabeling the image of a map by a bijection preserves entropy. -/
theorem shannonEntropy_map_equiv_comp {τ δ ε : Type*} [Fintype δ] [Fintype ε] (p : PMF τ)
    (f : τ → δ) (e : δ ≃ ε) : shannonEntropy (p.map (e ∘ f)) = shannonEntropy (p.map f) := by
  rw [← PMF.map_comp, shannonEntropy_map_equiv]

/-- Mutual information `I(X; Y)` of a finite joint law `p` of `(X, Y)`, in bits: the real value
of `measureMutualInformation` on `p`, which is finite here (`finiteMutualInformation_eq`). Each
finite alphabet carries the discrete σ-algebra. -/
noncomputable def finiteMutualInformation (p : PMF (α × β)) : ℝ :=
  letI : MeasurableSpace α := ⊤
  letI : MeasurableSpace β := ⊤
  (measureMutualInformation (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β))).toReal

/-- `I(X; Y) = H(X) + H(Y) - H(X, Y)` for a finite joint law. -/
theorem finiteMutualInformation_eq (p : PMF (α × β)) :
    finiteMutualInformation p =
      shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) - shannonEntropy p := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have : MeasurableSingletonClass β := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  rw [finiteMutualInformation, measureMutualInformation_toMeasure,
    ENNReal.toReal_ofReal (by linarith [shannonEntropy_le_add p])]

/-- The conditional mutual information `I(X; Y | Z)` of a finite joint law `p` of `(X, Y, Z)`, in
bits: `∑ p(x, y, z) log₂ (p(x, y, z) p(z) / (p(x, z) p(y, z)))`. -/
noncomputable def finiteConditionalMutualInformation (p : PMF (α × β × γ)) : ℝ :=
  ∑ a, ∑ b, ∑ c, (p (a, b, c)).toReal *
    logb 2 ((p (a, b, c)).toReal * ((p.map fun t ↦ t.2.2) c).toReal /
      (((p.map fun t ↦ (t.1, t.2.2)) (a, c)).toReal * ((p.map fun t ↦ t.2) (b, c)).toReal))

/-- `I(X; Y | Z) = H(X, Z) + H(Y, Z) - H(X, Y, Z) - H(Z)`. -/
theorem finiteConditionalMutualInformation_eq (p : PMF (α × β × γ)) :
    finiteConditionalMutualInformation p =
      shannonEntropy (p.map fun t ↦ (t.1, t.2.2)) + shannonEntropy (p.map fun t ↦ t.2) -
        shannonEntropy p - shannonEntropy (p.map fun t ↦ t.2.2) := by
  set fZ : α × β × γ → γ := fun t ↦ t.2.2
  set fXZ : α × β × γ → α × γ := fun t ↦ (t.1, t.2.2)
  set fYZ : α × β × γ → β × γ := fun t ↦ t.2
  have hsum : finiteConditionalMutualInformation p = ∑ t, (p t).toReal *
      logb 2 ((p t).toReal * ((p.map fZ) (fZ t)).toReal /
        (((p.map fXZ) (fXZ t)).toReal * ((p.map fYZ) (fYZ t)).toReal)) := by
    simp only [finiteConditionalMutualInformation, Fintype.sum_prod_type]
    rfl
  have hlog : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  have hterm : ∀ t, (p t).toReal * logb 2 ((p t).toReal * ((p.map fZ) (fZ t)).toReal /
        (((p.map fXZ) (fXZ t)).toReal * ((p.map fYZ) (fYZ t)).toReal)) =
      ((p t).toReal * log ((p.map id) (id t)).toReal +
        (p t).toReal * log ((p.map fZ) (fZ t)).toReal -
        (p t).toReal * log ((p.map fXZ) (fXZ t)).toReal -
        (p t).toReal * log ((p.map fYZ) (fYZ t)).toReal) / log 2 := by
    intro t
    simp only [PMF.map_id, id_eq]
    rcases (ENNReal.toReal_nonneg : 0 ≤ (p t).toReal).eq_or_lt with h | h
    · rw [← h]; simp
    have h1 := h.trans_le (toReal_le_map_apply p fZ t)
    have h2 := h.trans_le (toReal_le_map_apply p fXZ t)
    have h3 := h.trans_le (toReal_le_map_apply p fYZ t)
    rw [logb, log_div (mul_pos h h1).ne' (mul_pos h2 h3).ne', log_mul h.ne' h1.ne',
      log_mul h2.ne' h3.ne']
    ring
  rw [hsum, Finset.sum_congr rfl fun t _ ↦ hterm t, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_mul_log_map, sum_mul_log_map,
    sum_mul_log_map, sum_mul_log_map, PMF.map_id]
  field_simp
  ring

/-- The reference law `p(x, z) p(y, z) / p(z)` under which `X ⊥ Y | Z`. -/
private noncomputable def cmiRef {α β γ : Type*} (p : PMF (α × β × γ)) (t : α × β × γ) : ℝ≥0∞ :=
  (p.map fun t ↦ (t.1, t.2.2)) (t.1, t.2.2) * (p.map fun t ↦ t.2) t.2 /
    (p.map fun t ↦ t.2.2) t.2.2

/-- Summing out `X` from the law of `(X, Z)` gives the law of `Z`. -/
private theorem sum_map_xz {α β γ : Type*} [Fintype α] [Finite γ]
    (p : PMF (α × β × γ)) (c : γ) :
    ∑ a, (p.map fun t ↦ (t.1, t.2.2)) (a, c) = (p.map fun t ↦ t.2.2) c := by
  rw [← map_snd_apply, PMF.map_comp]
  rfl

/-- Summing out `Y` from the law of `(Y, Z)` gives the law of `Z`. -/
private theorem sum_map_yz {α β γ : Type*} [Fintype β] [Finite γ]
    (p : PMF (α × β × γ)) (c : γ) :
    ∑ b, (p.map fun t ↦ t.2) (b, c) = (p.map fun t ↦ t.2.2) c := by
  rw [← map_snd_apply, PMF.map_comp]
  rfl

/-- The reference law sums to one. -/
private theorem sum_cmiRef {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF (α × β × γ)) : ∑ t, cmiRef p t = 1 := by
  set pZ := p.map fun t ↦ t.2.2
  calc ∑ t, cmiRef p t
      = ∑ c, (∑ a, (p.map fun t ↦ (t.1, t.2.2)) (a, c)) * (∑ b, (p.map fun t ↦ t.2) (b, c)) *
          (pZ c)⁻¹ := by
        simp only [cmiRef, Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        conv_lhs => rw [Finset.sum_comm]
        conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
    _ = ∑ c, pZ c := by
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        rw [sum_map_xz, sum_map_yz]
        by_cases h : pZ c = 0
        · rw [h, zero_mul, zero_mul]
        · rw [mul_assoc, ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _), mul_one]
    _ = 1 := by
        have := PMF.tsum_coe pZ
        rwa [tsum_fintype] at this

/-- The reference law as a `PMF`. -/
private noncomputable def cmiRefPMF {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF (α × β × γ)) : PMF (α × β × γ) :=
  PMF.ofFintype (cmiRef p) (sum_cmiRef p)

/-- `p` is absolutely continuous with respect to the reference law. -/
private theorem cmiRefPMF_eq_zero {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF (α × β × γ)) (t : α × β × γ) (ht : cmiRefPMF p t = 0) : p t = 0 := by
  simp only [cmiRefPMF, PMF.ofFintype_apply, cmiRef, ENNReal.div_eq_zero_iff,
    PMF.apply_ne_top, or_false, mul_eq_zero] at ht
  rcases ht with h | h
  · exact le_antisymm ((le_map_apply p (fun t ↦ (t.1, t.2.2)) t).trans h.le) bot_le
  · exact le_antisymm ((le_map_apply p (fun t ↦ t.2) t).trans h.le) bot_le

/-- `I(X; Y | Z)` is the divergence of the reference law from `p`, in bits. -/
private theorem cmi_eq_klDiv {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : PMF (α × β × γ)) :
    letI : MeasurableSpace (α × β × γ) := ⊤
    finiteConditionalMutualInformation p =
      (klDiv p.toMeasure (cmiRefPMF p).toMeasure).toReal / log 2 := by
  let : MeasurableSpace (α × β × γ) := ⊤
  have : MeasurableSingletonClass (α × β × γ) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  rw [toReal_klDiv_toMeasure (cmiRefPMF_eq_zero p), Finset.sum_div,
    finiteConditionalMutualInformation]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [cmiRefPMF, PMF.ofFintype_apply, cmiRef, ENNReal.toReal_div, ENNReal.toReal_mul,
    logb, div_div_eq_mul_div]
  ring

/-- Conditional mutual information is nonnegative. -/
theorem finiteConditionalMutualInformation_nonneg (p : PMF (α × β × γ)) :
    0 ≤ finiteConditionalMutualInformation p := by
  rw [cmi_eq_klDiv]
  exact div_nonneg ENNReal.toReal_nonneg (log_pos one_lt_two).le

/-- `I(X; Y | Z) = 0` exactly when `X` and `Y` are conditionally independent given `Z`:
`p(x, y, z) p(z) = p(x, z) p(y, z)` for every atom. -/
theorem finiteConditionalMutualInformation_eq_zero_iff (p : PMF (α × β × γ)) :
    finiteConditionalMutualInformation p = 0 ↔
      ∀ a b c, p (a, b, c) * (p.map fun t ↦ t.2.2) c =
        (p.map fun t ↦ (t.1, t.2.2)) (a, c) * (p.map fun t ↦ t.2) (b, c) := by
  let : MeasurableSpace (α × β × γ) := ⊤
  have : MeasurableSingletonClass (α × β × γ) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hne : klDiv p.toMeasure (cmiRefPMF p).toMeasure ≠ ⊤ :=
    klDiv_ne_top (toMeasure_absolutelyContinuous (cmiRefPMF_eq_zero p)) Integrable.of_finite
  rw [cmi_eq_klDiv, div_eq_zero_iff, or_iff_left (log_pos one_lt_two).ne',
    ENNReal.toReal_eq_zero_iff, or_iff_left hne, klDiv_eq_zero_iff, PMF.toMeasure_inj]
  have hpt : ∀ a b c, p (a, b, c) = cmiRef p (a, b, c) ↔ p (a, b, c) * (p.map fun t ↦ t.2.2) c =
      (p.map fun t ↦ (t.1, t.2.2)) (a, c) * (p.map fun t ↦ t.2) (b, c) := by
    intro a b c
    by_cases hC : (p.map fun t ↦ t.2.2) c = 0
    · have hp0 : p (a, b, c) = 0 :=
        le_antisymm ((le_map_apply p (fun t ↦ t.2.2) (a, b, c)).trans hC.le) bot_le
      have hA0 : (p.map fun t ↦ (t.1, t.2.2)) (a, c) = 0 := by
        refine le_antisymm ?_ bot_le
        have := le_map_apply (p.map fun t ↦ (t.1, t.2.2)) Prod.snd (a, c)
        rw [PMF.map_comp] at this
        exact this.trans hC.le
      simp [cmiRef, hp0, hA0, hC]
    · rw [cmiRef, ENNReal.eq_div_iff hC (PMF.apply_ne_top _ _), mul_comm]
  rw [PMF.ext_iff, Prod.forall]
  simp only [Prod.forall, cmiRefPMF, PMF.ofFintype_apply]
  exact forall_congr' fun a ↦ forall_congr' fun b ↦ forall_congr' fun c ↦ hpt a b c

/-- **Chain rule for mutual information**: `I(X; (Y, Z)) = I(X; Z) + I(X; Y | Z)`. Here `p` is
read as a joint law of `X` and the pair `(Y, Z)`. -/
theorem finiteMutualInformation_chain_rule (p : PMF (α × β × γ)) :
    finiteMutualInformation p =
      finiteMutualInformation (p.map fun t ↦ (t.1, t.2.2)) +
        finiteConditionalMutualInformation p := by
  rw [finiteMutualInformation_eq, finiteMutualInformation_eq,
    finiteConditionalMutualInformation_eq, PMF.map_comp, PMF.map_comp]
  simp only [Function.comp_def]
  ring

/-- **Data-processing inequality**, first half: if `X` and `Z` are conditionally independent given
`Y` (a Markov chain `X - Y - Z`, stated as `I(X; Z | Y) = 0` for the joint law `p` of
`(X, Y, Z)`), then `I(X; Z) ≤ I(X; Y)`. -/
theorem finiteMutualInformation_le_left_of_markov (p : PMF (α × β × γ))
    (hp : finiteConditionalMutualInformation (p.map fun t ↦ (t.1, t.2.2, t.2.1)) = 0) :
    finiteMutualInformation (p.map fun t ↦ (t.1, t.2.2)) ≤
      finiteMutualInformation (p.map fun t ↦ (t.1, t.2.1)) := by
  have h0 := finiteConditionalMutualInformation_nonneg p
  rw [finiteConditionalMutualInformation_eq] at hp h0
  rw [finiteMutualInformation_eq, finiteMutualInformation_eq]
  simp only [PMF.map_comp, Function.comp_def] at hp h0 ⊢
  have e1 : shannonEntropy (p.map fun t ↦ (t.2.2, t.2.1)) = shannonEntropy (p.map fun t ↦ t.2) :=
    shannonEntropy_map_equiv_comp p (fun t ↦ t.2) (Equiv.prodComm β γ)
  have e2 : shannonEntropy (p.map fun t ↦ (t.1, t.2.2, t.2.1)) = shannonEntropy p :=
    shannonEntropy_map_equiv p ((Equiv.refl α).prodCongr (Equiv.prodComm β γ))
  linarith

/-- **Data-processing inequality**, second half: under the same Markov condition,
`I(X; Z) ≤ I(Y; Z)`. -/
theorem finiteMutualInformation_le_right_of_markov (p : PMF (α × β × γ))
    (hp : finiteConditionalMutualInformation (p.map fun t ↦ (t.1, t.2.2, t.2.1)) = 0) :
    finiteMutualInformation (p.map fun t ↦ (t.1, t.2.2)) ≤
      finiteMutualInformation (p.map fun t ↦ t.2) := by
  have h0 := finiteConditionalMutualInformation_nonneg (p.map fun t ↦ (t.2.1, t.2.2, t.1))
  rw [finiteConditionalMutualInformation_eq] at hp h0
  rw [finiteMutualInformation_eq, finiteMutualInformation_eq]
  simp only [PMF.map_comp, Function.comp_def] at hp h0 ⊢
  have e1 : shannonEntropy (p.map fun t ↦ (t.2.2, t.2.1)) = shannonEntropy (p.map fun t ↦ t.2) :=
    shannonEntropy_map_equiv_comp p (fun t ↦ t.2) (Equiv.prodComm β γ)
  have e2 : shannonEntropy (p.map fun t ↦ (t.1, t.2.2, t.2.1)) = shannonEntropy p :=
    shannonEntropy_map_equiv p ((Equiv.refl α).prodCongr (Equiv.prodComm β γ))
  have e3 : shannonEntropy (p.map fun t ↦ (t.2.1, t.1)) =
      shannonEntropy (p.map fun t ↦ (t.1, t.2.1)) :=
    shannonEntropy_map_equiv_comp p (fun t ↦ (t.1, t.2.1)) (Equiv.prodComm α β)
  have e4 : shannonEntropy (p.map fun t ↦ (t.2.2, t.1)) =
      shannonEntropy (p.map fun t ↦ (t.1, t.2.2)) :=
    shannonEntropy_map_equiv_comp p (fun t ↦ (t.1, t.2.2)) (Equiv.prodComm α γ)
  have e5 : shannonEntropy (p.map fun t ↦ (t.2.1, t.2.2, t.1)) = shannonEntropy p :=
    shannonEntropy_map_equiv p ((Equiv.prodComm α (β × γ)).trans (Equiv.prodAssoc β γ α))
  linarith

end InformationTheory
