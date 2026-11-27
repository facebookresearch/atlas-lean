/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Piling-up lemma and toy-substitution-permutation-network trail bias

Matsui's piling-up lemma (EUROCRYPT 1993 / CRYPTO 1994): for independent bits
with `Pr[X_i = false] = 1 / 2 + eps_i`, the xor satisfies
`Pr[xor = false] = 1 / 2 + 2 ^ (n - 1) * prod eps_i`. It is proved here in
correlation form (the xor correlation is the product of the correlations),
together with a finite toy-SPN model whose linear-trail bias telescopes to
the boundary parities. No attack procedure or key-recovery claim is made.
-/

open scoped BigOperators

@[expose] public section

namespace Cslib.Crypto.SymmetricKey.PilingUp

/-! ## Part 1: abstract piling-up lemma (L1-L5, L7) -/

/-- Bias of a Boolean distribution: `Pr[false] - 1/2`. -/
noncomputable def bias (p : PMF Bool) : Real :=
  (p false).toReal - 1 / 2

/-- Correlation of a Boolean distribution: `Pr[false] - Pr[true]`. -/
noncomputable def correlation (p : PMF Bool) : Real :=
  (p false).toReal - (p true).toReal

/-- The two Boolean probabilities sum to one. -/
theorem pmf_bool_toReal_add (p : PMF Bool) :
  (p false).toReal + (p true).toReal = 1 := by
  have hsum : (∑ b, p b) = 1 := by
    have h := p.tsum_coe
    rwa [tsum_fintype] at h
  have hfin : ∀ b ∈ (Finset.univ : Finset Bool), p b ≠ ⊤ := by
    intro b _
    exact ne_of_lt (lt_of_le_of_lt (p.coe_le_one b) ENNReal.one_lt_top)
  have hreal := ENNReal.toReal_sum hfin
  rw [hsum, ENNReal.toReal_one, Fintype.sum_bool] at hreal
  linarith

/-- Correlation is twice the bias. -/
theorem correlation_eq_two_mul_bias (p : PMF Bool) :
  correlation p = 2 * bias p := by
  unfold correlation bias
  have h := pmf_bool_toReal_add p
  linarith

/-- Product joint of independent Boolean factors (independence by construction). -/
noncomputable def jointPMF {n : Nat} (p : Fin n → PMF Bool) : PMF (Fin n → Bool) :=
  PMF.ofFintype (fun w => ∏ i, p i (w i)) (by
    have h1 : ∀ i : Fin n, (∑ b, p i b) = 1 := fun i => by
      have h := (p i).tsum_coe
      rwa [tsum_fintype] at h
    have hinter :=
      Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun i b => p i b)
    have hpi : Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset Bool))
      = Finset.univ := by
        ext f
        simp [Fintype.mem_piFinset]
    rw [hpi] at hinter
    rw [hinter]
    simp only [h1, Finset.prod_const_one])

/-- Applying the product joint gives the product of factor weights. -/
theorem jointPMF_apply (n : Nat) (p : Fin n → PMF Bool) (w : Fin n → Bool) :
  jointPMF p w = ∏ i, p i (w i) := rfl

/-- Real-valued weights of the product joint factorize. -/
theorem jointPMF_toReal (n : Nat) (p : Fin n → PMF Bool) (w : Fin n → Bool) :
  (jointPMF p w).toReal = ∏ i, ((p i (w i)).toReal) := by
  rw [jointPMF_apply]
  exact ENNReal.toReal_prod _ _

/-- Xor of all bits of a word, by recursion on the width. -/
def xorAll : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | m + 1, w => w 0 ^^ xorAll m (fun i => w i.succ)

/-- Xor over the empty word is `false`. -/
theorem xorAll_zero (w : Fin 0 → Bool) : xorAll 0 w = false := rfl

/-- Xor over a nonempty word splits off the first bit. -/
theorem xorAll_succ (m : Nat) (w : Fin (m + 1) → Bool) :
  xorAll (m + 1) w = (w 0 ^^ xorAll m (fun i => w i.succ)) := rfl

/-- Sign of a bit: `false` maps to `1`, `true` maps to `-1`. -/
def bitSign (b : Bool) : Real :=
  if b then -1 else 1

/-- Sign of xor is the product of signs. -/
theorem bitSign_xor (a b : Bool) : bitSign (a ^^ b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> simp [bitSign]

/-- Sign of `false` is one. -/
theorem bitSign_false : bitSign false = 1 := rfl

/-- Sign of `true` is negative one. -/
theorem bitSign_true : bitSign true = -1 := rfl

/-- Sign of the xor is the product of bit signs. -/
theorem bitSign_xorAll (n : Nat) : ∀ (w : Fin n → Bool),
  bitSign (xorAll n w) = ∏ i, bitSign (w i) := by
  induction n with
  | zero =>
    intro w
    simp [xorAll_zero, bitSign_false]
  | succ m ih =>
    intro w
    rw [xorAll_succ, bitSign_xor, ih, Fin.prod_univ_succ]

/-- Classical filters from `PMF.map_ofFintype` agree with computable ones. -/
theorem classical_filter_eq (α : Type*) (p : α → Prop) [DecidablePred p]
  (s : Finset α) :
  @Finset.filter α p (fun x => Classical.propDecidable (p x)) s
  = s.filter p := by
  ext x
  simp [Finset.mem_filter]

/-- The probability that the exclusive or of independent bits `w i ~ p i` equals `b` is the sum,
over the words `w` with `xorAll n w = b`, of `∏ i, p i (w i)`. -/
theorem map_xorAll_apply (n : Nat) (p : Fin n → PMF Bool) (b : Bool) :
  ((jointPMF p).map (xorAll n)) b
  = ∑ w ∈ Finset.univ.filter (fun w => xorAll n w = b),
  ∏ i, p i (w i) := by
  unfold jointPMF
  rw [PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply, classical_filter_eq]

/-- Real pushforward weights as filtered sums of factorized weights. -/
theorem map_xorAll_toReal (n : Nat) (p : Fin n → PMF Bool) (b : Bool) :
  (((jointPMF p).map (xorAll n)) b).toReal
  = ∑ w ∈ Finset.univ.filter (fun w => xorAll n w = b),
  ∏ i, ((p i (w i)).toReal) := by
  rw [map_xorAll_apply]
  have hfin : ∀ w ∈ Finset.univ.filter (fun w => xorAll n w = b),
    (∏ i, p i (w i)) ≠ ⊤ := by
      intro w _
      have hle : (∏ i, p i (w i)) ≤ 1 := by
        rw [← jointPMF_apply]
        exact (jointPMF p).coe_le_one w
      exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  rw [ENNReal.toReal_sum hfin]
  apply Finset.sum_congr rfl
  intro w _
  exact ENNReal.toReal_prod _ _

/-- Correlation as a signed sum over both bits. -/
theorem correlation_eq_sum_sign (p : PMF Bool) :
  correlation p = ∑ b, bitSign b * (p b).toReal := by
  rw [Fintype.sum_bool]
  unfold correlation
  simp [bitSign_true, bitSign_false]
  ring

/-- Product of correlations as a sum over all words. -/
theorem prod_correlation_eq_sum (n : Nat) (p : Fin n → PMF Bool) :
  (∏ i, correlation (p i))
  = ∑ w : Fin n → Bool, ∏ i, (bitSign (w i) * ((p i (w i)).toReal)) := by
  simp only [correlation_eq_sum_sign]
  rw [← Finset.sum_prod_piFinset]
  have hpi : Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset Bool))
    = Finset.univ := by
      ext f
      simp [Fintype.mem_piFinset]
  rw [hpi]

/-- Per-word product splits into xor sign times weight product. -/
theorem prod_sign_mul_toReal (n : Nat) (p : Fin n → PMF Bool)
  (w : Fin n → Bool) :
  (∏ i, (bitSign (w i) * ((p i (w i)).toReal)))
  = bitSign (xorAll n w) * (∏ i, ((p i (w i)).toReal)) := by
  rw [Finset.prod_mul_distrib, ← bitSign_xorAll n w]

/-- The signed sum over all words is the difference of fiber sums. -/
theorem sum_sign_mul_eq_sub (n : Nat) (p : Fin n → PMF Bool) :
  (∑ w, bitSign (xorAll n w) * (∏ i, ((p i (w i)).toReal)))
  = (∑ w ∈ Finset.univ.filter (fun w => xorAll n w = false),
  ∏ i, ((p i (w i)).toReal))
  - (∑ w ∈ Finset.univ.filter (fun w => xorAll n w = true),
  ∏ i, ((p i (w i)).toReal)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n → Bool)) (fun w => xorAll n w = false)
    (fun w => bitSign (xorAll n w) * (∏ i, ((p i (w i)).toReal)))
  have hF : (∑ w ∈ Finset.univ.filter (fun w => xorAll n w = false),
    bitSign (xorAll n w) * (∏ i, ((p i (w i)).toReal)))
    = ∑ w ∈ Finset.univ.filter (fun w => xorAll n w = false),
    ∏ i, ((p i (w i)).toReal) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hx : xorAll n w = false := (Finset.mem_filter.mp hw).2
      rw [hx, bitSign_false, one_mul]
  have hT : (∑ w ∈ Finset.univ.filter (fun w => ¬ xorAll n w = false),
    bitSign (xorAll n w) * (∏ i, ((p i (w i)).toReal)))
    = - (∑ w ∈ Finset.univ.filter (fun w => xorAll n w = true),
    ∏ i, ((p i (w i)).toReal)) := by
      have hfilter : (Finset.univ.filter
        (fun w : Fin n → Bool => ¬ xorAll n w = false))
        = Finset.univ.filter (fun w => xorAll n w = true) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          cases xorAll n w <;> simp
      rw [hfilter]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      have hx : xorAll n w = true := (Finset.mem_filter.mp hw).2
      rw [hx, bitSign_true]
      ring
  rw [hF, hT] at hsplit
  linarith [hsplit]

/-- Correlation of the xor is the product of correlations (L3). -/
theorem correlation_xor (n : Nat) (p : Fin n → PMF Bool) :
  correlation ((jointPMF p).map (xorAll n)) = ∏ i, correlation (p i) := by
  rw [prod_correlation_eq_sum]
  unfold correlation
  rw [map_xorAll_toReal n p false, map_xorAll_toReal n p true]
  have h1 : (∑ w : Fin n → Bool, ∏ i, (bitSign (w i) * ((p i (w i)).toReal)))
    = (∑ w, bitSign (xorAll n w) * (∏ i, ((p i (w i)).toReal))) :=
    Finset.sum_congr rfl (fun w _ => prod_sign_mul_toReal n p w)
  rw [h1, sum_sign_mul_eq_sub]

/-- The product of the correlations is `2 ^ n` times the product of the biases: `∏ i,
correlation (p i) = 2 ^ n * ∏ i, bias (p i)`. -/
theorem prod_correlation_eq_pow_mul_prod_bias (n : Nat) (p : Fin n → PMF Bool) :
  (∏ i, correlation (p i)) = (2 : Real) ^ n * (∏ i, bias (p i)) := by
  simp only [correlation_eq_two_mul_bias, Finset.prod_mul_distrib]
  congr 1
  simp [Finset.prod_const]

/-- Matsui form of the piling-up lemma for `n ≥ 1` (L4). -/
theorem pilingUp (n : Nat) (p : Fin n → PMF Bool) (hn : 1 ≤ n) :
  (((jointPMF p).map (xorAll n)) false).toReal
  = 1 / 2 + 2 ^ (n - 1) * (∏ i, bias (p i)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [show m.succ - 1 = m by omega]
  have hcorr := correlation_xor (m + 1) p
  rw [prod_correlation_eq_pow_mul_prod_bias] at hcorr
  unfold correlation at hcorr
  have hadd := pmf_bool_toReal_add ((jointPMF p).map (xorAll (m + 1)))
  have hpow : (2 : Real) ^ (m + 1) = 2 * 2 ^ m := by ring
  rw [hpow] at hcorr
  set C : Real := (2 : Real) ^ m * (∏ i, bias (p i)) with hC
  have key : (((jointPMF p).map (xorAll (m + 1))) false).toReal
    - (((jointPMF p).map (xorAll (m + 1))) true).toReal = 2 * C := by
      rw [hC]
      linear_combination hcorr
  linarith [hadd, key]

/-- Empty xor is always `false`, so its probability is one (L5). -/
theorem pilingUp_zero (p : Fin 0 → PMF Bool) :
  (((jointPMF p).map (xorAll 0)) false).toReal = 1 := by
  have hmap : (jointPMF p).map (xorAll 0) = PMF.pure false := by
    have hfun : xorAll 0 = Function.const (Fin 0 → Bool) false := by
      funext w
      exact xorAll_zero w
    rw [hfun]
    exact PMF.map_const _ _
  rw [hmap]
  simp [PMF.pure_apply]

/-- One-bit xor is the bit itself (L5). -/
theorem pilingUp_one (p : Fin 1 → PMF Bool) :
  (((jointPMF p).map (xorAll 1)) false).toReal = ((p 0) false).toReal := by
  have h := pilingUp 1 p (by norm_num)
  rw [Fin.prod_univ_one] at h
  unfold bias at h
  norm_num at h ⊢
  linarith [h]

/-- A zero-correlation factor kills the xor correlation (L5). -/
theorem correlation_xor_eq_zero (n : Nat) (p : Fin n → PMF Bool)
  (j : Fin n) (hj : correlation (p j) = 0) :
  correlation ((jointPMF p).map (xorAll n)) = 0 := by
  rw [correlation_xor]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hj

/-- Pushforward of an `ofFintype` law, as real filtered sums. -/
theorem map_ofFintype_toReal (α β : Type*) [Fintype α] [Fintype β]
  [DecidableEq β] (f : α → ENNReal) (h : ∑ a, f a = 1)
  (g : α → β) (b : β) :
  (((PMF.ofFintype f h).map g) b).toReal
  = ∑ a ∈ Finset.univ.filter (fun a => g a = b), (f a).toReal := by
  rw [PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply, classical_filter_eq]
  apply ENNReal.toReal_sum
  intro a _
  have hle : f a ≤ 1 := by
    have h1 : f a ≤ ∑ x, f x :=
      Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ a)
    rwa [h] at h1
  exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)

/-- Dependent weights: mass `1/2` on equal bits, `0` elsewhere. -/
noncomputable def depWeight : Bool × Bool → ENNReal :=
  fun b => if b = (false, false) ∨ b = (true, true)
  then ENNReal.ofReal (1 / 2) else 0

/-- The dependent weights sum to one. -/
theorem depWeight_sum : (∑ b, depWeight b) = 1 := by
  have h2 : ENNReal.ofReal (1 / 2 : Real) + ENNReal.ofReal (1 / 2 : Real) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      show (1 / 2 : Real) + 1 / 2 = 1 by norm_num, ENNReal.ofReal_one]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, depWeight, Prod.mk.injEq,
    Bool.false_eq_true, Bool.true_eq_false,
    and_false, and_true,
    false_or, or_false, ite_true, ite_false,
    add_zero, zero_add]
  exact h2

/-- Dependent joint on two bits (L7). -/
noncomputable def depJoint : PMF (Bool × Bool) :=
  PMF.ofFintype depWeight depWeight_sum

/-- The dependent weight at `(false, false)` is `1 / 2` as a real number. -/
theorem depWeight_toReal_FF : (depWeight (false, false)).toReal = 1 / 2 := by
  simp [depWeight]

/-- The dependent weight at `(true, true)` is `1 / 2` as a real number. -/
theorem depWeight_toReal_TT : (depWeight (true, true)).toReal = 1 / 2 := by
  simp [depWeight]

/-- The dependent weight at `(false, true)` is `0` as a real number. -/
theorem depWeight_toReal_FT : (depWeight (false, true)).toReal = 0 := by
  simp [depWeight]

/-- The dependent weight at `(true, false)` is `0` as a real number. -/
theorem depWeight_toReal_TF : (depWeight (true, false)).toReal = 0 := by
  simp [depWeight]

/-- The pairs of bits with first coordinate `false` are exactly `{(false, false), (false,
true)}`. -/
theorem fiber_fst_false : Finset.univ.filter (fun p : Bool × Bool => p.1 = false)
  = {(false, false), (false, true)} := by decide

/-- The pairs of bits with first coordinate `true` are exactly `{(true, false), (true, true)}`. -/
theorem fiber_fst_true : Finset.univ.filter (fun p : Bool × Bool => p.1 = true)
  = {(true, false), (true, true)} := by decide

/-- The pairs of bits with second coordinate `false` are exactly `{(false, false), (true,
false)}`. -/
theorem fiber_snd_false : Finset.univ.filter (fun p : Bool × Bool => p.2 = false)
  = {(false, false), (true, false)} := by decide

/-- The pairs of bits with second coordinate `true` are exactly `{(false, true), (true, true)}`. -/
theorem fiber_snd_true : Finset.univ.filter (fun p : Bool × Bool => p.2 = true)
  = {(false, true), (true, true)} := by decide

/-- The pairs of bits with exclusive or `false` are exactly `{(false, false), (true, true)}`. -/
theorem fiber_xor_false :
  Finset.univ.filter (fun p : Bool × Bool => (p.1 ^^ p.2) = false)
  = {(false, false), (true, true)} := by decide

/-- The pairs of bits with exclusive or `true` are exactly `{(false, true), (true, false)}`. -/
theorem fiber_xor_true :
  Finset.univ.filter (fun p : Bool × Bool => (p.1 ^^ p.2) = true)
  = {(false, true), (true, false)} := by decide

/-- First marginal at `false` is uniform. -/
theorem depJoint_fst_false : ((depJoint.map Prod.fst) false).toReal = 1 / 2 := by
  calc ((depJoint.map Prod.fst) false).toReal
    = ∑ p ∈ Finset.univ.filter (fun p => p.1 = false),
      (depWeight p).toReal :=
      map_ofFintype_toReal (Bool × Bool) Bool depWeight depWeight_sum
        Prod.fst false
    _ = (depWeight (false, false)).toReal
      + (depWeight (false, true)).toReal := by
      rw [fiber_fst_false]
      exact Finset.sum_pair (by decide)
    _ = 1 / 2 := by
      rw [depWeight_toReal_FF, depWeight_toReal_FT]
      norm_num

/-- First marginal at `true` is uniform. -/
theorem depJoint_fst_true : ((depJoint.map Prod.fst) true).toReal = 1 / 2 := by
  calc ((depJoint.map Prod.fst) true).toReal
    = ∑ p ∈ Finset.univ.filter (fun p => p.1 = true),
      (depWeight p).toReal :=
      map_ofFintype_toReal (Bool × Bool) Bool depWeight depWeight_sum
        Prod.fst true
    _ = (depWeight (true, false)).toReal
      + (depWeight (true, true)).toReal := by
      rw [fiber_fst_true]
      exact Finset.sum_pair (by decide)
    _ = 1 / 2 := by
      rw [depWeight_toReal_TF, depWeight_toReal_TT]
      norm_num

/-- Second marginal at `false` is uniform. -/
theorem depJoint_snd_false : ((depJoint.map Prod.snd) false).toReal = 1 / 2 := by
  calc ((depJoint.map Prod.snd) false).toReal
    = ∑ p ∈ Finset.univ.filter (fun p => p.2 = false),
      (depWeight p).toReal :=
      map_ofFintype_toReal (Bool × Bool) Bool depWeight depWeight_sum
        Prod.snd false
    _ = (depWeight (false, false)).toReal
      + (depWeight (true, false)).toReal := by
      rw [fiber_snd_false]
      exact Finset.sum_pair (by decide)
    _ = 1 / 2 := by
      rw [depWeight_toReal_FF, depWeight_toReal_TF]
      norm_num

/-- Second marginal at `true` is uniform. -/
theorem depJoint_snd_true : ((depJoint.map Prod.snd) true).toReal = 1 / 2 := by
  calc ((depJoint.map Prod.snd) true).toReal
    = ∑ p ∈ Finset.univ.filter (fun p => p.2 = true),
      (depWeight p).toReal :=
      map_ofFintype_toReal (Bool × Bool) Bool depWeight depWeight_sum
        Prod.snd true
    _ = (depWeight (false, true)).toReal
      + (depWeight (true, true)).toReal := by
      rw [fiber_snd_true]
      exact Finset.sum_pair (by decide)
    _ = 1 / 2 := by
      rw [depWeight_toReal_FT, depWeight_toReal_TT]
      norm_num

/-- Xor at `false` has probability one under the dependent joint. -/
theorem depJoint_xor_false :
  ((depJoint.map (fun p => p.1 ^^ p.2)) false).toReal = 1 := by
  calc ((depJoint.map (fun p => p.1 ^^ p.2)) false).toReal
    = ∑ p ∈ Finset.univ.filter (fun p => (p.1 ^^ p.2) = false),
      (depWeight p).toReal :=
      map_ofFintype_toReal (Bool × Bool) Bool depWeight depWeight_sum
        (fun p => p.1 ^^ p.2) false
    _ = (depWeight (false, false)).toReal
      + (depWeight (true, true)).toReal := by
      rw [fiber_xor_false]
      exact Finset.sum_pair (by decide)
    _ = 1 := by
      rw [depWeight_toReal_FF, depWeight_toReal_TT]
      norm_num

/-- Xor at `true` has probability zero under the dependent joint. -/
theorem depJoint_xor_true :
  ((depJoint.map (fun p => p.1 ^^ p.2)) true).toReal = 0 := by
  calc ((depJoint.map (fun p => p.1 ^^ p.2)) true).toReal
    = ∑ p ∈ Finset.univ.filter (fun p => (p.1 ^^ p.2) = true),
      (depWeight p).toReal :=
      map_ofFintype_toReal (Bool × Bool) Bool depWeight depWeight_sum
        (fun p => p.1 ^^ p.2) true
    _ = (depWeight (false, true)).toReal
      + (depWeight (true, false)).toReal := by
      rw [fiber_xor_true]
      exact Finset.sum_pair (by decide)
    _ = 0 := by
      rw [depWeight_toReal_FT, depWeight_toReal_TF]
      norm_num

/-- Both marginals have correlation zero (L7). -/
theorem depJoint_marginals_uniform :
  correlation (depJoint.map Prod.fst) = 0
  ∧ correlation (depJoint.map Prod.snd) = 0 := by
  unfold correlation
  rw [depJoint_fst_false, depJoint_fst_true,
    depJoint_snd_false, depJoint_snd_true]
  norm_num

/-- The xor has correlation one despite uniform marginals (L7). -/
theorem depJoint_xor_correlation :
  correlation (depJoint.map (fun p => p.1 ^^ p.2)) = 1 := by
  unfold correlation
  rw [depJoint_xor_false, depJoint_xor_true]
  norm_num

/-! ## Numeric instances against L4 -/

/-- Biased coin with `Pr[false] = a`. -/
noncomputable def biasedCoin (a : Real) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : PMF Bool :=
  PMF.ofFintype
  (fun b => if b = false then ENNReal.ofReal a else ENNReal.ofReal (1 - a))
  (by
    rw [Fintype.sum_bool]
    simp only [Bool.true_eq_false, ite_true, ite_false]
    rw [add_comm, ← ENNReal.ofReal_add ha0 (show (0 : Real) ≤ 1 - a by linarith),
      show a + (1 - a) = 1 by ring, ENNReal.ofReal_one])

/-- False probability of a biased coin. -/
theorem biasedCoin_false_toReal (a : Real) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
  ((biasedCoin a ha0 ha1) false).toReal = a := by
  simp [biasedCoin, ENNReal.toReal_ofReal ha0]

/-- True probability of a biased coin. -/
theorem biasedCoin_true_toReal (a : Real) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
  ((biasedCoin a ha0 ha1) true).toReal = 1 - a := by
  simp [biasedCoin, ENNReal.toReal_ofReal (show (0 : Real) ≤ 1 - a by linarith)]

/-- Bias of a biased coin. -/
theorem biasedCoin_bias (a : Real) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
  bias (biasedCoin a ha0 ha1) = a - 1 / 2 := by
  unfold bias
  rw [biasedCoin_false_toReal]

/-- Concrete coin with `Pr[false] = 3/4`. -/
noncomputable def coin34 : PMF Bool := biasedCoin (3 / 4) (by norm_num) (by norm_num)

/-- Concrete coin with `Pr[false] = 1/4`. -/
noncomputable def coin14 : PMF Bool := biasedCoin (1 / 4) (by norm_num) (by norm_num)

/-- Bias of `coin34`. -/
theorem bias_coin34 : bias coin34 = 1 / 4 := by
  unfold coin34
  rw [biasedCoin_bias]
  norm_num

/-- Bias of `coin14`. -/
theorem bias_coin14 : bias coin14 = -1 / 4 := by
  unfold coin14
  rw [biasedCoin_bias]
  norm_num

/-! ## Part 2: toy-SPN model (S1-S2) -/

/-- Pointwise xor of two `w`-bit vectors. -/
def xorVec {w : Nat} (x y : Fin w → Bool) : Fin w → Bool :=
  fun i => x i ^^ y i

/-- Permute coordinates: `(permute π z) i = z (π i)`. -/
def permute {w : Nat} (π : Equiv.Perm (Fin w)) (z : Fin w → Bool) : Fin w → Bool :=
  fun i => z (π i)

/-- One SPN round: add key, substitute, permute. -/
def spnRound {w : Nat} (k : Fin w → Bool) (S : (Fin w → Bool) → (Fin w → Bool))
  (π : Equiv.Perm (Fin w)) (x : Fin w → Bool) : Fin w → Bool :=
  permute π (S (xorVec x k))

/-- Parity of state `x` under mask `u`: xor-sum of `x i` over `i` with `u i`. -/
def parity {w : Nat} (u x : Fin w → Bool) : Bool :=
  decide (∑ i, (if u i && x i then (1 : ZMod 2) else 0) = 1)

/-- Transport a boundary mask back across a permutation. -/
def transportMask {w : Nat} (u : Fin w → Bool) (π : Equiv.Perm (Fin w)) :
  Fin w → Bool :=
  fun i => u (π.symm i)

/-- Per-coordinate parity contribution of xor is the sum of contributions. -/
theorem zmod_parity_add : ∀ (a b c : Bool),
  (if a && (b ^^ c) then (1 : ZMod 2) else 0)
  = (if a && b then (1 : ZMod 2) else 0)
  + (if a && c then (1 : ZMod 2) else 0) := by
  decide

/-- Decided equality against `1` distributes over addition as xor. -/
theorem decide_add_one : ∀ (A B : ZMod 2),
  decide (A + B = 1) = (decide (A = 1) ^^ decide (B = 1)) := by
  decide

/-- Parity of a xor is the xor of parities (S1). -/
theorem parity_xor (w : Nat) (u x y : Fin w → Bool) :
  parity u (xorVec x y) = (parity u x ^^ parity u y) := by
  unfold parity xorVec
  have hsum : (∑ i, (if u i && (x i ^^ y i) then (1 : ZMod 2) else 0))
    = (∑ i, (if u i && x i then (1 : ZMod 2) else 0))
    + (∑ i, (if u i && y i then (1 : ZMod 2) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact zmod_parity_add _ _ _
  rw [hsum, decide_add_one]

/-- Transported-mask parity equals permuted-state parity. -/
theorem parity_permute (w : Nat) (u z : Fin w → Bool) (π : Equiv.Perm (Fin w)) :
  parity (transportMask u π) z = parity u (permute π z) := by
  unfold parity transportMask permute
  congr 1
  have h1 : (∑ i, (if u (π.symm i) && z i then (1 : ZMod 2) else 0))
    = ∑ i, (if u (π.symm i) && z (π (π.symm i)) then (1 : ZMod 2) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Equiv.apply_symm_apply]
  have h2 : (∑ i, (if u (π.symm i) && z (π (π.symm i)) then (1 : ZMod 2) else 0))
    = ∑ i, (if u i && z (π i) then (1 : ZMod 2) else 0) :=
    Equiv.sum_comp π.symm (fun j => if u j && z (π j) then (1 : ZMod 2) else 0)
  rw [h1, h2]

/-- Round error bit: input parity xored with substituted transported parity. -/
def errBit {w : Nat} (u x a s : Fin w → Bool) : Bool :=
  parity u x ^^ parity a s

/-- Xor-fold of adjacent xors telescopes to the endpoints. -/
theorem foldr_range_xor_telescope (q e : Nat → Bool)
  (h : ∀ i, e i = (q i ^^ q (i + 1))) (r : Nat) (b : Bool) :
  ((List.range r).map e).foldr Bool.xor b = ((q 0 ^^ q r) ^^ b) := by
  induction r generalizing b with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.foldr_append]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [ih, h m]
    cases q 0 <;> cases q m <;> cases q (m + 1) <;> cases b <;> rfl

/-- Trail error bits telescope to boundary parities, with no key term (S2). -/
theorem trail_telescope (w r : Nat)
  (k : Nat → (Fin w → Bool))
  (S : Nat → ((Fin w → Bool) → (Fin w → Bool)))
  (π : Nat → Equiv.Perm (Fin w))
  (u x : Nat → (Fin w → Bool))
  (hx : ∀ i, x (i + 1) = spnRound (k i) (S i) (π i) (x i)) :
  ((List.range r).map (fun i =>
  errBit (u i) (x i) (transportMask (u (i + 1)) (π i))
  (S i (xorVec (x i) (k i))))).foldr Bool.xor false
  = (parity (u 0) (x 0) ^^ parity (u r) (x r)) := by
  have h : ∀ i, errBit (u i) (x i) (transportMask (u (i + 1)) (π i))
    (S i (xorVec (x i) (k i)))
    = (parity (u i) (x i) ^^ parity (u (i + 1)) (x (i + 1))) := by
      intro i
      unfold errBit
      have t := parity_permute w (u (i + 1)) (S i (xorVec (x i) (k i))) (π i)
      rw [t, hx i]
      rfl
  have tel := foldr_range_xor_telescope (fun i => parity (u i) (x i))
    (fun i => errBit (u i) (x i) (transportMask (u (i + 1)) (π i))
    (S i (xorVec (x i) (k i)))) h r false
  rw [tel]
  simp

/-! ## Toy-SPN concrete instances -/

/-- Swap permutation on two wires. -/
def swap2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- Mask selecting coordinate `0` on two wires. -/
def mask0 : Fin 2 → Bool := fun i => i = 0

/-! ## Trail bias bridge (S3) -/

/-- The trail check pushforward agrees with the xor pushforward under the
pointwise identification (from the telescoping identity) and the
product-joint assumption on error bits. -/
theorem map_trail_eq (r : Nat) (Ω : Type*) (q : PMF Ω)
  (E : Ω → (Fin r → Bool)) (T : Ω → Bool) (p : Fin r → PMF Bool)
  (hT : ∀ ω, T ω = xorAll r (E ω)) (hq : q.map E = jointPMF p) :
  q.map T = (jointPMF p).map (xorAll r) := by
  have hfun : T = xorAll r ∘ E := funext hT
  rw [hfun, ← PMF.map_comp, hq]

/-- Trail bias bridge, Matsui form (S3): under the explicit product-joint
assumption `hq` on error bits with biases `eps`, the trail parity
relation holds with probability `1/2 + 2^(r-1) ∏ eps` for `r ≥ 1`.
The product joint is an assumption, not derived from key independence. -/
theorem trail_bias_matsui (r : Nat) (Ω : Type*) (q : PMF Ω)
  (E : Ω → (Fin r → Bool)) (T : Ω → Bool) (p : Fin r → PMF Bool)
  (eps : Fin r → Real) (heps : ∀ i, bias (p i) = eps i)
  (hT : ∀ ω, T ω = xorAll r (E ω)) (hq : q.map E = jointPMF p)
  (hr : 1 ≤ r) :
  ((q.map T) false).toReal = 1 / 2 + 2 ^ (r - 1) * (∏ i, eps i) := by
  have hmap := map_trail_eq r Ω q E T p hT hq
  rw [hmap]
  have h := pilingUp r p hr
  rw [h]
  have heq : (∏ i, bias (p i)) = ∏ i, eps i :=
    Finset.prod_congr rfl (fun i _ => heps i)
  rw [heq]

/-- Trail bias bridge, correlation form (S3): same assumptions, all `r`. -/
theorem trail_bias_correlation (r : Nat) (Ω : Type*) (q : PMF Ω)
  (E : Ω → (Fin r → Bool)) (T : Ω → Bool) (p : Fin r → PMF Bool)
  (hT : ∀ ω, T ω = xorAll r (E ω)) (hq : q.map E = jointPMF p) :
  correlation (q.map T) = ∏ i, correlation (p i) := by
  have hmap := map_trail_eq r Ω q E T p hT hq
  rw [hmap]
  exact correlation_xor r p

end Cslib.Crypto.SymmetricKey.PilingUp
