/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.Sampling.MCMCConvergence
public import CSLibExt.MachineLearning.Sampling.ForwardSampling
public import CSLibExt.MachineLearning.GraphicalModels.MarkovBlanket

/-!
# Gibbs sampling for Bayesian-network posteriors

Gibbs sampling of the posterior of a Bayesian network given evidence: evidence coordinates stay
fixed and each free coordinate is resampled from its conditional law given its Markov blanket.
The full conditional is computed from the node's own table factor and its children's factors
(the Markov blanket factorization), the sweep leaves the posterior stationary, and under a
strictly positive table hypothesis the sweep matrix converges geometrically.

## Sources

* C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer, 2006, Sec. 8.2,
  pp. 382-383 (the conditional of a node given all other nodes keeps only the node's own
  factor and its children's factors; Markov blanket, Figure 8.26) and Sec. 11.3, pp. 542-546
  (Gibbs sampling, invariance, ergodicity when no conditional vanishes).
* S. Russell and P. Norvig, *Artificial Intelligence: A Modern Approach*, 4th ed.: the
  GIBBS-ASK pseudocode (evidence variables stay fixed; each non-evidence variable is resampled
  given its Markov blanket).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset
open Cslib.MachineLearning.Sampling

variable {α : Type*} {n : ℕ}

/-- The full assignment that agrees with the evidence `e` on `E` and with `z` off `E`. -/
def extendEvidence (E : Finset (Fin n)) (e : Fin n → α) (z : {i : Fin n // i ∉ E} → α) :
    Fin n → α :=
  fun i => if h : i ∈ E then e i else z ⟨i, h⟩

namespace BayesNet

/-- Every entry of every conditional probability table is positive. -/
def PositiveCPT (b : BayesNet α n) : Prop :=
  ∀ (k : Fin n) (u : b.pa k → α) (a : α), 0 < (b.cpt k u).weights a

/-- The factor of node `k` in `BayesNet.joint_eq_prod`. -/
noncomputable def cptFactor (b : BayesNet α n) (k : Fin n) (x : Fin n → α) : ℝ :=
  (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k)

/-- The factors of `BayesNet.joint_eq_prod` that involve the value of node `i`: its own table
entry and the table entries of its children. -/
noncomputable def blanketFactor (b : BayesNet α n) (i : Fin n) (x : Fin n → α) : ℝ :=
  b.cptFactor i x * ∏ k ∈ univ.filter (b.Edge i), b.cptFactor k x

theorem blanketFactor_pos {b : BayesNet α n} (hb : b.PositiveCPT) (i : Fin n)
    (x : Fin n → α) : 0 < b.blanketFactor i x :=
  mul_pos (hb _ _ _) (prod_pos fun _ _ => hb _ _ _)

/-- The posterior `P(· | X_E = e)` of the non-evidence variables: the image of
`BayesNet.posteriorPMF` under restriction to the coordinates outside `E`. -/
noncomputable def posteriorFree [Fintype α] [DecidableEq α] [Nonempty α] (b : BayesNet α n)
    (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0) :
    PMF ({i : Fin n // i ∉ E} → α) :=
  (b.posteriorPMF E e hE).map fun x i => x i.1

/-- The update law of the non-evidence variable `i` computed from local factors only:
`blanketFactor` at `z` with coordinate `i` set to `a`, normalized over `a`. -/
noncomputable def blanketLaw [Fintype α] [Nonempty α] {b : BayesNet α n} (hb : b.PositiveCPT)
    (E : Finset (Fin n)) (e : Fin n → α) (i : {i : Fin n // i ∉ E})
    (z : {i : Fin n // i ∉ E} → α) : PMF α :=
  PMF.normalize
    (fun a => ENNReal.ofReal (b.blanketFactor i.1 (extendEvidence E e (Function.update z i a))))
    (by
      intro h
      have h0 := ENNReal.tsum_eq_zero.1 h (Classical.arbitrary α)
      exact (ENNReal.ofReal_pos.2 (blanketFactor_pos hb i.1 _)).ne' h0)
    (by
      rw [tsum_fintype]
      exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top)

section Targets

/-- Positive tables give every configuration positive probability. -/
theorem joint_pos [Nonempty α] {b : BayesNet α n} (hb : b.PositiveCPT) (x : Fin n → α) :
    0 < b.joint x := by
  rw [b.joint_eq_prod]
  exact Finset.prod_pos fun k _ => hb k _ _

private theorem extendEvidence_agree {α : Type*} {n : ℕ} (E : Finset (Fin n)) (e : Fin n → α)
    (z : {i : Fin n // i ∉ E} → α) (k : Fin n) (hk : k ∈ E) :
    extendEvidence E e z k = e k := by
  simp only [extendEvidence, dite_eq_left hk]

private theorem restrict_extendEvidence {α : Type*} {n : ℕ} (E : Finset (Fin n)) (e : Fin n → α)
    (z : {i : Fin n // i ∉ E} → α) :
    (fun x i => x i.1) (extendEvidence E e z) = z := by
  funext ⟨i, hi⟩
  show extendEvidence E e z i = z ⟨i, hi⟩
  simp only [extendEvidence, dite_eq_right hi]

/-- Positive tables give every evidence positive probability. -/
theorem evidenceProb_ne_zero [Fintype α] [DecidableEq α] [Nonempty α] {b : BayesNet α n}
    (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α) : b.evidenceProb E e ≠ 0 := by
  have hw : ∀ k ∈ E, extendEvidence E e (fun _ => Classical.arbitrary α) k = e k :=
    fun k hk => extendEvidence_agree E e _ k hk
  have hlt : 0 < b.evidenceProb E e := by
    unfold evidenceProb
    refine Finset.sum_pos (fun x _ => joint_pos hb x)
      ⟨extendEvidence E e (fun _ => Classical.arbitrary α), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hw
  exact ne_of_gt hlt

/-- The posterior of the non-evidence variables is the network posterior `P(z, e) / P(e)`. -/
theorem posteriorFree_apply [Fintype α] [DecidableEq α] [Nonempty α] (b : BayesNet α n)
    (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0)
    (z : {i : Fin n // i ∉ E} → α) :
    b.posteriorFree E e hE z =
      ENNReal.ofReal (b.joint (extendEvidence E e z) / b.evidenceProb E e) := by
  classical
  have hagree : ∀ k ∈ E, extendEvidence E e z k = e k :=
    fun k hk => extendEvidence_agree E e z k hk
  have hval : b.posteriorPMF E e hE (extendEvidence E e z) =
      ENNReal.ofReal (b.joint (extendEvidence E e z) / b.evidenceProb E e) := by
    rw [posteriorPMF_apply, ite_eq_left hagree]
  have hmain : z = (fun x i => x i.1) (extendEvidence E e z) :=
    (restrict_extendEvidence E e z).symm
  rw [posteriorFree, PMF.map_apply, tsum_eq_single (extendEvidence E e z)]
  · simp only [ite_eq_left hmain, hval]
  · intro a ha
    by_cases h : z = (fun x i => x i.1) a
    · have hdis : ¬ ∀ k ∈ E, a k = e k := by
        intro hall
        apply ha
        funext k
        by_cases hk : k ∈ E
        · exact (hall k hk).trans (extendEvidence_agree E e z k hk).symm
        · have hkz : a k = z ⟨k, hk⟩ := (congrFun h ⟨k, hk⟩).symm
          rw [hkz]
          simp only [extendEvidence, dite_eq_right hk]
      simp only [ite_eq_left h, posteriorPMF_apply, ite_eq_right hdis]
    · simp only [ite_eq_right h]

/-- Full support: the hypothesis `hπ` of the Atlas Gibbs theorems. -/
theorem posteriorFree_ne_zero [Fintype α] [DecidableEq α] [Nonempty α] {b : BayesNet α n}
    (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0)
    (z : {i : Fin n // i ∉ E} → α) : b.posteriorFree E e hE z ≠ 0 := by
  rw [posteriorFree_apply]
  have hev : 0 < b.evidenceProb E e := by
    refine lt_of_le_of_ne ?_ (Ne.symm hE)
    unfold evidenceProb
    exact Finset.sum_nonneg fun x _ => b.toChain.joint_nonneg n x
  exact (ENNReal.ofReal_pos.2 (div_pos (joint_pos hb _) hev)).ne'

/-- The factors of `joint_eq_prod` outside `{i} ∪ children(i)` do not see the value of node `i`
(Bishop 2006, p. 382: they cancel between numerator and denominator). -/
theorem joint_update_eq_mul_blanketFactor [Nonempty α] (b : BayesNet α n) (i : Fin n)
    (x : Fin n → α) (a : α) :
    b.joint (Function.update x i a) =
      (∏ k ∈ (insert i (univ.filter (b.Edge i)))ᶜ, b.cptFactor k x) *
        b.blanketFactor i (Function.update x i a) := by
  have hedge : ∀ {k : Fin n} (j : b.pa k),
      b.Edge (Fin.castLE k.2.le (j : Fin k)) k := by
    intro k j
    exact ⟨(j : Fin k).isLt, j.property⟩
  have hfactor : ∀ k ∈ (insert i (univ.filter (b.Edge i)))ᶜ,
      b.cptFactor k (Function.update x i a) = b.cptFactor k x := by
    intro k hk
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or] at hk
    have h1 : ∀ j : b.pa k, Function.update x i a (Fin.castLE k.2.le (j : Fin k)) =
        x (Fin.castLE k.2.le (j : Fin k)) := by
      intro j
      have hne : Fin.castLE k.2.le (j : Fin k) ≠ i := by
        intro hcon
        have hhedge := hedge j
        rw [hcon] at hhedge
        exact hk.2 hhedge
      exact Function.update_of_ne hne _ _
    have h2 : Function.update x i a k = x k := Function.update_of_ne hk.1 _ _
    unfold cptFactor
    simp only [h1, h2]
  have hnotmem : i ∉ univ.filter (b.Edge i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hed
    obtain ⟨hlt, -⟩ := hed
    exact lt_irrefl _ hlt
  have hjoint : b.joint (Function.update x i a)
      = ∏ k, b.cptFactor k (Function.update x i a) := by
    unfold cptFactor
    rw [b.joint_eq_prod]
  have hsplit : (∏ k ∈ (insert i (univ.filter (b.Edge i)))ᶜ,
        b.cptFactor k (Function.update x i a))
        * (∏ k ∈ insert i (univ.filter (b.Edge i)), b.cptFactor k (Function.update x i a))
      = ∏ k, b.cptFactor k (Function.update x i a) :=
    Finset.prod_compl_mul_prod _ _
  rw [hjoint, ← hsplit]
  congr 1
  · exact Finset.prod_congr rfl hfactor
  · unfold blanketFactor
    rw [Finset.prod_insert hnotmem]

/-- With node `i` reset, `blanketFactor` depends only on the Markov blanket of `i`. -/
theorem blanketFactor_update_congr (b : BayesNet α n) {i : Fin n} {x x' : Fin n → α}
    (h : ∀ j ∈ b.markovBlanket i, x j = x' j) (a : α) :
    b.blanketFactor i (Function.update x i a) = b.blanketFactor i (Function.update x' i a) := by
  have hedge : ∀ {k : Fin n} (j : b.pa k),
      b.Edge (Fin.castLE k.2.le (j : Fin k)) k := by
    intro k j
    exact ⟨(j : Fin k).isLt, j.property⟩
  have hself : b.cptFactor i (Function.update x i a)
      = b.cptFactor i (Function.update x' i a) := by
    have h1 : ∀ j : b.pa i, Function.update x i a (Fin.castLE i.2.le (j : Fin i))
        = Function.update x' i a (Fin.castLE i.2.le (j : Fin i)) := by
      intro j
      have hne : Fin.castLE i.2.le (j : Fin i) ≠ i := by
        intro hcon
        have hcon2 := congrArg Fin.val hcon
        rw [Fin.val_castLE] at hcon2
        have hj := (j : Fin i).isLt
        omega
      rw [Function.update_of_ne hne _ _, Function.update_of_ne hne _ _]
      apply h
      rw [b.mem_markovBlanket]
      exact ⟨hne, Or.inl (hedge j)⟩
    have h2 : Function.update x i a i = Function.update x' i a i := by
      rw [Function.update_self _ _ _, Function.update_self _ _ _]
    unfold cptFactor
    simp only [h1, h2]
  have hchild : ∀ k ∈ univ.filter (b.Edge i), b.cptFactor k (Function.update x i a)
      = b.cptFactor k (Function.update x' i a) := by
    intro k hkmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkmem
    have hki : k ≠ i := by
      intro hcon
      subst hcon
      obtain ⟨hlt, -⟩ := hkmem
      exact lt_irrefl _ hlt
    have hkmem' : k ∈ b.markovBlanket i := by
      rw [b.mem_markovBlanket]
      exact ⟨hki, Or.inr (Or.inl hkmem)⟩
    have h1 : ∀ j : b.pa k, Function.update x i a (Fin.castLE k.2.le (j : Fin k))
        = Function.update x' i a (Fin.castLE k.2.le (j : Fin k)) := by
      intro j
      by_cases hqi : Fin.castLE k.2.le (j : Fin k) = i
      · rw [hqi]
        rw [Function.update_self _ _ _, Function.update_self _ _ _]
      · rw [Function.update_of_ne hqi _ _, Function.update_of_ne hqi _ _]
        apply h
        rw [b.mem_markovBlanket]
        exact ⟨hqi, Or.inr (Or.inr ⟨k, hkmem, hedge j⟩)⟩
    have h2 : Function.update x i a k = Function.update x' i a k := by
      rw [Function.update_of_ne hki _ _, Function.update_of_ne hki _ _]
      exact h k hkmem'
    unfold cptFactor
    simp only [h1, h2]
  unfold blanketFactor
  rw [hself]
  congr 1
  exact Finset.prod_congr rfl hchild

/-- **Full-conditional formula.** The Atlas Gibbs conditional of the posterior at a
non-evidence variable is the normalized product of the variable's own table entry and the
table entries of its children. -/
theorem condLaw_posteriorFree [Fintype α] [DecidableEq α] [Nonempty α] {b : BayesNet α n}
    (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0)
    (i : {i : Fin n // i ∉ E}) (z : {i : Fin n // i ∉ E} → α) :
    condLaw (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) i z =
      blanketLaw hb E e i z := by
  classical
  have hcomm : ∀ a : α, extendEvidence E e (Function.update z i a) =
      Function.update (extendEvidence E e z) i.1 a := by
    intro a
    funext k
    by_cases hkE : k ∈ E
    · have hki : k ≠ i.1 := fun h => i.2 (h ▸ hkE)
      simp only [extendEvidence, dite_eq_left hkE, Function.update_of_ne hki]
    · by_cases hki : k = i.1
      · subst hki
        have hsub : (⟨i.1, hkE⟩ : {i : Fin n // i ∉ E}) = i := Subtype.ext rfl
        simp only [extendEvidence, dite_eq_right hkE, hsub, Function.update_self]
      · have hsub : (⟨k, hkE⟩ : {i : Fin n // i ∉ E}) ≠ i :=
          fun h => hki (congrArg Subtype.val h)
        simp only [extendEvidence, dite_eq_right hkE, Function.update_of_ne hki,
          Function.update_of_ne hsub]
  have hsplit : ∀ a : α, b.joint (extendEvidence E e (Function.update z i a)) =
      (∏ k ∈ (insert i.1 (univ.filter (b.Edge i.1)))ᶜ,
        b.cptFactor k (extendEvidence E e z)) *
        b.blanketFactor i.1 (extendEvidence E e (Function.update z i a)) := by
    intro a
    have h := joint_update_eq_mul_blanketFactor b i.1 (extendEvidence E e z) a
    rwa [← hcomm a] at h
  set C : ℝ := ∏ k ∈ (insert i.1 (univ.filter (b.Edge i.1)))ᶜ,
    b.cptFactor k (extendEvidence E e z) with hC
  have hCpos : 0 < C := by
    rw [hC]
    exact Finset.prod_pos fun k _ => hb k _ _
  have hev : 0 < b.evidenceProb E e := by
    refine lt_of_le_of_ne ?_ (Ne.symm hE)
    unfold evidenceProb
    exact Finset.sum_nonneg fun x _ => b.toChain.joint_nonneg n x
  have hπ : ∀ a : α, b.posteriorFree E e hE (Function.update z i a) =
      ENNReal.ofReal ((C * b.blanketFactor i.1 (extendEvidence E e (Function.update z i a))) /
        b.evidenceProb E e) := by
    intro a
    rw [posteriorFree_apply, hsplit a]
  have hnorm : condNorm (b.posteriorFree E e hE) i z =
      ENNReal.ofReal ((C * ∑ a', b.blanketFactor i.1 (extendEvidence E e (Function.update z i a'))) /
        b.evidenceProb E e) := by
    simp only [condNorm, hπ]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun s _ => div_nonneg (mul_nonneg hCpos.le (le_of_lt (blanketFactor_pos hb _ _))) hev.le)]
    congr 1
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.mul_sum]
  have hSpos : 0 < ∑ a', b.blanketFactor i.1 (extendEvidence E e (Function.update z i a')) :=
    Finset.sum_pos (fun s _ => blanketFactor_pos hb _ _) Finset.univ_nonempty
  have hofReal_div : ∀ X Y : ℝ, 0 ≤ X → 0 < Y →
      ENNReal.ofReal X / ENNReal.ofReal Y = ENNReal.ofReal (X / Y) := by
    intro X Y hX hY
    rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos hY, ← ENNReal.ofReal_mul hX,
      div_eq_mul_inv]
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hSne : (∑ a', b.blanketFactor i.1 (extendEvidence E e (Function.update z i a'))) ≠ 0 :=
    ne_of_gt hSpos
  apply PMF.ext
  intro a
  simp only [condLaw, PMF.ofFintype_apply, hπ, hnorm, blanketLaw, PMF.normalize_apply,
    tsum_fintype]
  rw [hofReal_div _ _
      (div_nonneg (mul_nonneg hCpos.le (le_of_lt (blanketFactor_pos hb _ _))) hev.le)
      (div_pos (mul_pos hCpos hSpos) hev),
    ← ENNReal.ofReal_sum_of_nonneg (fun s _ => le_of_lt (blanketFactor_pos hb _ _)),
    ← ENNReal.ofReal_inv_of_pos hSpos,
    ← ENNReal.ofReal_mul (le_of_lt (blanketFactor_pos hb _ _))]
  congr 1
  field_simp

/-- **Full-conditional formula**, real form: `P(z_i = a | z_{-i}, e) = f(a) / ∑_{a'} f(a')`
with `f` the blanket factor. -/
theorem condLaw_posteriorFree_apply_toReal [Fintype α] [DecidableEq α] [Nonempty α]
    {b : BayesNet α n} (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α)
    (hE : b.evidenceProb E e ≠ 0) (i : {i : Fin n // i ∉ E}) (z : {i : Fin n // i ∉ E} → α)
    (a : α) :
    (condLaw (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) i z a).toReal =
      b.blanketFactor i.1 (extendEvidence E e (Function.update z i a)) /
        ∑ a', b.blanketFactor i.1 (extendEvidence E e (Function.update z i a')) := by
  rw [condLaw_posteriorFree hb E e hE i z]
  have hnn : ∀ s : α, 0 ≤ b.blanketFactor i.1 (extendEvidence E e (Function.update z i s)) :=
    fun s => le_of_lt (blanketFactor_pos hb _ _)
  have hsum : (∑ x, ENNReal.ofReal
      (b.blanketFactor i.1 (extendEvidence E e (Function.update z i x)))).toReal =
      ∑ a', b.blanketFactor i.1 (extendEvidence E e (Function.update z i a')) := by
    rw [ENNReal.toReal_sum (fun s _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl fun s _ => ENNReal.toReal_ofReal (hnn s)
  simp only [blanketLaw, PMF.normalize_apply, tsum_fintype]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, hsum, ENNReal.toReal_ofReal (hnn a),
    div_eq_mul_inv]

/-- **The full conditional depends only on the Markov blanket.** -/
theorem condLaw_posteriorFree_congr [Fintype α] [DecidableEq α] [Nonempty α]
    {b : BayesNet α n} (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α)
    (hE : b.evidenceProb E e ≠ 0) (i : {i : Fin n // i ∉ E}) {z z' : {i : Fin n // i ∉ E} → α}
    (h : ∀ j ∈ b.markovBlanket i.1, extendEvidence E e z j = extendEvidence E e z' j) :
    condLaw (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) i z =
      condLaw (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) i z' := by
  classical
  have hcomm : ∀ (w : {i : Fin n // i ∉ E} → α) (a : α),
      extendEvidence E e (Function.update w i a) =
        Function.update (extendEvidence E e w) i.1 a := by
    intro w a
    funext k
    by_cases hkE : k ∈ E
    · have hki : k ≠ i.1 := fun h => i.2 (h ▸ hkE)
      simp only [extendEvidence, dite_eq_left hkE, Function.update_of_ne hki]
    · by_cases hki : k = i.1
      · subst hki
        have hsub : (⟨i.1, hkE⟩ : {i : Fin n // i ∉ E}) = i := Subtype.ext rfl
        simp only [extendEvidence, dite_eq_right hkE, hsub, Function.update_self]
      · have hsub : (⟨k, hkE⟩ : {i : Fin n // i ∉ E}) ≠ i :=
          fun h => hki (congrArg Subtype.val h)
        simp only [extendEvidence, dite_eq_right hkE, Function.update_of_ne hki,
          Function.update_of_ne hsub]
  have hfun : (fun a => ENNReal.ofReal
        (b.blanketFactor i.1 (extendEvidence E e (Function.update z i a)))) =
      (fun a => ENNReal.ofReal
        (b.blanketFactor i.1 (extendEvidence E e (Function.update z' i a)))) := by
    funext a
    congr 1
    rw [hcomm z a, hcomm z' a]
    exact blanketFactor_update_congr b h a
  rw [condLaw_posteriorFree hb E e hE i z, condLaw_posteriorFree hb E e hE i z']
  simp only [blanketLaw, hfun]

/-- The Atlas Gibbs update of the posterior is the local sampler: resample `z i` from
`blanketLaw` (the GIBBS-ASK step). -/
theorem gibbsStep_posteriorFree [Fintype α] [DecidableEq α] [Nonempty α] {b : BayesNet α n}
    (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0)
    (i : {i : Fin n // i ∉ E}) (z : {i : Fin n // i ∉ E} → α) :
    gibbsStep (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) i z =
      (blanketLaw hb E e i z).map (Function.update z i) := by
  show (condLaw (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) i z).map
    (Function.update z i) = _
  rw [condLaw_posteriorFree hb E e hE i z]

/-- **Invariance of `P(· | e)`**: every systematic-scan Gibbs sweep over the non-evidence
variables leaves the posterior stationary. -/
theorem invariant_gibbsSweep_posteriorFree [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {b : BayesNet α n} (hb : b.PositiveCPT)
    (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0)
    (l : List {i : Fin n // i ∉ E}) :
    (gibbsSweep (b.posteriorFree E e hE) (posteriorFree_ne_zero hb E e hE) l).Invariant
      (b.posteriorFree E e hE).toMeasure := by
  exact invariant_gibbsSweep _ _ _

/-- **TV convergence corollary**: if the sweep visits every non-evidence variable, the powers
of the sweep matrix converge geometrically fast in total variation to the network posterior
`P(z, e) / P(e)`, uniformly in the start. -/
theorem exists_tvDist_gibbsSweepMatrix_posteriorFree_pow_le [Fintype α] [DecidableEq α]
    [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] {b : BayesNet α n}
    (hb : b.PositiveCPT) (E : Finset (Fin n)) (e : Fin n → α) (hE : b.evidenceProb E e ≠ 0)
    {l : List {i : Fin n // i ∉ E}} (hl : ∀ i, i ∈ l) :
    ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (N : ℕ) (z : {i : Fin n // i ∉ E} → α),
      MathlibExt.Probability.MarkovMixing.tvDist
          (fun y => (gibbsSweepMatrix (b.posteriorFree E e hE)
            (posteriorFree_ne_zero hb E e hE) l ^ N) z y)
          (fun y => b.joint (extendEvidence E e y) / b.evidenceProb E e) ≤
        C * ρ ^ N := by
  obtain ⟨C, ρ, hρ0, hρ1, hconv⟩ :=
    exists_tvDist_gibbsSweepMatrix_pow_le (b.posteriorFree E e hE)
      (posteriorFree_ne_zero hb E e hE) hl
  have hev : 0 < b.evidenceProb E e := by
    refine lt_of_le_of_ne ?_ (Ne.symm hE)
    unfold evidenceProb
    exact Finset.sum_nonneg fun x _ => b.toChain.joint_nonneg n x
  have hstat : (fun y => ((b.posteriorFree E e hE) y).toReal) =
      (fun y => b.joint (extendEvidence E e y) / b.evidenceProb E e) := by
    funext y
    rw [posteriorFree_apply]
    exact ENNReal.toReal_ofReal (div_nonneg (joint_pos hb _).le hev.le)
  exact ⟨C, ρ, hρ0, hρ1, fun N z => by simpa [hstat] using hconv N z⟩

end Targets

end BayesNet

end Cslib.MachineLearning.GraphicalModels
