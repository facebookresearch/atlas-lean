/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Pivotal
public import MathlibExt.Probability.Configuration.ProductMeasure
public import MathlibExt.Probability.CorrelationInequalities.BK
public import Mathlib.Analysis.Calculus.Deriv.Basic

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# Russo's formula

For a finite set `E` and `p ∈ ℝ`, let `prob p A = ∑ ω ∈ A, ∏ e, (if ω e then p else 1 - p)`; for
`p ∈ [0, 1]` this is the probability of `A` under independent Bernoulli(`p`) coordinates. For an
increasing event `A`, the derivative of `p ↦ prob p A` is the expected number of pivotal
coordinates.

## Main definitions

* `StatMech.edgeWeight`, `StatMech.configWeight`: the one-coordinate and product weights with
  parameter `p`.
* `StatMech.weightOff p e ω`: the product weight over all coordinates other than `e`.
* `StatMech.prob p A`: the weight of the event `A`.
* `StatMech.pivotalProb p A e`: the weight of the event that `e` is pivotal for `A`.

## Main results

* `StatMech.hasDerivAt_prob_eq_sum_pivotalProb`, `StatMech.deriv_prob_eq_sum_pivotalProb`:
  **Russo's formula** (also the Margulis–Russo formula),
  `d/dp prob p A = ∑ e, pivotalProb p A e` for increasing `A`.

`prob` is `StatMech.wprob` for the Bernoulli coordinate weights (`StatMech.prob_eq_wprob`).

## References

* L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981).
* G. A. Margulis, *Probabilistic characteristics of graphs with large connectivity*, Problemy
  Peredači Informacii 10 (1974).
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Section 2.4.
-/

namespace StatMech

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The weight of coordinate `e` in configuration `ω` with parameter `p`: `p` if `ω e` is open
(`true`), `1 - p` otherwise. -/
noncomputable def edgeWeight (p : ℝ) (ω : ConfigSpace E) (e : E) : ℝ :=
  if ω e then p else 1 - p

/-- The product of the coordinate weights over all coordinates except `e`. -/
noncomputable def weightOff (p : ℝ) (e : E) (ω : ConfigSpace E) : ℝ :=
  ∏ j ∈ univ.erase e, edgeWeight p ω j

/-- The product weight `∏ e, edgeWeight p ω e` of a configuration; for `p ∈ [0, 1]` the
probability of `ω` under independent Bernoulli(`p`) coordinates. -/
noncomputable def configWeight (p : ℝ) (ω : ConfigSpace E) : ℝ :=
  ∏ e, edgeWeight p ω e

/-- The weight `∑ ω ∈ A, configWeight p ω` of an event `A`; for `p ∈ [0, 1]` its probability
under independent Bernoulli(`p`) coordinates. -/
noncomputable def prob (p : ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * configWeight p ω

/-- The weight of the event that coordinate `e` is pivotal for `A`. -/
noncomputable def pivotalProb (p : ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  ∑ ω, (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeight p ω

omit [DecidableEq E] in
/-- `configWeight` is the product weight `StatMech.pweight` for Bernoulli coordinate weights. -/
lemma configWeight_eq_pweight (p : ℝ) (ω : ConfigSpace E) :
    configWeight p ω = pweight (fun _ b => if b then p else 1 - p) ω := rfl

omit [DecidableEq E] in
/-- The product weight `configWeight p ω` is nonnegative for `p ∈ [0, 1]`. -/
lemma configWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : ConfigSpace E) :
    0 ≤ configWeight p ω := by
  unfold configWeight edgeWeight
  apply Finset.prod_nonneg
  intro e _
  by_cases h : ω e <;> simp [h] <;> linarith

/-- The pivotal weight `pivotalProb p A e` is nonnegative for `p ∈ [0, 1]`. -/
lemma pivotalProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Set (ConfigSpace E))
    (e : E) : 0 ≤ pivotalProb p A e := by
  unfold pivotalProb
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (configWeight_nonneg hp0 hp1 ω)

/-- `prob` is `StatMech.wprob` for Bernoulli coordinate weights. -/
lemma prob_eq_wprob (p : ℝ) (A : Set (ConfigSpace E)) :
    prob p A = wprob (fun _ b => if b then p else 1 - p) A := rfl

/-- The product weight splits as the weight of `e` times the weight of the other coordinates. -/
lemma configWeight_eq (p : ℝ) (e : E) (ω : ConfigSpace E) :
    configWeight p ω = edgeWeight p ω e * weightOff p e ω := by
  unfold configWeight weightOff
  rw [← Finset.mul_prod_erase univ _ (mem_univ e)]

/-- `weightOff p e ω` depends only on the values of `ω` off `e`. -/
lemma weightOff_congr (p : ℝ) (e : E) {ω ω' : ConfigSpace E}
    (h : ∀ e', e' ≠ e → ω e' = ω' e') : weightOff p e ω = weightOff p e ω' := by
  unfold weightOff
  apply Finset.prod_congr rfl
  intro j hj
  have hje : j ≠ e := (Finset.mem_erase.mp hj).1
  unfold edgeWeight; rw [h j hje]

omit [Fintype E] [DecidableEq E] in
/-- The derivative in `p` of a coordinate weight is `1` if the coordinate is open, `-1`
otherwise. -/
lemma hasDerivAt_edgeWeight (ω : ConfigSpace E) (e : E) (p : ℝ) :
    HasDerivAt (fun p => edgeWeight p ω e) (if ω e then 1 else -1) p := by
  unfold edgeWeight
  by_cases h : ω e
  · simp only [h, ite_true]; exact hasDerivAt_id p
  · simp only [h]
    have : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by
      simpa using (hasDerivAt_id' p).const_sub (1 : ℝ)
    simpa using this

/-- The derivative in `p` of the product weight (product rule). -/
lemma hasDerivAt_configWeight (ω : ConfigSpace E) (p : ℝ) :
    HasDerivAt (fun p => configWeight p ω)
      (∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  unfold configWeight weightOff
  have h := HasDerivAt.finsetProd (u := (univ : Finset E)) (f := fun e p => edgeWeight p ω e)
    (f' := fun e => if ω e then (1 : ℝ) else -1) (fun e _ => hasDerivAt_edgeWeight ω e p)
  simp only [smul_eq_mul] at h
  convert h using 1
  funext q
  simp [Finset.prod_apply]

/-- The derivative in `p` of `prob p A`, before grouping by pivotal coordinates. -/
lemma hasDerivAt_prob (A : Set (ConfigSpace E)) (p : ℝ) :
    HasDerivAt (fun p => prob p A)
      (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
        ∑ e, weightOff p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  unfold prob
  apply HasDerivAt.fun_sum
  intro ω _
  exact (hasDerivAt_configWeight ω p).const_mul (A.indicator (fun _ => (1 : ℝ)) ω)

omit [Fintype E] in
/-- Opening `e` in the configuration with value `b` at `e` and `η` elsewhere. -/
lemma setOpen_symm (e : E) (b : Bool) (η : {j : E // j ≠ e} → Bool) :
    setOpen e ((Equiv.funSplitAt e Bool).symm (b, η))
      = (Equiv.funSplitAt e Bool).symm (true, η) := by
  funext j
  by_cases hj : j = e
  · subst hj; simp [setOpen, Equiv.funSplitAt, Equiv.piSplitAt]
  · rw [setOpen_of_ne hj]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]

omit [Fintype E] in
/-- Closing `e` in the configuration with value `b` at `e` and `η` elsewhere. -/
lemma setClosed_symm (e : E) (b : Bool) (η : {j : E // j ≠ e} → Bool) :
    setClosed e ((Equiv.funSplitAt e Bool).symm (b, η))
      = (Equiv.funSplitAt e Bool).symm (false, η) := by
  funext j
  by_cases hj : j = e
  · subst hj; simp [setClosed, Equiv.funSplitAt, Equiv.piSplitAt]
  · rw [setClosed_of_ne hj]; simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]

/-- Russo's formula on one fiber `{ωt, ωf}` of configurations differing only at `e`. -/
lemma russo_per_eta (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E)
    (ωt ωf : ConfigSpace E)
    (hwo : weightOff p e ωt = weightOff p e ωf)
    (hto : setOpen e ωt = ωt) (htc : setClosed e ωt = ωf)
    (ht : ωt e = true) (hf : ωf e = false) :
    A.indicator (fun _ => (1 : ℝ)) ωt * (weightOff p e ωt * if ωt e then 1 else -1) +
        A.indicator (fun _ => (1 : ℝ)) ωf * (weightOff p e ωf * if ωf e then 1 else -1) =
      {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ωt * configWeight p ωt +
        {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ωf * configWeight p ωf := by
  classical
  have hife : (if ωt e then (1 : ℝ) else -1) = 1 := by rw [ht]; rfl
  have hiff : (if ωf e then (1 : ℝ) else -1) = -1 := by rw [hf]; rfl
  rw [hife, hiff, configWeight_eq p e ωt, configWeight_eq p e ωf]
  have hewt : edgeWeight p ωt e = p := by unfold edgeWeight; rw [ht]; rfl
  have hewf : edgeWeight p ωf e = 1 - p := by unfold edgeWeight; rw [hf]; rfl
  rw [hewt, hewf, ← hwo]
  set w := weightOff p e ωt with hw
  have hpiv_eq : IsPivotal e A ωt ↔ IsPivotal e A ωf := by
    apply isPivotal_congr; intro e' he'; rw [← htc, setClosed_of_ne he']
  have hpiv_t : IsPivotal e A ωt ↔ (ωf ∉ A ∧ ωt ∈ A) := by
    rw [isPivotal_iff_of_isIncreasing hA, hto, htc]
  have pivInd : ∀ ω, {ω | IsPivotal e A ω}.indicator (fun _ => (1 : ℝ)) ω
      = if IsPivotal e A ω then 1 else 0 := fun ω => by
    rw [Set.indicator_apply]; congr 1
  rw [pivInd ωt, pivInd ωf]
  by_cases hmt : ωt ∈ A <;> by_cases hmf : ωf ∈ A
  · have hnp : ¬ IsPivotal e A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_mem hmt, Set.indicator_of_mem hmf, ite_eq_right hnp,
        ite_eq_right (hpiv_eq.not.mp hnp)]; ring
  · have hp : IsPivotal e A ωt := by rw [hpiv_t]; exact ⟨hmf, hmt⟩
    rw [Set.indicator_of_mem hmt, Set.indicator_of_notMem hmf, ite_eq_left hp,
        ite_eq_left (hpiv_eq.mp hp)]; ring
  · exfalso
    have hle : ωf ≤ ωt := by
      have := setClosed_le_setOpen e ωt; rwa [htc, hto] at this
    exact hmt (hA hle hmf)
  · have hnp : ¬ IsPivotal e A ωt := by rw [hpiv_t]; tauto
    rw [Set.indicator_of_notMem hmt, Set.indicator_of_notMem hmf, ite_eq_right hnp,
        ite_eq_right (hpiv_eq.not.mp hnp)]; ring

/-- The contribution of coordinate `e` to the derivative of `prob p A` is
`pivotalProb p A e`, for increasing `A`. -/
lemma russo_per_edge (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * (weightOff p e ω * (if ω e then (1 : ℝ) else -1))
      = pivotalProb p A e := by
  unfold pivotalProb
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
        (fun ω => A.indicator (fun _ => (1 : ℝ)) ω *
          (weightOff p e ω * (if ω e then (1 : ℝ) else -1)))]
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
        (fun ω => (Set.indicator {ω | IsPivotal e A ω} (fun _ => (1 : ℝ)) ω) * configWeight p ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η _
  set ωt := (Equiv.funSplitAt e Bool).symm (true, η) with hωt
  set ωf := (Equiv.funSplitAt e Bool).symm (false, η) with hωf
  have ht : ωt e = true := by rw [hωt]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : ωf e = false := by rw [hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hto : setOpen e ωt = ωt := by rw [hωt, setOpen_symm]
  have htc : setClosed e ωt = ωf := by rw [hωt, setClosed_symm]
  have hwo : weightOff p e ωt = weightOff p e ωf := by
    apply weightOff_congr; intro e' he'
    rw [hωt, hωf]; simp [Equiv.funSplitAt, Equiv.piSplitAt, he']
  exact russo_per_eta p A hA e ωt ωf hwo hto htc ht hf

/-- **Russo's formula** (Russo 1981; Margulis 1974): for an increasing event `A` on a finite
set of coordinates, `p ↦ prob p A` has derivative `∑ e, pivotalProb p A e` at every `p`. -/
theorem hasDerivAt_prob_eq_sum_pivotalProb
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (p : ℝ) :
    HasDerivAt (fun p => prob p A) (∑ e, pivotalProb p A e) p := by
  have hd := hasDerivAt_prob A p
  convert hd using 1
  rw [show (∑ e, pivotalProb p A e)
        = ∑ e, ∑ ω,
            A.indicator (fun _ => (1 : ℝ)) ω * (weightOff p e ω * (if ω e then (1 : ℝ) else -1))
        from Finset.sum_congr rfl (fun e _ => (russo_per_edge p A hA e).symm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]

/-- **Russo's formula**, `deriv` form: `d/dp prob p A = ∑ e, pivotalProb p A e` for
increasing `A`. -/
theorem deriv_prob_eq_sum_pivotalProb
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (p : ℝ) :
    deriv (fun p => prob p A) p = ∑ e, pivotalProb p A e :=
  (hasDerivAt_prob_eq_sum_pivotalProb A hA p).deriv

end StatMech
