/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Vickrey–Clarke–Groves mechanisms

Agents `i : ι` (finitely many) have valuations `v i : A → ℝ` over a set `A` of alternatives and
quasi-linear utilities. A direct mechanism asks for the valuations, chooses an alternative
`f v` and charges agent `i` the payment `p v i`; it is *incentive compatible* when no agent
gains by misreporting its valuation, whatever the others report (Nisan 2007, Definition 9.15).

A *VCG mechanism* (Nisan 2007, Definition 9.16) chooses an alternative maximizing the reported
social welfare `∑ i, v i a` and charges `h i (v₋ᵢ) - ∑_{j ≠ i} v j (f v)`, where `h i` does not
depend on agent `i`'s own report. Each agent's utility is then the social welfare minus a term
it cannot influence, so truthful reporting is a dominant strategy (Vickrey 1961, Clarke 1971,
Groves 1973). The *Clarke pivot rule* `h i (v₋ᵢ) = max_b ∑_{j ≠ i} v j b` charges each agent the
externality it imposes on the others.

## Main results

* `grovesPayment_truthful`, `isIncentiveCompatible_groves`: every VCG mechanism is incentive
  compatible (Nisan 2007, Theorem 9.17).
* `clarkePivot_independent`: the Clarke pivot term does not depend on the agent's own report.
* `clarkePayment_nonneg`, `clarke_utility_nonneg`: with Clarke pivot payments, no agent is ever
  paid, and when all valuations are nonnegative every truthful agent gets a nonnegative utility
  (Nisan 2007, Lemma 9.20).
* `grovesPayment_singleItem`, `secondPrice_truthful`: Vickrey's second-price auction is the VCG
  mechanism with Clarke pivot payments for one item, hence truthful (Nisan 2007, §9.3.5.1 and
  Proposition 9.13).

## References

* N. Nisan, "Introduction to mechanism design (for computer scientists)", Chapter 9 of
  N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*,
  Cambridge University Press, 2007, Definitions 9.12, 9.15, 9.16, 9.18, 9.19, Proposition 9.13,
  Theorem 9.17, Lemma 9.20 and §9.3.5.1.
* W. Vickrey, "Counterspeculation, auctions, and competitive sealed tenders", *J. Finance* 16
  (1961), 8–37; E. H. Clarke, "Multipart pricing of public goods", *Public Choice* 11 (1971),
  17–33; T. Groves, "Incentives in teams", *Econometrica* 41 (1973), 617–631 (cited through
  Nisan 2007, §9.3.3).
-/

namespace MathlibExt.GameTheory.MechanismDesign.VCG

open Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

/-- **Social welfare.** The total value `∑ i, v i a` of the alternative `a` for the valuation
profile `v`. -/
def welfare (v : ι → A → ℝ) (a : A) : ℝ := ∑ i, v i a

/-- **Welfare of the others.** The total value `∑_{j ≠ i} v j a` of the alternative `a` for the
agents other than `i`. -/
def othersWelfare (v : ι → A → ℝ) (i : ι) (a : A) : ℝ := ∑ j ∈ univ.erase i, v j a

/-- **Welfare decomposition.** The welfare is agent `i`'s value plus the others' welfare. -/
theorem welfare_eq (v : ι → A → ℝ) (i : ι) (a : A) :
    welfare v a = v i a + othersWelfare v i a := by
  unfold welfare othersWelfare
  rw [← add_sum_erase _ _ (mem_univ i)]

/-- **The others' welfare ignores the own valuation.** The welfare of the agents other than `i`
does not depend on agent `i`'s valuation. -/
theorem othersWelfare_update (v : ι → A → ℝ) (i : ι) (w : A → ℝ) (a : A) :
    othersWelfare (Function.update v i w) i a = othersWelfare v i a := by
  unfold othersWelfare
  refine sum_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

/-- **Incentive compatibility (quasi-linear, dominant strategies).** The direct mechanism
`(f, p)` is incentive compatible: for every agent `i`, every profile `v` and every report `w`
of agent `i`, `v i (f v) - p v i ≥ v i (f v') - p v' i` with `v' = update v i w`
(Nisan 2007, Definition 9.15). -/
def IsIncentiveCompatible (f : (ι → A → ℝ) → A) (p : (ι → A → ℝ) → ι → ℝ) : Prop :=
  ∀ i (v : ι → A → ℝ) (w : A → ℝ),
    v i (f (Function.update v i w)) - p (Function.update v i w) i ≤ v i (f v) - p v i

/-- **Groves payment.** The payment `h i v - ∑_{j ≠ i} v j (f v)` of agent `i` in the VCG
mechanism with alternative rule `f` and pivot terms `h` (Nisan 2007, Definition 9.16). -/
def grovesPayment (f : (ι → A → ℝ) → A) (h : ι → (ι → A → ℝ) → ℝ) (v : ι → A → ℝ) (i : ι) :
    ℝ :=
  h i v - othersWelfare v i (f v)

/-- **Pivot terms independent of the own report.** Each `h i` depends only on `v₋ᵢ`. -/
def IndependentOfOwn (h : ι → (ι → A → ℝ) → ℝ) : Prop :=
  ∀ i (v : ι → A → ℝ) (w : A → ℝ), h i (Function.update v i w) = h i v

/-- **VCG truthfulness, pointwise.** If the pivot terms do not depend on the agents' own
reports and `f v` has at least the welfare (at the true profile `v`) of the alternative chosen
after agent `i` reports `w`, then agent `i` does not gain by reporting `w` instead of `v i`. -/
theorem grovesPayment_truthful {f : (ι → A → ℝ) → A} {h : ι → (ι → A → ℝ) → ℝ}
    (hh : IndependentOfOwn h) (i : ι) (v : ι → A → ℝ) (w : A → ℝ)
    (hf : welfare v (f (Function.update v i w)) ≤ welfare v (f v)) :
    v i (f (Function.update v i w)) - grovesPayment f h (Function.update v i w) i ≤
      v i (f v) - grovesPayment f h v i := by
  unfold grovesPayment
  rw [hh i v w, othersWelfare_update, welfare_eq v i, welfare_eq v i] at *
  linarith

/-- **Vickrey–Clarke–Groves theorem.** A mechanism that chooses a welfare-maximizing
alternative for every reported profile and charges Groves payments with pivot terms that do not
depend on the agents' own reports is incentive compatible (Nisan 2007, Theorem 9.17). -/
theorem isIncentiveCompatible_groves {f : (ι → A → ℝ) → A} {h : ι → (ι → A → ℝ) → ℝ}
    (hf : ∀ v a, welfare v a ≤ welfare v (f v)) (hh : IndependentOfOwn h) :
    IsIncentiveCompatible f (grovesPayment f h) :=
  fun i v w => grovesPayment_truthful hh i v w (hf v _)

section Clarke

variable [Fintype A] [Nonempty A]

/-- **Clarke pivot term.** `max_b ∑_{j ≠ i} v j b`, the best welfare the other agents could get
without agent `i` (Nisan 2007, Definition 9.19). -/
def clarkePivot (i : ι) (v : ι → A → ℝ) : ℝ :=
  univ.sup' univ_nonempty fun b => othersWelfare v i b

/-- **The Clarke pivot term ignores the own report.** -/
theorem clarkePivot_independent : IndependentOfOwn (clarkePivot (ι := ι) (A := A)) := by
  intro i v w
  simp only [clarkePivot, othersWelfare_update]

/-- **VCG with Clarke pivot payments is incentive compatible.** -/
theorem isIncentiveCompatible_clarke {f : (ι → A → ℝ) → A}
    (hf : ∀ v a, welfare v a ≤ welfare v (f v)) :
    IsIncentiveCompatible f (grovesPayment f clarkePivot) :=
  isIncentiveCompatible_groves hf clarkePivot_independent

/-- **No positive transfers.** With Clarke pivot payments, every agent pays a nonnegative
amount (Nisan 2007, Lemma 9.20, first part). -/
theorem clarkePayment_nonneg (f : (ι → A → ℝ) → A) (v : ι → A → ℝ) (i : ι) :
    0 ≤ grovesPayment f clarkePivot v i := by
  unfold grovesPayment clarkePivot
  have := le_sup' (fun b => othersWelfare v i b) (mem_univ (f v))
  linarith

/-- **Individual rationality.** If `f v` maximizes the welfare at `v` and all valuations are
nonnegative, then with Clarke pivot payments every agent reporting truthfully gets a nonnegative
utility (Nisan 2007, Lemma 9.20, second part). -/
theorem clarke_utility_nonneg {f : (ι → A → ℝ) → A} {v : ι → A → ℝ}
    (hf : ∀ a, welfare v a ≤ welfare v (f v)) (hv : ∀ i a, 0 ≤ v i a) (i : ι) :
    0 ≤ v i (f v) - grovesPayment f clarkePivot v i := by
  unfold grovesPayment clarkePivot
  obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' univ_nonempty fun b => othersWelfare v i b
  rw [hb]
  have h1 := hf b
  rw [welfare_eq v i, welfare_eq v i] at h1
  linarith [hv i b]

end Clarke

/-! ### Vickrey's second-price auction -/

section SecondPrice

/-- **Single-item valuations.** The alternatives are the possible winners `a : ι` of one item,
and the bids `t` give agent `i` the value `t i` if it wins and `0` otherwise (Nisan 2007, §9.3.1
and §9.3.5.1). -/
def singleItem (t : ι → ℝ) : ι → ι → ℝ := fun i a => if a = i then t i else 0

/-- **Welfare of a winner.** With single-item valuations, the welfare of the alternative "`a`
wins" is `a`'s bid. -/
theorem welfare_singleItem (t : ι → ℝ) (a : ι) : welfare (singleItem t) a = t a := by
  simp only [welfare, singleItem]
  rw [Finset.sum_ite_eq]
  simp

/-- **Others' welfare of a winner.** With single-item valuations, the others' welfare is `0` when
agent `i` wins and the winner's bid otherwise. -/
theorem othersWelfare_singleItem (t : ι → ℝ) (i a : ι) :
    othersWelfare (singleItem t) i a = if a = i then 0 else t a := by
  unfold othersWelfare singleItem
  rw [Finset.sum_ite_eq]
  by_cases h : a = i
  · simp [h]
  · simp [h]

omit [Fintype ι] in
/-- **Changing one bid changes one valuation.** -/
theorem update_singleItem (t : ι → ℝ) (i : ι) (s : ℝ) :
    Function.update (singleItem t) i (singleItem (Function.update t i s) i) =
      singleItem (Function.update t i s) := by
  funext j a
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h, singleItem]

variable [Nontrivial ι]

/-- **Some other agent exists.** With at least two agents, the agents other than `i` form a
nonempty set. -/
theorem nonempty_others (i : ι) : (univ.erase i).Nonempty := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨j, mem_erase.2 ⟨hj, mem_univ j⟩⟩

/-- **Second-price payment.** In the auction with winner rule `w`, the winner pays the highest
competing bid `max_{j ≠ i} t j` and losers pay nothing (Nisan 2007, Definition 9.12). -/
noncomputable def secondPricePayment (w : (ι → ℝ) → ι) (t : ι → ℝ) (i : ι) : ℝ :=
  if w t = i then (univ.erase i).sup' (nonempty_others i) t else 0

/-- **The second-price auction is the VCG mechanism with Clarke pivot payments.** For
nonnegative bids and a winner rule `w` that picks a highest bid, the Clarke pivot payment of the
VCG mechanism on single-item valuations is the second-price payment (Nisan 2007,
§9.3.5.1). -/
theorem grovesPayment_singleItem {w : (ι → ℝ) → ι} (hw : ∀ (t : ι → ℝ) (j : ι), t j ≤ t (w t))
    {t : ι → ℝ}
    (ht : ∀ j, 0 ≤ t j) (i : ι) :
    grovesPayment (fun v => w fun j => v j j) clarkePivot (singleItem t) i =
      secondPricePayment w t i := by
  have hdiag : (fun j => singleItem t j j) = t := by funext j; simp [singleItem]
  have hpiv : clarkePivot i (singleItem t) = (univ.erase i).sup' (nonempty_others i) t := by
    unfold clarkePivot
    simp only [othersWelfare_singleItem]
    apply le_antisymm
    · refine sup'_le _ _ fun b _ => ?_
      split_ifs with hb
      · obtain ⟨j, hj⟩ := nonempty_others i
        exact (ht j).trans (le_sup' t hj)
      · exact le_sup' t (mem_erase.2 ⟨hb, mem_univ b⟩)
    · refine sup'_le _ _ fun b hb => ?_
      have hb' := (mem_erase.1 hb).1
      refine le_trans ?_ (le_sup' (fun b => if b = i then (0 : ℝ) else t b) (mem_univ b))
      simp [hb']
  unfold grovesPayment secondPricePayment
  change clarkePivot i (singleItem t) -
    othersWelfare (singleItem t) i (w fun j => singleItem t j j) = _
  rw [hdiag, hpiv, othersWelfare_singleItem]
  by_cases hwi : w t = i
  · simp [hwi]
  · simp only [hwi, ite_false]
    have : (univ.erase i).sup' (nonempty_others i) t = t (w t) :=
      le_antisymm (sup'_le _ _ fun b _ => hw t b) (le_sup' t (mem_erase.2 ⟨hwi, mem_univ _⟩))
    rw [this, sub_self]

/-- **Vickrey's theorem.** In the second-price auction with a winner rule `w` that picks a
highest bid, no bidder gains by bidding `s` instead of its value `t i`, whatever the other
nonnegative bids: its utility `t i - (price)` if it wins, `0` otherwise, is largest when it bids
its value (Vickrey 1961, through Nisan 2007, Proposition 9.13). The statement is for nonnegative
values and bids, the valuation domain of Nisan 2007, §9.3.5.1, and is derived from the VCG
theorem. -/
theorem secondPrice_truthful {w : (ι → ℝ) → ι} (hw : ∀ (t : ι → ℝ) (j : ι), t j ≤ t (w t))
    {t : ι → ℝ}
    (ht : ∀ j, 0 ≤ t j) (i : ι) {s : ℝ} (hs : 0 ≤ s) :
    (if w (Function.update t i s) = i then t i else 0) -
        secondPricePayment w (Function.update t i s) i ≤
      (if w t = i then t i else 0) - secondPricePayment w t i := by
  have ht' : ∀ j, 0 ≤ Function.update t i s j := by
    intro j; by_cases h : j = i
    · subst h; simpa using hs
    · simpa [Function.update_of_ne h] using ht j
  have hdiag : ∀ t' : ι → ℝ, (fun j => singleItem t' j j) = t' := by
    intro t'; funext j; simp [singleItem]
  have key := grovesPayment_truthful (f := fun v => w fun j => v j j) clarkePivot_independent i
    (singleItem t) (singleItem (Function.update t i s) i) (by
      rw [update_singleItem]
      simp only [hdiag, welfare_singleItem]
      exact hw t _)
  rw [update_singleItem, grovesPayment_singleItem hw ht' i, grovesPayment_singleItem hw ht i]
    at key
  rw [hdiag, hdiag] at key
  exact key

end SecondPrice

end MathlibExt.GameTheory.MechanismDesign.VCG
