/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# Homogeneous-product Bertrand duopoly (Atlas EC17.T03)

Two firms with the same constant marginal cost `c` set prices for an identical good.
The lower-priced firm serves all demand, a tie splits demand equally, and there are no
capacity limits. Marginal-cost pricing is an equilibrium whenever demand is
nonnegative; with positive nonincreasing demand it is the only equilibrium (the
Bertrand paradox).

`IsBertrandNash` is stated in no-profitable-deviation form. It is the Nash condition of
the strategic game with players `Fin 2`, strategies `ℝ` and payoffs `bertrandProfit`;
it should be unified with the strategic-game interface of Atlas EC12.T01 once that
lands.

## Main results

* `MathlibExt.Economics.Bertrand.isBertrandNash_marginalCost`
* `MathlibExt.Economics.Bertrand.isBertrandNash_iff`

## References

* J. Bertrand, review of Cournot and Walras, *Journal des Savants* 67 (1883),
  499--508.
* J. Tirole, *The Theory of Industrial Organization*, MIT Press, 1988, §5.1.
-/

namespace MathlibExt.Economics.Bertrand

/-- Quantity sold by firm `i` in the homogeneous-product Bertrand duopoly with market demand
`D` at the price profile `p` (the rival of `i` is `i.rev`): the whole market demand at a
strictly lower price, half of it at a tie, nothing at a strictly higher price. Firms have no
capacity limits. -/
noncomputable def bertrandQuantity (D : ℝ → ℝ) (p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if p i < p i.rev then D (p i) else if p i = p i.rev then D (p i) / 2 else 0

/-- Profit of firm `i` when both firms have the same constant marginal cost `c` and no fixed
cost. -/
noncomputable def bertrandProfit (c : ℝ) (D : ℝ → ℝ) (p : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  (p i - c) * bertrandQuantity D p i

/-- A price profile is a (pure-strategy) Nash equilibrium of the Bertrand pricing game when no
firm can raise its profit by a unilateral price change. This is the no-profitable-deviation
form of Nash equilibrium for the strategic game with players `Fin 2`, strategy set `ℝ` and
payoffs `bertrandProfit c D`. -/
def IsBertrandNash (c : ℝ) (D : ℝ → ℝ) (p : Fin 2 → ℝ) : Prop :=
  ∀ (i : Fin 2) (t : ℝ), bertrandProfit c D (Function.update p i t) i ≤ bertrandProfit c D p i

private theorem ec17t03_rev_ne (i : Fin 2) : i.rev ≠ i := by
  fin_cases i <;> decide

private theorem ec17t03_rev_zero : (0 : Fin 2).rev = 1 := by decide

private theorem ec17t03_rev_one : (1 : Fin 2).rev = 0 := by decide

private theorem ec17t03_profit_low {c : ℝ} {D : ℝ → ℝ} {p : Fin 2 → ℝ} {i : Fin 2}
    (hlt : p i < p i.rev) : bertrandProfit c D p i = (p i - c) * D (p i) := by
  unfold bertrandProfit bertrandQuantity
  rw [ite_eq_left hlt]

private theorem ec17t03_profit_tie {c : ℝ} {D : ℝ → ℝ} {p : Fin 2 → ℝ} {i : Fin 2}
    (htie : p i = p i.rev) : bertrandProfit c D p i = (p i - c) * (D (p i) / 2) := by
  have hnotlt : ¬ p i < p i.rev := by rw [htie]; exact lt_irrefl _
  unfold bertrandProfit bertrandQuantity
  rw [ite_eq_right hnotlt, ite_eq_left htie]

private theorem ec17t03_profit_high {c : ℝ} {D : ℝ → ℝ} {p : Fin 2 → ℝ} {i : Fin 2}
    (hgt : p i.rev < p i) : bertrandProfit c D p i = 0 := by
  have hnotlt : ¬ p i < p i.rev := by linarith
  have hne : ¬ p i = p i.rev := by linarith
  unfold bertrandProfit bertrandQuantity
  rw [ite_eq_right hnotlt, ite_eq_right hne, mul_zero]

private theorem ec17t03_deviate_above {c : ℝ} {D : ℝ → ℝ} {p : Fin 2 → ℝ} {i : Fin 2} :
    bertrandProfit c D (Function.update p i (p i.rev + 1)) i = 0 := by
  have hq_i : Function.update p i (p i.rev + 1) i = p i.rev + 1 :=
    Function.update_self _ _ _
  have hq_r : Function.update p i (p i.rev + 1) i.rev = p i.rev :=
    Function.update_of_ne (ec17t03_rev_ne i) _ _
  have hgt : Function.update p i (p i.rev + 1) i.rev
      < Function.update p i (p i.rev + 1) i := by
    rw [hq_i, hq_r]; linarith
  exact ec17t03_profit_high hgt

private theorem ec17t03_not_nash_below {c : ℝ} {D : ℝ → ℝ} (hpos : ∀ x, 0 < D x)
    {p : Fin 2 → ℝ} {i : Fin 2} (hlt : p i < p i.rev) (hbelow : p i < c) :
    ¬ IsBertrandNash c D p := by
  intro hNash
  have hcur_neg : bertrandProfit c D p i < 0 := by
    rw [ec17t03_profit_low hlt]
    exact mul_neg_of_neg_of_pos (by linarith) (hpos _)
  have hdev := hNash i (p i.rev + 1)
  rw [ec17t03_deviate_above] at hdev
  linarith

private theorem ec17t03_not_nash_at_low {c : ℝ} {D : ℝ → ℝ} (hpos : ∀ x, 0 < D x)
    {p : Fin 2 → ℝ} {i : Fin 2} (hlt : p i < p i.rev) (heq : p i = c) :
    ¬ IsBertrandNash c D p := by
  intro hNash
  have hcur0 : bertrandProfit c D p i = 0 := by
    rw [ec17t03_profit_low hlt, heq, sub_self, zero_mul]
  have hci : c < p i.rev := by linarith
  have hmid_lt : (c + p i.rev) / 2 < p i.rev := by linarith
  have hmid_gt : c < (c + p i.rev) / 2 := by linarith
  have hdev := hNash i ((c + p i.rev) / 2)
  have hq_i : Function.update p i ((c + p i.rev) / 2) i = (c + p i.rev) / 2 :=
    Function.update_self _ _ _
  have hq_r : Function.update p i ((c + p i.rev) / 2) i.rev = p i.rev :=
    Function.update_of_ne (ec17t03_rev_ne i) _ _
  have hlt' : Function.update p i ((c + p i.rev) / 2) i
      < Function.update p i ((c + p i.rev) / 2) i.rev := by
    rw [hq_i, hq_r]; exact hmid_lt
  have hdev_pos : 0 < bertrandProfit c D (Function.update p i ((c + p i.rev) / 2)) i := by
    rw [ec17t03_profit_low hlt', hq_i]
    exact mul_pos (by linarith) (hpos _)
  linarith

private theorem ec17t03_not_nash_high_match {c : ℝ} {D : ℝ → ℝ} (hpos : ∀ x, 0 < D x)
    {p : Fin 2 → ℝ} {i : Fin 2} (hlt : p i < p i.rev) (habove : c < p i) :
    ¬ IsBertrandNash c D p := by
  intro hNash
  have hrev : i.rev.rev = i := Fin.rev_rev i
  have hcur0 : bertrandProfit c D p i.rev = 0 := by
    have hgt : p i.rev.rev < p i.rev := by rw [hrev]; exact hlt
    exact ec17t03_profit_high hgt
  have hdev := hNash i.rev (p i)
  have hq_j : Function.update p i.rev (p i) i.rev = p i := Function.update_self _ _ _
  have hq_r : Function.update p i.rev (p i) i.rev.rev = p i.rev.rev :=
    Function.update_of_ne (by rw [hrev]; exact Ne.symm (ec17t03_rev_ne i)) _ _
  have htie : Function.update p i.rev (p i) i.rev
      = Function.update p i.rev (p i) i.rev.rev := by
    rw [hq_j, hq_r, hrev]
  have hdev_pos : 0 < bertrandProfit c D (Function.update p i.rev (p i)) i.rev := by
    rw [ec17t03_profit_tie htie, hq_j]
    exact mul_pos (by linarith) (by linarith [hpos (p i)])
  linarith

private theorem ec17t03_not_nash_tie_below {c : ℝ} {D : ℝ → ℝ} (hpos : ∀ x, 0 < D x)
    {p : Fin 2 → ℝ} {i : Fin 2} (htie : p i = p i.rev) (hbelow : p i < c) :
    ¬ IsBertrandNash c D p := by
  intro hNash
  have hcur_neg : bertrandProfit c D p i < 0 := by
    rw [ec17t03_profit_tie htie]
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith [hpos (p i)])
  have hdev := hNash i (p i.rev + 1)
  rw [ec17t03_deviate_above] at hdev
  linarith

private theorem ec17t03_not_nash_tie_above {c : ℝ} {D : ℝ → ℝ} (hpos : ∀ x, 0 < D x)
    (hanti : Antitone D) {p : Fin 2 → ℝ} {i : Fin 2}
    (htie : p i = p i.rev) (habove : c < p i) :
    ¬ IsBertrandNash c D p := by
  intro hNash
  have hmid : (p i + c) / 2 < p i := by linarith
  obtain ⟨t, hmt, htp⟩ := exists_between hmid
  have hle : t ≤ p i := le_of_lt htp
  have hD : D (p i) ≤ D t := hanti hle
  have hdev := hNash i t
  have hq_i : Function.update p i t i = t := Function.update_self _ _ _
  have hq_r : Function.update p i t i.rev = p i.rev :=
    Function.update_of_ne (ec17t03_rev_ne i) _ _
  have hlt' : Function.update p i t i < Function.update p i t i.rev := by
    rw [hq_i, hq_r, ← htie]; exact htp
  have hcur : bertrandProfit c D p i = (p i - c) * (D (p i) / 2) :=
    ec17t03_profit_tie htie
  have hdev_eq : bertrandProfit c D (Function.update p i t) i = (t - c) * D t := by
    rw [ec17t03_profit_low hlt', hq_i]
  have hk : 0 < (p i - c) / 2 := by linarith
  have htc : (p i - c) / 2 < t - c := by linarith
  have h1 : ((p i - c) / 2) * D t < (t - c) * D t :=
    mul_lt_mul_of_pos_right htc (hpos t)
  have h2 : ((p i - c) / 2) * D (p i) ≤ ((p i - c) / 2) * D t :=
    mul_le_mul_of_nonneg_left hD (le_of_lt hk)
  have heq : ((p i - c) / 2) * D (p i) = (p i - c) * (D (p i) / 2) := by ring
  rw [hcur, hdev_eq] at hdev
  linarith

private theorem ec17t03_eq_of_both_cost {c : ℝ} {p : Fin 2 → ℝ}
    (h0 : p 0 = c) (h1 : p 1 = c) : p = fun _ => c := by
  funext j
  fin_cases j <;> simp [*]

/-- Marginal-cost pricing by both firms is a Bertrand equilibrium whenever demand is
nonnegative. -/
theorem isBertrandNash_marginalCost {c : ℝ} {D : ℝ → ℝ} (hD : ∀ x, 0 ≤ D x) :
    IsBertrandNash c D (fun _ => c) := by
  intro i t
  have hcur0 : bertrandProfit c D (fun _ => c) i = 0 := by
    have htie : (fun _ => c) i = (fun _ => c) i.rev := rfl
    rw [ec17t03_profit_tie (p := fun _ => c) (i := i) htie, sub_self, zero_mul]
  rw [hcur0]
  have hq_i : Function.update (fun _ => c) i t i = t := Function.update_self _ _ _
  have hq_r : Function.update (fun _ => c) i t i.rev = (fun _ => c) i.rev :=
    Function.update_of_ne (ec17t03_rev_ne i) _ _
  rcases lt_trichotomy t c with htc | htc | htc
  · have hlt' : Function.update (fun _ => c) i t i
        < Function.update (fun _ => c) i t i.rev := by
      rw [hq_i, hq_r]; exact htc
    rw [ec17t03_profit_low hlt', hq_i]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hD t)
  · have htie' : Function.update (fun _ => c) i t i
        = Function.update (fun _ => c) i t i.rev := by
      rw [hq_i, hq_r]; exact htc
    have hdev0 : bertrandProfit c D (Function.update (fun _ => c) i t) i = 0 := by
      rw [ec17t03_profit_tie htie', hq_i, htc, sub_self, zero_mul]
    linarith
  · have hgt' : Function.update (fun _ => c) i t i.rev
        < Function.update (fun _ => c) i t i := by
      rw [hq_i, hq_r]; exact htc
    have hdev0 : bertrandProfit c D (Function.update (fun _ => c) i t) i = 0 :=
      ec17t03_profit_high hgt'
    linarith

/-- Bertrand paradox: with equal marginal costs, the tie-splitting rule, no capacity limits,
and positive nonincreasing demand, a price profile is a Bertrand equilibrium exactly when
both firms price at marginal cost. -/
theorem isBertrandNash_iff {c : ℝ} {D : ℝ → ℝ} (hpos : ∀ x, 0 < D x) (hanti : Antitone D)
    (p : Fin 2 → ℝ) :
    IsBertrandNash c D p ↔ p = fun _ => c := by
  constructor
  · intro hNash
    have hr0 : (0 : Fin 2).rev = 1 := ec17t03_rev_zero
    have hr1 : (1 : Fin 2).rev = 0 := ec17t03_rev_one
    rcases lt_trichotomy (p 0) (p 1) with h01 | h01 | h01
    · have hlt0 : p (0 : Fin 2) < p (0 : Fin 2).rev := by rwa [hr0]
      rcases lt_trichotomy (p 0) c with h0c | h0c | h0c
      · exact absurd hNash (ec17t03_not_nash_below hpos hlt0 h0c)
      · exact absurd hNash (ec17t03_not_nash_at_low hpos hlt0 h0c)
      · exact absurd hNash (ec17t03_not_nash_high_match hpos hlt0 h0c)
    · have htie0 : p (0 : Fin 2) = p (0 : Fin 2).rev := by rwa [hr0]
      rcases lt_trichotomy (p 0) c with h0c | h0c | h0c
      · exact absurd hNash (ec17t03_not_nash_tie_below hpos htie0 h0c)
      · exact ec17t03_eq_of_both_cost h0c (h01.symm.trans h0c)
      · exact absurd hNash (ec17t03_not_nash_tie_above hpos hanti htie0 h0c)
    · have hlt1 : p (1 : Fin 2) < p (1 : Fin 2).rev := by rwa [hr1]
      rcases lt_trichotomy (p 1) c with h1c | h1c | h1c
      · exact absurd hNash (ec17t03_not_nash_below hpos hlt1 h1c)
      · exact absurd hNash (ec17t03_not_nash_at_low hpos hlt1 h1c)
      · exact absurd hNash (ec17t03_not_nash_high_match hpos hlt1 h1c)
  · intro hpc
    rw [hpc]
    exact isBertrandNash_marginalCost (fun x => le_of_lt (hpos x))

end MathlibExt.Economics.Bertrand
