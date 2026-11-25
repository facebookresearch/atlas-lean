/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/818.lean` (Formal Conjectures), for the conjecture statement.
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 818

`conjecture_holds` gives a lower bound for the size of the product set of a finite set of
integers with small additive doubling. The proof uses Solymosi's multiplicative energy bound.
-/

@[expose] public section

open scoped Pointwise
open Finset

namespace MathlibExt.NumberTheory.ErdosProblem818Wanted

/-- **Erdős Problem 818.** The statement that for every real $K > 0$ there are reals $C > 0$ and
$c > 0$ such that every finite set $A$ of integers with $|A| \ge 2$ and $|A + A| \le K|A|$
satisfies $c|A|^2 / (\log |A|)^C \le |A \cdot A|$. Here $A + A = \{a + b : a, b \in A\}$,
$A \cdot A = \{ab : a, b \in A\}$ and $\log$ is the natural logarithm. -/
def conjecture : Prop :=
  ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ A : Finset ℤ, 2 ≤ A.card → ((A + A).card : ℝ) ≤ K * (A.card : ℝ) →
      c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C ≤ ((A * A).card : ℝ)

/-- Abscissas of points of the grid on the ray of slope `r`. -/
private noncomputable def ray (B : Finset ℝ) (r : ℝ) : Finset ℝ :=
  B.filter fun x => r * x ∈ B

private lemma energy_le_sum_rays (B : Finset ℝ) (hB : ∀ x ∈ B, 0 < x) :
    B.mulEnergy B ≤ ∑ r ∈ B / B, (ray B r).card ^ 2 := by
  classical
  let Q := ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun p => p.1.1 * p.2.1 = p.1.2 * p.2.2
  let slope (p : (ℝ × ℝ) × ℝ × ℝ) := p.1.2 / p.1.1
  change Q.card ≤ _
  rw [card_eq_sum_card_fiberwise (f := slope) (t := B / B) (s := Q) (by
    intro p hp
    obtain ⟨⟨⟨ha, hb⟩, _⟩, _⟩ := by simpa [Q] using hp
    exact div_mem_div hb ha)]
  refine sum_le_sum fun r _ => ?_
  rw [sq, ← card_product]
  have data (p) (hp : p ∈ Q.filter fun p => slope p = r) :
      p.1.1 ∈ B ∧ p.2.2 ∈ B ∧ r * p.1.1 = p.1.2 ∧ r * p.2.2 = p.2.1 ∧
        p.1.2 ∈ B ∧ p.2.1 ∈ B := by
    simp only [Q, slope, mem_filter, mem_product] at hp
    obtain ⟨⟨⟨⟨ha, hb⟩, hc, hd⟩, he⟩, hr⟩ := hp
    have ha' := (hB _ ha).ne'
    have hm := (div_eq_iff ha').mp hr
    refine ⟨ha, hd, hm.symm, ?_, hb, hc⟩
    apply mul_left_cancel₀ ha'
    rw [hm] at he
    linear_combination -he
  apply card_le_card_of_injOn (fun p => (p.1.1, p.2.2))
  · intro p hp
    obtain ⟨ha, hd, h₁, h₂, hb, hc⟩ := data p hp
    simpa [ray, h₁, h₂] using And.intro (And.intro ha hb) (And.intro hd hc)
  · intro p hp q hq he
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj he
    obtain ⟨_, _, hpb, hpc, _⟩ := data p hp
    obtain ⟨_, _, hqb, hqc, _⟩ := data q hq
    exact Prod.ext (Prod.ext h₁ (by rw [← hpb, ← hqb, h₁]))
      (Prod.ext (by rw [← hpc, ← hqc, h₂]) h₂)

/-- The sum of two positive vectors of distinct slopes lies strictly between their rays. -/
private lemma slope_between {r s x y : ℝ} (hrs : r < s) (hx : 0 < x) (hy : 0 < y) :
    r < (r * x + s * y) / (x + y) ∧ (r * x + s * y) / (x + y) < s := by
  rw [lt_div_iff₀ (add_pos hx hy), div_lt_iff₀ (add_pos hx hy)]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hrs) hy]
  · nlinarith [mul_pos (sub_pos.mpr hrs) hx]

/-- For a class of rays with at least `t` points each, count the sums from consecutive rays.
The final ray costs at most one more copy of the sum grid. -/
private lemma rich_rays_bound (B D : Finset ℝ) (hB : ∀ x ∈ B, 0 < x)
    (t : ℕ) (ht : ∀ r ∈ D, t ≤ (ray B r).card) :
    D.card * t ^ 2 ≤ 2 * (B + B).card ^ 2 := by
  classical
  cases hD : D.card with
  | zero => simp
  | succ m =>
    let r := D.orderEmbOfFin hD
    let x (i : Fin (m + 1)) := (ray B (r i)).orderEmbOfCardLe (ht _ (D.orderEmbOfFin_mem hD i))
    have hx (i j) : x i j ∈ B ∧ r i * x i j ∈ B :=
      mem_filter.mp ((ray B (r i)).orderEmbOfCardLe_mem _ _)
    let f (p : Fin m × Fin t × Fin t) : ℝ × ℝ :=
      let a := x p.1.castSucc p.2.1
      let b := x p.1.succ p.2.2
      (a + b, r p.1.castSucc * a + r p.1.succ * b)
    have sector (p) : r p.1.castSucc < (f p).2 / (f p).1 ∧
        (f p).2 / (f p).1 < r p.1.succ :=
      slope_between (r.strictMono p.1.castSucc_lt_succ)
        (hB _ (hx _ _).1) (hB _ (hx _ _).1)
    have hsep (p q) (hpq : f p = f q) : ¬ p.1 < q.1 := by
      intro h
      have hij : p.1.succ ≤ q.1.castSucc := h
      exact (sector q).1.not_ge <| (hpq ▸ (sector p).2.le).trans (r.monotone hij)
    have hgrid := card_le_card_of_injOn (s := univ) (t := (B + B) ×ˢ (B + B)) f (by
      intro p _
      exact mem_product.mpr ⟨add_mem_add (hx _ _).1 (hx _ _).1,
        add_mem_add (hx _ _).2 (hx _ _).2⟩) (by
      rintro ⟨i, j, k⟩ _ ⟨i', j', k'⟩ _ he
      obtain rfl : i = i' := le_antisymm (le_of_not_gt (hsep _ _ he.symm))
        (le_of_not_gt (hsep _ _ he))
      obtain ⟨hs, hw⟩ := Prod.mk.inj he
      have hd := (r.strictMono i.castSucc_lt_succ).ne
      change x i.castSucc j + x i.succ k = x i.castSucc j' + x i.succ k' at hs
      change r i.castSucc * x i.castSucc j + r i.succ * x i.succ k =
        r i.castSucc * x i.castSucc j' + r i.succ * x i.succ k' at hw
      have hz : (r i.castSucc - r i.succ) * (x i.castSucc j - x i.castSucc j') = 0 := by
        linear_combination hw - r i.succ * hs
      have hj := (x i.castSucc).injective (sub_eq_zero.mp <|
        (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hd))
      subst j'
      obtain rfl := (x i.succ).injective (add_left_cancel hs)
      rfl)
    have hfirst := ht _ (D.orderEmbOfFin_mem hD (0 : Fin (m + 1)))
    have hlast : t ≤ (B + B).card :=
      (hfirst.trans (card_filter_le _ _)).trans (card_le_card_add_self)
    simp only [card_univ, Fintype.card_prod, Fintype.card_fin, card_product] at hgrid
    rw [Nat.succ_mul]
    nlinarith [Nat.pow_le_pow_left hlast 2]

/-- Sum the energy over dyadic classes of ray multiplicities. -/
private lemma energy_bound (B : Finset ℝ) (hB : ∀ x ∈ B, 0 < x) :
    B.mulEnergy B ≤ (Nat.log 2 B.card + 1) * (8 * (B + B).card ^ 2) := by
  classical
  let level (r : ℝ) := Nat.log 2 (ray B r).card
  let levels := range (Nat.log 2 B.card + 1)
  have hlevels (r : ℝ) (_ : r ∈ B / B) : level r ∈ levels :=
    mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (card_filter_le _ _)))
  apply (energy_le_sum_rays B hB).trans
  rw [← sum_fiberwise_of_maps_to hlevels]
  calc
    _ ≤ ∑ _i ∈ levels, 8 * (B + B).card ^ 2 := by
      refine sum_le_sum fun i _ => ?_
      let D := (B / B).filter fun r => level r = i
      have size (r) (hr : r ∈ D) :
          2 ^ i ≤ (ray B r).card ∧ (ray B r).card ≤ 2 * 2 ^ i := by
        obtain ⟨hr', hi⟩ := mem_filter.mp hr
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_div.mp hr'
        have hne : (ray B (a / b)).Nonempty :=
          ⟨b, mem_filter.mpr ⟨hb, by simpa [div_mul_cancel₀ _ (hB _ hb).ne'] using ha⟩⟩
        rw [← hi]
        refine ⟨Nat.pow_log_le_self _ hne.card_pos.ne', ?_⟩
        simpa [level, pow_succ, mul_comm] using
          (Nat.lt_pow_succ_log_self (b := 2) (by decide) (ray B (a / b)).card).le
      have hrich := rich_rays_bound B D hB (2 ^ i) fun r hr => (size r hr).1
      calc
        ∑ r ∈ D, (ray B r).card ^ 2 ≤ ∑ _r ∈ D, (2 * 2 ^ i) ^ 2 :=
          sum_le_sum fun r hr => Nat.pow_le_pow_left (size r hr).2 _
        _ = 4 * (D.card * (2 ^ i) ^ 2) := by simp [mul_pow]; ring
        _ ≤ _ := by omega
    _ = _ := by simp [levels]

/-- Discard zero and take the larger sign class, reflecting it when necessary. -/
private lemma exists_positive_part (A : Finset ℝ) (hA : 2 ≤ A.card) :
    ∃ B : Finset ℝ, (∀ x ∈ B, 0 < x) ∧ A.card ≤ 3 * B.card ∧ B.card ≤ A.card ∧
      (B + B).card ≤ (A + A).card ∧ (B * B).card ≤ (A * A).card := by
  classical
  let P := A.filter fun a => 0 < a
  let N := A.filter fun a => a < 0
  have hcover : A ⊆ (P ∪ N) ∪ {0} := by
    intro a ha
    rcases lt_trichotomy a 0 with h | rfl | h
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ha, h⟩))
    · simp
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ha, h⟩))
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  have hu := card_union_le P N
  rw [card_singleton] at hc
  have hP : P ⊆ A := filter_subset _ _
  have hN : N ⊆ A := filter_subset _ _
  by_cases h : N.card ≤ P.card
  · exact ⟨P, fun _ hx => (mem_filter.mp hx).2, by omega, card_le_card hP,
      card_le_card (add_subset_add hP hP), card_le_card (mul_subset_mul hP hP)⟩
  · refine ⟨-N, ?_, by rw [card_neg]; omega, by simpa using card_le_card hN, ?_, ?_⟩
    · intro x hx
      exact neg_lt_zero.mp (mem_filter.mp (mem_neg'.mp hx) : -x ∈ A ∧ -x < 0).2
    · have he : -N + -N = -(N + N) :=
        (image_add (s := N) (t := N) (negAddMonoidHom : ℝ →+ ℝ)).symm
      rw [he, card_neg]
      exact card_le_card (add_subset_add hN hN)
    · simpa using card_le_card (mul_subset_mul hN hN)

private lemma real_sum_product (A : Finset ℝ) (hA : 2 ≤ A.card) :
    Real.log 2 * (A.card : ℝ) ^ 4 ≤
      1296 * (A * A).card * (A + A).card ^ (2 : ℕ) * Real.log A.card := by
  obtain ⟨B, hB, hlarge, hsmall, hs, hp⟩ := exists_positive_part A hA
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.natLog_le_logb B.card 2
  rw [Real.logb] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hlevels : ((Nat.log 2 B.card + 1 : ℕ) : ℝ) * Real.log 2 ≤ 2 * Real.log A.card := by
    have hb : 0 < (B.card : ℝ) := by exact_mod_cast (show 0 < B.card by omega)
    have h₁ := Real.log_le_log hb (show (B.card : ℝ) ≤ A.card by exact_mod_cast hsmall)
    have ha := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ A.card by exact_mod_cast hA)
    push_cast
    linarith [(le_div_iff₀ h₂).mp hlog]
  have henergy := (le_card_mul_mul_mulEnergy B B).trans
    (Nat.mul_le_mul_left _ (energy_bound B hB))
  have hprod : (B.card : ℝ) ^ 2 * B.card ^ 2 ≤
      (A * A).card * (((Nat.log 2 B.card + 1 : ℕ) : ℝ) * (8 * (A + A).card ^ (2 : ℕ))) := by
    exact_mod_cast henergy.trans (Nat.mul_le_mul hp (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hs 2))))
  calc
    _ ≤ Real.log 2 * (3 * (B.card : ℝ)) ^ 4 := by
      gcongr
      exact_mod_cast hlarge
    _ = (81 * ((B.card : ℝ) ^ 2 * B.card ^ 2)) * Real.log 2 := by ring
    _ ≤ (81 * ((A * A).card * (((Nat.log 2 B.card + 1 : ℕ) : ℝ) *
          (8 * (A + A).card ^ (2 : ℕ))))) * Real.log 2 := by gcongr
    _ = (648 * (A * A).card * ((A + A).card : ℝ) ^ 2) *
          (((Nat.log 2 B.card + 1 : ℕ) : ℝ) * Real.log 2) := by ring
    _ ≤ (648 * (A * A).card * ((A + A).card : ℝ) ^ 2) * (2 * Real.log A.card) := by gcongr
    _ = _ := by ring

/--
**Erdős Problem 818 is true.** For every real $K > 0$ there are reals $C > 0$ and $c > 0$ such
that every finite set $A$ of integers with $|A| \ge 2$ and $|A + A| \le K|A|$ satisfies
$c|A|^2 / (\log |A|)^C \le |A \cdot A|$. Here $A + A = \{a + b : a, b \in A\}$,
$A \cdot A = \{ab : a, b \in A\}$ and $\log$ is the natural logarithm.

József Solymosi proved a stronger bound, with a single logarithm in the denominator.

Source: József Solymosi, Bounding multiplicative energy by the sumset, Advances
in Mathematics 222 (2009), 402–408, https://doi.org/10.1016/j.aim.2009.04.006. Moved from
`OpenConjectures/NumberTheory/ErdosProblem818`.
-/
theorem conjecture_holds : conjecture := by
  classical
  intro K hK
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1, zero_lt_one, Real.log 2 / (1296 * K ^ 2), by positivity, ?_⟩
  intro A hA hsum
  let f := Int.castRingHom ℝ
  have hcard (S : Finset ℤ) : (S.image f).card = S.card :=
    card_image_of_injective _ Int.cast_injective
  have hbound := real_sum_product (A.image f) (by simpa only [hcard] using hA)
  rw [← image_mul f, ← image_add f] at hbound
  simp only [hcard] at hbound
  have hn : 1 < (A.card : ℝ) := by exact_mod_cast (show 1 < A.card from hA)
  have hlog := Real.log_pos hn
  have hsum' : ((A + A).card : ℝ) ^ 2 ≤ (K * A.card) ^ 2 := by gcongr
  have hamb : Real.log 2 * (A.card : ℝ) ^ 4 ≤
      1296 * (A * A).card * (K * A.card) ^ 2 * Real.log A.card := by
    apply hbound.trans
    gcongr
  rw [Real.rpow_one, div_le_iff₀ hlog, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right (a := (A.card : ℝ) ^ 2) _ (by positivity)
  nlinarith only [hamb]

end MathlibExt.NumberTheory.ErdosProblem818Wanted
