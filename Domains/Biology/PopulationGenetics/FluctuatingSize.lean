/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# Effective population size under fluctuating population size

A neutral Wright–Fisher population of diploids has size `N i ≥ 1` in generation `i`, so `2 N i`
gene copies. Each gene copy of generation `i + 1` is a copy of a gene copy of generation `i`
chosen uniformly at random, independently of the other copies. A genealogy over `t` generations,
the parent of every gene copy of generations `1, …, t`, is therefore a uniformly random element of
the finite set `Genealogy N t`, and probabilities are proportions of genealogies.

Two gene copies of generation `t` are identical by descent if they descend from the same gene copy
of generation `0`, or from two gene copies of generation `0` that are identical by descent, as a
given relation `R` on generation `0` records. The probability `h t = nonIdentityProb N R t` that
two distinct gene copies of generation `t`, drawn at random, are not identical by descent
satisfies `h (i + 1) = (1 - 1 / (2 N i)) h i`, hence `h t = Φ t * h 0` with
`Φ t = ∏_{i < t} (1 - 1 / (2 N i))` (`nonIdentityFactor`). The inbreeding effective size
`inbreedingEffectiveSize N t` is the constant size giving the same factor over `t ≥ 1`
generations, and it is compared with the harmonic mean `harmonicMeanSize N t` of the sizes.

## Main definitions

* `Genealogy N t`, `ancestor`: the parent assignments over `t` generations, and the gene copy of
  generation `0` from which a gene copy of generation `t` descends.
* `IdenticalByDescent N R g a b`: identity by descent under a genealogy.
* `nonIdentityProb N R t`: the probability `h t` of non-identity by descent.
* `nonIdentityFactor N t`: the factor `Φ t`.
* `inbreedingEffectiveSize N t`: the inbreeding effective size `N_e`.
* `harmonicMeanSize N t`: the harmonic mean `N_H` of `N 0, …, N (t - 1)`.

## Main results

* `effectiveSize_fluctuating`: the recursion and the product formula for `h`, the
  characterisation of `N_e`, the comparison of `Φ t` with `(1 - 1 / (2 N_H)) ^ t`, and
  `N_H ≤ (∏ N i) ^ (1 / t) ≤ (∑ N i) / t`.

## Design

The genealogy is a finite uniform probability space, so `nonIdentityProb` is a ratio of
cardinalities. It averages over the ordered pairs of distinct gene copies as well as over the
genealogies: for `t = 0` the status of a fixed pair is given by `R` and is not random. The lower
bound on the logarithms is Jensen's inequality `ConcaveOn.le_map_sum` for `Real.log`, and the
comparison of the means is Mathlib's `Real.harm_mean_le_geom_mean` and
`Real.geom_mean_le_arith_mean`.

## References

* J. Felsenstein, *Theoretical Evolutionary Genetics* (version of December 2019), Section VI.7,
  equations (VI-39)–(VI-44).
-/

@[expose] public section

open Finset Real

namespace Domains.Biology.PopulationGenetics.FluctuatingSize

variable (N : ℕ → ℕ)

/-- A Wright–Fisher genealogy over `t` generations of a diploid population whose size in
generation `i` is `N i`: for each `i < t`, the map sending each of the `2 N (i + 1)` gene copies
of generation `i + 1` to the gene copy of generation `i` of which it is a copy. A genealogy over
`t + 1` generations is a genealogy over `t` generations together with the parent map from
generation `t + 1` to generation `t`. -/
def Genealogy : ℕ → Type
  | 0 => Unit
  | t + 1 => Genealogy t × (Fin (2 * N (t + 1)) → Fin (2 * N t))

instance instFintypeGenealogy : ∀ t, Fintype (Genealogy N t)
  | 0 => inferInstanceAs (Fintype Unit)
  | t + 1 =>
    letI := instFintypeGenealogy t
    inferInstanceAs (Fintype (Genealogy N t × (Fin (2 * N (t + 1)) → Fin (2 * N t))))

/-- The gene copy of generation `0` from which the gene copy `a` of generation `t` descends under
the genealogy `g`, following the parent maps of `g` back from generation `t` to generation
`0`. -/
def ancestor : (t : ℕ) → Genealogy N t → Fin (2 * N t) → Fin (2 * N 0)
  | 0, _, a => a
  | t + 1, g, a => ancestor t g.1 (g.2 a)

/-- Gene copies `a` and `b` of generation `t` are identical by descent under the genealogy `g`
when they descend from the same gene copy of generation `0`, or from two gene copies of
generation `0` related by `R`, the identity by descent of generation `0`. -/
def IdenticalByDescent (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) {t : ℕ} (g : Genealogy N t)
    (a b : Fin (2 * N t)) : Prop :=
  ancestor N t g a = ancestor N t g b ∨ R (ancestor N t g a) (ancestor N t g b)

instance (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) [DecidableRel R] {t : ℕ}
    (g : Genealogy N t) (a b : Fin (2 * N t)) : Decidable (IdenticalByDescent N R g a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The probability `h t` that two distinct gene copies of generation `t` are not identical by
descent, in a neutral Wright–Fisher population of diploids of size `N i` in generation `i`, given
the identity by descent `R` of generation `0`. The genealogy is uniformly random, and the two
gene copies `a ≠ b` are drawn uniformly at random, independently of it: `h t` is the proportion of
triples `(g, a, b)` with `a ≠ b` for which `a` and `b` are not identical by descent under `g`. So
`h 0` is the proportion of ordered pairs of distinct gene copies of generation `0` that `R` does
not relate. This is a probability when the sizes are positive through the sampled generation,
`N i ≥ 1` for every `i ≤ t`. Otherwise there is no triple to draw, as no genealogy exists or
generation `t` has fewer than two gene copies, and `h t = 0 / 0 = 0` by the convention
`x / 0 = 0`: an empty sample is not a uniform draw. -/
noncomputable def nonIdentityProb (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) [DecidableRel R]
    (t : ℕ) : ℝ :=
  (#{x : Genealogy N t × Fin (2 * N t) × Fin (2 * N t) |
      x.2.1 ≠ x.2.2 ∧ ¬IdenticalByDescent N R x.1 x.2.1 x.2.2} : ℝ) /
    #{x : Genealogy N t × Fin (2 * N t) × Fin (2 * N t) | x.2.1 ≠ x.2.2}

/-- The factor `Φ t = ∏_{i < t} (1 - 1 / (2 N i))` by which `t` generations of a Wright–Fisher
population of sizes `N 0, …, N (t - 1)` multiply the probability of non-identity by descent
(Felsenstein, (VI-40)). It has this meaning when the sizes are positive through the sampled
generation, `N i ≥ 1` for every `i ≤ t`. Outside that case the formula still evaluates, with
the convention `x / 0 = 0`: a size `N i = 0` contributes the factor `1 - 1 / (2 * 0) = 1`. -/
noncomputable def nonIdentityFactor (t : ℕ) : ℝ :=
  ∏ i ∈ range t, (1 - 1 / (2 * (N i : ℝ)))

/-- The inbreeding effective size `N_e = 1 / (2 (1 - Φ t ^ (1 / t)))` of a Wright–Fisher
population of sizes `N 0, …, N (t - 1)` over `t ≥ 1` generations, where `Φ t` is
`nonIdentityFactor N t` (Felsenstein, (VI-42)). It is the constant size of a Wright–Fisher
population giving the same factor `Φ t` when the horizon is nonempty, `t ≥ 1`, and the parental
sizes `N 0, …, N (t - 1)` are positive. Otherwise the formula still evaluates, with the
convention `x / 0 = 0`: it is `0` for `t = 0`, and also when every parental size is `0`. -/
noncomputable def inbreedingEffectiveSize (t : ℕ) : ℝ :=
  1 / (2 * (1 - nonIdentityFactor N t ^ (1 / (t : ℝ))))

/-- The harmonic mean `N_H = t / ∑_{i < t} 1 / N i` of the sizes `N 0, …, N (t - 1)`
(Felsenstein, (VI-44)), when the horizon is nonempty, `t ≥ 1`, and these sizes are positive.
Otherwise the formula still evaluates, with the convention `x / 0 = 0`: it is `0` for `t = 0`,
and a size `N i = 0` contributes `1 / 0 = 0` to the sum, so that the sizes `1, 0` give
`2 / 1 = 2`, more than either size. -/
noncomputable def harmonicMeanSize (t : ℕ) : ℝ :=
  t / ∑ i ∈ range t, 1 / (N i : ℝ)

/-! ### Counting genealogies -/

/-- For distinct `a` and `b`, summing a function of `(f a, f b)` over all maps `f : α → β` counts
every pair of values `|β| ^ |α| / |β| ^ 2` times. -/
private lemma sum_apply_apply {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    {a b : α} (hab : a ≠ b) (F : β → β → ℝ) :
    ∑ f : α → β, F (f a) (f b) =
      (Fintype.card β : ℝ) ^ Fintype.card α / (Fintype.card β : ℝ) ^ 2 * ∑ x, ∑ y, F x y := by
  classical
  set c : ℕ := ∏ j : α, if j = a then 1 else if j = b then 1 else Fintype.card β
  have hcard : ∀ x y : β, #{f : α → β | (f a, f b) = (x, y)} = c := by
    intro x y
    have : ({f : α → β | (f a, f b) = (x, y)} : Finset (α → β)) =
        Fintype.piFinset fun j => if j = a then {x} else if j = b then {y} else univ := by
      ext f
      simp only [Prod.mk.injEq, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨rfl, rfl⟩ j
        split_ifs <;> simp_all
      · intro h
        have ha := h a
        have hb := h b
        simp only [ite_true, mem_singleton] at ha
        simp only [hab.symm, ite_false, ite_true, mem_singleton] at hb
        exact ⟨ha, hb⟩
    rw [this, Fintype.card_piFinset]
    refine prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hsum : ∀ G : β → β → ℝ, ∑ f : α → β, G (f a) (f b) = c * ∑ x, ∑ y, G x y := by
    intro G
    rw [← sum_fiberwise univ (fun f : α → β => (f a, f b)) (fun f => G (f a) (f b)),
      Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_congr rfl (g := fun _ => G x y) fun f hf => by
        simp only [Prod.mk.injEq, mem_filter] at hf
        rw [hf.2.1, hf.2.2],
      sum_const, hcard, nsmul_eq_mul]
  have hc : (Fintype.card β : ℝ) ^ Fintype.card α = c * (Fintype.card β : ℝ) ^ 2 := by
    have := hsum fun _ _ => 1
    simp only [sum_const, card_univ, Fintype.card_fun, nsmul_eq_mul, mul_one] at this
    push_cast at this
    rw [this]
    ring
  rw [hsum, hc]
  rcases eq_or_ne (Fintype.card β) 0 with h | h
  · have : IsEmpty β := Fintype.card_eq_zero_iff.mp h
    simp
  · field_simp

/-- The number of ordered pairs of distinct elements of `Fin n`. -/
private lemma card_ne_pairs (n : ℕ) :
    (#{p : Fin n × Fin n | p.1 ≠ p.2} : ℝ) = (n : ℝ) * n - n := by
  have : ({p : Fin n × Fin n | p.1 ≠ p.2} : Finset (Fin n × Fin n)) =
      (univ : Finset (Fin n)).offDiag := by
    ext p
    simp
  rw [this, offDiag_card, card_univ, Fintype.card_fin, Nat.cast_sub (Nat.le_mul_self n)]
  push_cast
  ring

/-- The denominator of `nonIdentityProb`. -/
private lemma card_ne (G : Type*) [Fintype G] (n : ℕ) :
    (#{x : G × Fin n × Fin n | x.2.1 ≠ x.2.2} : ℝ) = Fintype.card G * ((n : ℝ) * n - n) := by
  have : ({x : G × Fin n × Fin n | x.2.1 ≠ x.2.2} : Finset (G × Fin n × Fin n)) =
      (univ : Finset G) ×ˢ ({p : Fin n × Fin n | p.1 ≠ p.2} : Finset (Fin n × Fin n)) := by
    ext x
    simp
  rw [this, card_product, card_univ, Nat.cast_mul, card_ne_pairs]

/-- `∑ a, ∑ b, (if a = b then 0 else c) = (m * m - m) * c` over `Fin m`. -/
private lemma sum_sum_ite_eq_zero (m : ℕ) (c : ℝ) :
    ∑ a : Fin m, ∑ b : Fin m, (if a = b then 0 else c) = ((m : ℝ) * m - m) * c := by
  have : ∀ a b : Fin m, (if a = b then 0 else c) = c - if a = b then c else 0 := by
    intro a b
    split_ifs <;> ring
  simp only [this, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_ite_eq, mem_univ, ite_true]
  ring

variable {N}

/-- A genealogy over `t + 1` generations is a genealogy over `t` generations and the parent map
from generation `t + 1` to generation `t`. -/
private def succEquiv (t : ℕ) :
    Genealogy N (t + 1) ≃ Genealogy N t × (Fin (2 * N (t + 1)) → Fin (2 * N t)) :=
  Equiv.refl _

private lemma identicalByDescent_succEquiv (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) {t : ℕ}
    (g : Genealogy N t) (f : Fin (2 * N (t + 1)) → Fin (2 * N t)) (a b : Fin (2 * N (t + 1))) :
    IdenticalByDescent N R ((succEquiv t).symm (g, f)) a b ↔
      IdenticalByDescent N R g (f a) (f b) :=
  Iff.rfl

/-- The numerator of `nonIdentityProb`, as a sum over genealogies and pairs of gene copies. -/
private lemma card_not_ibd (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) [DecidableRel R] (t : ℕ) :
    (#{x : Genealogy N t × Fin (2 * N t) × Fin (2 * N t) |
      x.2.1 ≠ x.2.2 ∧ ¬IdenticalByDescent N R x.1 x.2.1 x.2.2} : ℝ) =
      ∑ g : Genealogy N t, ∑ a, ∑ b, if IdenticalByDescent N R g a b then 0 else 1 := by
  rw [← sum_boole, Fintype.sum_prod_type]
  refine sum_congr rfl fun g _ => ?_
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · subst hab
    simp [IdenticalByDescent]
  · by_cases h : IdenticalByDescent N R g a b <;> simp [hab, h]

/-- **One Wright–Fisher generation.** Two distinct gene copies of generation `t + 1` are copies
of the same gene copy of generation `t` with probability `1 / (2 N t)`, and otherwise copies of
two distinct gene copies of generation `t`, so `h (t + 1) = (1 - 1 / (2 N t)) h t`. -/
private lemma nonIdentityProb_succ (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) [DecidableRel R]
    (t : ℕ) (h₀ : N t ≠ 0) (h₁ : N (t + 1) ≠ 0) :
    nonIdentityProb N R (t + 1) = (1 - 1 / (2 * (N t : ℝ))) * nonIdentityProb N R t := by
  set n : ℕ := 2 * N t with hn_def
  set m : ℕ := 2 * N (t + 1) with hm_def
  have hn : (2 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ N t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h₀
    rw [hn_def]
    push_cast
    linarith
  have hm : (2 : ℝ) ≤ m := by
    have : (1 : ℝ) ≤ N (t + 1) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h₁
    rw [hm_def]
    push_cast
    linarith
  set T : Genealogy N t → ℝ := fun g => ∑ x, ∑ y, if IdenticalByDescent N R g x y then 0 else 1
  have hS : (∑ G : Genealogy N (t + 1), ∑ a, ∑ b,
      if IdenticalByDescent N R G a b then (0 : ℝ) else 1) =
      ((m : ℝ) * m - m) * ((n : ℝ) ^ m / (n : ℝ) ^ 2) * ∑ g, T g := by
    rw [← (succEquiv t).symm.sum_comp, Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun g _ => ?_
    have hstep : ∀ a b : Fin m, (∑ f : Fin m → Fin n,
        if IdenticalByDescent N R ((succEquiv t).symm (g, f)) a b then (0 : ℝ) else 1) =
        if a = b then 0 else ((n : ℝ) ^ m / (n : ℝ) ^ 2) * T g := by
      intro a b
      split_ifs with hab
      · subst hab
        refine sum_eq_zero fun f _ => ?_
        simp [IdenticalByDescent]
      · have := sum_apply_apply (β := Fin n) hab
          (fun x y => if IdenticalByDescent N R g x y then (0 : ℝ) else 1)
        simp only [Fintype.card_fin] at this
        simp only [identicalByDescent_succEquiv]
        exact this
    rw [sum_comm, sum_congr rfl fun a _ => sum_comm]
    trans ∑ a : Fin m, ∑ b : Fin m, if a = b then (0 : ℝ) else (n : ℝ) ^ m / (n : ℝ) ^ 2 * T g
    · exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => hstep a b
    rw [sum_sum_ite_eq_zero]
    ring
  have hden : ∀ s : ℕ, (#{x : Genealogy N s × Fin (2 * N s) × Fin (2 * N s) | x.2.1 ≠ x.2.2} : ℝ)
      = Fintype.card (Genealogy N s) * ((2 * N s : ℕ) * (2 * N s : ℕ) - (2 * N s : ℕ) : ℝ) :=
    fun s => card_ne _ _
  have hGsucc : (Fintype.card (Genealogy N (t + 1)) : ℝ) =
      Fintype.card (Genealogy N t) * (n : ℝ) ^ m := by
    rw [Fintype.card_congr (succEquiv t), Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  have h2N : 2 * (N t : ℝ) = n := by
    rw [hn_def]
    push_cast
    ring
  unfold nonIdentityProb
  rw [card_not_ibd, card_not_ibd, hS, hden, hden, hGsucc, h2N, ← hm_def]
  change _ = _ * ((∑ g, T g) / _)
  rw [← hn_def]
  generalize ∑ g, T g = S
  generalize (Fintype.card (Genealogy N t) : ℝ) = c
  rcases eq_or_ne c 0 with hc | hc
  · simp [hc]
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  rw [show (m : ℝ) * m - m = m * (m - 1) by ring, show (n : ℝ) * n - n = n * (n - 1) by ring]
  field_simp

/-- The product formula `h t = Φ t * h 0`. -/
private lemma nonIdentityProb_eq (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) [DecidableRel R]
    (hN : ∀ i, N i ≠ 0) (t : ℕ) :
    nonIdentityProb N R t = nonIdentityFactor N t * nonIdentityProb N R 0 := by
  induction t with
  | zero => simp [nonIdentityFactor]
  | succ t ih =>
    rw [nonIdentityProb_succ R t (hN t) (hN (t + 1)), ih, nonIdentityFactor, nonIdentityFactor,
      prod_range_succ]
    ring

/-! ### The inbreeding effective size -/

/-- `1 / (2 k)` lies in `(0, 1 / 2]` for a positive natural number `k`. -/
private lemma one_div_two_mul_mem {k : ℕ} (hk : k ≠ 0) :
    0 < 1 / (2 * (k : ℝ)) ∧ 1 / (2 * (k : ℝ)) ≤ 1 / 2 := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

private lemma nonIdentityFactor_pos (hN : ∀ i, N i ≠ 0) (t : ℕ) : 0 < nonIdentityFactor N t :=
  prod_pos fun i _ => by
    have := (one_div_two_mul_mem (hN i)).2
    linarith

private lemma nonIdentityFactor_lt_one (hN : ∀ i, N i ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    nonIdentityFactor N t < 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have h₁ : nonIdentityFactor N s ≤ 1 := prod_le_one₀
    (fun i _ => by have := (one_div_two_mul_mem (hN i)).2; linarith)
    (fun i _ => by have := (one_div_two_mul_mem (hN i)).1; linarith)
  have h₂ := one_div_two_mul_mem (hN s)
  have h₃ := nonIdentityFactor_pos hN s
  rw [nonIdentityFactor, prod_range_succ, ← nonIdentityFactor]
  nlinarith

/-- `N_e` is the unique size `M > 1 / 2` with `(1 - 1 / (2 M)) ^ t = Φ t`. -/
private lemma inbreedingEffectiveSize_spec (hN : ∀ i, N i ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    1 / 2 < inbreedingEffectiveSize N t ∧ ∀ M : ℝ, 1 / 2 < M →
      ((1 - 1 / (2 * M)) ^ t = nonIdentityFactor N t ↔ M = inbreedingEffectiveSize N t) := by
  have hΦ0 := nonIdentityFactor_pos hN t
  have hΦ1 := nonIdentityFactor_lt_one hN ht
  have ht0 : (0 : ℝ) < 1 / (t : ℝ) := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    positivity
  set r := nonIdentityFactor N t ^ (1 / (t : ℝ)) with hr
  have hr0 : 0 < r := rpow_pos_of_pos hΦ0 _
  have hr1 : r < 1 := rpow_lt_one hΦ0.le hΦ1 ht0
  have hrt : r ^ t = nonIdentityFactor N t := by
    rw [hr, one_div]
    exact rpow_inv_natCast_pow hΦ0.le (by omega)
  have hNe : inbreedingEffectiveSize N t = 1 / (2 * (1 - r)) := rfl
  refine ⟨?_, fun M hM => ?_⟩
  · rw [hNe, lt_div_iff₀ (by linarith)]
    linarith
  · have hM0 : 0 < 2 * M := by linarith
    have hq0 : 0 ≤ 1 - 1 / (2 * M) := by
      rw [sub_nonneg, div_le_one hM0]
      linarith
    rw [← hrt, pow_left_inj₀ hq0 hr0.le (by omega), hNe]
    have h1r : 1 - r ≠ 0 := by linarith
    constructor
    · intro h
      field_simp
      field_simp at h
      linarith
    · intro h
      rw [h]
      field_simp
      ring

/-! ### Comparison with the harmonic mean -/

/-- `0 ≤ -log (1 - x) - x ≤ x ^ 2` for `0 ≤ x ≤ 1 / 2`. -/
private lemma neg_log_one_sub_bounds {x : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 2) :
    x ≤ -log (1 - x) ∧ -log (1 - x) ≤ x + x ^ 2 := by
  have h₁ : 0 < 1 - x := by linarith
  refine ⟨by linarith [log_le_sub_one_of_pos h₁], ?_⟩
  have hv : 0 ≤ x + x ^ 2 := by positivity
  have hexp := quadratic_le_exp_of_nonneg hv
  have : -(x + x ^ 2) ≤ log (1 - x) := by
    rw [le_log_iff_exp_le h₁, exp_neg, inv_le_comm₀ (exp_pos _) h₁]
    refine le_trans ?_ hexp
    rw [inv_le_iff_one_le_mul₀ h₁]
    nlinarith [sq_nonneg x, mul_nonneg hx₀ (sq_nonneg x)]
  linarith

/-- The harmonic mean of sizes `N i ≥ 1` is at least `1`. -/
private lemma one_le_harmonicMeanSize (hN : ∀ i, N i ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ harmonicMeanSize N t := by
  have hNpos : ∀ i, (1 : ℝ) ≤ N i := fun i => by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hN i)
  have hsum_pos : 0 < ∑ i ∈ range t, 1 / (N i : ℝ) :=
    sum_pos (fun i _ => by have := hNpos i; positivity) (nonempty_range_iff.mpr (by omega))
  have hle : ∑ i ∈ range t, 1 / (N i : ℝ) ≤ t := by
    calc ∑ i ∈ range t, 1 / (N i : ℝ) ≤ ∑ _i ∈ range t, (1 : ℝ) :=
          sum_le_sum fun i _ => by rw [div_le_one (by linarith [hNpos i])]; exact hNpos i
      _ = t := by simp
  rw [harmonicMeanSize, le_div_iff₀ hsum_pos, one_mul]
  exact hle

/-- The harmonic-mean comparison: with `x i = 1 / (2 N i)`, whose mean is `1 / (2 N_H)`,
`0 ≤ t log (1 - 1 / (2 N_H)) - ∑ log (1 - x i) ≤ ∑ x i ^ 2`. -/
private lemma log_harmonicMeanSize_bounds (hN : ∀ i, N i ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    0 ≤ t * log (1 - 1 / (2 * harmonicMeanSize N t)) -
        ∑ i ∈ range t, log (1 - 1 / (2 * (N i : ℝ))) ∧
      t * log (1 - 1 / (2 * harmonicMeanSize N t)) -
          ∑ i ∈ range t, log (1 - 1 / (2 * (N i : ℝ))) ≤
        ∑ i ∈ range t, 1 / (4 * (N i : ℝ) ^ 2) := by
  set x : ℕ → ℝ := fun i => 1 / (2 * (N i : ℝ)) with hx
  have hx0 : ∀ i, 0 < x i := fun i => (one_div_two_mul_mem (hN i)).1
  have hx1 : ∀ i, x i ≤ 1 / 2 := fun i => (one_div_two_mul_mem (hN i)).2
  have hNpos : ∀ i, (0 : ℝ) < N i := fun i => by exact_mod_cast Nat.pos_of_ne_zero (hN i)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hsum_pos : 0 < ∑ i ∈ range t, 1 / (N i : ℝ) :=
    sum_pos (fun i _ => by have := hNpos i; positivity) (nonempty_range_iff.mpr (by omega))
  have hxsum : ∑ i ∈ range t, x i = (∑ i ∈ range t, 1 / (N i : ℝ)) / 2 := by
    rw [sum_div]
    refine sum_congr rfl fun i _ => ?_
    simp only [hx]
    field_simp
  set xbar := (∑ i ∈ range t, x i) / t with hxbar
  have hmean : 1 / (2 * harmonicMeanSize N t) = xbar := by
    rw [hxbar, hxsum, harmonicMeanSize]
    field_simp
  have hxbar1 : xbar ≤ 1 / 2 := by
    rw [hxbar, div_le_iff₀ htR]
    calc ∑ i ∈ range t, x i ≤ ∑ _i ∈ range t, (1 / 2 : ℝ) := sum_le_sum fun i _ => hx1 i
      _ = 1 / 2 * t := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hxbar0 : 0 < 1 - xbar := by linarith
  rw [hmean]
  -- Jensen for the concave function `log` at the points `1 - x i`
  have hjensen : ∑ i ∈ range t, log (1 - x i) ≤ t * log (1 - xbar) := by
    have := ConcaveOn.le_map_sum strictConcaveOn_log_Ioi.concaveOn (t := range t)
      (w := fun _ => 1 / (t : ℝ)) (p := fun i => 1 - x i) (fun _ _ => by positivity)
      (by rw [sum_const, card_range, nsmul_eq_mul]; field_simp)
      (fun i _ => by simp only [Set.mem_Ioi]; linarith [hx1 i])
    simp only [smul_eq_mul, ← mul_sum, sum_sub_distrib, sum_const, card_range,
      nsmul_eq_mul, mul_one] at this
    rw [show 1 / (t : ℝ) * (t - ∑ i ∈ range t, x i) = 1 - xbar by rw [hxbar]; field_simp] at this
    rw [← div_le_iff₀' htR, div_eq_inv_mul, ← one_div]
    exact this
  -- `log (1 - xbar) ≤ -xbar` and `-log (1 - x i) ≤ x i + x i ^ 2`
  have hupper : t * log (1 - xbar) ≤ -∑ i ∈ range t, x i := by
    have := log_le_sub_one_of_pos hxbar0
    have h : (t : ℝ) * xbar = ∑ i ∈ range t, x i := by rw [hxbar]; field_simp
    nlinarith
  have hsum : -∑ i ∈ range t, log (1 - x i) ≤ ∑ i ∈ range t, (x i + x i ^ 2) := by
    rw [← sum_neg_distrib]
    exact sum_le_sum fun i _ => (neg_log_one_sub_bounds (hx0 i).le (hx1 i)).2
  have hsq : ∑ i ∈ range t, x i ^ 2 = ∑ i ∈ range t, 1 / (4 * (N i : ℝ) ^ 2) := by
    refine sum_congr rfl fun i _ => ?_
    simp only [hx]
    field_simp
    ring
  rw [sum_add_distrib, hsq] at hsum
  exact ⟨by linarith, by linarith⟩

/-- **Effective population size under fluctuating population size** (Felsenstein, Section VI.7,
(VI-39)–(VI-44)). In a neutral Wright–Fisher population of diploids whose size in generation `i`
is `N i ≥ 1` (`2 N i` gene copies), let `h t = nonIdentityProb N R t` be the probability that two
distinct gene copies of generation `t`, drawn at random together with a random genealogy, are not
identical by descent, given the identity by descent `R` of generation `0`. Then:

* `h (i + 1) = (1 - 1 / (2 N i)) h i` for every `i`, and so `h s = Φ s * h 0` for every `s`,
  where `Φ s = ∏_{i < s} (1 - 1 / (2 N i))`; in particular `Φ s = h s / h 0` when `h 0 > 0`.

For `t ≥ 1` generations:

* the inbreeding effective size `N_e = 1 / (2 (1 - Φ t ^ (1 / t)))` is greater than `1 / 2`, and
  it is the only `M > 1 / 2` with `(1 - 1 / (2 M)) ^ t = Φ t`: the constant size of a
  Wright–Fisher population giving the same factor `Φ t`;
* with `N_H = t / ∑_{i < t} 1 / N i` the harmonic mean of the sizes and
  `E = ∑_{i < t} 1 / (4 N i ^ 2)`,
  `0 ≤ t log (1 - 1 / (2 N_H)) - ∑_{i < t} log (1 - 1 / (2 N i)) ≤ E`, so
  `Φ t / (1 - 1 / (2 N_H)) ^ t` lies in `[exp (-E), 1]`;
* `N_H ≤ (∏_{i < t} N i) ^ (1 / t) ≤ (∑_{i < t} N i) / t`: the harmonic mean of the sizes is at
  most their geometric mean, which is at most their arithmetic mean. -/
theorem effectiveSize_fluctuating (hN : ∀ i, 1 ≤ N i)
    (R : Fin (2 * N 0) → Fin (2 * N 0) → Prop) [DecidableRel R] {t : ℕ} (ht : 1 ≤ t) :
    (∀ i, nonIdentityProb N R (i + 1) = (1 - 1 / (2 * (N i : ℝ))) * nonIdentityProb N R i) ∧
    (∀ s, nonIdentityProb N R s = nonIdentityFactor N s * nonIdentityProb N R 0) ∧
    (∀ s, 0 < nonIdentityProb N R 0 →
      nonIdentityFactor N s = nonIdentityProb N R s / nonIdentityProb N R 0) ∧
    1 / 2 < inbreedingEffectiveSize N t ∧
    (∀ M : ℝ, 1 / 2 < M →
      ((1 - 1 / (2 * M)) ^ t = nonIdentityFactor N t ↔ M = inbreedingEffectiveSize N t)) ∧
    0 ≤ t * log (1 - 1 / (2 * harmonicMeanSize N t)) -
      ∑ i ∈ range t, log (1 - 1 / (2 * (N i : ℝ))) ∧
    t * log (1 - 1 / (2 * harmonicMeanSize N t)) -
        ∑ i ∈ range t, log (1 - 1 / (2 * (N i : ℝ))) ≤
      ∑ i ∈ range t, 1 / (4 * (N i : ℝ) ^ 2) ∧
    nonIdentityFactor N t / (1 - 1 / (2 * harmonicMeanSize N t)) ^ t ∈
      Set.Icc (exp (-∑ i ∈ range t, 1 / (4 * (N i : ℝ) ^ 2))) 1 ∧
    harmonicMeanSize N t ≤ (∏ i ∈ range t, (N i : ℝ)) ^ (1 / (t : ℝ)) ∧
    (∏ i ∈ range t, (N i : ℝ)) ^ (1 / (t : ℝ)) ≤ (∑ i ∈ range t, (N i : ℝ)) / t := by
  have hN' : ∀ i, N i ≠ 0 := fun i => Nat.one_le_iff_ne_zero.mp (hN i)
  have hprod := nonIdentityProb_eq R hN'
  obtain ⟨hNe, hNe'⟩ := inbreedingEffectiveSize_spec hN' ht
  obtain ⟨hlow, hupp⟩ := log_harmonicMeanSize_bounds hN' ht
  have hNpos : ∀ i, (0 : ℝ) < N i := fun i => by exact_mod_cast Nat.pos_of_ne_zero (hN' i)
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  -- the factor `Φ t / (1 - 1 / (2 N_H)) ^ t = exp (-(t log (1 - 1 / (2 N_H)) - ∑ log (1 - x i)))`
  have hfactor : nonIdentityFactor N t / (1 - 1 / (2 * harmonicMeanSize N t)) ^ t =
      exp (-(t * log (1 - 1 / (2 * harmonicMeanSize N t)) -
        ∑ i ∈ range t, log (1 - 1 / (2 * (N i : ℝ))))) := by
    have hH := one_le_harmonicMeanSize hN' ht
    have hq : 0 < 1 - 1 / (2 * harmonicMeanSize N t) := by
      rw [sub_pos, div_lt_one (by linarith)]
      linarith
    have hΦ : nonIdentityFactor N t = exp (∑ i ∈ range t, log (1 - 1 / (2 * (N i : ℝ)))) := by
      rw [exp_sum, nonIdentityFactor]
      refine prod_congr rfl fun i _ => (exp_log ?_).symm
      have := (one_div_two_mul_mem (hN' i)).2
      linarith
    rw [hΦ, ← exp_log hq, ← exp_nat_mul, ← exp_sub, exp_log hq]
    ring_nf
  have hcard : ∑ _i ∈ range t, (1 : ℝ) = t := by simp
  have hHG := harm_mean_le_geom_mean (range t) (fun _ => (1 : ℝ)) (fun i => (N i : ℝ))
    (fun _ _ => one_pos) (by rw [hcard]; exact htR) (fun i _ => hNpos i)
  have hGA := geom_mean_le_arith_mean (range t) (fun _ => (1 : ℝ)) (fun i => (N i : ℝ))
    (fun _ _ => zero_le_one) (by rw [hcard]; exact htR) (fun i _ => (hNpos i).le)
  simp only [hcard, rpow_one, one_mul] at hHG hGA
  refine ⟨fun i => nonIdentityProb_succ R i (hN' i) (hN' (i + 1)), hprod,
    fun s h0 => by rw [hprod, mul_div_cancel_right₀ _ h0.ne'], hNe, hNe', hlow, hupp, ?_, ?_, ?_⟩
  · rw [hfactor]
    exact ⟨exp_le_exp.mpr (by linarith), exp_le_one_iff.mpr (by linarith)⟩
  · rw [harmonicMeanSize, one_div (t : ℝ)]
    exact hHG
  · rw [one_div (t : ℝ)]
    exact hGA

end Domains.Biology.PopulationGenetics.FluctuatingSize
