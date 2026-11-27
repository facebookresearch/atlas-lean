/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Under a multiplicative model `λ - 1` more than halves per degree

For finitely many loci with first-degree ratios `lam₁ i ≥ 1` and second-degree ratios
halving `λ - 1`, this module proves `prod_sub_one_ge_two_mul`: the multilocus ratios satisfy
`∏ lam₁ - 1 ≥ 2 (∏ lam₂ - 1)`, strictly so when two distinct loci have `lam₁ > 1`.

## References

* N. Risch, "Linkage strategies for genetically complex traits. I. Multilocus models",
  Am. J. Hum. Genet. 46 (1990) 222–228 (abstract; the body formulas are restated from the
  definitions).
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted

open Finset

private lemma prod_half_le_prod {ι : Type*} (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (s : Finset ι) :
    ∏ i ∈ s, (1 + x i / 2) ≤ ∏ i ∈ s, (1 + x i) := by
  apply Finset.prod_le_prod₀ (fun i _ => by linarith [hx i]) (fun i _ => by linarith [hx i])

open scoped Classical in
private lemma two_mul_prod_sub_one_le {ι : Type*} (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (s : Finset ι) :
    2 * (∏ i ∈ s, (1 + x i / 2)) - 1 ≤ ∏ i ∈ s, (1 + x i) := by
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact le_of_eq (by ring)
  | insert k s hk ih =>
      have hle : ∏ i ∈ s, (1 + x i / 2) ≤ ∏ i ∈ s, (1 + x i) :=
        prod_half_le_prod x hx s
      have hnn : 0 ≤ x k * ((∏ i ∈ s, (1 + x i)) - ∏ i ∈ s, (1 + x i / 2)) :=
        mul_nonneg (hx k) (sub_nonneg.mpr hle)
      have hih : 0 ≤ (∏ i ∈ s, (1 + x i)) - 2 * (∏ i ∈ s, (1 + x i / 2)) + 1 := by
        linarith
      have hsum : 0 ≤ ((∏ i ∈ s, (1 + x i)) - 2 * (∏ i ∈ s, (1 + x i / 2)) + 1) +
          x k * ((∏ i ∈ s, (1 + x i)) - ∏ i ∈ s, (1 + x i / 2)) :=
        add_nonneg hih hnn
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      have heq : (1 + x k) * (∏ i ∈ s, (1 + x i)) -
          (2 * ((1 + x k / 2) * (∏ i ∈ s, (1 + x i / 2))) - 1) =
          ((∏ i ∈ s, (1 + x i)) - 2 * (∏ i ∈ s, (1 + x i / 2)) + 1) +
          x k * ((∏ i ∈ s, (1 + x i)) - ∏ i ∈ s, (1 + x i / 2)) := by
        ring
      linarith

private lemma diff_insert_le {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (s : Finset ι) (k : ι) (hk : k ∉ s) :
    (∏ i ∈ s, (1 + x i)) - 2 * (∏ i ∈ s, (1 + x i / 2)) + 1 ≤
      (∏ i ∈ insert k s, (1 + x i)) - 2 * (∏ i ∈ insert k s, (1 + x i / 2)) + 1 := by
  have hle : ∏ i ∈ s, (1 + x i / 2) ≤ ∏ i ∈ s, (1 + x i) :=
    prod_half_le_prod x hx s
  have hnn : 0 ≤ x k * ((∏ i ∈ s, (1 + x i)) - ∏ i ∈ s, (1 + x i / 2)) :=
    mul_nonneg (hx k) (sub_nonneg.mpr hle)
  rw [Finset.prod_insert hk, Finset.prod_insert hk]
  have heq : ((1 + x k) * (∏ i ∈ s, (1 + x i)) -
      2 * ((1 + x k / 2) * (∏ i ∈ s, (1 + x i / 2))) + 1) -
      ((∏ i ∈ s, (1 + x i)) - 2 * (∏ i ∈ s, (1 + x i / 2)) + 1) =
      x k * ((∏ i ∈ s, (1 + x i)) - ∏ i ∈ s, (1 + x i / 2)) := by
    ring
  linarith

private lemma diff_union_le {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (s0 t : Finset ι) :
    (∏ i ∈ s0, (1 + x i)) - 2 * (∏ i ∈ s0, (1 + x i / 2)) + 1 ≤
      (∏ i ∈ s0 ∪ t, (1 + x i)) - 2 * (∏ i ∈ s0 ∪ t, (1 + x i / 2)) + 1 := by
  induction t using Finset.induction_on with
  | empty =>
      rw [Finset.union_empty]
  | insert k t hk ih =>
      have hunion : s0 ∪ insert k t = insert k (s0 ∪ t) := Finset.union_insert k s0 t
      by_cases hmem : k ∈ s0 ∪ t
      · rw [hunion, Finset.insert_eq_of_mem hmem]
        exact ih
      · rw [hunion]
        exact le_trans ih (diff_insert_le x hx (s0 ∪ t) k hmem)

private lemma diff_pair {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    (∏ k ∈ ({i, j} : Finset ι), (1 + x k)) -
      2 * (∏ k ∈ ({i, j} : Finset ι), (1 + x k / 2)) + 1 = x i * x j / 2 := by
  rw [Finset.prod_pair hij, Finset.prod_pair hij]
  ring

open scoped Classical in
/-- **Under a multiplicative model `λ - 1` more than halves per degree** (Risch 1990, abstract):
if each locus has `λ_{1,i} ≥ 1` for first-degree relatives and halves `λ - 1` for second-degree
relatives, `λ_{2,i} - 1 = (λ_{1,i} - 1) / 2` (one locus, no dominance variance), then the
multilocus ratios `∏ λ_{1,i}` and `∏ λ_{2,i}` satisfy `∏ λ_{1,i} - 1 ≥ 2 (∏ λ_{2,i} - 1)`, with
strict inequality as soon as two distinct loci have `λ_{1,i} > 1`.

Source: Risch (1990), abstract. -/
public theorem prod_sub_one_ge_two_mul {ι : Type*} [Fintype ι] (lam₁ lam₂ : ι → ℝ)
    (h₁ : ∀ i, 1 ≤ lam₁ i) (hhalf : ∀ i, lam₂ i - 1 = (lam₁ i - 1) / 2) :
    2 * (∏ i, lam₂ i - 1) ≤ ∏ i, lam₁ i - 1 ∧
      ((∃ i j, i ≠ j ∧ 1 < lam₁ i ∧ 1 < lam₁ j) → 2 * (∏ i, lam₂ i - 1) < ∏ i, lam₁ i - 1) := by
  have hx : ∀ i, 0 ≤ lam₁ i - 1 := fun i => sub_nonneg.mpr (h₁ i)
  have e1 : ∏ i, lam₁ i = ∏ i ∈ Finset.univ, (1 + (lam₁ i - 1)) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have e2 : ∏ i, lam₂ i = ∏ i ∈ Finset.univ, (1 + (lam₁ i - 1) / 2) :=
    Finset.prod_congr rfl (fun i _ => by linarith [hhalf i])
  have hmain : 2 * (∏ i ∈ Finset.univ, (1 + (lam₁ i - 1) / 2)) - 1 ≤
      ∏ i ∈ Finset.univ, (1 + (lam₁ i - 1)) :=
    two_mul_prod_sub_one_le (fun i => lam₁ i - 1) hx Finset.univ
  have hle : 2 * (∏ i, lam₂ i - 1) ≤ ∏ i, lam₁ i - 1 := by
    rw [e1, e2]
    linarith [hmain]
  refine ⟨hle, fun hex => ?_⟩
  obtain ⟨i, j, hij, hli, hlj⟩ := hex
  have hxi : 0 < lam₁ i - 1 := sub_pos.mpr hli
  have hxj : 0 < lam₁ j - 1 := sub_pos.mpr hlj
  have hpair : (∏ k ∈ ({i, j} : Finset ι), (1 + (lam₁ k - 1))) -
      2 * (∏ k ∈ ({i, j} : Finset ι), (1 + (lam₁ k - 1) / 2)) + 1 =
      (lam₁ i - 1) * (lam₁ j - 1) / 2 :=
    diff_pair (fun k => lam₁ k - 1) i j hij
  have hpos : 0 < (lam₁ i - 1) * (lam₁ j - 1) / 2 :=
    div_pos (mul_pos hxi hxj) two_pos
  have hDpair : 0 < (∏ k ∈ ({i, j} : Finset ι), (1 + (lam₁ k - 1))) -
      2 * (∏ k ∈ ({i, j} : Finset ι), (1 + (lam₁ k - 1) / 2)) + 1 := by
    rw [hpair]
    exact hpos
  have hmono : (∏ k ∈ ({i, j} : Finset ι), (1 + (lam₁ k - 1))) -
      2 * (∏ k ∈ ({i, j} : Finset ι), (1 + (lam₁ k - 1) / 2)) + 1 ≤
      (∏ k ∈ Finset.univ, (1 + (lam₁ k - 1))) -
        2 * (∏ k ∈ Finset.univ, (1 + (lam₁ k - 1) / 2)) + 1 := by
    have h := diff_union_le (fun k => lam₁ k - 1) hx ({i, j} : Finset ι) Finset.univ
    rwa [Finset.union_eq_right.mpr (Finset.subset_univ _)] at h
  have hDuniv : 0 < (∏ k ∈ Finset.univ, (1 + (lam₁ k - 1))) -
      2 * (∏ k ∈ Finset.univ, (1 + (lam₁ k - 1) / 2)) + 1 :=
    lt_of_lt_of_le hDpair hmono
  rw [e1, e2]
  linarith [hDuniv]

end WantedExt.Biology.StatisticalGenetics.RischRecurrenceWanted
