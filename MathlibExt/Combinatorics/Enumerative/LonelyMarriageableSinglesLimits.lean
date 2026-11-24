/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import MathlibExt.Combinatorics.Enumerative.LonelyMarriageableSingles

/-!
# Growth of the marriageable and lonely singles counts

Both counts tend to infinity. We exhibit a growing family in each class by isolating one point
or two adjacent points as singletons and putting the remaining points in one block.
-/

namespace MetaMathlibExt

namespace tendsto_marriageable_lonely_atTop

open NoncrossingPartition

variable {n : ℕ}

/-- Collapse the complement of the interval of singleton points into one block. -/
private def intervalSetoid (n k w : ℕ) : Setoid (Fin n) where
  r x y := x = y ∨ (x.val ∉ Set.Ico k (k + w) ∧ y.val ∉ Set.Ico k (k + w))
  iseqv := ⟨fun _ => Or.inl rfl, by grind, by grind⟩

private noncomputable def intervalPartition (n k w : ℕ) : SetPartition n := by
  classical
  exact Finpartition.ofSetoid (intervalSetoid n k w)

private theorem mem_part {k w : ℕ} {x y : Fin n} :
    x ∈ (intervalPartition n k w).part y ↔
      x = y ∨ (x.val ∉ Set.Ico k (k + w) ∧ y.val ∉ Set.Ico k (k + w)) := by
  classical
  rw [intervalPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact Setoid.comm' _

private theorem part_eq {k w : ℕ} {x y : Fin n} :
    (intervalPartition n k w).part x = (intervalPartition n k w).part y ↔
      x = y ∨ (x.val ∉ Set.Ico k (k + w) ∧ y.val ∉ Set.Ico k (k + w)) :=
  ((intervalPartition n k w).mem_part_iff_part_eq_part
    (Finset.mem_univ x) (Finset.mem_univ y)).symm.trans mem_part

private noncomputable def family (n k w : ℕ) : _root_.NoncrossingPartition n :=
  ⟨intervalPartition n k w, by
    rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
    rw [part_eq] at hac hbd
    exact hne <| part_eq.mpr <| Or.inr
      ⟨(hac.resolve_left (hab.trans hbc).ne).1, (hbd.resolve_left (hbc.trans hcd).ne).1⟩⟩

private theorem singleton_of_mem {k w : ℕ} {x : Fin n} (hx : x.val ∈ Set.Ico k (k + w)) :
    (intervalPartition n k w).part x = {x} := by
  ext y
  simp [mem_part, hx]

/-- Varying the start of the interval gives distinct partitions. Point zero is outside every
interval, so its block detects which points belong to the interval. -/
private theorem le_count {m w : ℕ} (hw : 0 < w) (hn : m + 2 ≤ n)
    (p : SetPartition n → Prop) [DecidablePred p]
    (hp : ∀ i < m, p (intervalPartition n (i + 2) w)) :
    m ≤ (Finset.univ.filter fun P : _root_.NoncrossingPartition n => p P.val).card := by
  apply Finset.le_card_of_inj_on_range (fun i => family n (i + 2) w)
  · exact fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hi⟩
  · intro i hi j hj h
    let z : Fin n := ⟨0, by omega⟩
    have same (x : Fin n) := Iff.of_eq <|
      congrArg (fun P : _root_.NoncrossingPartition n => x ∈ P.val.part z) h
    have hi' := same ⟨i + 2, by omega⟩
    have hj' := same ⟨j + 2, by omega⟩
    simp only [family, mem_part, Set.mem_Ico, z, Fin.ext_iff] at hi' hj'
    omega

private theorem lonely {k : ℕ} (hk : 2 ≤ k) (hkn : k < n) :
    ¬ IsMarriageableSingles (intervalPartition n k 1) := by
  have onlySingleton (x : Fin n) (hx : (intervalPartition n k 1).part x = {x}) : x.val = k := by
    by_contra h
    -- Outside the isolated point, the block contains both zero and one.
    have mem (v : ℕ) (hv : v < k) :
        (⟨v, by omega⟩ : Fin n) ∈ (intervalPartition n k 1).part x := by
      apply mem_part.mpr <| Or.inr ?_
      simp only [Set.mem_Ico]
      omega
    have h₀ := mem 0 (by omega)
    have h₁ := mem 1 (by omega)
    simp only [hx, Finset.mem_singleton, Fin.ext_iff] at h₀ h₁
    omega
  rintro ⟨i, j, hij, hi, hj, -⟩
  exact hij (Fin.ext ((onlySingleton i hi).trans (onlySingleton j hj).symm))

private theorem marriageable {k : ℕ} (hk : k + 1 < n) :
    IsMarriageableSingles (intervalPartition n k 2) := by
  let i : Fin n := ⟨k, by omega⟩
  let j : Fin n := ⟨k + 1, hk⟩
  have hi : (intervalPartition n k 2).part i = {i} :=
    singleton_of_mem (by simp [i, Set.mem_Ico])
  have hj : (intervalPartition n k 2).part j = {j} :=
    singleton_of_mem (by simp [j, Set.mem_Ico])
  refine ⟨i, j, by simp [i, j, Fin.ext_iff], hi, hj, ?_⟩
  rintro ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hne⟩
  simp only [mergedSameBlock, hi, hj, Finset.mem_singleton, part_eq, Set.mem_Ico,
    Fin.ext_iff, i, j] at hac hbd hne
  simp only [Fin.lt_def] at hab hbc hcd
  omega

end tendsto_marriageable_lonely_atTop

open tendsto_marriageable_lonely_atTop in
/-- **The marriageable and lonely singles counts tend to infinity.** Let $M_n$ and $L_n$ be the
numbers of noncrossing partitions of $\{0, \dots, n-1\}$ that are marriageable singles partitions
and lonely singles partitions, respectively. Then $M_n \to \infty$ and $L_n \to \infty$ as
$n \to \infty$.

Source: Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and
Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Corollary 21
(`jis-2025-25.1.1-cor-21`). -/
public theorem tendsto_marriageable_lonely_atTop :
    Filter.Tendsto marriageableSinglesCount Filter.atTop Filter.atTop ∧
      Filter.Tendsto lonelySinglesCount Filter.atTop Filter.atTop := by
  constructor <;> apply Filter.tendsto_atTop_atTop.mpr <;> intro m
    <;> refine ⟨m + 3, fun n hn => ?_⟩
  · exact le_count (w := 2) (by decide) (by omega) IsMarriageableSingles
      (fun i hi => marriageable (by omega))
  · exact le_count (w := 1) (by decide) (by omega) (fun P => ¬ IsMarriageableSingles P)
      (fun i hi => lonely (by omega) (by omega))

end MetaMathlibExt
