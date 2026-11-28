/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Combinatorics.Enumerative.PatternContainment
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

private theorem exists_between {n : ℕ} (σ : Equiv.Perm (Fin n)) {i j : Fin n}
    (hij : σ i < σ j) (hgap : (σ i : ℕ) + 1 ≠ σ j) :
    ∃ k : Fin n, σ i < σ k ∧ σ k < σ j := by
  have hlt : (σ i : ℕ) + 1 < σ j := lt_of_le_of_ne hij hgap
  obtain ⟨k, hk⟩ := σ.surjective ⟨(σ i : ℕ) + 1, hlt.trans (σ j).isLt⟩
  exact ⟨k, by rw [hk]; exact Nat.lt_succ_self _, by rw [hk]; exact hlt⟩

private theorem exists_132 {n : ℕ} (hn : 2 ≤ n) (σ : Equiv.Perm (Fin n))
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    ∃ i j k : Fin n, i < j ∧ j < k ∧ σ i < σ k ∧ σ k < σ j := by
  by_contra h
  have no132 {i j k : Fin n} (hij : i < j) (hjk : j < k) (hik : σ i < σ k)
      (hkj : σ k < σ j) : False := h ⟨i, j, k, hij, hjk, hik, hkj⟩
  -- A block whose values form an interval cannot have two or more entries.
  have noBlock (d : ℕ) (a b : Fin n) (hd : (b : ℕ) - (a : ℕ) = d) (hab : a < b)
      (closed : ∀ {i j k : Fin n}, a ≤ i → i ≤ b → a ≤ j → j ≤ b →
        σ i ≤ σ k → σ k ≤ σ j → a ≤ k ∧ k ≤ b) : False := by
    induction d using Nat.strong_induction_on generalizing a b with
    | ind d ih =>
      obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.Icc a b) σ
        ⟨a, Finset.mem_Icc.mpr ⟨le_rfl, hab.le⟩⟩
      obtain ⟨ham, hmb⟩ := Finset.mem_Icc.mp hm
      have max_lt {k : Fin n} (hak : a ≤ k) (hkb : k ≤ b) (hkm : k ≠ m) :
          σ k < σ m := lt_of_le_of_ne (hmax k (Finset.mem_Icc.mpr ⟨hak, hkb⟩))
            (fun hkm' => hkm (σ.injective hkm'))
      by_cases ha : a < m
      · -- If the left block is nonempty, its values lie above the right block's.
        let p : Fin n := ⟨(m : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩
        have hpm : p < m := by
          change (p : ℕ) < (m : ℕ)
          exact Nat.sub_lt (Nat.zero_lt_of_lt ha) (by decide)
        rcases lt_or_ge a p with hap | hpa
        · refine ih _ (show (p : ℕ) - (a : ℕ) < d by
              change (a : ℕ) < (p : ℕ) at hap
              change (p : ℕ) < (m : ℕ) at hpm
              change (m : ℕ) ≤ (b : ℕ) at hmb
              omega) a p rfl hap ?_
          intro i j k hai hip haj hjp hik hkj
          obtain ⟨hak, hkb⟩ := closed hai (hip.trans (hpm.le.trans hmb)) haj
            (hjp.trans (hpm.le.trans hmb)) hik hkj
          refine ⟨hak, ?_⟩
          have hkm : k < m := by
            by_contra! hmk
            have hjm := max_lt haj (hjp.trans (hpm.le.trans hmb)) (hjp.trans_lt hpm).ne
            have hkm' : σ k < σ m := hkj.trans_lt hjm
            have hmk' : m < k := hmk.lt_of_ne (fun e => hkm'.ne (congrArg σ e.symm))
            have hik' : σ i < σ k := lt_of_le_of_ne hik (fun e =>
              (lt_of_le_of_lt hip (hpm.trans hmk')).ne (σ.injective e))
            exact no132 (hip.trans_lt hpm) hmk' hik' hkm'
          change (k : ℕ) ≤ (p : ℕ)
          exact Nat.le_sub_one_of_lt hkm
        · -- The sole entry to the left must be consecutive with the maximum.
          have hstep : (m : ℕ) = (a : ℕ) + 1 := by
            change (m : ℕ) - 1 ≤ (a : ℕ) at hpa
            change (a : ℕ) < (m : ℕ) at ha
            omega
          obtain ⟨k, hak', hkm'⟩ := exists_between σ (max_lt le_rfl hab.le ha.ne)
            (hking a m hstep).1
          obtain ⟨hak, _⟩ := closed le_rfl hab.le ham hmb hak'.le hkm'.le
          have hakpos : a < k := hak.lt_of_ne (fun e => hak'.ne (congrArg σ e))
          have hmk : m < k := by
            change (a : ℕ) < (k : ℕ) at hakpos
            have hne : (k : ℕ) ≠ (m : ℕ) := fun e => hkm'.ne (congrArg σ (Fin.ext e))
            change (m : ℕ) < (k : ℕ)
            omega
          exact no132 ha hmk hak' hkm'
      · -- The maximum is the first entry; the remaining block is still an interval.
        have hma : m = a := le_antisymm (le_of_not_gt ha) ham
        subst m
        let p : Fin n := ⟨(a : ℕ) + 1, Nat.lt_of_le_of_lt hab b.isLt⟩
        have hap : a < p := Nat.lt_succ_self _
        rcases lt_or_ge p b with hpb | hbp
        · refine ih _ (show (b : ℕ) - (p : ℕ) < d by
              change (a : ℕ) + 1 < (b : ℕ) at hpb
              change (b : ℕ) - ((a : ℕ) + 1) < d
              omega) p b rfl hpb ?_
          intro i j k hpi hib hpj hjb hik hkj
          obtain ⟨hak, hkb⟩ := closed (hap.le.trans hpi) hib (hap.le.trans hpj) hjb hik hkj
          have hka : σ k < σ a := hkj.trans_lt (max_lt (hap.le.trans hpj) hjb
            (hap.trans_le hpj).ne')
          exact ⟨Nat.succ_le_of_lt (hak.lt_of_ne (fun e => hka.ne (congrArg σ e.symm))), hkb⟩
        · have hstep : (b : ℕ) = (a : ℕ) + 1 := by
            change (b : ℕ) ≤ (a : ℕ) + 1 at hbp
            change (a : ℕ) < (b : ℕ) at hab
            omega
          obtain ⟨k, hbk', hka'⟩ := exists_between σ (max_lt hab.le le_rfl hab.ne')
            (hking a b hstep).2
          obtain ⟨hak, hkb⟩ := closed hab.le le_rfl le_rfl hab.le hbk'.le hka'.le
          have hne₁ : (a : ℕ) ≠ k := fun e => hka'.ne' (congrArg σ (Fin.ext e))
          have hne₂ : (k : ℕ) ≠ b := fun e => hbk'.ne' (congrArg σ (Fin.ext e))
          change (a : ℕ) ≤ (k : ℕ) at hak
          change (k : ℕ) ≤ (b : ℕ) at hkb
          omega
  exact noBlock _ ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl (by change 0 < n - 1; omega)
    (fun {i j k} _ _ _ _ _ _ => ⟨Nat.zero_le _, Nat.le_sub_one_of_lt k.isLt⟩)

private theorem hasPattern_pair {n : ℕ} {σ : Equiv.Perm (Fin n)} {i j : Fin n}
    (hij : i < j) (π : Fin 2 → Fin 2)
    (h₁ : σ i < σ j ↔ π 0 < π 1) (h₂ : σ j < σ i ↔ π 1 < π 0) : HasPattern σ π := by
  refine ⟨![i, j], ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | exact hij
      | exact False.elim (by revert hab; decide)
  · intro a b
    fin_cases a <;> fin_cases b <;> first
      | exact h₁
      | exact h₂
      | exact iff_of_false (lt_irrefl _) (lt_irrefl _)

private theorem hasPattern_132 {n : ℕ} {σ : Equiv.Perm (Fin n)} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (hik : σ i < σ k) (hkj : σ k < σ j) :
    HasPattern σ ![0, 2, 1] := by
  refine ⟨![i, j, k], ?_, ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | exact hij
      | exact hjk
      | exact hij.trans hjk
      | exact False.elim (by revert hab; decide)
  · intro a b
    fin_cases a <;> fin_cases b <;> simp [hik, hkj, hik.trans hkj,
      hik.not_gt, hkj.not_gt, (hik.trans hkj).not_gt]

/-- Reversing two consecutive positions makes their reversals consecutive in the opposite order. -/
public theorem rev_adjacent {n : ℕ} {i j : Fin n} (h : (j : ℕ) = i + 1) :
    (i.rev : ℕ) = (j.rev : ℕ) + 1 := by
  simp only [Fin.val_rev]
  have := j.isLt
  omega

/-- Reversing positions preserves the king condition that no adjacent entries differ by one. -/
public theorem king_reverse {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ((Fin.revPerm.trans σ) i : ℕ) + 1 ≠ (Fin.revPerm.trans σ) j ∧
      ((Fin.revPerm.trans σ) j : ℕ) + 1 ≠ (Fin.revPerm.trans σ) i :=
  fun i j h => (hking j.rev i.rev (rev_adjacent h)).symm

private theorem king_complement {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    ∀ i j : Fin n, (j : ℕ) = i + 1 →
      ((σ.trans Fin.revPerm) i : ℕ) + 1 ≠ (σ.trans Fin.revPerm) j ∧
      ((σ.trans Fin.revPerm) j : ℕ) + 1 ≠ (σ.trans Fin.revPerm) i := by
  intro i j h
  obtain ⟨h₁, h₂⟩ := hking i j h
  refine ⟨fun e => h₂ ?_, fun e => h₁ ?_⟩
  · simpa using (rev_adjacent e.symm).symm
  · simpa using (rev_adjacent e.symm).symm

private theorem hasPattern_of_reverse {n k : ℕ} {σ : Equiv.Perm (Fin n)} {π : Fin k → Fin k}
    (h : HasPattern (Fin.revPerm.trans σ) π) : HasPattern σ (π ∘ Fin.rev) := by
  obtain ⟨e, he, hπ⟩ := h
  exact ⟨fun i => (e i.rev).rev,
    fun i j hij => Fin.rev_lt_rev.mpr (he _ _ (Fin.rev_lt_rev.mpr hij)),
    fun i j => hπ i.rev j.rev⟩

private theorem hasPattern_of_complement {n k : ℕ} {σ : Equiv.Perm (Fin n)} {π : Fin k → Fin k}
    (h : HasPattern (σ.trans Fin.revPerm) π) : HasPattern σ (Fin.rev ∘ π) := by
  obtain ⟨e, he, hπ⟩ := h
  refine ⟨e, he, fun i j => ?_⟩
  exact Fin.rev_lt_rev.symm.trans ((hπ j i).trans Fin.rev_lt_rev.symm)

/-- **King permutations of length at least $2$ contain $12$, $21$, $132$, $213$, $231$ and $312$.**
For every $n \ge 2$, every permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$ in which adjacent
entries never differ by exactly $1$, that is, $|\sigma(i + 1) - \sigma(i)| \ne 1$ whenever
$i + 1 < n$, contains each of the classical patterns $12$, $21$, $132$, $213$, $231$ and $312$.

Theorem 1 also lists nine partially ordered patterns that no such permutation avoids; they are
not part of this statement.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Theorem 1 (`integers-2026-A59-thm-1`). -/
public theorem king_permutation_hasPattern_classical (n : ℕ) (hn : 2 ≤ n)
    (σ : Equiv.Perm (Fin n))
    (hking : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (σ i : ℕ) + 1 ≠ σ j ∧ (σ j : ℕ) + 1 ≠ σ i) :
    HasPattern σ ![0, 1] ∧ HasPattern σ ![1, 0] ∧ HasPattern σ ![0, 2, 1] ∧
      HasPattern σ ![1, 0, 2] ∧ HasPattern σ ![1, 2, 0] ∧ HasPattern σ ![2, 0, 1] := by
  have h132 (τ : Equiv.Perm (Fin n)) (hτ : ∀ i j : Fin n, (j : ℕ) = i + 1 →
      (τ i : ℕ) + 1 ≠ τ j ∧ (τ j : ℕ) + 1 ≠ τ i) : HasPattern τ ![0, 2, 1] := by
    obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := exists_132 hn τ hτ
    exact hasPattern_132 hij hjk hik hkj
  obtain ⟨i, j, k, hij, hjk, hik, hkj⟩ := exists_132 hn σ hking
  refine ⟨hasPattern_pair (hij.trans hjk) ![0, 1]
      (iff_of_true hik (by decide)) (iff_of_false hik.not_gt (by decide)),
    hasPattern_pair hjk ![1, 0]
      (iff_of_false hkj.not_gt (by decide)) (iff_of_true hkj (by decide)),
    hasPattern_132 hij hjk hik hkj, ?_, ?_, ?_⟩
  · have hp : (Fin.rev ∘ (![0, 2, 1] : Fin 3 → Fin 3)) ∘ Fin.rev = ![1, 0, 2] := by
      funext a; fin_cases a <;> decide
    rw [← hp]
    exact hasPattern_of_reverse
      (hasPattern_of_complement (h132 _ (king_complement (king_reverse hking))))
  · have hp : (![0, 2, 1] : Fin 3 → Fin 3) ∘ Fin.rev = ![1, 2, 0] := by
      funext a; fin_cases a <;> decide
    rw [← hp]
    exact hasPattern_of_reverse (h132 _ (king_reverse hking))
  · have hp : Fin.rev ∘ (![0, 2, 1] : Fin 3 → Fin 3) = ![2, 0, 1] := by
      funext a; fin_cases a <;> decide
    rw [← hp]
    exact hasPattern_of_complement (h132 _ (king_complement hking))

end MetaMathlibExt
