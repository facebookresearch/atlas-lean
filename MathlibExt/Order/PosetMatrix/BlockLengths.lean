/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.PosetMatrix
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Relabeling poset matrices with sorted block lengths

The theorem `not_relabel_equiv_of_blockLengths_ne` rules out relabeling two poset matrices
whose connected blocks have different sorted lengths.
-/

namespace MetaMathlibExt

namespace not_relabel_equiv_of_blockLengths_ne

open Finset

variable {n t : ℕ} {l : Fin (t + 1) → ℕ}

/-- Label each vertex by the unique interval of consecutive boundaries containing it. -/
private theorem exists_labels (h₀ : l 0 = 0) (hlast : l (Fin.last t) = n) (hl : StrictMono l) :
    ∃ b : Fin n → Fin t, Function.Surjective b ∧
      ∀ i k, b i = k ↔ l k.castSucc ≤ i.val ∧ i.val < l k.succ := by
  have cover (i : Fin n) : ∃ k : Fin t, l k.castSucc ≤ i.val ∧ i.val < l k.succ := by
    by_contra! h
    have hle (k : Fin (t + 1)) : l k ≤ i.val := by
      induction k using Fin.induction with
      | zero => simp [h₀]
      | succ k ih => exact h k ih
    exact i.isLt.not_ge (hlast ▸ hle (Fin.last t))
  choose b hb using cover
  have spec (i : Fin n) (k : Fin t) : b i = k ↔ l k.castSucc ≤ i.val ∧ i.val < l k.succ := by
    refine ⟨fun h => h ▸ hb i, fun ⟨hlo, hhi⟩ => ?_⟩
    obtain h | h | h := lt_trichotomy (b i) k
    · exact False.elim ((hb i).2.not_ge ((hl.monotone (Fin.succ_le_castSucc_iff.2 h)).trans hlo))
    · exact h
    · exact False.elim (hhi.not_ge ((hl.monotone (Fin.succ_le_castSucc_iff.2 h)).trans (hb i).1))
  refine ⟨b, fun k => ?_, spec⟩
  have hlt := hl k.castSucc_lt_succ
  have hend := hl.monotone (Fin.le_last k.succ)
  exact ⟨⟨l k.castSucc, hlt.trans_le (hlast ▸ hend)⟩, (spec _ _).2 ⟨le_rfl, hlt⟩⟩

/-- Every true matrix entry has its two indices in the same block. -/
private theorem label_eq_of_entry {M : Matrix (Fin n) (Fin n) Bool} (hM : IsPosetMatrix n M)
    (hl : StrictMono l) (b : Fin n → Fin t)
    (hb : ∀ i, l (b i).castSucc ≤ i.val ∧ i.val < l (b i).succ)
    (hzero : ∀ k : Fin (t + 1), ∀ i j : Fin n, i.val < l k → l k ≤ j.val → M i j = false)
    {i j : Fin n} (hij : M i j = true) : b i = b j := by
  obtain h | h | h := lt_trichotomy (b i) (b j)
  · have hlt := (hb i).2.trans_le (hl.monotone (Fin.succ_le_castSucc_iff.2 h))
    simp [hzero _ i j hlt (hb j).1] at hij
  · exact h
  · have hlt := (hb j).2.trans_le (hl.monotone (Fin.succ_le_castSucc_iff.2 h))
    simp [hM.upper i j (hlt.trans_le (hb i).1)] at hij

/-- A labeling constant across true entries is constant throughout each block.
The first vertex on each side of the split connects to every vertex on the other side. -/
private theorem factors_on_blocks {α : Type*} {M : Matrix (Fin n) (Fin n) Bool}
    (hlast : l (Fin.last t) = n) (hl : StrictMono l) (b : Fin n → Fin t)
    (hb : ∀ i, l (b i).castSucc ≤ i.val ∧ i.val < l (b i).succ)
    (hone : ∀ k : Fin t, ∃ s, 1 ≤ s ∧ l k.castSucc + s < l k.succ ∧
      ∀ i j : Fin n, l k.castSucc ≤ i.val → i.val < l k.castSucc + s →
        l k.castSucc + s ≤ j.val → j.val < l k.succ → M i j = true)
    (f : Fin n → α) (hf : ∀ i j, M i j = true → f i = f j) :
    ∃ p : Fin t → α, ∀ i, f i = p (b i) := by
  have hend (k : Fin t) : l k.succ ≤ n := hlast ▸ hl.monotone (Fin.le_last k.succ)
  let first (k : Fin t) : Fin n := ⟨l k.castSucc, (hl k.castSucc_lt_succ).trans_le (hend k)⟩
  refine ⟨fun k => f (first k), fun i => ?_⟩
  let k := b i
  obtain ⟨s, hs, hlt, hcross⟩ := hone k
  let cut : Fin n := ⟨l k.castSucc + s, hlt.trans_le (hend k)⟩
  have hfirst : (first k).val < l k.castSucc + s := Nat.lt_add_of_pos_right hs
  by_cases hi : i.val < l k.castSucc + s
  · exact (hf i cut (hcross i cut (hb i).1 hi le_rfl hlt)).trans
      (hf (first k) cut (hcross _ _ le_rfl hfirst le_rfl hlt)).symm
  · exact (hf (first k) i (hcross _ _ le_rfl hfirst (le_of_not_gt hi) (hb i).2)).symm

/-- Counting the vertices with a given label gives the corresponding boundary gap. -/
private theorem card_block (hlast : l (Fin.last t) = n) (hl : StrictMono l)
    (b : Fin n → Fin t) (hb : ∀ i k, b i = k ↔ l k.castSucc ≤ i.val ∧ i.val < l k.succ)
    (k : Fin t) : #{i | b i = k} = l k.succ - l k.castSucc := by
  have hend : l k.succ ≤ n := hlast ▸ hl.monotone (Fin.le_last k.succ)
  have heq : ({i | b i = k} : Finset (Fin n)) = (Ico (l k.castSucc) (l k.succ)).attachFin
      (fun _ hi => (mem_Ico.1 hi).2.trans_le hend) := by
    ext i
    simp [hb]
  rw [heq, card_attachFin, Nat.card_Ico]

end not_relabel_equiv_of_blockLengths_ne

open not_relabel_equiv_of_blockLengths_ne in
set_option linter.unusedVariables false in
/-- **Direct sum criterion for relabeling inequivalence.** Let $n, t \ge 2$ and let
$M$ and $M'$ be poset matrices of order $n$, Boolean matrices with rows and columns indexed by
$0, \dots, n - 1$. Let $0 = l_0 < l_1 < \dots < l_t = n$ be such that the gaps $l_{k+1} - l_k$ are
nondecreasing in $k$. Suppose that for every $k \le t$, $M_{ij}$ is false for all $i < l_k \le j$,
and that for every $k < t$ there is $s \ge 1$ with $l_k + s < l_{k+1}$ such that $M_{ij}$ is true
for all $i, j$ with $l_k \le i < l_k + s \le j < l_{k+1}$. Suppose the same of $M'$ with a sequence
$0 = l'_0 < l'_1 < \dots < l'_t = n$ whose gaps are nondecreasing. If $l_k \ne l'_k$ for some $k$,
then $M$ and $M'$ are not relabeling equivalent: there is no permutation $\sigma$ of
$\{0, \dots, n - 1\}$ with $M'_{ij} = M_{\sigma(i) \sigma(j)}$ for all $i, j$.

The source assumes in addition that $M$ and $M'$ represent quasi-full $t$-ary rooted forests; the
statement holds without that assumption.

Source: Salah Uddin Mohammad, Md. Shah Noor, and Md. Rashed Talukder, *Recognition and
Enumeration of the Quasi-Full Rooted Trees*, Journal of Integer Sequences 28 (2025),
Article 25.6.3, Theorem 11 (`jis-2025-25.6.3-thm-11`). -/
public theorem not_relabel_equiv_of_blockLengths_ne (n t : ℕ) (hn : 2 ≤ n) (ht : 2 ≤ t)
    (M M' : Matrix (Fin n) (Fin n) Bool) (hM : IsPosetMatrix n M) (hM' : IsPosetMatrix n M')
    (l l' : Fin (t + 1) → ℕ)
    (hl : l 0 = 0 ∧ l (Fin.last t) = n ∧ StrictMono l ∧
      Monotone fun k : Fin t => l k.succ - l k.castSucc)
    (hl' : l' 0 = 0 ∧ l' (Fin.last t) = n ∧ StrictMono l' ∧
      Monotone fun k : Fin t => l' k.succ - l' k.castSucc)
    (hzero : ∀ k : Fin (t + 1), ∀ i j : Fin n, (i : ℕ) < l k → l k ≤ (j : ℕ) → M i j = false)
    (hzero' : ∀ k : Fin (t + 1), ∀ i j : Fin n, (i : ℕ) < l' k → l' k ≤ (j : ℕ) →
      M' i j = false)
    (hone : ∀ k : Fin t, ∃ s, 1 ≤ s ∧ l k.castSucc + s < l k.succ ∧
      ∀ i j : Fin n, l k.castSucc ≤ (i : ℕ) → (i : ℕ) < l k.castSucc + s →
        l k.castSucc + s ≤ (j : ℕ) → (j : ℕ) < l k.succ → M i j = true)
    (hone' : ∀ k : Fin t, ∃ s, 1 ≤ s ∧ l' k.castSucc + s < l' k.succ ∧
      ∀ i j : Fin n, l' k.castSucc ≤ (i : ℕ) → (i : ℕ) < l' k.castSucc + s →
        l' k.castSucc + s ≤ (j : ℕ) → (j : ℕ) < l' k.succ → M' i j = true)
    (hne : l ≠ l') :
    ¬ ∃ σ : Equiv.Perm (Fin n), M' = M.submatrix σ σ := by
  rintro ⟨σ, hσ⟩
  obtain ⟨h₀, hlast, hmono, hsorted⟩ := hl
  obtain ⟨h₀', hlast', hmono', hsorted'⟩ := hl'
  obtain ⟨b, hsurj, hb⟩ := exists_labels h₀ hlast hmono
  obtain ⟨b', hsurj', hb'⟩ := exists_labels h₀' hlast' hmono'
  have hentry (i j : Fin n) : M' i j = M (σ i) (σ j) := congrFun (congrFun hσ i) j
  have hbounds i := (hb i _).1 rfl
  have hbounds' i := (hb' i _).1 rfl
  obtain ⟨p, hp⟩ := factors_on_blocks hlast' hmono' b' hbounds' hone' (b ∘ σ)
    (fun i j hij => label_eq_of_entry hM hmono b hbounds hzero ((hentry i j).symm.trans hij))
  obtain ⟨q, hq⟩ := factors_on_blocks hlast hmono b hbounds hone (b' ∘ σ.symm)
    (fun i j hij => label_eq_of_entry hM' hmono' b' hbounds' hzero' (by
      simpa [hentry] using hij))
  simp only [Function.comp_apply] at hp hq
  let e : Equiv.Perm (Fin t) :=
    { toFun := p
      invFun := q
      left_inv := hsurj'.forall.mpr fun i => by
        rw [← hp, ← hq, σ.symm_apply_apply]
      right_inv := hsurj.forall.mpr fun i => by
        rw [← hq, ← hp, σ.apply_symm_apply] }
  let gap (k : Fin t) := l k.succ - l k.castSucc
  let gap' (k : Fin t) := l' k.succ - l' k.castSucc
  have hgap : gap' = gap ∘ e := by
    funext k
    change l' k.succ - l' k.castSucc = l (e k).succ - l (e k).castSucc
    rw [← card_block hlast' hmono' b' hb', ← card_block hlast hmono b hb]
    apply Finset.card_equiv σ
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hp]
    exact e.injective.eq_iff.symm
  have heq : gap' = gap := hgap.trans
    (Tuple.unique_monotone (τ := Equiv.refl _) (hgap ▸ hsorted') hsorted)
  apply hne
  funext k
  induction k using Fin.induction with
  | zero => exact h₀.trans h₀'.symm
  | succ k ih =>
    have hg := congrFun heq k
    dsimp [gap, gap'] at hg
    have hlt := hmono k.castSucc_lt_succ
    have hlt' := hmono' k.castSucc_lt_succ
    omega

end MetaMathlibExt
