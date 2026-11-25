/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Numbers of distinct permuted products

Every count from one through `n!` occurs among the permuted products of `n` distinct group
elements. Following van Doorn, Judin, Monticone and Morrison, we encode the ordering by a
factorial-weighted inversion count and read this count modulo the desired cardinality.
We realize the group elements as permutations of pairs `(x, z)`. Reading a product from
right to left, the counter `x j` records how many smaller letters have appeared. The letter
`j` adds `j! * x j` to `z` and increments the counters for all larger letters.

## Record carried over from the retired wanted module

From `WantedExt/GroupTheory/PermutedProductsCountKourovka18Problem50Wanted.lean`:

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.50 (S. Kohl). UnsolvedMath record
UM-00701479 (`KOU-18.50`), dataset ulamai/UnsolvedMath v1.8.0.

The product `g_{σ(1)} ⋯ g_{σ(n)}` is the product of `List.ofFn (g ∘ σ)`; groups are taken in `Type`.
The resolution is an AI-generated solution confirmed by S. Kohl, with an independent account by van
Doorn, Judin, Monticone and Morrison.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PermutedProductsCountKourovka18Problem50Wanted

/-- **Kohl's permuted-products statement (Kourovka 18.50).** The assertion that for all natural
numbers $n$ and $k$ with $1 \le k \le n!$ there are a group $G$ and pairwise distinct elements
$g_1, \dots, g_n \in G$ such that the set
$\lbrace g_{\sigma(1)} g_{\sigma(2)} \cdots g_{\sigma(n)} : \sigma \in S_n \rbrace$ of products
obtained by permuting the factors has exactly $k$ elements. -/
def permutedProductsTakeEveryCount : Prop :=
  ∀ n k : ℕ, 1 ≤ k → k ≤ n.factorial →
    ∃ (G : Type) (_ : Group G) (g : Fin n → G), Function.Injective g ∧
      (Set.range fun σ : Equiv.Perm (Fin n) => (List.ofFn fun i => g (σ i)).prod).ncard = k

/-- Factorial-weighted inversions, grouped by their larger letter. -/
private def rank : List ℕ → ℕ
  | [] => 0
  | j :: l => rank l + j.factorial * l.countP (· < j)

private theorem rank_insert_max (n : ℕ) (a b : List ℕ)
    (ha : ∀ i ∈ a, i < n) (hb : ∀ i ∈ b, i < n) :
    rank (a ++ n :: b) = rank (a ++ b) + n.factorial * b.length := by
  induction a with
  | nil =>
    have h : b.countP (· < n) = b.length := List.countP_eq_length.mpr (by simpa using hb)
    simp [rank, h]
  | cons j a ih =>
    have hj := ha j (by simp)
    simp only [List.cons_append, rank, List.countP_append, List.countP_cons,
      decide_eq_true_eq, ite_eq_right (Nat.not_lt.mpr hj.le), Nat.add_zero]
    rw [ih (fun i hi => ha i (by simp [hi]))]
    omega

/-- Insert the new maximum with exactly the quotient number of letters to its right. -/
private theorem exists_rank (n r : ℕ) (hr : r < n.factorial) :
    ∃ l : List ℕ, l.Perm (List.range n) ∧ rank l = r := by
  induction n generalizing r with
  | zero =>
    have : r = 0 := by simpa using hr
    exact ⟨[], .refl _, this.symm⟩
  | succ n ih =>
    have hq : r / n.factorial < n + 1 :=
      (Nat.div_lt_iff_lt_mul n.factorial_pos).mpr (by simpa [Nat.factorial_succ] using hr)
    obtain ⟨l, hl, hcode⟩ := ih (r % n.factorial) (Nat.mod_lt _ n.factorial_pos)
    have hlen : l.length = n := by simpa using hl.length_eq
    have hlt (i) (hi : i ∈ l) := List.mem_range.mp (hl.mem_iff.mp hi)
    let p := n - r / n.factorial
    refine ⟨l.take p ++ n :: l.drop p, ?_, ?_⟩
    · rw [List.range_succ]
      apply List.perm_middle.trans
      rw [List.take_append_drop]
      exact (hl.cons n).trans (List.perm_append_comm (l₁ := [n]))
    · rw [rank_insert_max n _ _ (fun i hi => hlt i (List.mem_of_mem_take hi))
        (fun i hi => hlt i (List.mem_of_mem_drop hi)), List.take_append_drop, hcode]
      have hdrop : (l.drop p).length = r / n.factorial := by
        rw [List.length_drop, hlen]
        exact Nat.sub_sub_self (by omega : r / n.factorial ≤ n)
      rw [hdrop, Nat.mod_add_div]

/-- Action of the letters of `l` with a prescribed central translation `r`. -/
private def action {k : ℕ} (l : List ℕ) (r : ZMod k) : Equiv.Perm ((ℕ → ℤ) × ZMod k) :=
  Equiv.prodShear (Equiv.addRight (fun j => (l.countP (· < j) : ℤ)))
    (fun x => Equiv.addRight ((l.map fun j => (j.factorial : ZMod k) * (x j : ZMod k)).sum + r))

private theorem action_apply {k : ℕ} (l : List ℕ) (r : ZMod k) (x : ℕ → ℤ) (z : ZMod k) :
    action l r (x, z) = (fun j => x j + l.countP (· < j),
      z + ((l.map fun j => (j.factorial : ZMod k) * (x j : ZMod k)).sum + r)) := rfl

private theorem action_perm {k : ℕ} {l t : List ℕ} (h : l.Perm t) (r : ZMod k) :
    action l r = action t r := by
  apply Equiv.ext
  rintro ⟨x, z⟩
  simp only [action_apply, h.countP_eq, (h.map _).sum_eq]

private theorem action_injective {k : ℕ} (l : List ℕ) : Function.Injective (action (k := k) l) := by
  intro r s h
  have := congrArg (fun e : Equiv.Perm ((ℕ → ℤ) × ZMod k) => (e (0, 0)).2) h
  simpa [action_apply] using this

private def letter (k i : ℕ) := action [i] (0 : ZMod k)

private theorem letter_injective (k : ℕ) : Function.Injective (letter k) := by
  intro i j h
  have ht (t : ℕ) := congrArg (fun e : Equiv.Perm ((ℕ → ℤ) × ZMod k) => (e (0, 0)).1 t) h
  by_contra! hne
  obtain hij | hji := Nat.lt_or_gt_of_ne hne
  · simpa [letter, action_apply, List.countP_cons, hij] using ht j
  · simpa [letter, action_apply, List.countP_cons, hji] using ht i

private theorem prod_letters (k : ℕ) (l : List ℕ) :
    (l.map (letter k)).prod = action l (rank l : ZMod k) := by
  induction l with
  | nil =>
    apply Equiv.ext
    rintro ⟨x, z⟩
    simp [rank, action_apply]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    apply Equiv.ext
    rintro ⟨x, z⟩
    simp only [Equiv.Perm.mul_apply, letter, action_apply]
    apply Prod.ext
    · funext j
      by_cases hij : i < j <;> simp [hij, add_assoc]
    · simp [rank]
      ring

private def indices {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn (Fin.val ∘ σ)

private theorem indices_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (indices σ).Perm (List.range n) := by
  have h : List.ofFn (Fin.val : Fin n → ℕ) = List.range n := by
    apply List.ext_getElem <;> simp
  exact h ▸ σ.ofFn_comp_perm Fin.val

private theorem exists_indices {n : ℕ} {l : List ℕ} (h : l.Perm (List.range n)) :
    ∃ σ : Equiv.Perm (Fin n), indices σ = l := by
  have hlen : n = l.length := by simpa using h.length_eq.symm
  let f (i : Fin n) : Fin n := ⟨l.get (i.cast hlen),
    List.mem_range.mp (h.mem_iff.mp (l.get_mem _))⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact (finCongr hlen).injective ((h.nodup_iff.mpr List.nodup_range).injective_get
      (congrArg Fin.val hij))
  refine ⟨Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩, ?_⟩
  apply List.ext_getElem
  · simpa [indices] using hlen
  · intro i hi hi'
    simp [indices, f]

/-- **Every number of distinct permuted products occurs (Kourovka 18.50).** For all natural
numbers $n$ and $k$ with $1 \le k \le n!$ there are a group $G$ and pairwise distinct elements
$g_1, \dots, g_n \in G$ such that the set
$\lbrace g_{\sigma(1)} g_{\sigma(2)} \cdots g_{\sigma(n)} : \sigma \in S_n \rbrace$ of products
obtained by permuting the factors has exactly $k$ elements.

The Kourovka Notebook (21st issue) answers 18.50 "Yes, it is true", by an AI-generated solution
confirmed by S. Kohl (P. Monticone, 2026); van Doorn, Judin, Monticone and Morrison (2026) give
an independent account.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 18.50 (S. Kohl); resolution: P. Monticone, preprint, 2026 (AI solution confirmed by S.
Kohl), https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/05/18_50.pdf; W. van Doorn,
E. Judin, P. Monticone and D. Morrison, On some problems from the Kourovka Notebook, preprint,
arXiv:2607.17477 (2026), arXiv:2607.17477 abstract: for every 1 ≤ k ≤ n! there is a group containing
n distinct elements whose n! ordered products take exactly k distinct values (found and verified in
Lean by the Aristotle agent); the Kourovka Notebook (21st issue) marks 18.50 solved,
https://arxiv.org/abs/2607.17477.
-/
theorem permutedProductsTakeEveryCount_holds : permutedProductsTakeEveryCount := by
  intro n k hk hkn
  have : NeZero k := ⟨by omega⟩
  let g (i : Fin n) := letter k i
  refine ⟨_, inferInstance, g, (letter_injective k).comp Fin.val_injective, ?_⟩
  have product_eq (σ : Equiv.Perm (Fin n)) :
      (List.ofFn fun i => g (σ i)).prod = action (List.range n) (rank (indices σ) : ZMod k) := by
    rw [← action_perm (indices_perm σ), ← prod_letters]
    simp [indices, List.map_ofFn, Function.comp_def, g]
  have hrange : (Set.range fun σ : Equiv.Perm (Fin n) => (List.ofFn fun i => g (σ i)).prod) =
      Set.range (action (k := k) (List.range n)) := by
    ext e
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨_, (product_eq σ).symm⟩
    · rintro ⟨r, rfl⟩
      obtain ⟨l, hl, hcode⟩ := exists_rank n r.val (r.val_lt.trans_le hkn)
      obtain ⟨σ, hσ⟩ := exists_indices hl
      exact ⟨σ, (product_eq σ).trans (by rw [hσ, hcode, ZMod.natCast_zmod_val])⟩
  rw [hrange, Set.ncard_range_of_injective (action_injective _), Nat.card_zmod]

end MathlibExt.GroupTheory.PermutedProductsCountKourovka18Problem50Wanted
