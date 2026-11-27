/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.End
public import Mathlib.Computability.Partrec
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Order.Lattice.Nat

import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Short bases of fixed subgroups of free group automorphisms

Kourovka Notebook Problem 14.23 has a negative answer when one bound must work in every rank.
In rank `r`, cyclically permuting the generators and then conjugating by the first generator
fixes their ordered product. Every fixed word has equal exponent sums in all generators.
A word shorter than `r` omits a generator, so if it is fixed, those sums are all zero.
Such words cannot generate the ordered product, whose exponent sums are all one.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23Wanted

/-- **Norm of an automorphism of a free group.** Let $F_n$ be the free group on the basis
$x_0, \dots, x_{n-1}$, and for $w \in F_n$ let $|w|$ be the length of the reduced word
representing $w$. The norm of an automorphism $\alpha$ of $F_n$ is
$\|\alpha\| = \max(|\alpha(x_0)|, \dots, |\alpha(x_{n-1})|)$, taken to be $0$ when $n = 0$. -/
def autNorm {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : ℕ :=
  Finset.univ.sup fun i => (α (FreeGroup.of i)).norm

/-- **Fixed subgroup of a free group automorphism.** For an automorphism $\alpha$ of the free
group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup of $\alpha$ is the subgroup
$\mathrm{Fix}(\alpha) = \{x \in F_n \mid \alpha(x) = x\}$ of $F_n$. -/
def fixedSubgroup {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : Subgroup (FreeGroup (Fin n)) :=
  (α : FreeGroup (Fin n) →* FreeGroup (Fin n)).eqLocus (MonoidHom.id _)

/-- **Fixed subgroups with a short free basis.** Let $\alpha$ be an automorphism of the free group
$F_n$ on $x_0, \dots, x_{n-1}$, let $|w|$ be the length of the reduced word representing
$w \in F_n$, and let $L$ be a natural number. The fixed subgroup $\mathrm{Fix}(\alpha)$ has a
short free basis with bound $L$ when, for some $k \ge 0$, it has a free basis
$y_1, \dots, y_k$ with $|y_i| \le L$ for every $i$. -/
def HasShortFixedBasis {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (L : ℕ) : Prop :=
  ∃ (k : ℕ) (b : FreeGroupBasis (Fin k) (fixedSubgroup α)),
    ∀ i, ((b i : fixedSubgroup α) : FreeGroup (Fin n)).norm ≤ L

/-- **Kourovka Problem 14.23, rank-dependent form.** For every $n$ there is a computable
function $f : \mathbb{N} \to \mathbb{N}$ such that for every automorphism $\alpha$ of the free
group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a finite
free basis all of whose elements have reduced word length at most $f(\|\alpha\|)$, where
$\|\alpha\|$ is the maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

This is the form of Kourovka Notebook Problem 14.23 (O. V. Bogopolski) in which $f$ may depend
on the rank $n$. -/
def fixedSubgroupBasisRecursiveBoundEachRank : Prop :=
  ∀ n : ℕ, ∃ f : ℕ → ℕ, Computable f ∧
    ∀ α : MulAut (FreeGroup (Fin n)), HasShortFixedBasis α (f (autNorm α))

/-- **Kourovka Problem 14.23, rank-uniform form.** There is a computable function
$f : \mathbb{N} \to \mathbb{N}$ such that for every $n$ and every automorphism $\alpha$ of the
free group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a
finite free basis all of whose elements have reduced word length at most $f(\|\alpha\|)$, where
$\|\alpha\|$ is the maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

This is the form of Kourovka Notebook Problem 14.23 (O. V. Bogopolski) in which one $f$ must
work for all ranks $n$. -/
def fixedSubgroupBasisRecursiveBoundUniform : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧
    ∀ (n : ℕ) (α : MulAut (FreeGroup (Fin n))), HasShortFixedBasis α (f (autNorm α))

open FreeGroup

-- Rotate the letters, then conjugate so that their ordered product is fixed.
private def twist (n : ℕ) : MulAut (FreeGroup (Fin (n + 1))) :=
  (freeGroupCongr (finRotate _)).trans (MulAut.conj (of 0))

private lemma autNorm_twist_le (n : ℕ) : autNorm (twist n) ≤ 3 := by
  apply Finset.sup_le
  intro i _
  change (of 0 * FreeGroup.map (finRotate _) (of i) * (of 0)⁻¹).norm ≤ 3
  rw [map.of]
  calc
    _ ≤ (of 0 * of (finRotate _ i)).norm + (of 0)⁻¹.norm := norm_mul_le _ _
    _ ≤ 3 := by
      have h := norm_mul_le (of (0 : Fin (n + 1))) (of (finRotate _ i))
      simp only [norm_of, norm_inv_eq] at h ⊢
      omega

private lemma rotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

private def orderedWord (n : ℕ) : FreeGroup (Fin (n + 1)) :=
  (List.ofFn of).prod

private lemma orderedWord_fixed (n : ℕ) : orderedWord n ∈ fixedSubgroup (twist n) := by
  change of 0 * FreeGroup.map (finRotate _) (List.ofFn of).prod * (of 0)⁻¹ =
    (List.ofFn (of (α := Fin (n + 1)))).prod
  rw [map_list_prod, List.map_ofFn, List.ofFn_succ' (fun _ => _), List.ofFn_succ (f := of)]
  simp [List.concat_eq_append, mul_assoc]

-- Read the exponent sum of one generator, written multiplicatively to use the free-group lift.
private def coordinate {n : ℕ} (i : Fin n) : FreeGroup (Fin n) →* Multiplicative ℤ :=
  lift fun j => if j = i then Multiplicative.ofAdd 1 else 1

private lemma coordinate_orderedWord (n : ℕ) :
    coordinate 0 (orderedWord n) = Multiplicative.ofAdd 1 := by
  simp [orderedWord, map_list_prod, coordinate, Function.comp_def]

private lemma coordinate_rotate {n : ℕ} (i : Fin (n + 1)) :
    (coordinate (finRotate _ i)).comp (twist n).toMonoidHom = coordinate i := by
  apply FreeGroup.ext_hom
  intro j
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, twist, MulEquiv.trans_apply,
    MulAut.conj_apply, _root_.map_mul, _root_.map_inv, mul_inv_cancel_comm, freeGroupCongr_apply,
    map.of, coordinate, lift_apply_of, EmbeddingLike.apply_eq_iff_eq]

private lemma coordinate_fixed {n : ℕ} {w : FreeGroup (Fin (n + 1))}
    (hw : w ∈ fixedSubgroup (twist n)) (i : Fin (n + 1)) :
    coordinate i w = coordinate 0 w := by
  change twist n w = w at hw
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have h := DFunLike.congr_fun (coordinate_rotate i.castSucc) w
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw, rotate_castSucc]
      using h.trans ih

-- A reduced word shorter than the rank omits at least one generator.
private lemma coordinate_short_fixed {n : ℕ} {w : FreeGroup (Fin (n + 1))}
    (hw : w ∈ fixedSubgroup (twist n)) (hlen : w.norm < n + 1) :
    coordinate 0 w = 1 := by
  let letters := w.toWord.map Prod.fst
  have hcard : letters.toFinset.card < n + 1 := calc
    _ ≤ letters.length := List.toFinset_card_le _
    _ = w.norm := List.length_map _
    _ < _ := hlen
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), i ∉ letters.toFinset := by
    by_contra! h
    rw [Finset.eq_univ_of_forall h, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  rw [← coordinate_fixed hw i, ← mk_toWord (x := w), coordinate, lift_mk]
  apply List.prod_eq_one
  intro x hx
  obtain ⟨⟨j, sign⟩, hj, rfl⟩ := List.mem_map.mp hx
  have hji : j ≠ i := by
    rintro rfl
    exact hi (List.mem_toFinset.mpr (List.mem_map_of_mem hj))
  cases sign <;> simp [hji]

/--
**Kourovka Problem 14.23 fails uniformly in the rank.** There is no computable function
$f : \mathbb{N} \to \mathbb{N}$ such that for every $n$ and every automorphism $\alpha$ of the
free group $F_n$ on $x_0, \dots, x_{n-1}$, the fixed subgroup $\mathrm{Fix}(\alpha)$ has a
finite free basis all of whose elements have reduced word length at most $f(\|\alpha\|)$, where
$\|\alpha\|$ is the maximum of the reduced word lengths of $\alpha(x_0), \dots, \alpha(x_{n-1})$.

Kharlampovich (Theorem 1) proves more: for every $r \ge 3$ there is an automorphism $\alpha_r$
of the free group of rank $2r - 1$ with $\|\alpha_r\| = 3$ such that every generating set of
$\mathrm{Fix}(\alpha_r)$ contains an element of length at least $r$, so no function at all,
computable or not, works for all ranks; the Kourovka Notebook (21st issue) records this answer.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 14.23 (O. V. Bogopolski); resolution: O. Kharlampovich, Two observations on Problems 14.23
and 17.32 of the Kourovka Notebook, preprint (2026), Proposition 2 (each rank); O. Kharlampovich, A
counterexample to the rank-uniform form of Kourovka Notebook Problem 14.23, preprint (2026), Theorem
1, the Kourovka Notebook (21st issue) marks 14.23 solved: true for each given rank, false if one
function must work for all ranks,
https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/08/kourovka_14_23_uniform_counterexample.pdf.
-/
theorem fixedSubgroupBasisRecursiveBoundUniform_refuted :
    ¬ fixedSubgroupBasisRecursiveBoundUniform := by
  rintro ⟨f, _, hf⟩
  let L := (Finset.range 4).sup f
  obtain ⟨k, b, hb⟩ := hf (L + 1) (twist L)
  have hbound : f (autNorm (twist L)) ≤ L :=
    Finset.le_sup (f := f) (Finset.mem_range.mpr (Nat.lt_succ_of_le (autNorm_twist_le L)))
  let χ := (coordinate (0 : Fin (L + 1))).comp (fixedSubgroup (twist L)).subtype
  have hχ : χ = 1 := b.ext_hom _ _ fun i =>
    coordinate_short_fixed (b i).property (Nat.lt_succ_of_le ((hb i).trans hbound))
  have h := DFunLike.congr_fun hχ ⟨orderedWord L, orderedWord_fixed L⟩
  change coordinate 0 (orderedWord L) = 1 at h
  rw [coordinate_orderedWord] at h
  exact one_ne_zero (α := ℤ) h

end MathlibExt.GroupTheory.FixedSubgroupBasisLengthKourovka14Problem23Wanted
