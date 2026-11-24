/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

/-!
# Polynomial-size colouring lists for hereditary discrepancy

We refute the polynomial-size colouring list conjecture using matrices whose rows are
indicators of disjoint blocks of columns.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.PolysizeColoringListWanted

/-! Source record `AIM-COMBINATORICS-0047__20000922`. -/

open scoped BigOperators

/-- **Discrepancy of a matrix on a set of columns.** For a real $n \times m$ matrix $A$ and a set
$S$ of columns of $A$, the discrepancy of $A$ on $S$ is the minimum, over all sign vectors
$\varepsilon \in \{-1, 1\}^m$, of $\max_i \left|\sum_{j \in S} A_{ij} \varepsilon_j\right|$, the
largest absolute value of a row sum of $A$ restricted to $S$ and weighted by $\varepsilon$
(taken to be $0$ when $A$ has no rows). -/
noncomputable def discrepancyOn {n m : ℕ} (A : Fin n → Fin m → ℝ)
    (S : Finset (Fin m)) : ℝ :=
  sInf ((fun ε : Fin m → Bool =>
    ⨆ i : Fin n, |∑ j ∈ S, A i j * (if ε j then (1 : ℝ) else -1)|) ''
    Set.univ)

/-- **Hereditary discrepancy of a real matrix.** The hereditary discrepancy
$\operatorname{herdisc}(A)$ of a real $n \times m$ matrix $A$ is the maximum, over all sets $S$
of columns of $A$, of the discrepancy of $A$ on $S$. -/
noncomputable def hereditaryDisc {n m : ℕ} (A : Fin n → Fin m → ℝ) : ℝ :=
  ⨆ S : Finset (Fin m), discrepancyOn A S

/-- **Polynomial-size colouring list conjecture.** The statement that there exist a real number
$C > 0$ and a natural number $k$ such that for all positive integers $n$ and $m$ and every real
$n \times m$ matrix $A$ there is a set $L$ of at most $m^k$ sign vectors in $\{-1, 1\}^m$ with
the following property: for every set $S$ of columns of $A$ some $\varepsilon \in L$ satisfies
$\left|\sum_{j \in S} A_{ij} \varepsilon_j\right| \le C \operatorname{herdisc}(A)$ for every row
$i$, where $\operatorname{herdisc}(A)$ is the hereditary discrepancy of $A$.

Source: AIM-COMBINATORICS-0047__20000922; AIM Hereditary discrepancy, item 1.85. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ A : Fin n → Fin m → ℝ,
      ∃ L : Finset (Fin m → ℝ),
        (L.card : ℝ) ≤ (m : ℝ) ^ k ∧
        (∀ ε ∈ L, ∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ S : Finset (Fin m),
          ∃ ε ∈ L, ∀ i, |∑ j ∈ S, A i j * ε j| ≤
            C * hereditaryDisc A

private theorem exists_balanced_signs {α : Type*} (s : Finset α) :
    ∃ ε : α → Bool,
      (∑ j ∈ s, if ε j then (1 : ℝ) else -1) = 0 ∨
      (∑ j ∈ s, if ε j then (1 : ℝ) else -1) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => true, Or.inl (by simp)⟩
  | @insert a s ha ih =>
    obtain ⟨ε, hε⟩ := ih
    let value : Bool := decide ((∑ j ∈ s, if ε j then (1 : ℝ) else -1) = 0)
    let ε' := Function.update ε a value
    have hsum : (∑ j ∈ s, if ε' j then (1 : ℝ) else -1) =
        ∑ j ∈ s, if ε j then (1 : ℝ) else -1 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≠ a := fun h => ha (h ▸ hj)
      simp [ε', Function.update_of_ne hja]
    refine ⟨ε', ?_⟩
    rw [Finset.sum_insert ha, hsum]
    rcases hε with h | h <;> rw [h] <;> norm_num [ε', value, h]

private noncomputable def blockMatrix (r b : ℕ) (i : Fin r) (j : Fin (r * b)) : ℝ :=
  if (finProdFinEquiv.symm j).1 = i then 1 else 0

private def rowColumns {r b : ℕ} (S : Finset (Fin (r * b))) (i : Fin r) : Finset (Fin b) :=
  Finset.univ.filter fun j => finProdFinEquiv (i, j) ∈ S

private theorem sum_blockMatrix {r b : ℕ} (S : Finset (Fin (r * b)))
    (i : Fin r) (ε : Fin (r * b) → ℝ) :
    ∑ j ∈ S, blockMatrix r b i j * ε j =
      ∑ j ∈ rowColumns S i, ε (finProdFinEquiv (i, j)) := by
  simp only [blockMatrix, ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => (finProdFinEquiv.symm j).2) ?_ ?_ ?_ ?_
  · intro j hj
    obtain ⟨hj, hi⟩ := Finset.mem_filter.mp hj
    have heq : (i, (finProdFinEquiv.symm j).2) = finProdFinEquiv.symm j := Prod.ext hi.symm rfl
    simpa only [rowColumns, Finset.mem_filter, Finset.mem_univ, true_and, heq,
      Equiv.apply_symm_apply] using hj
  · intro j hj k hk h
    apply finProdFinEquiv.symm.injective
    exact Prod.ext ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm) h
  · intro j hj
    refine ⟨finProdFinEquiv (i, j), Finset.mem_filter.mpr ⟨?_, by simp⟩, by simp⟩
    simpa [rowColumns] using hj
  · intro j hj
    rw [← (Finset.mem_filter.mp hj).2, Prod.mk.eta, Equiv.apply_symm_apply]

private theorem hereditaryDisc_blockMatrix_le_one {r b : ℕ} [Nonempty (Fin r)] :
    hereditaryDisc (blockMatrix r b) ≤ 1 := by
  classical
  apply ciSup_le
  intro S
  choose ε hε using fun i : Fin r => exists_balanced_signs (rowColumns S i)
  let signs (j : Fin (r * b)) := ε (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  apply (csInf_le (Set.finite_univ.image _).bddBelow
    (Set.mem_image_of_mem _ (Set.mem_univ signs))).trans
  apply ciSup_le
  intro i
  rw [sum_blockMatrix]
  simp only [signs, Equiv.symm_apply_apply]
  rcases hε i with h | h <;> simp [h]

private theorem exists_bad_subset {b : ℕ} {C : ℝ} (hC : C < (b : ℝ) / 2)
    (ε : Fin b → ℝ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) :
    ∃ S : Finset (Fin b), C < |∑ j ∈ S, ε j| := by
  classical
  let P : Finset (Fin b) := Finset.univ.filter fun j => ε j = 1
  let N : Finset (Fin b) := Finset.univ.filter fun j => ε j ≠ 1
  have hcard : P.card + N.card = b := by
    simpa [P, N] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun j => ε j = 1)
  have hcast : (P.card : ℝ) + (N.card : ℝ) = b := by exact_mod_cast hcard
  by_cases hp : C < (P.card : ℝ)
  · refine ⟨P, ?_⟩
    have hsum : ∑ j ∈ P, ε j = (P.card : ℝ) := by
      calc
        _ = ∑ _j ∈ P, (1 : ℝ) := Finset.sum_congr rfl fun _ hj => (Finset.mem_filter.mp hj).2
        _ = _ := by simp
    rwa [hsum, abs_of_nonneg (Nat.cast_nonneg _)]
  · refine ⟨N, ?_⟩
    have hsum : ∑ j ∈ N, ε j = -(N.card : ℝ) := by
      calc
        _ = ∑ _j ∈ N, (-1 : ℝ) := Finset.sum_congr rfl fun j hj =>
          (hε j).resolve_left (Finset.mem_filter.mp hj).2
        _ = _ := by simp
    rw [hsum, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    linarith

/-- Sufficiently many blocks make the bound on the covered subsets smaller than their total. -/
private theorem exists_block_count (b k q : ℕ) (hq : 0 < q) :
    ∃ r : ℕ, 0 < r ∧ (r * b) ^ k * (q - 1) ^ r < q ^ r := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) / q := div_nonneg (Nat.cast_nonneg _) hq'.le
  have hratio' : (((q - 1 : ℕ) : ℝ) / q) < 1 := by
    apply (div_lt_one hq').mpr
    exact_mod_cast (show q - 1 < q by omega)
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one k hratio hratio').const_mul
    ((b : ℝ) ^ k)
  have hlt : ∀ᶠ r : ℕ in Filter.atTop,
      (b : ℝ) ^ k * ((r : ℝ) ^ k * (((q - 1 : ℕ) : ℝ) / q) ^ r) < 1 :=
    hlim.eventually_lt_const (by rw [mul_zero]; exact zero_lt_one)
  obtain ⟨r, hr, hr'⟩ := ((Filter.eventually_gt_atTop (0 : ℕ)).and hlt).exists
  refine ⟨r, hr, ?_⟩
  rw [div_pow, ← mul_div_assoc, ← mul_div_assoc, ← mul_assoc, ← mul_pow,
    mul_comm (b : ℝ) (r : ℝ)] at hr'
  exact_mod_cast (div_lt_one (pow_pos hq' r)).mp hr'

/--
**The polynomial-size colouring list conjecture is false.** There do not exist a real number
$C > 0$ and a natural number $k$ such that for all positive integers $n$ and $m$ and every real
$n \times m$ matrix $A$ there is a set $L$ of at most $m^k$ sign vectors in $\{-1, 1\}^m$ with
the following property: for every set $S$ of columns of $A$ some $\varepsilon \in L$ satisfies
$\left|\sum_{j \in S} A_{ij} \varepsilon_j\right| \le C \operatorname{herdisc}(A)$ for every row
$i$, where $\operatorname{herdisc}(A)$ is the hereditary discrepancy of $A$.

The AIM problem list records this negative answer: for the $0/1$ matrix with $m$ columns whose
$\sqrt{m}$ rows are the indicators of disjoint sets of $\sqrt{m}$ columns, the hereditary
discrepancy is $1$, yet for fixed $C$ and lists of polynomial size some set of columns has
discrepancy above $C$ under every listed colouring.

Source: AIM Problem Lists,
Hereditary discrepancy and factorization norms, Problem 1.85 (Polysize list of colorings),
https://aimpl.org/hereddiscrep/1/. Moved from
`OpenConjectures/Combinatorics/PolysizeColoringList`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  classical
  rintro ⟨C, hC, k, hlist⟩
  obtain ⟨b, hb⟩ := exists_nat_gt (2 * C)
  have hb' : C < (b : ℝ) / 2 := by linarith
  have hbpos : 0 < b := by exact_mod_cast (show 0 < (b : ℝ) by linarith)
  let q := Fintype.card (Finset (Fin b))
  have hq : 0 < q := Fintype.card_pos
  obtain ⟨r, hr, hbound⟩ := exists_block_count b k q hq
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨L, hL, hsign, hcover⟩ := hlist r (r * b) hr (Nat.mul_pos hr hbpos) (blockMatrix r b)
  have hL' : L.card ≤ (r * b) ^ k := by exact_mod_cast hL
  have hdisc := hereditaryDisc_blockMatrix_le_one (r := r) (b := b)
  -- For each listed colouring, discard one bad choice of subset independently in each block.
  choose bad hbad using fun (ε : L) (i : Fin r) =>
    exists_bad_subset hb' (fun j => ε.val (finProdFinEquiv (i, j)))
      (fun j => hsign _ ε.prop _)
  let covered (ε : L) : Finset (Fin r → Finset (Fin b)) :=
    Fintype.piFinset fun i => Finset.univ.erase (bad ε i)
  have hcovered (ε : L) : (covered ε).card = (q - 1) ^ r := by
    simp [covered, Fintype.card_piFinset, Finset.card_erase_of_mem, q]
  have hsub : (Finset.univ : Finset (Fin r → Finset (Fin b))) ⊆
      Finset.univ.biUnion covered := by
    intro T _
    let S : Finset (Fin (r * b)) := Finset.univ.filter fun j =>
      (finProdFinEquiv.symm j).2 ∈ T (finProdFinEquiv.symm j).1
    have hS (i : Fin r) : rowColumns S i = T i := by
      ext j
      simp only [rowColumns, S, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.symm_apply_apply]
    obtain ⟨ε, hε, hgood⟩ := hcover S
    refine Finset.mem_biUnion.mpr ⟨⟨ε, hε⟩, Finset.mem_univ _, Fintype.mem_piFinset.mpr ?_⟩
    intro i
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro heq
    have hi := hgood i
    rw [sum_blockMatrix, hS, heq] at hi
    exact (hbad ⟨ε, hε⟩ i).not_ge
      (hi.trans ((mul_le_mul_of_nonneg_left hdisc hC.le).trans_eq (mul_one C)))
  have htotal : q ^ r ≤ L.card * (q - 1) ^ r := by
    calc
      q ^ r = (Finset.univ : Finset (Fin r → Finset (Fin b))).card := by simp [q]
      _ ≤ (Finset.univ.biUnion covered).card := Finset.card_le_card hsub
      _ ≤ ∑ ε : L, (covered ε).card := Finset.card_biUnion_le
      _ = _ := by simp [hcovered]
  exact hbound.not_ge (htotal.trans (Nat.mul_le_mul_right _ hL'))

end MathlibExt.Combinatorics.PolysizeColoringListWanted
