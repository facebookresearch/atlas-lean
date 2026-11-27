/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Combinatorics.Additive.SumFreeFinset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# The number of maximal sum-free subsets of `{1, …, n}` (Erdős Problem 877)

Erdős Problem 877 (Cameron and Erdős): let `f_m(n)` count the maximal sum-free subsets `A ⊆ {1, …,
n}` (no solutions to `a = b + c` in `A`, and `A` maximal with this property). Estimate `f_m(n)`; is
it true that `f_m(n) = o(2^{n/2})`?

Source: T. F. Bloom, Erdős Problems, Problem #877, https://www.erdosproblems.com/877 (status
PROVED). UnsolvedMath record UM-30007069 (`EP-877`), dataset ulamai/UnsolvedMath v1.8.0.

Sum-free is `IsSumFree` of the Green Problem 1 entry, reused here: no `x + y ∈ A` with `x, y ∈ A`
(`x = y` allowed). Maximality is within `{1, …, n}`. The open-ended 'estimate `f_m(n)`'
(Balogh, Liu, Sharifzadeh and Treglown: `f_m(n) = 2^{(1/4 + o(1)) n}`) is not formalized. Compared
with the formal-conjectures statement `ErdosProblems/877.lean` (equivalent; no code imported).

We prove the little-o bound by counting completions of partial subsets of the interval.
If more than `51n/100` elements remain, the largest is the sum of many pairs of remaining
elements. A graph records these pairs. Its edge count and maximum degree control the branches
that include or exclude a vertex. Once the remaining set is small, a Schur triple rules out one
of the membership patterns on at most three elements. When the entire available set is sum-free,
maximality determines the completion.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace MathlibExt.Combinatorics.MaximalSumFreeSetsCountErdosProblem877Wanted

open MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted (IsSumFree)

open Classical in
/-- **Number of maximal sum-free subsets of $\{1, \dots, n\}$.** For a natural number $n$,
$f_m(n)$ is the number of sets $A \subseteq \{1, \dots, n\}$ that are sum-free, meaning
$x + y \notin A$ for all $x, y \in A$ (including $x = y$), and maximal with this property:
every sum-free set $B$ with $A \subseteq B \subseteq \{1, \dots, n\}$ equals $A$. -/
noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun A =>
    IsSumFree A ∧ ∀ B ⊆ Finset.Icc 1 n, A ⊆ B → IsSumFree B → B = A).card

/-- **Erdős Problem 877 on maximal sum-free sets.** Let $f_m(n)$ be the number of maximal
sum-free subsets of $\{1, \dots, n\}$. This is the statement, asked by Cameron and Erdős, that
$f_m(n) / 2^{n/2} \to 0$ as $n \to \infty$, that is, $f_m(n) = o(2^{n/2})$. -/
def maximalSumFreeCountSmall : Prop :=
  Filter.Tendsto (fun n : ℕ => (maximalSumFreeCount n : ℝ) / 2 ^ ((n : ℝ) / 2))
    Filter.atTop (nhds 0)


section

variable (n : ℕ)

open Classical in
/-- Maximal sum-free sets extending the fixed part `T` using only remaining elements of `A`. -/
private noncomputable def family (T A : Finset ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 n).powerset.filter fun S =>
    IsSumFree S ∧ ∀ B ⊆ Icc 1 n, S ⊆ B → IsSumFree B → B = S).filter
      fun S => T ⊆ S ∧ S ⊆ T ∪ A

private lemma mem_family {T A S : Finset ℕ} :
    S ∈ family n T A ↔ S ⊆ Icc 1 n ∧ IsSumFree S ∧
      (∀ B ⊆ Icc 1 n, S ⊆ B → IsSumFree B → B = S) ∧ T ⊆ S ∧ S ⊆ T ∪ A := by
  classical
  simp [family, and_assoc]

private lemma card_family_le_sum {T A : Finset ℕ} {ι : Type*} (s : Finset ι)
    (U V : ι → Finset ℕ)
    (h : ∀ S ∈ family n T A, ∃ i ∈ s, S ∈ family n (U i) (V i)) :
    (family n T A).card ≤ ∑ i ∈ s, (family n (U i) (V i)).card := by
  classical
  exact (card_le_card (show family n T A ⊆ s.biUnion (fun i => family n (U i) (V i))
    from fun S hS => mem_biUnion.mpr (h S hS))).trans card_biUnion_le

/-- Branch over the proper subsets of the unfixed part of a Schur triple. -/
private lemma fixed_count_le (T A : Finset ℕ) (hTA : T ∪ A ⊆ Icc 1 n) :
    ((family n T A).card : ℝ) ≤ (2 : ℝ) ^ ((15 / 16 : ℝ) * A.card) := by
  classical
  by_cases hs : IsSumFree (T ∪ A)
  · have h : (family n T A).card ≤ 1 := by
      rw [← card_singleton (T ∪ A)]
      apply card_le_card
      intro S hS
      obtain ⟨_, _, hm, _, hsub⟩ := (mem_family n).1 hS
      exact mem_singleton.2 (hm _ hTA hsub hs).symm
    exact (show ((family n T A).card : ℝ) ≤ 1 by exact_mod_cast h).trans
      (Real.one_le_rpow (by norm_num) (by positivity))
  · have hw : ∃ x ∈ T ∪ A, ∃ y ∈ T ∪ A, x + y ∈ T ∪ A := by
      simpa only [IsSumFree, not_forall, not_imp, not_not, exists_prop] using hs
    obtain ⟨x, hx, y, hy, hz⟩ := hw
    let E : Finset ℕ := {x, y, x + y}
    let B := E ∩ A
    have hB : B ⊆ A := inter_subset_right
    have hE : E ⊆ T ∪ A := by
      intro z hz'
      simp only [E, mem_insert, mem_singleton] at hz'
      rcases hz' with rfl | rfl | rfl <;> assumption
    have hmiss {S : Finset ℕ} (hS : S ∈ family n T A) : ¬ B ⊆ S := by
      obtain ⟨_, hfree, _, hTS, _⟩ := (mem_family n).1 hS
      intro hBS
      have hES : E ⊆ S := by
        intro z hz'
        rcases mem_union.1 (hE hz') with ht | ha
        · exact hTS ht
        · exact hBS (mem_inter.2 ⟨hz', ha⟩)
      exact hfree x (hES (by simp [E])) y (hES (by simp [E])) (hES (by simp [E]))
    by_cases hB0 : B = ∅
    · have hempty : family n T A = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun S hS => hmiss hS (by simp [hB0])
      simp only [hempty, card_empty, Nat.cast_zero]
      positivity
    have hBp : 0 < B.card := card_pos.mpr (nonempty_iff_ne_empty.2 hB0)
    have hB3 : B.card ≤ 3 := by
      apply (card_le_card inter_subset_left).trans
      dsimp [E]
      exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
        (Nat.succ_le_succ (card_singleton _).le)))
    have hlt : (A \ B).card < A.card := by
      rw [card_sdiff_of_subset hB]
      exact Nat.sub_lt (hBp.trans_le (card_le_card hB)) hBp
    have hsum := card_family_le_sum n (B.powerset.erase B) (fun C => T ∪ C) (fun _ => A \ B)
      (T := T) (A := A) (by
        intro S hS
        obtain ⟨hi, hf, hm, hTS, hSsub⟩ := (mem_family n).1 hS
        refine ⟨S ∩ B, mem_erase.2 ⟨?_, mem_powerset.2 inter_subset_right⟩, ?_⟩
        · exact fun he => hmiss hS (he ▸ inter_subset_left)
        · apply (mem_family n).2
          refine ⟨hi, hf, hm, union_subset hTS inter_subset_left, ?_⟩
          intro z hz'
          by_cases hb : z ∈ B
          · exact mem_union_left _ (mem_union_right _ (mem_inter.2 ⟨hz', hb⟩))
          rcases mem_union.1 (hSsub hz') with ht | ha
          · exact mem_union_left _ (mem_union_left _ ht)
          · exact mem_union_right _ (mem_sdiff.2 ⟨ha, hb⟩))
    have hpow : ((B.powerset.erase B).card : ℝ) ≤ (2 : ℝ) ^ ((15 / 16 : ℝ) * B.card) := by
      rw [card_erase_of_mem (mem_powerset_self _), card_powerset]
      have hcases : B.card = 1 ∨ B.card = 2 ∨ B.card = 3 := by omega
      rcases hcases with h | h | h <;> rw [h] <;> norm_num <;>
        rw [← Real.rpow_le_rpow_iff (by positivity) (by positivity) (show (0 : ℝ) < 16 by norm_num),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] <;> norm_num [Real.rpow_natCast]
    calc
      ((family n T A).card : ℝ) ≤
          ∑ C ∈ B.powerset.erase B, ((family n (T ∪ C) (A \ B)).card : ℝ) := by
        exact_mod_cast hsum
      _ ≤ ∑ _C ∈ B.powerset.erase B, (2 : ℝ) ^ ((15 / 16 : ℝ) * (A \ B).card) := by
        refine sum_le_sum fun C hC => ?_
        have hCB := mem_powerset.1 (mem_of_mem_erase hC)
        exact fixed_count_le (T ∪ C) (A \ B)
          (by
            intro z hz'
            simp only [mem_union, mem_sdiff] at hz'
            rcases hz' with (ht | hc) | ⟨ha, _⟩
            · exact hTA (mem_union_left _ ht)
            · exact hTA (mem_union_right _ (hB (hCB hc)))
            · exact hTA (mem_union_right _ ha))
      _ ≤ (2 : ℝ) ^ ((15 / 16 : ℝ) * B.card) *
          (2 : ℝ) ^ ((15 / 16 : ℝ) * (A \ B).card) := by
        simpa only [sum_const, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right hpow (by positivity :
            0 ≤ (2 : ℝ) ^ ((15 / 16 : ℝ) * (A \ B).card))
      _ = _ := by
        rw [← Real.rpow_add (by norm_num), ← mul_add, ← Nat.cast_add,
          add_comm, card_sdiff_add_card_eq_card hB]
termination_by A.card
decreasing_by
  simpa [B] using hlt

end

private def neighbors (A M : Finset ℕ) (x : ℕ) : Finset ℕ :=
  A.filter fun y => y ≠ x ∧ x + y ∈ M

private def edges (A B M : Finset ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter fun p => p.2 ≠ p.1 ∧ p.1 + p.2 ∈ M

private lemma mem_neighbors {A M : Finset ℕ} {x y : ℕ} :
    y ∈ neighbors A M x ↔ y ∈ A ∧ y ≠ x ∧ x + y ∈ M := by
  simp [neighbors]

private lemma mem_edges {A B M : Finset ℕ} {x y : ℕ} :
    (x, y) ∈ edges A B M ↔ x ∈ A ∧ y ∈ B ∧ y ≠ x ∧ x + y ∈ M := by
  simp [edges, and_assoc]

private lemma neighbors_mono {A B M : Finset ℕ} (h : A ⊆ B) (x : ℕ) :
    neighbors A M x ⊆ neighbors B M x := by
  intro y hy
  obtain ⟨ha, hyx, hm⟩ := mem_neighbors.1 hy
  exact mem_neighbors.2 ⟨h ha, hyx, hm⟩

private lemma edges_card_le {A B M : Finset ℕ} {D : ℕ}
    (h : ∀ x ∈ A, (neighbors B M x).card ≤ D) :
    (edges A B M).card ≤ D * A.card := by
  calc
    (edges A B M).card ≤ ∑ x ∈ A, (neighbors B M x).card := by
      have hsub : edges A B M ⊆ A.biUnion (fun x => (neighbors B M x).image (Prod.mk x)) := by
        rintro ⟨x, y⟩ hp
        obtain ⟨hx, hy, hne, hm⟩ := mem_edges.1 hp
        exact mem_biUnion.2 ⟨x, hx, mem_image.2 ⟨y, mem_neighbors.2 ⟨hy, hne, hm⟩, rfl⟩⟩
      exact ((card_le_card hsub).trans card_biUnion_le).trans
        (sum_le_sum fun x _ => card_image_le)
    _ ≤ ∑ _x ∈ A, D := sum_le_sum h
    _ = D * A.card := by simp [mul_comm]

private lemma edges_card_swap (A B M : Finset ℕ) :
    (edges A B M).card = (edges B A M).card := by
  have map_swap (C F : Finset ℕ) : (edges C F M).image Prod.swap ⊆ edges F C M := by
    rintro ⟨x, y⟩ hp
    rcases mem_image.1 hp with ⟨⟨a, b⟩, hab, heq⟩
    cases heq
    obtain ⟨ha, hb, hne, hm⟩ := mem_edges.1 hab
    exact mem_edges.2 ⟨hb, ha, Ne.symm hne, Nat.add_comm a b ▸ hm⟩
  have le_swap (C F : Finset ℕ) : (edges C F M).card ≤ (edges F C M).card := by
    rw [← card_image_of_injective _ Prod.swap_injective]
    exact card_le_card (map_swap C F)
  exact (le_swap A B).antisymm (le_swap B A)

/-- Each deleted vertex accounts for at most `D` edges in each orientation. -/
private lemma edges_card_loss {A B M : Finset ℕ} {D : ℕ}
    (hD : ∀ x ∈ A, (neighbors A M x).card ≤ D) :
    (edges A A M).card ≤ (edges B B M).card + 2 * D * (A \ B).card := by
  have hsubset : edges A A M ⊆ edges B B M ∪ (edges (A \ B) A M ∪ edges A (A \ B) M) := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hne, hm⟩ := mem_edges.1 hxy
    by_cases hx' : x ∈ B
    · by_cases hy' : y ∈ B
      · exact mem_union_left _ (mem_edges.2 ⟨hx', hy', hne, hm⟩)
      · exact mem_union_right _ (mem_union_right _
          (mem_edges.2 ⟨hx, mem_sdiff.2 ⟨hy, hy'⟩, hne, hm⟩))
    · exact mem_union_right _ (mem_union_left _
        (mem_edges.2 ⟨mem_sdiff.2 ⟨hx, hx'⟩, hy, hne, hm⟩))
  have hbound := edges_card_le (A := A \ B) (B := A) (M := M) (D := D)
    fun x hx => hD x (mem_sdiff.1 hx).1
  have hcard := (card_le_card hsubset).trans (card_union_le _ _)
  have hu : (edges (A \ B) A M ∪ edges A (A \ B) M).card ≤ 2 * (D * (A \ B).card) := by
    apply (card_union_le _ _).trans
    rw [edges_card_swap A (A \ B), two_mul]
    exact Nat.add_le_add hbound hbound
  calc
    (edges A A M).card ≤ (edges B B M).card + 2 * (D * (A \ B).card) :=
      hcard.trans (Nat.add_le_add_left hu _)
    _ = _ := by rw [mul_assoc]

private lemma neighbors_card_insert_le (A M : Finset ℕ) (m x : ℕ) :
    (neighbors A (insert m M) x).card ≤ (neighbors A M x).card + 1 := by
  have hsub : neighbors A (insert m M) x ⊆ insert (m - x) (neighbors A M x) := by
    intro y hy
    obtain ⟨ha, hne, hm⟩ := mem_neighbors.1 hy
    rcases mem_insert.1 hm with he | hm
    · exact mem_insert.2 (Or.inl (by omega))
    · exact mem_insert.2 (Or.inr (mem_neighbors.2 ⟨ha, hne, hm⟩))
  exact (card_le_card hsub).trans (card_insert_le _ _)

/-- Intersecting `B` with its reflection about `m / 2` supplies the new edges. -/
private lemma edges_card_gain {B M : Finset ℕ} {m : ℕ}
    (hm : m ∉ M) (hm_pos : 1 ≤ m) (hB : B ⊆ Icc 1 (m - 1)) :
    2 * B.card + (edges B B M).card ≤ (edges B B (insert m M)).card + m := by
  let f : ℕ → ℕ := fun x => m - x
  let R := B.image f
  have hfB : Set.MapsTo f B (Icc 1 (m - 1) : Finset ℕ) := by
    intro x hx
    have hb := mem_Icc.1 (hB hx)
    exact mem_Icc.2 ⟨by dsimp [f]; omega, by dsimp [f]; omega⟩
  have hf_inj : Set.InjOn f (B : Set ℕ) := by
    intro a ha b hb he
    have h1 := (mem_Icc.1 (hB ha)).2
    have h2 := (mem_Icc.1 (hB hb)).2
    dsimp [f] at he
    omega
  have hRcard : R.card = B.card := card_image_of_injOn hf_inj
  have hUcard : (B ∪ R).card ≤ m - 1 := by
    have hU : B ∪ R ⊆ Icc 1 (m - 1) := union_subset hB (image_subset_iff.mpr hfB)
    simpa [Nat.card_Icc] using card_le_card hU
  have hsize := card_union_add_card_inter B R
  let F := (B ∩ R).erase (m / 2)
  have hF : (B ∩ R).card ≤ F.card + 1 := by
    have h : B ∩ R ⊆ insert (m / 2) F := by
      intro x hx
      by_cases he : x = m / 2
      · exact mem_insert.2 (Or.inl he)
      · exact mem_insert.2 (Or.inr (mem_erase.2 ⟨he, hx⟩))
    exact (card_le_card h).trans (card_insert_le _ _)
  let g : ℕ → ℕ × ℕ := fun x => (x, f x)
  have hg_inj : Function.Injective g := fun _ _ h => congrArg Prod.fst h
  have hg_edges : F.image g ⊆ edges B B (insert m M) := by
    intro p hp
    rcases mem_image.1 hp with ⟨x, hx, rfl⟩
    obtain ⟨hne, hx'⟩ := mem_erase.1 hx
    obtain ⟨hxB, hxR⟩ := mem_inter.1 hx'
    rcases mem_image.1 hxR with ⟨y, hy, hxy⟩
    have hb := (mem_Icc.1 (hB hy)).2
    have ha := (mem_Icc.1 (hB hxB)).2
    have hfx : f x = y := by dsimp [f] at *; omega
    apply mem_edges.2
    refine ⟨hxB, hfx ▸ hy, ?_, mem_insert.2 (Or.inl ?_)⟩
    · dsimp [f]
      omega
    · dsimp [f]
      omega
  have hM_edges : edges B B M ⊆ edges B B (insert m M) := by
    rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy, hne, hxy⟩ := mem_edges.1 hp
    exact mem_edges.2 ⟨hx, hy, hne, mem_insert_of_mem hxy⟩
  have hdis : Disjoint (edges B B M) (F.image g) := by
    apply disjoint_left.2
    intro p hp hp'
    rcases mem_image.1 hp' with ⟨a, ha, rfl⟩
    have haB : a ∈ B := (mem_inter.1 (mem_erase.1 ha).2).1
    have hau := (mem_Icc.1 (hB haB)).2
    have he : a + f a = m := by dsimp [f]; omega
    exact hm (he ▸ (mem_edges.1 hp).2.2.2)
  have hbig := card_le_card (union_subset hM_edges hg_edges)
  rw [card_union_of_disjoint hdis, card_image_of_injective _ hg_inj] at hbig
  rw [hRcard] at hsize
  omega


private lemma family_split (n : ℕ) {T A U : Finset ℕ} {x : ℕ}
    (h : ∀ S ∈ family n T A, x ∈ S → ∀ y ∈ U, y ∈ S → y = x) :
    (family n T A).card ≤
      (family n T (A.erase x)).card + (family n (insert x T) (A \ U)).card := by
  classical
  apply (card_le_card (t := family n T (A.erase x) ∪ family n (insert x T) (A \ U)) ?_).trans
    (card_union_le _ _)
  intro S hS
  obtain ⟨hi, hf, hm, hTS, hSA⟩ := (mem_family n).1 hS
  by_cases hxS : x ∈ S
  · apply mem_union_right _ ((mem_family n).2 ⟨hi, hf, hm, insert_subset hxS hTS, ?_⟩)
    intro y hy
    by_cases hyU : y ∈ U
    · exact mem_union_left _ (mem_insert.2 (Or.inl (h S hS hxS y hyU hy)))
    rcases mem_union.1 (hSA hy) with ht | ha
    · exact mem_union_left _ (mem_insert_of_mem ht)
    · exact mem_union_right _ (mem_sdiff.2 ⟨ha, hyU⟩)
  · apply mem_union_left _ ((mem_family n).2 ⟨hi, hf, hm, hTS, ?_⟩)
    intro y hy
    rcases mem_union.1 (hSA hy) with ht | ha
    · exact mem_union_left _ ht
    · exact mem_union_right _ (mem_erase.2 ⟨fun e => hxS (e ▸ hy), ha⟩)

private def degreeLimit : ℕ := 4096

/-- The normalized potential pays for both vertex deletion and the addition of new edges. -/
private noncomputable def potential (A M : Finset ℕ) : ℝ :=
  (3 * degreeLimit * (A.card : ℝ) - (edges A A M).card) / (300 * degreeLimit)

private lemma potential_nonneg {A M : Finset ℕ}
    (hD : ∀ x ∈ A, (neighbors A M x).card ≤ degreeLimit) :
    0 ≤ potential A M := by
  have h : ((edges A A M).card : ℝ) ≤ (degreeLimit : ℝ) * A.card := by
    exact_mod_cast edges_card_le hD
  have hA : (0 : ℝ) ≤ A.card := by positivity
  norm_num [potential, degreeLimit] at h ⊢
  linarith

private lemma potential_delete {A B M : Finset ℕ} (hBA : B ⊆ A)
    (hD : ∀ x ∈ A, (neighbors A M x).card ≤ degreeLimit) :
    potential B M + ((A \ B).card : ℝ) / 300 ≤ potential A M := by
  have h : ((edges A A M).card : ℝ) ≤ (edges B B M).card + 2 * degreeLimit * (A \ B).card := by
    exact_mod_cast edges_card_loss (B := B) hD
  have hcard : ((A \ B).card : ℝ) + B.card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hBA
  norm_num [potential, degreeLimit] at *
  linarith

private lemma branch_weights : (2 : ℝ) ^ (-(1 / 300) : ℝ) + 2 ^ (-10 : ℝ) ≤ 1 := by
  have hBern := one_add_mul_le_pow (a := -(1 / 1024 : ℝ)) (by norm_num) 512
  have hroot : (2 : ℝ) ^ (-(1 / 512) : ℝ) ≤ 1 - 1 / 1024 := by
    rw [← Real.rpow_le_rpow_iff (by positivity) (by norm_num) (show (0 : ℝ) < 512 by norm_num),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [show (-(1 / 512) : ℝ) * 512 = -1 by norm_num, Real.rpow_neg,
      Real.rpow_natCast] at *
    simpa using hBern
  have h := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (show (-(1 / 300) : ℝ) ≤ -(1 / 512) by norm_num)).trans hroot
  norm_num [Real.rpow_neg, Real.rpow_natCast] at *
  linarith

private lemma branch_bound {u v w K a b c : ℝ} (hK : 0 ≤ K)
    (hc : u ≤ v + w) (hno : v ≤ K * (2 : ℝ) ^ a) (hyes : w ≤ K * (2 : ℝ) ^ b)
    (ha : a + 1 / 300 ≤ c) (hb : b + 10 ≤ c) : u ≤ K * (2 : ℝ) ^ c := by
  have hmono (d r : ℝ) (h : d + r ≤ c) : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ c * 2 ^ (-r) := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    u ≤ K * (2 : ℝ) ^ a + K * (2 : ℝ) ^ b := hc.trans (add_le_add hno hyes)
    _ ≤ K * ((2 : ℝ) ^ c * 2 ^ (-(1 / 300 : ℝ))) +
        K * ((2 : ℝ) ^ c * 2 ^ (-10 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmono _ _ ha) hK)
        (mul_le_mul_of_nonneg_left (hmono _ _ hb) hK)
    _ = (K * (2 : ℝ) ^ c) * (2 ^ (-(1 / 300 : ℝ)) + 2 ^ (-10 : ℝ)) := by ring
    _ ≤ K * (2 : ℝ) ^ c := mul_le_of_le_one_right (by positivity) branch_weights

private noncomputable def leafBound (n : ℕ) : ℝ := (2 : ℝ) ^ ((153 / 320 : ℝ) * n)

private lemma leafBound_nonneg (n : ℕ) : 0 ≤ leafBound n := by
  unfold leafBound
  positivity

/-- Branch on a high-degree vertex, or add the pairs summing to the current maximum. -/
private lemma family_count_le (n : ℕ) (hn : 1000000000 ≤ n) (T A M : Finset ℕ)
    (hTA : T ∪ A ⊆ Icc 1 n) (hMT : M ⊆ T) (hMA : Disjoint M A)
    (hD : ∀ x ∈ A, (neighbors A M x).card ≤ degreeLimit) :
    ((family n T A).card : ℝ) ≤ leafBound n * (2 : ℝ) ^ potential A M := by
  classical
  by_cases hsmall : (A.card : ℝ) ≤ (51 / 100 : ℝ) * n
  · calc
      ((family n T A).card : ℝ) ≤ (2 : ℝ) ^ ((15 / 16 : ℝ) * A.card) :=
        fixed_count_le n T A hTA
      _ ≤ leafBound n := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ _ := le_mul_of_one_le_right (leafBound_nonneg n) (Real.one_le_rpow (by norm_num)
        (potential_nonneg hD))
  have hA : A.Nonempty := by
    by_contra! he
    have hz : A.card = 0 := card_eq_zero.2 he
    rw [hz, Nat.cast_zero] at hsmall
    exact hsmall (by positivity)
  have hAin : A ⊆ Icc 1 n := fun _ hx => hTA (mem_union_right _ hx)
  have hExcept (x : ℕ) (hx : x ∈ A) :
      ((family n T (A.erase x)).card : ℝ) ≤ leafBound n * 2 ^ potential (A.erase x) M ∧
      potential (A.erase x) M + 1 / 300 ≤ potential A M := by
    have hsub := erase_subset x A
    have hcard : (A \ A.erase x).card = 1 := by
      have hc := card_sdiff_add_card_eq_card hsub
      have he := card_erase_add_one hx
      omega
    refine ⟨family_count_le n hn T (A.erase x) M (Subset.trans (union_subset_union_right hsub) hTA)
      hMT (hMA.mono_right hsub) (fun y hy => ?_), ?_⟩
    · exact (card_le_card (neighbors_mono hsub y)).trans (hD y (hsub hy))
    · simpa [hcard] using potential_delete hsub hD
  have hIncluded (x : ℕ) (hx : x ∈ A) {B : Finset ℕ} (hB : B ⊆ A) :
      insert x T ∪ B ⊆ Icc 1 n := by
    intro y hy
    rcases mem_union.1 hy with he | hb
    · rcases mem_insert.1 he with rfl | ht
      · exact hAin hx
      · exact hTA (mem_union_left _ ht)
    · exact hAin (hB hb)
  by_cases hHigh : ∃ x ∈ A, degreeLimit ≤ (neighbors A M x).card
  · obtain ⟨x, hx, hd⟩ := hHigh
    let U := insert x (neighbors A M x)
    have hU : U ⊆ A := insert_subset hx (filter_subset _ _)
    have hxU : x ∈ U := mem_insert_self _ _
    have hsplit := family_split n (T := T) (A := A) (U := U) (x := x) (by
      intro S hS hxS y hyU hyS
      rcases mem_insert.1 hyU with he | hy
      · exact he
      · obtain ⟨_, hf, _, hTS, _⟩ := (mem_family n).1 hS
        exact False.elim (hf x hxS y hyS (hTS (hMT (mem_neighbors.1 hy).2.2))))
    let B := A \ U
    have hB : B ⊆ A := sdiff_subset
    have hdB : degreeLimit ≤ (A \ B).card := by
      apply hd.trans
      apply card_le_card
      intro y hy
      have hu : y ∈ U := mem_insert_of_mem hy
      exact mem_sdiff.2 ⟨hU hu, fun h => (mem_sdiff.1 h).2 hu⟩
    have hlt : B.card < A.card := card_lt_card
      (Finset.ssubset_iff_subset_ne.2 ⟨hB, fun he => (mem_sdiff.1 (he.symm ▸ hx : x ∈ B)).2 hxU⟩)
    have hyes := family_count_le n hn (insert x T) B M (hIncluded x hx hB)
      (hMT.trans (subset_insert _ _)) (hMA.mono_right hB)
      (fun y hy => (card_le_card (neighbors_mono hB y)).trans (hD y (hB hy)))
    have hdrop : potential B M + 10 ≤ potential A M := by
      have hc : (degreeLimit : ℝ) ≤ (A \ B).card := by exact_mod_cast hdB
      have hp := potential_delete hB hD
      change (4096 : ℝ) ≤ ((A \ B).card : ℝ) at hc
      linarith
    exact branch_bound (leafBound_nonneg n) (by exact_mod_cast hsplit)
      (hExcept x hx).1 hyes (hExcept x hx).2 hdrop
  · push Not at hHigh
    let x := A.max' hA
    have hx : x ∈ A := max'_mem _ _
    let B := A.erase x
    have hB : B ⊆ A := erase_subset _ _
    have hlt : B.card < A.card := card_erase_lt_of_mem hx
    have hxM : x ∉ M := fun hxM => disjoint_left.1 hMA hxM hx
    have hBx : B ⊆ Icc 1 (x - 1) := by
      intro y hy
      have ⟨hne, hyA⟩ := mem_erase.1 hy
      have hle : y ≤ x := le_max' _ _ hyA
      exact mem_Icc.2 ⟨(mem_Icc.1 (hAin hyA)).1, by omega⟩
    have hxle : (x : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 (hAin hx)).2
    have hBn : (B.card : ℝ) + 1 = A.card := by exact_mod_cast card_erase_add_one hx
    have hn' : (1000000000 : ℝ) ≤ n := by exact_mod_cast hn
    have hgain : (2 : ℝ) * B.card + (edges B B M).card ≤
        (edges B B (insert x M)).card + x := by
      exact_mod_cast edges_card_gain hxM (mem_Icc.1 (hAin hx)).1 hBx
    have hdrop : potential B (insert x M) + 10 ≤ potential A M := by
      have hp := potential_delete hB hD
      have hd : (0 : ℝ) ≤ (A \ B).card := by positivity
      have hlarge := lt_of_not_ge hsmall
      norm_num [potential, degreeLimit] at hp ⊢
      linarith only [hgain, hp, hd, hlarge, hBn, hxle, hn']
    have hD' : ∀ y ∈ B, (neighbors B (insert x M) y).card ≤ degreeLimit := by
      intro y hy
      exact (neighbors_card_insert_le B M x y).trans
        (Nat.succ_le_of_lt ((card_le_card (neighbors_mono hB y)).trans_lt (hHigh y (hB hy))))
    have hMA' : Disjoint (insert x M) B := by
      apply disjoint_left.2
      intro y hyM hyB
      rcases mem_insert.1 hyM with rfl | hyM
      · exact (mem_erase.1 hyB).1 rfl
      · exact disjoint_left.1 hMA hyM (hB hyB)
    have hyes := family_count_le n hn (insert x T) B (insert x M) (hIncluded x hx hB)
      (insert_subset_insert _ hMT) hMA' hD'
    have hsplit := family_split n (T := T) (A := A) (U := {x}) (x := x)
      (fun _ _ _ _ hy _ => mem_singleton.1 hy)
    rw [sdiff_singleton_eq_erase] at hsplit
    exact branch_bound (leafBound_nonneg n) (by exact_mod_cast hsplit)
      (hExcept x hx).1 hyes (hExcept x hx).2 hdrop
termination_by A.card
decreasing_by
  all_goals first | exact hlt | exact card_erase_lt_of_mem hx


private lemma count_le (n : ℕ) (hn : 1000000000 ≤ n) :
    (maximalSumFreeCount n : ℝ) ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * n) := by
  have h := family_count_le n hn ∅ (Icc 1 n) ∅ (by simp) (by simp) (by simp)
    (by simp [neighbors])
  have hpot : potential (Icc 1 n) ∅ = (n : ℝ) / 100 := by
    simp only [potential, degreeLimit, edges, notMem_empty, and_false, filter_false, card_empty,
      Nat.cast_zero, sub_zero, Nat.card_Icc, Nat.add_sub_cancel]
    ring
  have hcount : (family n ∅ (Icc 1 n)).card = maximalSumFreeCount n := by
    classical
    unfold family maximalSumFreeCount
    congr 1
    apply filter_eq_self.2
    intro S hS
    simp only [mem_filter, mem_powerset] at hS
    exact ⟨empty_subset _, by simpa only [empty_union] using hS.1⟩
  rw [hcount, hpot, leafBound, ← Real.rpow_add (by norm_num)] at h
  refine h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  linarith

/-- **Maximal sum-free subsets of $\{1, \dots, n\}$ number $o(2^{n/2})$.** Let $f_m(n)$ be the
number of maximal sum-free subsets of $\{1, \dots, n\}$. Then $f_m(n) / 2^{n/2} \to 0$ as
$n \to \infty$, that is, $f_m(n) = o(2^{n/2})$.

Source: T. F. Bloom, Erdős Problems, Problem #877, https://www.erdosproblems.com/877 (status
PROVED); resolution: T. Łuczak and T. Schoen, On the number of maximal sum-free sets, Proc. Amer.
Math. Soc. 129 (2001), 2205-2207, abstract: {1, 2, …, n} contains at most 2^{n/2 - 2^{-28} n}
maximal sum-free subsets, provided n is large enough; erdosproblems.com/877: this resolves the
question, and Balogh, Liu, Sharifzadeh and Treglown later proved f_m(n) = 2^{(1/4 + o(1)) n},
https://doi.org/10.1090/S0002-9939-00-05815-9.
-/
theorem maximalSumFreeCountSmall_holds : maximalSumFreeCountSmall := by
  have hpow : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ (-(1 / 100) : ℝ)) ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  unfold maximalSumFreeCountSmall
  refine Filter.Tendsto.squeeze' tendsto_const_nhds hpow
    (Filter.Eventually.of_forall fun n => by positivity) ?_
  filter_upwards [Filter.eventually_ge_atTop (1000000000 : ℕ)] with n hn
  calc
    (maximalSumFreeCount n : ℝ) / 2 ^ ((n : ℝ) / 2)
        ≤ (2 : ℝ) ^ ((49 / 100 : ℝ) * n) / 2 ^ ((n : ℝ) / 2) :=
      div_le_div_of_nonneg_right (count_le n hn) (by positivity)
    _ = ((2 : ℝ) ^ (-(1 / 100) : ℝ)) ^ n := by
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end MathlibExt.Combinatorics.MaximalSumFreeSetsCountErdosProblem877Wanted
