/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Sum
public import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Lattice

/-! # Counting non-degenerate Boolean functions by inclusion–exclusion -/

namespace MetaMathlibExt

open Finset Function

namespace card_nondegenerate_boolFun_eq_alternating_sum

/-- Coordinates ignored individually may all be replaced at once. -/
private theorem apply_piecewise {n : ℕ} (f : (Fin n → Bool) → Bool) (s : Finset (Fin n))
    (hs : ∀ i ∈ s, ¬ IsBoolFunNondegenerateOn f i) (x y : Fin n → Bool) :
    f (s.piecewise x y) = f y := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [piecewise_insert]
    have h := ih (fun j hj => hs j (mem_insert_of_mem hj))
    rcases Bool.eq_or_eq_not (x i) (s.piecewise x y i) with he | he
    · simpa only [he, update_eq_self] using h
    · rw [he, ← h]
      exact (not_ne_iff.mp fun hn => hs i (mem_insert_self ..) ⟨_, hn⟩).symm

/-- Restricting to the complement of a set of dummy variables preserves the count. -/
private theorem card_ignoring (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    {n : ℕ} (s : Finset (Fin n)) :
    Nat.card {f : {f : (Fin n → Bool) → Bool // P n f} //
      ∀ i ∈ s, ¬ IsBoolFunNondegenerateOn f.val i} =
      Nat.card {g : (Fin (n - s.card) → Bool) → Bool // P _ g} := by
  classical
  let e := sᶜ.orderEmbOfFin (k := n - s.card) (by simp [card_compl])
  let restrict (x : Fin n → Bool) := x ∘ e
  have hrange : Set.range e = (sᶜ : Finset _) := range_orderEmbOfFin ..
  let lift (g : {g : (Fin (n - s.card) → Bool) → Bool // P _ g}) :
      {f : {f : (Fin n → Bool) → Bool // P n f} //
        ∀ i ∈ s, ¬ IsBoolFunNondegenerateOn f.val i} := by
    refine ⟨⟨g.val ∘ restrict, (hP _ _ e.toEmbedding g.val).2 g.property⟩, ?_⟩
    intro i hi
    rintro ⟨x, hx⟩
    apply hx
    apply congrArg g.val
    exact (update_comp_eq_of_forall_ne x _ fun j he =>
      (mem_compl.mp (sᶜ.orderEmbOfFin_mem _ j)) (he ▸ hi)).symm
  symm
  apply Nat.card_eq_of_bijective lift
  constructor
  · intro g h heq
    apply Subtype.ext
    exact e.injective.surjective_comp_right.injective_comp_right
      (congrArg (fun f => f.val.val) heq)
  · rintro ⟨⟨f, hf⟩, hs⟩
    have hfactor : f.FactorsThrough restrict := by
      intro x y hxy
      have heq : s.piecewise x y = x := by
        funext i
        by_cases hi : i ∈ s
        · simp [hi]
        · have hmem : i ∈ Set.range e := hrange.symm ▸ mem_compl.mpr hi
          obtain ⟨j, rfl⟩ := hmem
          simpa [hi, restrict] using (congrFun hxy j).symm
      simpa only [heq] using apply_piecewise f s hs x y
    obtain ⟨g, rfl⟩ := (factorsThrough_iff f).mp hfactor
    exact ⟨⟨g, (hP _ _ e.toEmbedding g).1 hf⟩, rfl⟩

end card_nondegenerate_boolFun_eq_alternating_sum

open card_nondegenerate_boolFun_eq_alternating_sum

/-- **Counting non-degenerate Boolean functions by inclusion–exclusion.** Let $P$ be a property
of Boolean functions on any number of variables that is invariant under renaming variables
along injections: for all $m, n$, every injective map $e$ from $\{1, \dots, m\}$ to
$\{1, \dots, n\}$ and every $m$-variable function $g$, the $n$-variable function
$x \mapsto g(x_{e(1)}, \dots, x_{e(m)})$ has $P$ if and only if $g$ has $P$. Write $P_i$ for the
number of $i$-variable Boolean functions with $P$ and $\mathrm{nd}\text{-}P_n$ for the number of
non-degenerate $n$-variable Boolean functions with $P$. Then for every $n \ge 0$,

$$\mathrm{nd}\text{-}P_n = \sum_{i=0}^{n} (-1)^{n-i} \binom{n}{i} P_i.$$

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 1 (`jis-2025-25.3.4-prop-1`). -/
public theorem card_nondegenerate_boolFun_eq_alternating_sum
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    (Nat.card {f : (Fin n → Bool) → Bool // IsNondegenerateBoolFun f ∧ P n f} : ℤ)
      = ∑ i ∈ Finset.range (n + 1),
          (-1) ^ (n - i) * (n.choose i : ℤ) * Nat.card {f : (Fin i → Bool) → Bool // P i f} := by
  classical
  let dummy (i : Fin n) : Finset {f : (Fin n → Bool) → Bool // P n f} :=
    univ.filter fun f => ¬ IsBoolFunNondegenerateOn f.val i
  let count (i : ℕ) : ℤ := Nat.card {f : (Fin i → Bool) → Bool // P i f}
  have hall : Nat.card {f : (Fin n → Bool) → Bool // IsNondegenerateBoolFun f ∧ P n f} =
      (univ.inf fun i => (dummy i)ᶜ).card := by
    trans Nat.card {f : {f : (Fin n → Bool) → Bool // P n f} // IsNondegenerateBoolFun f.val}
    · apply Nat.card_congr
      exact (Equiv.subtypeEquivRight (fun _ => and_comm)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
    · apply Nat.subtype_card
      simp [Finset.mem_inf, dummy, IsNondegenerateBoolFun]
  have hinter (s : Finset (Fin n)) : ((s.inf dummy).card : ℤ) = count (n - s.card) := by
    apply congrArg Nat.cast
    rw [← card_ignoring P hP s]
    symm
    apply Nat.subtype_card
    simp [Finset.mem_inf, dummy]
  rw [hall, inclusion_exclusion_card_inf_compl]
  simp_rw [hinter]
  rw [sum_powerset_apply_card (fun k => (-1 : ℤ) ^ k * count (n - k))]
  simp only [card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← sum_range_reflect (fun i => (-1 : ℤ) ^ (n - i) * n.choose i * count i)]
  apply sum_congr rfl
  intro i hi
  have hi' := Nat.le_of_lt_succ (mem_range.mp hi)
  simp [Nat.sub_sub_self hi', Nat.choose_symm hi', mul_left_comm, mul_assoc]

end MetaMathlibExt
