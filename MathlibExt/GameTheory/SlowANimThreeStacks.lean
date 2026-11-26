/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SlowANim

/-!
# Slow {1, 2}-Nim on three stacks

A position is a P-position exactly when all three stack heights have the same parity.
-/

namespace MetaMathlibExt

namespace slowANim_one_two_three_isP_iff

private def uniformPositions : Set (Fin 3 → ℕ) :=
  {p | (∀ i, Even (p i)) ∨ ∀ i, Odd (p i)}

private theorem mod_two_eq {p : Fin 3 → ℕ} (hp : p ∈ uniformPositions) (i j : Fin 3) :
    p i % 2 = p j % 2 := by
  rcases hp with h | h
  · rw [Nat.even_iff.mp (h i), Nat.even_iff.mp (h j)]
  · rw [Nat.odd_iff.mp (h i), Nat.odd_iff.mp (h j)]

private theorem move_from_uniform {p q : Fin 3 → ℕ} (hp : p ∈ uniformPositions)
    (hq : q ∈ slowANimMoves {1, 2} p) : q ∉ uniformPositions := by
  simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter] at hq
  obtain ⟨S, ⟨-, ⟨i, hi⟩, hcard, hpos⟩, rfl⟩ := hq
  obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
    by_contra! hall
    simp [Finset.eq_univ_of_forall hall] at hcard
  intro hafter
  have hbefore := mod_two_eq hp i j
  have hpar := mod_two_eq hafter i j
  simp only [slowANimAfter, hi, hj, ite_true, ite_false] at hpar
  have := hpos i hi
  omega

private theorem move_to_uniform (p : Fin 3 → ℕ) (hp : p ∉ uniformPositions) :
    ∃ q ∈ slowANimMoves {1, 2} p, q ∈ uniformPositions := by
  let S := Finset.univ.filter fun i => Odd (p i)
  obtain ⟨i, hi⟩ := not_forall.mp (fun h => hp (Or.inl h))
  obtain ⟨j, hj⟩ := not_forall.mp (fun h => hp (Or.inr h))
  have hne : S.Nonempty := ⟨i, by simpa [S] using Nat.not_even_iff_odd.mp hi⟩
  have hjS : j ∉ S := by simpa [S] using hj
  have hlt : S.card < 3 := by simpa using Finset.card_lt_univ_of_notMem hjS
  refine ⟨slowANimAfter p S, ?_, Or.inl ?_⟩
  · simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter]
    refine ⟨S, ⟨Finset.mem_univ _, hne, ?_, ?_⟩, rfl⟩
    · have := hne.card_pos
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · intro k hk
      have hodd := Nat.odd_iff.mp (Finset.mem_filter.mp hk).2
      omega
  · intro k
    by_cases hk : Odd (p k)
    · simpa [slowANimAfter, S, hk] using hk.tsub_odd (by decide : Odd (1 : ℕ))
    · simpa [slowANimAfter, S, hk] using Nat.not_odd_iff_even.mp hk

end slowANim_one_two_three_isP_iff

open slowANim_one_two_three_isP_iff in
set_option linter.unusedVariables false in
/-- **P-positions of Slow $\{1,2\}$-Nim on three stacks.** In Slow $A$-Nim with $A = \{1, 2\}$
on three stacks, let $p = (p_0, p_1, p_2)$ be a position with $p_0 \le p_1 \le p_2$. Then $p$
is a P-position if and only if its three stack heights are all even or all odd.

Source: Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of
Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Theorem 3. -/
public theorem slowANim_one_two_three_isP_iff (p : Fin 3 → ℕ) (hp : Monotone p) :
    SpragueGrundy.IsP (slowANimGame 3 {1, 2}) p ↔ (∀ i, Even (p i)) ∨ ∀ i, Odd (p i) := by
  let G := slowANimGame 3 {1, 2}
  have hP : IsPPositionSet (fun x y => y ∈ G.moves x) {x | SpragueGrundy.IsP G x} := by
    refine ⟨fun x y hx hy => (SpragueGrundy.isP_iff G x).1 hx y hy, ?_⟩
    intro x hx
    change ¬ SpragueGrundy.IsP G x at hx
    rw [SpragueGrundy.isP_iff] at hx
    simpa only [Set.mem_ofPred_eq, not_forall, exists_prop, not_not] using hx
  have hu : IsPPositionSet (fun x y => y ∈ G.moves x) uniformPositions :=
    ⟨fun _ _ => move_from_uniform, move_to_uniform⟩
  exact Set.ext_iff.mp (hP.eq (SpragueGrundy.wfRel G) hu) p

end MetaMathlibExt
