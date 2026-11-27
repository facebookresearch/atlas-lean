/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions
import all MathlibExt.Combinatorics.Enumerative.OneMeteredParkingFunctions

/-!
# 1-metered parking with two spots

With two spots, a car fails exactly when it prefers the occupied spot `1`. In a prefix where
all cars have parked, the last car holds `1` precisely when the last lace is `[1]` or `[0, 0]`.
In either case a new preference of `1` would extend the lace and cause a failure.

## References

* Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*,
  INTEGERS 25 (2025), Article A73, pp. 1–37, Corollary 3 (p. 13),
  <https://math.colgate.edu/~integers/z73/z73.pdf>. The paper derives the characterization
  from its Lemma 1 and Theorem 1; here we track the two spots directly.
* S. Alex Bradt, Jennifer Elder, Pamela E. Harris, Gordon Rojas Kirby, Eva Reutercrona, Yuxuan
  (Susan) Wang, and Juliet Whidden, *Unit Interval Parking Functions and the r-Fubini Numbers*,
  La Matematica 3 (2024), pp. 370–384, Definition 2.7, <https://doi.org/10.1007/s44007-024-00089-y>.
* Lucas Chaves Meyles, Pamela E. Harris, Richter Jordaan, Gordon Rojas Kirby, Sam Sehayek, and
  Ethan Spingarn, *Unit-Interval Parking Functions and the Permutohedron*, arXiv:2305.15554
  (2023), Remark 2.7, <https://arxiv.org/abs/2305.15554>.
  The latter two references are credited for related decompositions in Remark 3 of
  *Metered Parking Functions*.
-/

namespace MetaMathlibExt

open meteredParkingCount_one_binet (lastSpot nextSpot meteredOutcome_one_append lastSpot_append
  nextSpot_eq_some_iff nextSpot_eq_none_iff)

private def GoodLaces (cs : List (List ℕ)) : Prop :=
  ∀ c ∈ cs, 1 ∈ c → c.length = 1

-- Once a lace containing `1` is too long, appending a new entry cannot repair it.
private theorem goodLaces_of_laceStep (cs : List (List ℕ)) (a : ℕ)
    (h : GoodLaces (laceStep cs a)) : GoodLaces cs := by
  have htrim (bs : List (List ℕ)) (c : List ℕ) :
      GoodLaces (bs ++ [c ++ [a]]) → GoodLaces (bs ++ [c]) := by
    simp only [GoodLaces, List.forall_mem_append, List.forall_mem_singleton]
    rintro ⟨hbs, hc⟩
    refine ⟨hbs, fun hmem => ?_⟩
    have hlen := hc (List.mem_append_left _ hmem)
    have hpos := List.length_pos_of_mem hmem
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  have hkeep (bs : List (List ℕ)) : GoodLaces (bs ++ [[a]]) → GoodLaces bs := by
    simp only [GoodLaces, List.forall_mem_append, List.forall_mem_singleton]
    exact And.left
  rcases cs.eq_nil_or_concat with rfl | ⟨cs, c, rfl⟩
  · simp [GoodLaces]
  · simp only [List.concat_eq_append] at h ⊢
    rcases c with _ | ⟨p, _ | ⟨q, rest⟩⟩
    · exact hkeep (cs ++ [[]]) (by simpa [laceStep] using h)
    · by_cases hp : a = p
      · exact htrim cs [p] (by simpa [laceStep, hp] using h)
      · exact hkeep (cs ++ [[p]]) (by simpa [laceStep, hp] using h)
    · by_cases he : a = (p :: q :: rest).getLastD 0 + 1
      · exact htrim cs (p :: q :: rest) (by
          simpa only [laceStep, List.getLast?_append, List.getLast?_singleton, Option.some_or,
            ite_eq_left he, List.dropLast_append_cons, List.dropLast_singleton,
            List.append_nil] using h)
      · exact hkeep (cs ++ [p :: q :: rest]) (by
          simpa only [laceStep, List.getLast?_append, List.getLast?_singleton, Option.some_or,
            ite_eq_right he] using h)

-- The final lace and the occupied spot in a successful prefix.
private inductive TwoSpotLast : List (List ℕ) → Option ℕ → Prop
  | empty : TwoSpotLast [] none
  | zero (cs : List (List ℕ)) : TwoSpotLast (cs ++ [[0]]) (some 0)
  | one (cs : List (List ℕ)) : TwoSpotLast (cs ++ [[1]]) (some 1)
  | bumped (cs : List (List ℕ)) : TwoSpotLast (cs ++ [[0, 0]]) (some 1)

private theorem twoSpot_step {cs : List (List ℕ)} {o : Option ℕ} {a : ℕ}
    (hs : TwoSpotLast cs o) (ha : a < 2) (hg : GoodLaces cs) :
    (GoodLaces (laceStep cs a) ↔ nextSpot 2 o a ≠ none) ∧
      (nextSpot 2 o a ≠ none → TwoSpotLast (laceStep cs a) (nextSpot 2 o a)) := by
  have happend (bs ds : List (List ℕ)) :
      GoodLaces (bs ++ ds) ↔ GoodLaces bs ∧ GoodLaces ds := List.forall_mem_append
  have hcons (c : List ℕ) (bs : List (List ℕ)) :
      GoodLaces (c :: bs) ↔ (1 ∈ c → c.length = 1) ∧ GoodLaces bs := List.forall_mem_cons
  have hnil : GoodLaces [] := by simp [GoodLaces]
  have h00 : nextSpot 2 (some 0) 0 = some 1 := by
    simp [nextSpot_eq_some_iff (by decide : (0 : ℕ) < 2)]
  have h10 : nextSpot 2 (some 1) 0 = some 0 := by
    simp [nextSpot_eq_some_iff (by decide : (0 : ℕ) < 2)]
  have h01 : nextSpot 2 (some 0) 1 = some 1 := by
    simp [nextSpot_eq_some_iff (by decide : (1 : ℕ) < 2)]
  have ha' : a = 0 ∨ a = 1 := by omega
  refine ⟨?_, ?_⟩
  · rcases ha' with rfl | rfl <;> cases hs <;>
      simp_all [laceStep, nextSpot_eq_none_iff ha]
  · rcases ha' with rfl | rfl
    · cases hs with
      | empty => exact fun _ => TwoSpotLast.zero []
      | zero cs => intro _; simpa [laceStep, h00] using TwoSpotLast.bumped cs
      | one cs =>
        intro _
        have hz := TwoSpotLast.zero (cs ++ [[1]])
        rw [List.append_assoc] at hz
        simpa [laceStep, h10] using hz
      | bumped cs =>
        intro _
        have hz := TwoSpotLast.zero (cs ++ [[0, 0]])
        rw [List.append_assoc] at hz
        simpa [laceStep, h10] using hz
    · cases hs with
      | empty => exact fun _ => TwoSpotLast.one []
      | zero cs =>
        intro _
        have ho := TwoSpotLast.one (cs ++ [[0]])
        rw [List.append_assoc] at ho
        simpa [laceStep, h01] using ho
      | one _ | bumped _ => exact fun h => (h rfl).elim

private theorem twoSpot_invariant (l : List ℕ) (hl : ∀ a ∈ l, a < 2) :
    (none ∉ meteredOutcome 1 2 l ↔ GoodLaces (laceDecomposition l)) ∧
      (none ∉ meteredOutcome 1 2 l → TwoSpotLast (laceDecomposition l) (lastSpot 2 l)) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨by simp [meteredOutcome, GoodLaces, laceDecomposition], fun _ => .empty⟩
  | append_singleton l a ih =>
    have ha : a < 2 := hl a (by simp)
    obtain ⟨ihGood, ihLast⟩ := ih fun b hb => hl b (by simp [hb])
    rw [meteredOutcome_one_append, lastSpot_append,
      show laceDecomposition (l ++ [a]) = laceStep (laceDecomposition l) a by
        simp [laceDecomposition, List.foldl_append]]
    simp only [List.mem_append, List.mem_singleton, not_or, ne_comm (a := none)]
    by_cases hp : none ∉ meteredOutcome 1 2 l
    · obtain ⟨hgood, hlast⟩ := twoSpot_step (ihLast hp) ha (ihGood.mp hp)
      exact ⟨⟨fun hh => hgood.mpr hh.2, fun hg => ⟨hp, hgood.mp hg⟩⟩, fun hh => hlast hh.2⟩
    · refine ⟨⟨fun hh => (hp hh.1).elim, fun hg => ?_⟩, fun hh => (hp hh.1).elim⟩
      exact (hp (ihGood.mpr (goodLaces_of_laceStep _ _ hg))).elim

-- Retain the source's nonempty hypothesis; the empty list also satisfies the equivalence.
set_option linter.unusedVariables false in
/-- **One-metered parking functions with two spots.** Let $m \ge 1$ and
$f : \{0, \dots, m-1\} \to \{0, 1\}$. Then $f$ is a $1$-metered parking function with $m$ cars and
$2$ spots if and only if every lace of the lace decomposition of $(f(0), \dots, f(m-1))$ that
contains the value $1$ has length $1$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Corollary 3 (`integers-2025-A73-cor-3`). -/
public theorem isMeteredParkingFunction_one_two_iff_lace {m : ℕ} (hm : 1 ≤ m)
    (f : Fin m → Fin 2) :
    IsMeteredParkingFunction 1 f ↔
      ∀ c ∈ laceDecomposition (List.ofFn fun i => (f i : ℕ)), 1 ∈ c → c.length = 1 := by
  let l := List.ofFn fun i => (f i : ℕ)
  have hl : ∀ a ∈ l, a < 2 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact (f i).isLt
  suffices hn : IsMeteredParkingFunction 1 f ↔ none ∉ meteredOutcome 1 2 l from
    hn.trans (twoSpot_invariant l hl).1
  exact ⟨fun h hm => h none hm rfl, fun h _ ho he => h (he ▸ ho)⟩

end MetaMathlibExt
