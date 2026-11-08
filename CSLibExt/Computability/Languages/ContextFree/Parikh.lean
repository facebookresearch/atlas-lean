/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Yields

/-!
# Parikh images and semilinear sets

The Parikh vector of a word counts, for each letter, how many times it
occurs; the Parikh image of a language is the set of Parikh vectors of
its words. A set of vectors is *linear* when it is a single coset of a
finitely generated submonoid (a base vector plus arbitrary nonnegative
combinations of finitely many period vectors), and *semilinear* when it
is a finite union of linear sets. Parikh's theorem says the Parikh
image of every context-free language is semilinear. That theorem is not
formalized here.

## Main definitions

* `Cslib.Language.parikhVector`: the Parikh vector of a word.
* `Cslib.Language.parikhImage`: the Parikh image of a language.
* `Cslib.Language.linComb`: a linear combination of period vectors,
  with one coefficient per position in the period list; it is `0`
  when the two lists have different lengths.
* `Cslib.Language.IsLinear`: linear sets of vectors.
* `Cslib.Language.IsSemilinear`: semilinear sets of vectors.

## Main results

* `Cslib.Language.parikhVector_append`: Parikh vectors add over
  concatenation.
* `Cslib.Language.IsLinear.isSemilinear`: linear sets are semilinear.
* `Cslib.Language.IsSemilinear.union`: semilinear sets are closed
  under union.
-/

@[expose] public section

namespace Cslib.Language

variable {T : Type*}

/-- The Parikh vector of a word: the function counting, for each
letter, how many times it occurs in the word.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
def parikhVector (w : List T) [DecidableEq T] : T → ℕ :=
  fun a => w.count a

/-- The Parikh image of a language: the set of Parikh vectors of its
words.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
def parikhImage (L : Language T) [DecidableEq T] : Set (T → ℕ) :=
  (fun w => parikhVector w) '' L

/-- The Parikh vector of the empty word is zero.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem parikhVector_nil [DecidableEq T] : parikhVector ([] : List T) = 0 := by
  funext a
  simp [parikhVector]

/-- Parikh vectors add over concatenation.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem parikhVector_append [DecidableEq T] (u v : List T) :
    parikhVector (u ++ v) = parikhVector u + parikhVector v := by
  funext a
  simp [parikhVector, List.count_append]

/-- The Parikh image of a union is the union of the Parikh images.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem parikhImage_union [DecidableEq T] (L M : Language T) :
    parikhImage (L + M) = parikhImage L ∪ parikhImage M := by
  ext v
  simp only [parikhImage, Set.mem_union]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases (Language.mem_add _ _ _).mp hw with h | h
    · exact Or.inl ⟨w, h, rfl⟩
    · exact Or.inr ⟨w, h, rfl⟩
  · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
    · exact ⟨w, (Language.mem_add _ _ _).mpr (Or.inl hw), rfl⟩
    · exact ⟨w, (Language.mem_add _ _ _).mpr (Or.inr hw), rfl⟩

/-- The Parikh image of the empty language is empty.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem parikhImage_empty [DecidableEq T] :
    parikhImage (0 : Language T) = ∅ := by
  ext v
  simp only [parikhImage, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨x, hx, -⟩ := h
  exact Language.notMem_zero x hx

/-- The Parikh image of a singleton language is the singleton of the
Parikh vector.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem parikhImage_singleton [DecidableEq T] (w : List T) :
    parikhImage ({w} : Language T) = {parikhVector w} := by
  change (fun w => parikhVector w) '' ({w} : Set (List T)) = {parikhVector w}
  exact Set.image_singleton

/-- The linear combination of a list of period vectors with a
coefficient list `c`: pair the two lists position by position and
sum the scaled periods, and reject mismatched lengths by
returning `0` (the length guard is checked up front, before the
recursion, so a shorter coefficient list cannot silently truncate
and a longer one cannot silently drop coefficients). Coefficients
are indexed by *position* in `P`, not by period value, so duplicate
periods get independent coefficients: for `P = [p, p]`,
`linComb P [1, 0] = p`, not `2 • p`.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
def linComb (P : List (T → ℕ)) (c : List ℕ) : T → ℕ :=
  if P.length = c.length then linCombAux P c else 0
where
  /-- The unguarded recursion behind `linComb`: pair the two lists
  position by position. Used only behind the length guard in
  `linComb`, so the two lists have equal length here. -/
  linCombAux : List (T → ℕ) → List ℕ → T → ℕ
    | [], _ => 0
    | _, [] => 0
    | p :: P, n :: c => n • p + linCombAux P c

/-- The unguarded recursion agrees with `linComb` on equal-length
inputs.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem linComb_eq_aux_of_length_eq {P : List (T → ℕ)} {c : List ℕ}
    (h : P.length = c.length) : linComb P c = linComb.linCombAux P c := by
  unfold linComb
  simp only [ite_eq_left h]

/-- Mismatched lengths are rejected: a shorter coefficient list
does not silently truncate.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem linComb_eq_zero_of_length_lt {P : List (T → ℕ)} {c : List ℕ}
    (h : c.length < P.length) : linComb P c = 0 := by
  unfold linComb
  simp only [ite_eq_right (by omega : ¬ P.length = c.length)]

/-- Mismatched lengths are rejected: a longer coefficient list
does not silently drop coefficients.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem linComb_eq_zero_of_length_gt {P : List (T → ℕ)} {c : List ℕ}
    (h : P.length < c.length) : linComb P c = 0 := by
  unfold linComb
  simp only [ite_eq_right (by omega : ¬ P.length = c.length)]

/-- Duplicate periods get independent coefficients: with
`P = [p, p]`, the coefficients `(1, 0)` give `p`.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem linComb_dup (p : T → ℕ) : linComb [p, p] [1, 0] = p := by
  rw [linComb_eq_aux_of_length_eq rfl]
  funext a
  show (1 : ℕ) * p a + ((0 : ℕ) * p a + 0) = p a
  simp

/-- A set of vectors is linear when it consists of a base vector plus
arbitrary nonnegative combinations of finitely many period vectors,
with one coefficient per position in the period list.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
def IsLinear (S : Set (T → ℕ)) : Prop :=
  ∃ (b : T → ℕ) (P : List (T → ℕ)),
    S = {v | ∃ c : List ℕ, c.length = P.length ∧ v = b + linComb P c}

/-- A set of vectors is semilinear when it is a finite union of
linear sets.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
def IsSemilinear (S : Set (T → ℕ)) : Prop :=
  ∃ (F : Finset (Set (T → ℕ))), (∀ S' ∈ F, IsLinear S') ∧ ⋃₀ F = S

/-- A singleton set of vectors is linear, with no periods.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem isLinear_singleton (b : T → ℕ) : IsLinear ({b} : Set (T → ℕ)) := by
  refine ⟨b, [], ?_⟩
  ext v
  constructor
  · intro hv
    refine ⟨[], rfl, ?_⟩
    change v = b + 0
    rw [Set.mem_singleton_iff.mp hv, add_zero]
  · rintro ⟨c, hc, hv⟩
    have h0 : linComb (T := T) [] c = (0 : T → ℕ) := by
      cases c with
      | nil => rfl
      | cons _ c => simp at hc
    rw [h0] at hv
    simpa using hv

/-- Linear sets are semilinear.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem IsLinear.isSemilinear {S : Set (T → ℕ)} (hS : IsLinear S) :
    IsSemilinear S :=
  ⟨{S}, by simp [hS], by simp⟩

/-- The empty set of vectors is semilinear.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem isSemilinear_empty : IsSemilinear (∅ : Set (T → ℕ)) :=
  ⟨∅, by simp, by simp⟩

/-- A singleton set of vectors is semilinear.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem isSemilinear_singleton (b : T → ℕ) :
    IsSemilinear ({b} : Set (T → ℕ)) :=
  (isLinear_singleton b).isSemilinear

/-- Semilinear sets are closed under union.
Source: Parikh, "On context-free languages", Journal of the ACM 13
(1966), 570-581. -/
theorem IsSemilinear.union {S S' : Set (T → ℕ)}
    (hS : IsSemilinear S) (hS' : IsSemilinear S') :
    IsSemilinear (S ∪ S') := by
  obtain ⟨F, hF, hFun⟩ := hS
  obtain ⟨F', hF', hF'un⟩ := hS'
  refine ⟨F ∪ F', fun S'' hS'' => ?_, ?_⟩
  · rcases Finset.mem_union.mp hS'' with h | h
    · exact hF S'' h
    · exact hF' S'' h
  · rw [Finset.coe_union, Set.sUnion_union, hFun, hF'un]

end Cslib.Language
