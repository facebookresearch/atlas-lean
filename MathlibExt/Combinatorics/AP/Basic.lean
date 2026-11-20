/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
import Mathlib.Tactic

@[expose] public section

/-! # Arithmetic progressions -/

variable {α : Type*} [AddCommMonoid α]

/-- A set is an arithmetic progression of length `l` with first term `a` and difference `d`. -/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- A set is an arithmetic progression of length `l` for some first term and difference. -/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

namespace Set.IsAPOfLength

variable {s : Set α} {l : ℕ∞}

/-- The cardinality of a set arithmetic progression is its declared length. -/
theorem card (h : s.IsAPOfLength l) : ENat.card s = l :=
  h.choose_spec.choose_spec.1

/-- Unpack a set arithmetic progression into its first term and common difference. -/
theorem eq (h : s.IsAPOfLength l) :
    ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩

/-- The only arithmetic progression of length `0` is the empty set.

Ported from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` of
google-deepmind/formal-conjectures, unchanged. -/
@[simp] theorem zero : s.IsAPOfLength 0 ↔ s = ∅ := by
  simp [Set.IsAPOfLength, Set.IsAPOfLengthWith]

/-- The arithmetic progressions of length `1` are the singletons.

Ported from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` of
google-deepmind/formal-conjectures, unchanged. -/
@[simp] theorem one : s.IsAPOfLength 1 ↔ ∃ a, s = {a} := by
  simp only [Set.IsAPOfLength, Set.IsAPOfLengthWith]
  constructor
  · rintro ⟨a, d, -, hs⟩
    exact ⟨a, by simpa using hs⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, 0, by simp, by simp⟩

end Set.IsAPOfLength

/-- A list is an arithmetic progression of length `l` with first term `a` and difference `d`. -/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨
    s = (List.range l).reverse.map (fun n ↦ a + n • d)

/-- A list is an arithmetic progression of length `l` for some first term and difference. -/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/-- `f` contains a monotone arithmetic progression of length `k`. -/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

/-- A set is free of nontrivial arithmetic progressions of length `l`. -/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

/-- A nontrivial arithmetic progression is not free of progressions of its own length. -/
theorem Set.IsAPOfLength.not_isAPOfLengthFree {s : Set α} {l : ℕ∞}
    (hs : s.IsAPOfLength l) (hl : 1 < l) : ¬ s.IsAPOfLengthFree l := by
  simpa [Set.IsAPOfLengthFree] using ⟨s, le_rfl, ⟨hs, hl⟩⟩

/-- A finite set is free of nontrivial arithmetic progressions of length `l`. -/
def Finset.IsAPOfLengthFree (s : Finset α) (l : ℕ∞) : Prop :=
  (s : Set α).IsAPOfLengthFree l

@[simp] theorem Finset.isAPOfLengthFree_coe (s : Finset α) (l : ℕ∞) :
    s.IsAPOfLengthFree l ↔ (s : Set α).IsAPOfLengthFree l :=
  Iff.rfl

/-- Mathlib's `ThreeAPFree` predicate implies freedom from three-term progressions in the
general-length API. -/
theorem ThreeAPFree.isAPOfLengthFree_three {s : Set ℕ} (hs : ThreeAPFree s) :
    s.IsAPOfLengthFree 3 := by
  intro t hts ht
  rcases ht with ⟨a, d, hcard, rfl⟩
  have ha : a ∈ s := hts ⟨0, by norm_num, by simp⟩
  have hb : a + d ∈ s := hts ⟨1, by norm_num, by simp⟩
  have hc : a + 2 * d ∈ s := hts ⟨2, by norm_num, by simp⟩
  have had : a = a + d := hs ha hb hc (by omega)
  have hd : d = 0 := by omega
  subst d
  have hset :
      {x : ℕ | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < 3), a + n • 0 = x} = {a} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, by norm_num, by simp⟩
  rw [hset] at hcard
  norm_num at hcard

/-- The largest size of a subset of `{1, ..., N}` containing no nontrivial `k`-term
arithmetic progression. -/
noncomputable def Set.IsAPOfLengthFree.maxCard (k N : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest
      (fun m ↦ ∃ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
      N

namespace Set.IsAPOfLengthFree

/-- The extremal cardinality is at most the size of `{1, ..., N}`. -/
theorem maxCard_le (k N : ℕ) : maxCard k N ≤ N :=
  by
    classical
    unfold maxCard
    exact Nat.findGreatest_le N

/-- An extremal progression-free subset attaining `maxCard` exists. -/
theorem maxCard_spec (k N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧
      S.card = maxCard k N ∧ S.IsAPOfLengthFree k := by
  classical
  unfold maxCard
  refine Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
    (Nat.zero_le N) ?_
  refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
  intro t ht hAP
  have ht' : t ⊆ (∅ : Set ℕ) := by simpa using ht
  have ht0 : t = ∅ := Set.subset_empty_iff.mp ht'
  subst t
  have hk : (k : ℕ∞) = 0 := by simpa using hAP.card.symm
  simp [hk]

/-- Every admissible subset has cardinality at most `maxCard`. -/
theorem card_le_maxCard {S : Finset ℕ} {k N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (hfree : S.IsAPOfLengthFree k) :
    S.card ≤ maxCard k N := by
  classical
  unfold maxCard
  apply Nat.le_findGreatest
  · exact (Finset.card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S, hS, rfl, hfree⟩

end Set.IsAPOfLengthFree

/-- A colouring of a set `M` contains a monochromatic arithmetic progression of
length `k`: some colour class contains a set of `M`-elements whose underlying
values form an arithmetic progression of length `k`.

Ported from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` of
google-deepmind/formal-conjectures, unchanged. -/
def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : Set M, ((·.1) '' ap).IsAPOfLength k ∧
    ∀ m ∈ ap, coloring m = c
