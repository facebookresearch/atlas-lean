/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.ExponentCoordinates

/-!
# Length filtration of ordered PBW normal forms

Let `R` be a commutative ring and `b : I → L` an `R`-basis indexed by a linearly ordered
alphabet. The normal-form module consists of finitely supported `R`-linear combinations of
weakly increasing words.

Its degree stage `q` is spanned by words of length at most `q`, and its lower stage by words
of length strictly below `q`. Normalizing a word stays within its length bound. The normal
form minus the single canonical ordered word with the same multiplicities lies in the strictly
shorter stage, because bracket contractions reduce length.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "N" => (OrderedWord I →₀ R)

/-- The bounded-length submodule of ordered normal forms.

Stage `q` is spanned by the single ordered-word terms whose word length is at most `q`. -/
def normalFormDegreeSpan (q : ℕ) : Submodule R N :=
  Submodule.span R ((fun xs : OrderedWord I => Finsupp.single xs 1) ''
    {xs | xs.val.length ≤ q})

/-- The strictly shorter submodule of ordered normal forms.

Stage `q` is spanned by the single ordered-word terms whose word length is strictly less than
`q`. -/
def normalFormLowerSpan (q : ℕ) : Submodule R N :=
  Submodule.span R ((fun xs : OrderedWord I => Finsupp.single xs 1) ''
    {xs | xs.val.length < q})

/-- Monotonicity of bounded-length normal-form stages.

The submodules of ordered normal forms increase with the length bound. -/
theorem normalFormDegreeSpan_mono : Monotone (normalFormDegreeSpan (R := R) (I := I)) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro z ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans hpq, rfl⟩

/-- Containment of a degree stage in a larger strict-length stage.

If `p<q`, every ordered normal form supported in lengths at most `p` is supported in lengths
strictly below `q`. -/
theorem normalFormDegreeSpan_le_lower {p q : ℕ} (hpq : p < q) :
    normalFormDegreeSpan (R := R) (I := I) p ≤ normalFormLowerSpan q := by
  apply Submodule.span_mono
  rintro z ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans_lt hpq, rfl⟩

/-- The length bound of a PBW normal form.

Normalizing a basis word produces a finite combination of ordered words of length at most the
input length. -/
theorem normalize_mem_degreeSpan (b : Module.Basis I R L) (xs : List I) :
    normalize b xs ∈ normalFormDegreeSpan xs.length := by
  generalize hn : List.inversionWeight xs = n
  induction n using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
      cases hr : List.adjacentInversion xs with
      | none =>
          have hordered : normalize b xs =
              Finsupp.single (⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩ :
                OrderedWord I) 1 :=
            normalize_ordered b ⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩
          rw [hordered]
          exact Submodule.subset_span
            ⟨⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩,
              by change xs.length ≤ xs.length; exact le_rfl, rfl⟩
      | some data =>
          rcases data with ⟨p, i, j, s⟩
          obtain ⟨hxs, hji⟩ := List.adjacentInversion_spec xs p i j s hr
          have hswap : List.inversionWeight (p ++ j :: i :: s) < n := by
            rw [← hn, hxs]
            exact List.inversionWeight_adjacent_swap_lt p i j s hji
          have hlength : (p ++ j :: i :: s).length = xs.length := by
            rw [hxs]
            simp only [List.length_append, List.length_cons]
          rw [normalize_of_adjacentInversion b hr]
          apply (normalFormDegreeSpan xs.length).add_mem
          · simpa only [hlength] using
              ih (List.inversionWeight (p ++ j :: i :: s)) hswap (p ++ j :: i :: s) rfl
          · simp only [Finsupp.sum]
            apply (normalFormDegreeSpan xs.length).sum_mem
            intro k hk
            apply (normalFormDegreeSpan xs.length).smul_mem
            have hweight : List.inversionWeight (p ++ k :: s) < n := by
              rw [← hn, hxs]
              exact List.inversionWeight_contract_lt p i j k s
            apply normalFormDegreeSpan_mono (show (p ++ k :: s).length ≤ xs.length by
              rw [hxs]
              simp only [List.length_append, List.length_cons]
              omega)
            exact ih (List.inversionWeight (p ++ k :: s)) hweight (p ++ k :: s) rfl

/-- The strictly shorter correction to canonical word ordering.

The normal form of `xs` minus the single canonical ordered word with the same multiplicities
belongs to the normal-form submodule of lengths strictly below `xs.length`. -/
theorem normalize_sub_canonical_mem_lowerSpan (b : Module.Basis I R L) (xs : List I) :
    normalize b xs - Finsupp.single (canonicalOrderedWord xs) 1 ∈
      normalFormLowerSpan xs.length := by
  generalize hn : List.inversionWeight xs = n
  induction n using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
      cases hr : List.adjacentInversion xs with
      | none =>
          let ys : OrderedWord I := ⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩
          have hcanon : canonicalOrderedWord xs = ys := canonicalOrderedWord_ordered ys
          have hordered : normalize b xs = Finsupp.single ys 1 := normalize_ordered b ys
          rw [hordered, hcanon, sub_self]
          exact (normalFormLowerSpan xs.length).zero_mem
      | some data =>
          rcases data with ⟨p, i, j, s⟩
          obtain ⟨hxs, hji⟩ := List.adjacentInversion_spec xs p i j s hr
          have hswap : List.inversionWeight (p ++ j :: i :: s) < n := by
            rw [← hn, hxs]
            exact List.inversionWeight_adjacent_swap_lt p i j s hji
          have hlength : (p ++ j :: i :: s).length = xs.length := by
            rw [hxs]
            simp only [List.length_append, List.length_cons]
          have hcanon : canonicalOrderedWord xs = canonicalOrderedWord (p ++ j :: i :: s) := by
            rw [hxs]
            exact canonicalOrderedWord_adjacent_swap p s i j
          have hleft : normalize b (p ++ j :: i :: s) -
              Finsupp.single (canonicalOrderedWord (p ++ j :: i :: s)) 1 ∈
                normalFormLowerSpan xs.length := by
            simpa only [hlength] using
              ih (List.inversionWeight (p ++ j :: i :: s)) hswap (p ++ j :: i :: s) rfl
          have hright : (b.repr ⁅b i, b j⁆).sum
              (fun k r => r • normalize b (p ++ k :: s)) ∈ normalFormLowerSpan xs.length := by
            simp only [Finsupp.sum]
            apply (normalFormLowerSpan xs.length).sum_mem
            intro k hk
            apply (normalFormLowerSpan xs.length).smul_mem
            apply normalFormDegreeSpan_le_lower (show (p ++ k :: s).length < xs.length by
              rw [hxs]
              simp only [List.length_append, List.length_cons]
              omega)
            exact normalize_mem_degreeSpan b (p ++ k :: s)
          rw [normalize_of_adjacentInversion b hr, hcanon]
          have hsum :
              normalize b (p ++ j :: i :: s) +
                  (b.repr ⁅b i, b j⁆).sum (fun k r => r • normalize b (p ++ k :: s)) -
                  Finsupp.single (canonicalOrderedWord (p ++ j :: i :: s)) 1 =
                (normalize b (p ++ j :: i :: s) -
                  Finsupp.single (canonicalOrderedWord (p ++ j :: i :: s)) 1) +
                  (b.repr ⁅b i, b j⁆).sum (fun k r => r • normalize b (p ++ k :: s)) := by
            abel
          rw [hsum]
          exact (normalFormLowerSpan xs.length).add_mem hleft hright

end UniversalEnvelopingAlgebra.PBW
