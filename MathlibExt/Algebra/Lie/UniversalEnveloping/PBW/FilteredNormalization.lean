/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.ExponentCoordinates

/-!
# Length bounds and the leading ordered term of normalization

Every computed normal-form word has length at most the original word. The
canonical ordered word has the original multiplicities, and subtracting it
leaves only strictly shorter words. The induction follows the actual first
inversion: its swap preserves multiplicities, while each bracket contraction
shortens the word.
-/

@[expose] public section

noncomputable section

universe u v w

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "N" => (OrderedWord I →₀ R)

/-- Finite combinations of ordered words of length at most `q`. -/
def normalFormDegreeSpan (q : ℕ) : Submodule R N :=
  Submodule.span R ((fun xs : OrderedWord I => Finsupp.single xs 1) ''
    {xs | xs.val.length ≤ q})

/-- Finite combinations of ordered words strictly shorter than `q`. -/
def normalFormLowerSpan (q : ℕ) : Submodule R N :=
  Submodule.span R ((fun xs : OrderedWord I => Finsupp.single xs 1) ''
    {xs | xs.val.length < q})

theorem normalFormDegreeSpan_mono : Monotone (normalFormDegreeSpan (R := R) (I := I)) := by
  intro p q hpq
  apply Submodule.span_mono
  rintro z ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans hpq, rfl⟩

theorem normalFormDegreeSpan_le_lower {p q : ℕ} (hpq : p < q) :
    normalFormDegreeSpan (R := R) (I := I) p ≤ normalFormLowerSpan q := by
  apply Submodule.span_mono
  rintro z ⟨xs, hxs, rfl⟩
  exact ⟨xs, hxs.trans_lt hpq, rfl⟩

/-- The actual recursive normalizer never increases word length. -/
theorem normalize_mem_degreeSpan (b : Module.Basis I R L) (xs : List I) :
    normalize b xs ∈ normalFormDegreeSpan xs.length := by
  generalize hn : List.inversionWeight xs = n
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases hr : List.adjacentInversion xs with
      | none =>
          have hordered : normalize b xs =
              Finsupp.single (⟨xs, List.pairwise_le_of_adjacentInversion_eq_none xs hr⟩ : OrderedWord I) 1 :=
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

/-- Subtracting the actual canonical ordered word leaves only strictly shorter
computed words, with all coefficients supplied by the original Lie bracket. -/
theorem normalize_sub_canonical_mem_lowerSpan (b : Module.Basis I R L) (xs : List I) :
    normalize b xs - Finsupp.single (canonicalOrderedWord xs) 1 ∈
      normalFormLowerSpan xs.length := by
  generalize hn : List.inversionWeight xs = n
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
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
