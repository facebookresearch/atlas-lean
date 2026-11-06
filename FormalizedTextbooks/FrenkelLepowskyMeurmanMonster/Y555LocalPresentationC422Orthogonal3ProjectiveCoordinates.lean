/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact projective coordinate equality means equality up to the actual two field scalars. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3Coordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Equal actual projective vector codes identify vectors up to their exact sign. -/
theorem y422Orthogonal3ProjectiveVectorCode_eq_iff (v w : Fin 8 → ZMod 3) :
    y422Orthogonal3ProjectiveVectorCode v = y422Orthogonal3ProjectiveVectorCode w ↔
      v = w ∨ v = -w := by
  constructor
  · intro h
    by_cases hv : y422Orthogonal3VectorCode v ≤ y422Orthogonal3VectorCode (-v)
    · by_cases hw : y422Orthogonal3VectorCode w ≤ y422Orthogonal3VectorCode (-w)
      · have he : y422Orthogonal3VectorCode v = y422Orthogonal3VectorCode w := by
          simpa only [y422Orthogonal3ProjectiveVectorCode, min_eq_left hv,
            min_eq_left hw] using h
        exact Or.inl (y422Orthogonal3VectorCode_injective he)
      · have hw' : y422Orthogonal3VectorCode (-w) ≤ y422Orthogonal3VectorCode w :=
          le_of_lt (lt_of_not_ge hw)
        have he : y422Orthogonal3VectorCode v = y422Orthogonal3VectorCode (-w) := by
          simpa only [y422Orthogonal3ProjectiveVectorCode, min_eq_left hv,
            min_eq_right hw'] using h
        exact Or.inr (y422Orthogonal3VectorCode_injective he)
    · have hv' : y422Orthogonal3VectorCode (-v) ≤ y422Orthogonal3VectorCode v :=
        le_of_lt (lt_of_not_ge hv)
      by_cases hw : y422Orthogonal3VectorCode w ≤ y422Orthogonal3VectorCode (-w)
      · have he : y422Orthogonal3VectorCode (-v) = y422Orthogonal3VectorCode w := by
          simpa only [y422Orthogonal3ProjectiveVectorCode, min_eq_right hv',
            min_eq_left hw] using h
        have he' := congrArg Neg.neg (y422Orthogonal3VectorCode_injective he)
        exact Or.inr (by simpa only [neg_neg] using he')
      · have hw' : y422Orthogonal3VectorCode (-w) ≤ y422Orthogonal3VectorCode w :=
          le_of_lt (lt_of_not_ge hw)
        have he : y422Orthogonal3VectorCode (-v) = y422Orthogonal3VectorCode (-w) := by
          simpa only [y422Orthogonal3ProjectiveVectorCode, min_eq_right hv',
            min_eq_right hw'] using h
        exact Or.inl (neg_injective (y422Orthogonal3VectorCode_injective he))
  · rintro (rfl | rfl)
    · rfl
    · exact y422Orthogonal3ProjectiveVectorCode_neg w

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
