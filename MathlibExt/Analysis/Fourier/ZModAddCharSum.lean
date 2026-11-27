/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

@[expose] public section

/-!
# Character sums of linear and affine forms over `ZMod N`

Orthogonality relations for the standard additive character `ZMod.stdAddChar`: the sum of
`stdAddChar` of a linear form over all argument vectors vanishes unless the form is zero,
and the affine version factors the constant term out.

Extracted from the absolutely-maximally-entangled-state development now in
`PhyslibExt.QuantumInfo.AbsolutelyMaximallyEntangled`.
-/

namespace MetaMathlibExt

/-- Orthogonality for the standard additive character of `ZMod N`, for a positive modulus
`N` and a finite index type `ι`: summing `stdAddChar (∑ i, c i * z i)` over all
`z : ι → ZMod N` gives `N ^ card ι` when the coefficient vector `c` vanishes and `0`
otherwise. -/
lemma sum_stdAddChar_dot {N : ℕ} [NeZero N] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (c : ι → ZMod N) :
    (∑ z : ι → ZMod N, ZMod.stdAddChar (∑ i, c i * z i)) =
      if c = 0 then (N ^ Fintype.card ι : ℂ) else 0 := by
  have h1 (t : ZMod N) : (∑ a : ZMod N, ZMod.stdAddChar (t * a)) =
      if t = 0 then (N : ℂ) else 0 := by
    split_ifs with h
    · simp [h, ZMod.card]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)
  have hmap' (s : Finset ι) (z : ι → ZMod N) :
      ZMod.stdAddChar (∑ i ∈ s, c i * z i) =
        ∏ i ∈ s, ZMod.stdAddChar (c i * z i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, AddChar.map_add_eq_mul, ih]
  have hmap (z : ι → ZMod N) :
      ZMod.stdAddChar (∑ i, c i * z i) =
        ∏ i, ZMod.stdAddChar (c i * z i) := by
    simpa using hmap' Finset.univ z
  calc
    _ = ∑ z : ι → ZMod N, ∏ i, ZMod.stdAddChar (c i * z i) := by
      simp_rw [hmap]
    _ = ∏ i, ∑ a : ZMod N, ZMod.stdAddChar (c i * a) :=
      (@Fintype.prod_sum ι ℂ _ _ _ (fun _ => ZMod N) _
        (fun i a => ZMod.stdAddChar (c i * a))).symm
    _ = _ := by
      simp_rw [h1]
      split_ifs with h
      · subst c
        simp [ZMod.card]
      · have hi : ∃ i, c i ≠ 0 := by
          simpa [funext_iff] using h
        obtain ⟨i, hi⟩ := hi
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]

/-- `stdAddChar a * conj (stdAddChar b) = stdAddChar (a - b)`. -/
lemma stdAddChar_mul_star {N : ℕ} [NeZero N] (a b : ZMod N) :
    ZMod.stdAddChar a * star (ZMod.stdAddChar b) = ZMod.stdAddChar (a - b) := by
  change ZMod.stdAddChar a * (starRingEnd ℂ) (ZMod.stdAddChar b) = _
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]

/-- The standard additive character of `ZMod N` takes values of modulus one. -/
lemma norm_stdAddChar {N : ℕ} [NeZero N] (a : ZMod N) :
    ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

/-- The character sum of an affine form, for a positive modulus `N` and a finite index type
`ι`: summing `stdAddChar (b + ∑ i, c i * z i)` over all `z : ι → ZMod N` gives
`stdAddChar b * N ^ card ι` when the coefficient vector `c` vanishes and `0` otherwise;
the constant term factors out of `sum_stdAddChar_dot`. -/
lemma sum_stdAddChar_affine {N : ℕ} [NeZero N] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : ZMod N) (c : ι → ZMod N) :
    (∑ z : ι → ZMod N, ZMod.stdAddChar (b + ∑ i, c i * z i)) =
      ZMod.stdAddChar b * (if c = 0 then (N ^ Fintype.card ι : ℂ) else 0) := by
  simp_rw [AddChar.map_add_eq_mul, ← Finset.mul_sum]
  rw [sum_stdAddChar_dot]

end MetaMathlibExt
