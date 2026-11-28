/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear sums of Legendre symbols
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

@[expose] public section

open scoped BigOperators

namespace legendreSym

/-- **Linear Legendre-symbol sums vanish.** Let $p$ be an odd prime and let $b$ and $c$ be
integers with $p \nmid b$. Then the Legendre symbols $\left(\frac{b\ell + c}{p}\right)$ for
$\ell = 0, 1, \dots, p - 1$ sum to $0$.

Source: This is the first corollary of Theorem `thm1` in Ram Krishna Pandey and
Anshumaan Parashar, *On Certain Sums with Quadratic Expressions Involving the
Legendre Symbol*, Journal of Integer Sequences 21 (2018), Article 18.4.7,
lines 190–193,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Pandey/pandey14.tex>.
The proof here reindexes Mathlib's `quadraticChar_sum_zero`
through the affine permutation `x ↦ b * x + c` of `ZMod p`. -/
public theorem sum_linear_eq_zero
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p) (b c : ℤ) (hb : ¬ (p : ℤ) ∣ b) :
    ∑ ℓ ∈ Finset.range p, legendreSym p (b * (ℓ : ℤ) + c) = 0 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero p := ⟨hp0⟩
  have hb' : (b : ZMod p) ≠ 0 :=
    fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have hp2 : p ≠ 2 := hpodd.ne_two_of_dvd_nat (dvd_refl p)
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hsum :
      (∑ x : ZMod p,
          quadraticChar (ZMod p) ((b : ZMod p) * x + (c : ZMod p))) = 0 := by
    calc
      _ = ∑ x : ZMod p, quadraticChar (ZMod p) x := by
        exact Fintype.sum_bijective
          (fun x : ZMod p ↦ (b : ZMod p) * x + (c : ZMod p))
          ((AddGroup.addRight_bijective (c : ZMod p)).comp
            (mulLeft_bijective₀ (b : ZMod p) hb')) _ _ (fun _ ↦ rfl)
      _ = 0 := quadraticChar_sum_zero hF
  have e_bij : Function.Bijective (fun i : Fin p => ((i.val : ℕ) : ZMod p)) := by
    constructor
    · intro a b hab
      have hmod : a.val ≡ b.val [MOD p] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hab
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod a.isLt b.isLt)
    · intro x
      refine ⟨⟨x.val, ZMod.val_lt x⟩, ?_⟩
      change ((x.val : ℕ) : ZMod p) = x
      rw [ZMod.natCast_val, ZMod.cast_id]
  have hbridge := Function.Bijective.sum_comp e_bij
    (fun x : ZMod p => quadraticChar (ZMod p) ((b : ZMod p) * x + (c : ZMod p)))
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [legendreSym, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  simpa using hbridge.trans hsum

end legendreSym

end
