/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.DegreeSymbolHom

/-!
# Slot laws for n-ary Milnor symbols

Inverse, division, and power laws for `symbolList` in a designated slot,
derived structurally from the fixed-slot additive homomorphism
`symbolSlotHom` in `MathlibExt.KTheory.Milnor.DegreeSymbolHom`.

For fixed `pref` and `suff`, the map `a ↦ pref ++ [a] ++ suff` is identified
with the degree element `symbolSlotDegreeElement` and factors through
`symbolSlotHom : Additive Fˣ →+ degree`.  The list laws are then corollaries
of the group homomorphism laws `symbolSlotHom_inv/div/pow/zpow`, transported
back to `MilnorKRing F` via `symbolSlotHom_apply` and
`symbolSlotDegreeElement_coe`; equality in `MilnorKRing F` is exposed via
subtype coercion which preserves `-, -, •`.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable (F : Type*) [Field F]

/-- Inverse in a designated slot negates the n-ary symbol. -/
theorem symbolList_inv_middle (pref suff : List Fˣ) (a : Fˣ) :
    symbolList F (pref ++ [a⁻¹] ++ suff) = - symbolList F (pref ++ [a] ++ suff) := by
  calc
    symbolList F (pref ++ [a⁻¹] ++ suff)
        = (symbolSlotDegreeElement F pref suff a⁻¹ : MilnorKRing F) :=
          (symbolSlotDegreeElement_coe F pref suff a⁻¹).symm
    _ = (symbolSlotHom F pref suff (Additive.ofMul a⁻¹) : MilnorKRing F) := by
          rw [← symbolSlotHom_apply]
    _ = ((-(symbolSlotHom F pref suff (Additive.ofMul a)) :
          ↥(degree F (symbolSlotDegree F pref suff))) :
          MilnorKRing F) := by
          rw [symbolSlotHom_inv]
    _ = -(symbolSlotHom F pref suff (Additive.ofMul a) : MilnorKRing F) := by
          simp
    _ = -(symbolSlotDegreeElement F pref suff a : MilnorKRing F) := by
          rw [symbolSlotHom_apply]
    _ = -symbolList F (pref ++ [a] ++ suff) := by
          rw [symbolSlotDegreeElement_coe]

/-- For a field `F`, fix ordered lists of units `pref, suff : List Fˣ` and
let `a, b : Fˣ`. In the Milnor K-ring, the symbol of `pref ++ [a / b] ++ suff`
equals the symbol of `pref ++ [a] ++ suff` minus the symbol of
`pref ++ [b] ++ suff`, keeping both lists in their original order. -/
theorem symbolList_div_middle (pref suff : List Fˣ) (a b : Fˣ) :
    symbolList F (pref ++ [a / b] ++ suff) =
      symbolList F (pref ++ [a] ++ suff) - symbolList F (pref ++ [b] ++ suff) := by
  calc
    symbolList F (pref ++ [a / b] ++ suff)
        = (symbolSlotDegreeElement F pref suff (a / b) : MilnorKRing F) :=
          (symbolSlotDegreeElement_coe F pref suff (a / b)).symm
    _ = (symbolSlotHom F pref suff (Additive.ofMul (a / b)) : MilnorKRing F) := by
          rw [← symbolSlotHom_apply]
    _ = (((symbolSlotHom F pref suff (Additive.ofMul a) -
          symbolSlotHom F pref suff (Additive.ofMul b)) :
          ↥(degree F (symbolSlotDegree F pref suff))) :
          MilnorKRing F) := by
          rw [symbolSlotHom_div]
    _ = (symbolSlotHom F pref suff (Additive.ofMul a) : MilnorKRing F) -
          (symbolSlotHom F pref suff (Additive.ofMul b) : MilnorKRing F) := by
          simp
    _ = (symbolSlotDegreeElement F pref suff a : MilnorKRing F) -
          (symbolSlotDegreeElement F pref suff b : MilnorKRing F) := by
          rw [symbolSlotHom_apply, symbolSlotHom_apply]
    _ = symbolList F (pref ++ [a] ++ suff) -
          symbolList F (pref ++ [b] ++ suff) := by
          rw [symbolSlotDegreeElement_coe, symbolSlotDegreeElement_coe]

/-- Natural power in a designated slot is `n` times the symbol. -/
theorem symbolList_pow_middle (pref suff : List Fˣ) (a : Fˣ) (n : ℕ) :
    symbolList F (pref ++ [a ^ n] ++ suff) = n • symbolList F (pref ++ [a] ++ suff) := by
  calc
    symbolList F (pref ++ [a ^ n] ++ suff)
        = (symbolSlotDegreeElement F pref suff (a ^ n) : MilnorKRing F) :=
          (symbolSlotDegreeElement_coe F pref suff (a ^ n)).symm
    _ = (symbolSlotHom F pref suff (Additive.ofMul (a ^ n)) : MilnorKRing F) := by
          rw [← symbolSlotHom_apply]
    _ = (((n • symbolSlotHom F pref suff (Additive.ofMul a)) :
          ↥(degree F (symbolSlotDegree F pref suff))) :
          MilnorKRing F) := by
          rw [symbolSlotHom_pow]
    _ = n • (symbolSlotHom F pref suff (Additive.ofMul a) : MilnorKRing F) := by
          simp
    _ = n • (symbolSlotDegreeElement F pref suff a : MilnorKRing F) := by
          rw [symbolSlotHom_apply]
    _ = n • symbolList F (pref ++ [a] ++ suff) := by
          rw [symbolSlotDegreeElement_coe]

/-- Integer power in a designated slot is `z` times the symbol. -/
theorem symbolList_zpow_middle (pref suff : List Fˣ) (a : Fˣ) (z : ℤ) :
    symbolList F (pref ++ [a ^ z] ++ suff) = z • symbolList F (pref ++ [a] ++ suff) := by
  calc
    symbolList F (pref ++ [a ^ z] ++ suff)
        = (symbolSlotDegreeElement F pref suff (a ^ z) : MilnorKRing F) :=
          (symbolSlotDegreeElement_coe F pref suff (a ^ z)).symm
    _ = (symbolSlotHom F pref suff (Additive.ofMul (a ^ z)) : MilnorKRing F) := by
          rw [← symbolSlotHom_apply]
    _ = (((z • symbolSlotHom F pref suff (Additive.ofMul a)) :
          ↥(degree F (symbolSlotDegree F pref suff))) :
          MilnorKRing F) := by
          rw [symbolSlotHom_zpow]
    _ = z • (symbolSlotHom F pref suff (Additive.ofMul a) : MilnorKRing F) := by
          simp
    _ = z • (symbolSlotDegreeElement F pref suff a : MilnorKRing F) := by
          rw [symbolSlotHom_apply]
    _ = z • symbolList F (pref ++ [a] ++ suff) := by
          rw [symbolSlotDegreeElement_coe]

end MilnorKRing
end MilnorK
