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

public import MathlibExt.KTheory.Milnor.DegreeSymbols

/-!
# Designated-slot homomorphisms in Milnor K-theory

For a field `F` and fixed lists `pref` and `suff`, the map
`a ↦ pref ++ [a] ++ suff` in the fixed degree
`pref.length + 1 + suff.length` gives an additive homomorphism
`Additive Fˣ →+ degree`.

The public helper `symbolSlotDegreeElement` names the fixed-degree symbol
before further degreewise maps.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable (F : Type*) [Field F]

/-- Canonical target degree for a designated slot with fixed prefix and suffix. -/
def symbolSlotDegree (pref suff : List Fˣ) : ℕ :=
  pref.length + 1 + suff.length

/-- The canonical degree equals the length of `pref ++ [a] ++ suff`. -/
theorem symbolSlotDegree_eq_length (pref suff : List Fˣ) (a : Fˣ) :
    symbolSlotDegree F pref suff = (pref ++ [a] ++ suff).length := by
  unfold symbolSlotDegree
  simp [List.length_append, Nat.add_comm, Nat.add_left_comm]

/-- The designated-slot symbol, transported to its canonical target degree. -/
def symbolSlotDegreeElement (pref suff : List Fˣ) (a : Fˣ) :
    ↥(degree F (symbolSlotDegree F pref suff)) :=
  degreeCastEquiv F (symbolSlotDegree_eq_length F pref suff a).symm
    (symbolListDegree F (pref ++ [a] ++ suff))

/-- The underlying `MilnorKRing` element of `symbolSlotDegreeElement` is
`symbolList F (pref ++ [a] ++ suff)`. -/
theorem symbolSlotDegreeElement_coe (pref suff : List Fˣ) (a : Fˣ) :
    (symbolSlotDegreeElement F pref suff a : MilnorKRing F) =
      symbolList F (pref ++ [a] ++ suff) := by
  unfold symbolSlotDegreeElement
  have h := symbolSlotDegree_eq_length F pref suff a
  have hcast := degreeCastEquiv_val (F := F)
      (m := (pref ++ [a] ++ suff).length)
      (n := symbolSlotDegree F pref suff)
      (h := h.symm)
      (x := symbolListDegree F (pref ++ [a] ++ suff))
  change (degreeCastEquiv F h.symm
      (symbolListDegree F (pref ++ [a] ++ suff))).1 = _
  rw [hcast]
  rfl

/-- The designated-slot element at `1` is zero in its canonical degree,
since Milnor symbols vanish when any entry is `1`. -/
theorem symbolSlotDegreeElement_one (pref suff : List Fˣ) :
    symbolSlotDegreeElement F pref suff (1 : Fˣ) =
      (0 : ↥(degree F (symbolSlotDegree F pref suff))) := by
  apply Subtype.ext
  change (symbolSlotDegreeElement F pref suff 1 : MilnorKRing F) =
      (0 : MilnorKRing F)
  simpa only [symbolSlotDegreeElement_coe] using
    symbolList_one_middle F pref suff

/-- The designated-slot element is additive in the slot entry:
`a * b` maps to the sum of the symbols at `a` and `b`. -/
theorem symbolSlotDegreeElement_mul (pref suff : List Fˣ) (a b : Fˣ) :
    symbolSlotDegreeElement F pref suff (a * b) =
      symbolSlotDegreeElement F pref suff a +
      symbolSlotDegreeElement F pref suff b := by
  apply Subtype.ext
  change (symbolSlotDegreeElement F pref suff (a * b) : MilnorKRing F) =
      (symbolSlotDegreeElement F pref suff a +
        symbolSlotDegreeElement F pref suff b : MilnorKRing F)
  simpa only [symbolSlotDegreeElement_coe] using
    symbolList_mul_middle F pref suff a b

/-- Integral designated-slot additive homomorphism. -/
def symbolSlotHom (pref suff : List Fˣ) :
    Additive Fˣ →+ ↥(degree F (symbolSlotDegree F pref suff)) where
  toFun := fun x =>
    let a : Fˣ := Additive.toMul x
    symbolSlotDegreeElement F pref suff a
  map_zero' := by
    change symbolSlotDegreeElement F pref suff 1 = 0
    rw [symbolSlotDegreeElement_one]
  map_add' := fun x y => by
    let a := Additive.toMul x
    let b := Additive.toMul y
    change symbolSlotDegreeElement F pref suff (a * b) =
      symbolSlotDegreeElement F pref suff a +
        symbolSlotDegreeElement F pref suff b
    rw [symbolSlotDegreeElement_mul]

/-- Application formula for `symbolSlotHom`. -/
theorem symbolSlotHom_apply (pref suff : List Fˣ) (a : Fˣ) :
    symbolSlotHom F pref suff (Additive.ofMul a) =
      symbolSlotDegreeElement F pref suff a :=
  rfl

/-- Multiplicative formulation for `symbolSlotHom`: `a * b` maps to sum. -/
theorem symbolSlotHom_mul (pref suff : List Fˣ) (a b : Fˣ) :
    symbolSlotHom F pref suff (Additive.ofMul (a * b)) =
      symbolSlotHom F pref suff (Additive.ofMul a) +
        symbolSlotHom F pref suff (Additive.ofMul b) := by
  change symbolSlotHom F pref suff (Additive.ofMul a + Additive.ofMul b) = _
  rw [map_add]

/-- The designated-slot homomorphism vanishes at `1`. -/
@[simp]
theorem symbolSlotHom_one (pref suff : List Fˣ) :
    symbolSlotHom F pref suff (Additive.ofMul (1 : Fˣ)) = 0 := by
  calc
    symbolSlotHom F pref suff (Additive.ofMul (1 : Fˣ))
        = symbolSlotHom F pref suff 0 := by
          rw [ofMul_one]
    _ = 0 := map_zero _

/-- Inverse in the designated slot negates the symbol. -/
theorem symbolSlotHom_inv (pref suff : List Fˣ) (a : Fˣ) :
    symbolSlotHom F pref suff (Additive.ofMul a⁻¹) =
      -symbolSlotHom F pref suff (Additive.ofMul a) := by
  calc
    symbolSlotHom F pref suff (Additive.ofMul a⁻¹)
        = symbolSlotHom F pref suff (-Additive.ofMul a) := by
          rw [ofMul_inv]
    _ = -symbolSlotHom F pref suff (Additive.ofMul a) := by
          rw [map_neg]

/-- Division in the designated slot splits as a difference. -/
theorem symbolSlotHom_div (pref suff : List Fˣ) (a b : Fˣ) :
    symbolSlotHom F pref suff (Additive.ofMul (a / b)) =
      symbolSlotHom F pref suff (Additive.ofMul a) -
        symbolSlotHom F pref suff (Additive.ofMul b) := by
  calc
    symbolSlotHom F pref suff (Additive.ofMul (a / b))
        = symbolSlotHom F pref suff
            (Additive.ofMul a - Additive.ofMul b) := by
          rw [ofMul_div]
    _ = symbolSlotHom F pref suff (Additive.ofMul a) -
          symbolSlotHom F pref suff (Additive.ofMul b) := by
          rw [map_sub]

/-- Natural power in the designated slot is scalar multiplication. -/
theorem symbolSlotHom_pow (pref suff : List Fˣ) (a : Fˣ) (n : ℕ) :
    symbolSlotHom F pref suff (Additive.ofMul (a ^ n)) =
      n • symbolSlotHom F pref suff (Additive.ofMul a) := by
  calc
    symbolSlotHom F pref suff (Additive.ofMul (a ^ n))
        = symbolSlotHom F pref suff (n • Additive.ofMul a) := by
          rw [ofMul_pow]
    _ = n • symbolSlotHom F pref suff (Additive.ofMul a) := by
          rw [map_nsmul]

/-- Integer power in the designated slot is scalar multiplication. -/
theorem symbolSlotHom_zpow (pref suff : List Fˣ) (a : Fˣ) (z : ℤ) :
    symbolSlotHom F pref suff (Additive.ofMul (a ^ z)) =
      z • symbolSlotHom F pref suff (Additive.ofMul a) := by
  calc
    symbolSlotHom F pref suff (Additive.ofMul (a ^ z))
        = symbolSlotHom F pref suff (z • Additive.ofMul a) := by
          rw [ofMul_zpow]
    _ = z • symbolSlotHom F pref suff (Additive.ofMul a) := by
          rw [map_zsmul]

end MilnorKRing
end MilnorK
