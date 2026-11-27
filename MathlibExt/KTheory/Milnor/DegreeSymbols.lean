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

public import MathlibExt.KTheory.Milnor.DegreePieces
public import MathlibExt.KTheory.Milnor.DegreeMod

/-!
# Symbol classes in degree pieces and mod-ℓ quotients

This file promotes Milnor symbols to filtered representatives in
`MilnorKRing.degree F n` and to their images in the mod-`ℓ` quotients
`DegreeMod F n ℓ`.  Degree-aware wrappers are provided for arbitrary-length
symbol lists, for degree-one symbols, and for degree-two K₂ symbols, together
with the projected classes in `DegreeMod`.

It also records the two basic vanishing statements in `DegreeMod`: a list
containing `1` maps to zero, and a list containing an adjacent Steinberg pair
`a, 1-a` maps to zero, lifting the corresponding identities from
`MilnorK.MilnorKRing.symbolList`.

## Main definitions

* `symbolListDegree`, `symbolDegree`, `k2SymbolDegree`
* `symbolListMod`, `symbolMod`, `k2SymbolMod`

## Main results

* `symbolListDegree_coe`, `symbolListDegree_singleton_eq`, `symbolListMod_singleton`
* `symbolListMod_one_middle`, `symbolListMod_steinberg_middle`
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable (F : Type*) [Field F]

/-- The symbol list `xs` as an element of the degree `|xs|` piece
`degree F |xs|`. Its underlying `MilnorKRing` element is `symbolList F xs`. -/
def symbolListDegree (xs : List Fˣ) : ↥(degree F xs.length) :=
  ⟨symbolList F xs, symbolList_mem_degree F xs⟩

/-- The underlying Milnor K-ring element of `symbolListDegree F xs`
is `symbolList F xs`. -/
@[simp]
theorem symbolListDegree_coe (xs : List Fˣ) :
    (symbolListDegree F xs : MilnorKRing F) = symbolList F xs :=
  rfl

/-- Degree-one symbol `{a}` as an element of `degree F 1`. Its coercion is
`symbol F a`. -/
def symbolDegree (a : Fˣ) : ↥(degree F 1) :=
  ⟨symbol F a, symbol_mem_degree_one F a⟩

/-- Degree-two symbol `{a, b}` as an element of `degree F 2`. Its coercion
is the product `symbol F a * symbol F b` via `k2Symbol`. -/
def k2SymbolDegree (a b : Fˣ) : ↥(degree F 2) :=
  ⟨k2Symbol (F := F) a b, k2Symbol_mem_degree_two (F := F) a b⟩

/-- Canonical image of the symbol list `xs` in `DegreeMod F |xs| ℓ`,
obtained by projecting `symbolListDegree F xs` via `DegreeMod.mk`. -/
def symbolListMod (ℓ : ℕ) (xs : List Fˣ) : DegreeMod F xs.length ℓ :=
  DegreeMod.mk F xs.length ℓ (symbolListDegree F xs)

/-- Singleton mod-`ℓ` class `{a}` in `DegreeMod F 1 ℓ`, i.e. the projection
of `symbolDegree F a`. -/
def symbolMod (ℓ : ℕ) (a : Fˣ) : DegreeMod F 1 ℓ :=
  DegreeMod.mk F 1 ℓ (symbolDegree F a)

/-- Binary mod-`ℓ` class `{a, b}` in `DegreeMod F 2 ℓ`, i.e. the projection
of `k2SymbolDegree F a b`. -/
def k2SymbolMod (ℓ : ℕ) (a b : Fˣ) : DegreeMod F 2 ℓ :=
  DegreeMod.mk F 2 ℓ (k2SymbolDegree F a b)

/-- A singleton symbol list `[a]` agrees with the degree-one symbol `a`
inside `degree F 1`. -/
theorem symbolListDegree_singleton_eq (a : Fˣ) :
    symbolListDegree F [a] = symbolDegree F a := by
  apply Subtype.ext
  simp only [symbolListDegree, symbolDegree]
  exact symbolList_singleton F a

/-- Mod-`ℓ` singleton identification: `symbolListMod F ℓ [a]` equals
`symbolMod F ℓ a`. -/
theorem symbolListMod_singleton (ℓ : ℕ) (a : Fˣ) :
    symbolListMod F ℓ [a] = symbolMod F ℓ a := by
  unfold symbolListMod symbolMod
  rw [symbolListDegree_singleton_eq]
  rfl

/-! ## Zero relations in `DegreeMod` -/

/-- A symbol list containing `1` projects to zero in `DegreeMod`.
This is the `DegreeMod` lift of `symbolList_one_middle`. -/
theorem symbolListMod_one_middle (pref suff : List Fˣ) (ℓ : ℕ) :
    symbolListMod F ℓ (pref ++ [(1 : Fˣ)] ++ suff) = 0 := by
  unfold symbolListMod
  have hdeg : symbolListDegree F (pref ++ [(1 : Fˣ)] ++ suff) =
      (0 : ↥(degree F (pref ++ [(1 : Fˣ)] ++ suff).length)) := by
    apply Subtype.ext
    simp only [symbolListDegree]
    exact symbolList_one_middle F pref suff
  calc DegreeMod.mk F (pref ++ [(1 : Fˣ)] ++ suff).length ℓ
          (symbolListDegree F (pref ++ [(1 : Fˣ)] ++ suff))
      = DegreeMod.mk F _ ℓ (0 : ↥(degree F _)) := by rw [hdeg]
    _ = 0 := map_zero _

/-- A symbol list containing an adjacent Steinberg pair `a, 1-a` projects
to zero in `DegreeMod`. This lifts `symbolList_steinberg_middle`. -/
theorem symbolListMod_steinberg_middle (pref suff : List Fˣ) (a : F)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ℓ : ℕ) :
    let b : Fˣ := Units.mk0 a ha0
    let c : Fˣ := Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)
    symbolListMod F ℓ (pref ++ [b, c] ++ suff) = 0 := by
  intro b c
  unfold symbolListMod
  have hdeg : symbolListDegree F (pref ++ [b, c] ++ suff) =
      (0 : ↥(degree F (pref ++ [b, c] ++ suff).length)) := by
    apply Subtype.ext
    simp only [symbolListDegree]
    exact symbolList_steinberg_middle F pref suff a ha0 ha1
  calc DegreeMod.mk F (pref ++ [b, c] ++ suff).length ℓ
          (symbolListDegree F (pref ++ [b, c] ++ suff))
      = DegreeMod.mk F _ ℓ (0 : ↥(degree F _)) := by rw [hdeg]
    _ = 0 := map_zero _

end MilnorKRing
end MilnorK
