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

public import MathlibExt.KTheory.Milnor.ClassicalDegree
public import MathlibExt.KTheory.Milnor.DegreeSymbolGeneration

/-!
# Classical symbols

Symbols in the classical degree `MilnorK F n`. `MilnorK F n` is definitionally
`MilnorKRing.degree F n`, so `symbolList`, `symbol`, `k2Symbol`,
`symbolTuple` and `symbolMultilinear` are direct aliases of
`MilnorKRing.symbolListDegree`, `MilnorKRing.symbolDegree`,
`MilnorKRing.k2SymbolDegree`, `MilnorKRing.symbolTuple` and
`MilnorKRing.symbolMultilinear`. Vanishing, multilinearity, generation and
extensionality are direct consequences of the degree-level API.

## Main definitions
* `MilnorK.symbolList`
* `MilnorK.symbol`
* `MilnorK.k2Symbol`
* `MilnorK.symbolTuple`
* `MilnorK.symbolMultilinear`

## Main results
* `MilnorK.symbolList_one_middle`
* `MilnorK.symbolList_steinberg_middle`
* `MilnorK.symbol_one`
* `MilnorK.k2Symbol_one_left`
* `MilnorK.k2Symbol_one_right`
* `MilnorK.k2Symbol_steinberg`
* `MilnorK.symbolTuple_span`
* `MilnorK.symbolTuple_ext`
* `MilnorK.symbolMultilinear_apply`
* `MilnorK.symbolMultilinear_map_mul`
* `MilnorK.symbolMultilinear_map_zsmul`
* `MilnorK.symbolMultilinear_update_one`
* `MilnorK.symbolMultilinear_steinberg`
* `MilnorK.symbolMultilinear_two_apply`
-/

@[expose] public section

namespace MilnorK

variable (F : Type*) [Field F]

/-- Symbol in `MilnorK F n` attached to a list of units. -/
def symbolList (xs : List Fˣ) : MilnorK F xs.length :=
  MilnorKRing.symbolListDegree F xs

/-- A `1` entry makes `symbolList` vanish. -/
theorem symbolList_one_middle (pref suff : List Fˣ) :
    symbolList F (pref ++ [(1 : Fˣ)] ++ suff) = 0 :=
  Subtype.ext (MilnorKRing.symbolList_one_middle F pref suff)

/-- An adjacent Steinberg pair makes `symbolList` vanish. -/
theorem symbolList_steinberg_middle (pref suff : List Fˣ) (a : F)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    let b : Fˣ := Units.mk0 a ha0
    let c : Fˣ := Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)
    symbolList F (pref ++ [b, c] ++ suff) = 0 := by
  intro b c
  exact Subtype.ext (MilnorKRing.symbolList_steinberg_middle F pref suff a ha0 ha1)

/-- Degree-one symbol in `MilnorK F 1`. -/
def symbol (a : Fˣ) : MilnorK F 1 :=
  MilnorKRing.symbolDegree F a

/-- The degree-one symbol coincides with the singleton list symbol. -/
theorem symbol_eq_symbolList_singleton (a : Fˣ) :
    symbol F a = symbolList F [a] :=
  Subtype.ext (MilnorKRing.symbolList_singleton F a).symm

/-- The symbol `{1}` vanishes in `MilnorK F 1`. -/
@[simp]
theorem symbol_one : symbol F (1 : Fˣ) = 0 :=
  Subtype.ext (MilnorKRing.symbol_one F)

/-- Degree-two symbol in `MilnorK F 2`. -/
def k2Symbol (a b : Fˣ) : MilnorK F 2 :=
  MilnorKRing.k2SymbolDegree F a b

/-- The `K₂` symbol coincides with the pair list symbol `[a, b]`. -/
theorem k2Symbol_eq_symbolList_pair (a b : Fˣ) :
    k2Symbol F a b = symbolList F [a, b] :=
  Subtype.ext (MilnorKRing.k2Symbol_eq_symbolList_pair a b)

/-- The `K₂` symbol vanishes when its first entry is `1`. -/
@[simp]
theorem k2Symbol_one_left (b : Fˣ) : k2Symbol F (1 : Fˣ) b = 0 :=
  Subtype.ext (MilnorKRing.k2Symbol_one_left b)

/-- The `K₂` symbol vanishes when its second entry is `1`. -/
@[simp]
theorem k2Symbol_one_right (a : Fˣ) : k2Symbol F a (1 : Fˣ) = 0 :=
  Subtype.ext (MilnorKRing.k2Symbol_one_right a)

/-- Steinberg relation `{a, 1-a} = 0` for the `K₂` symbol. -/
theorem k2Symbol_steinberg (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    k2Symbol F (Units.mk0 a ha0)
        (Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) = 0 :=
  Subtype.ext (MilnorKRing.k2Symbol_steinberg a ha0 ha1)

/-- Symbol in `MilnorK F n` attached to a tuple. -/
noncomputable def symbolTuple (n : ℕ) (v : Fin n → Fˣ) : MilnorK F n :=
  MilnorKRing.symbolTuple F n v

/-- The range of `symbolTuple F n` spans `MilnorK F n`. -/
theorem symbolTuple_span (n : ℕ) :
    Submodule.span ℤ (Set.range (symbolTuple F n)) = ⊤ :=
  MilnorKRing.span_range_symbolTuple_eq_top F n

/-- Two `ℤ`-linear maps out of `MilnorK F n` agree when they agree on all tuple symbols. -/
theorem symbolTuple_ext {M : Type*} [AddCommGroup M] [Module ℤ M] {n : ℕ}
    (f g : MilnorK F n →ₗ[ℤ] M)
    (h : ∀ v : Fin n → Fˣ, f (symbolTuple F n v) = g (symbolTuple F n v)) :
    f = g :=
  MilnorKRing.symbolTuple_ext F f g h

/-- Multilinear symbol into `MilnorK F n`. -/
noncomputable def symbolMultilinear (n : ℕ) :
    MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => Additive Fˣ) (MilnorK F n) :=
  MilnorKRing.symbolMultilinear F n

/-- Evaluation of `symbolMultilinear` on `ofMul` coincides with `symbolTuple`. -/
theorem symbolMultilinear_apply (n : ℕ) (v : Fin n → Fˣ) :
    symbolMultilinear F n (fun i => Additive.ofMul (v i)) = symbolTuple F n v :=
  rfl

/-- `a * b` splits as a sum in one coordinate via multilinearity. -/
theorem symbolMultilinear_map_mul {n : ℕ} (v : Fin n → Additive Fˣ) (i : Fin n)
    (a b : Fˣ) :
    symbolMultilinear F n (Function.update v i (Additive.ofMul (a * b))) =
      symbolMultilinear F n (Function.update v i (Additive.ofMul a)) +
        symbolMultilinear F n (Function.update v i (Additive.ofMul b)) :=
  MilnorKRing.symbolMultilinear_map_mul (F := F) v i a b

/-- Power `a ^ c` is `c •` in one coordinate via multilinearity. -/
theorem symbolMultilinear_map_zsmul {n : ℕ} (v : Fin n → Additive Fˣ) (i : Fin n)
    (c : ℤ) (a : Fˣ) :
    symbolMultilinear F n (Function.update v i (Additive.ofMul (a ^ c))) =
      c • symbolMultilinear F n (Function.update v i (Additive.ofMul a)) :=
  MilnorKRing.symbolMultilinear_map_zsmul (F := F) v i c a

/-- The arity-two classical multilinear symbol on `![a, b]` coincides with
the `K₂` symbol `{a, b}`. -/
theorem symbolMultilinear_two_apply (a b : Fˣ) :
    symbolMultilinear F 2 ![Additive.ofMul a, Additive.ofMul b] = k2Symbol F a b :=
  Subtype.ext
    ((MilnorKRing.symbolMultilinear_apply_coe F 2 _).trans
      (MilnorKRing.k2Symbol_eq_symbolList_pair a b).symm)

/-- A `1` entry makes `symbolMultilinear` vanish. -/
theorem symbolMultilinear_update_one (n : ℕ) (m : Fin n → Additive Fˣ)
    (i : Fin n) :
    symbolMultilinear F n (Function.update m i 0) = 0 :=
  MilnorKRing.symbolMultilinear_map_one (F := F) m i

/-- An adjacent Steinberg pair makes `symbolMultilinear` vanish. -/
theorem symbolMultilinear_steinberg {n : ℕ} (v : Fin n → Additive Fˣ)
    (i : Fin n) (hi : i.val + 1 < n) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (h1 : Additive.toMul (v i) = Units.mk0 a ha0)
    (h2 : Additive.toMul (v ⟨i.val + 1, hi⟩) =
      Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)) :
    symbolMultilinear F n v = 0 :=
  MilnorKRing.symbolMultilinear_steinberg F v i hi a ha0 ha1 h1 h2

end MilnorK
