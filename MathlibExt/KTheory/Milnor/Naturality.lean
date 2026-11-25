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

public import MathlibExt.KTheory.Milnor.Map
public import MathlibExt.KTheory.Milnor.Symbols
public import MathlibExt.KTheory.Milnor.K2

/-!
# Naturality of Milnor symbols for field homomorphisms

For a field homomorphism `f : F →+* K`, the induced map `MilnorKRing.map f`
is natural for symbols assembled as ordered list products.

This module retains a minimal canonical API:

* `map_symbolList`: general naturality of `symbolList` for an arbitrary list,
  `map f (symbolList F xs)` equals `symbolList K` of the mapped units;
* `map_symbolList_append_mul`: appended-list factorization,
  naturality for `l₁ ++ l₂` factors as a product of the two mapped
  symbol lists;
* `k2Symbol_eq_symbolList_pair`: K₂/list bridge identifying the binary
  symbol `k2Symbol a b` with `symbolList [a, b]`;
* `map_k2Symbol`: binary K₂ naturality of `k2Symbol` under `map f`.

Fixed-length specializations of the general list theorem and wrapper
compositions of the bridge with binary naturality are not retained.
-/

@[expose] public section

namespace MilnorK
namespace MilnorKRing

variable {F K : Type*} [Field F] [Field K]

/-- Naturality of `symbolList` for a field homomorphism. -/
theorem map_symbolList (f : F →+* K) (xs : List Fˣ) :
    map f (symbolList F xs) =
      symbolList K (xs.map (Units.map f.toMonoidHom)) := by
  induction xs with
  | nil =>
    simp only [symbolList_nil, List.map_nil, map_one]
  | cons hd tl ih =>
    calc
      map f (symbolList F (hd :: tl))
          = map f (symbol F hd * symbolList F tl) := rfl
      _ = map f (symbol F hd) * map f (symbolList F tl) := by
          rw [map_mul]
      _ = symbol K (Units.map f.toMonoidHom hd) *
            symbolList K (tl.map (Units.map f.toMonoidHom)) := by
          rw [map_symbol, ih]
      _ = symbolList K ((hd :: tl).map (Units.map f.toMonoidHom)) := by
          simp only [List.map_cons, symbolList_cons]

/-- Naturality for appended lists, in multiplicative factorization form. -/
theorem map_symbolList_append_mul (f : F →+* K) (l₁ l₂ : List Fˣ) :
    map f (symbolList F (l₁ ++ l₂)) =
      symbolList K (l₁.map (Units.map f.toMonoidHom)) *
        symbolList K (l₂.map (Units.map f.toMonoidHom)) := by
  calc
    map f (symbolList F (l₁ ++ l₂))
        = symbolList K ((l₁ ++ l₂).map (Units.map f.toMonoidHom)) := map_symbolList f _
    _ = symbolList K (l₁.map (Units.map f.toMonoidHom) ++ l₂.map (Units.map f.toMonoidHom)) := by
        rw [List.map_append]
    _ = symbolList K (l₁.map (Units.map f.toMonoidHom)) *
          symbolList K (l₂.map (Units.map f.toMonoidHom)) := by
        rw [symbolList_append]

/-- The binary symbol equals the symbol list of a pair, respecting order. -/
theorem k2Symbol_eq_symbolList_pair (a b : Fˣ) :
    k2Symbol (F := F) a b = symbolList F [a, b] := by
  calc
    k2Symbol a b = symbol F a * symbol F b := rfl
    _ = symbolList F [a, b] := (symbolList_pair F a b).symm

/-- Naturality of the binary K₂ symbol for a field homomorphism. -/
theorem map_k2Symbol (f : F →+* K) (a b : Fˣ) :
    map f (k2Symbol (F := F) a b) =
      k2Symbol (F := K) (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by
  calc
    map f (k2Symbol a b)
        = map f (symbol F a * symbol F b) := rfl
    _ = map f (symbol F a) * map f (symbol F b) := by rw [map_mul]
    _ = symbol K (Units.map f.toMonoidHom a) *
          symbol K (Units.map f.toMonoidHom b) := by rw [map_symbol, map_symbol]
    _ = k2Symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := rfl

end MilnorKRing
end MilnorK
