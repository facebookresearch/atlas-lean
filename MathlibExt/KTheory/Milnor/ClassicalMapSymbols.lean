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

public import MathlibExt.KTheory.Milnor.ClassicalMap
public import MathlibExt.KTheory.Milnor.ClassicalSymbols

/-!
# Functoriality of classical symbols under field homomorphisms

For a ring homomorphism `f : F →+* K` between fields, the functorial map
`MilnorK.map f n : MilnorK F n →ₗ[ℤ] MilnorK K n` is definitionally
`MilnorKRing.mapDegree f n` because `MilnorK F n = MilnorKRing.degree F n`.
On symbols it sends `{a₁,…,aₙ}` to `{f(a₁),…,f(aₙ)}`, where `f` is applied to
units via `Units.map f.toMonoidHom` and to additive units via
`MilnorKRing.unitsAddHom f`.

This file proves compatibility of `map` with the classical symbol
constructions `symbolList`, `symbol`, `k2Symbol`, `symbolTuple`, and
`symbolMultilinear`.  The proofs are direct from the degree-level API:
`map` is `mapDegree`, symbols are `*Degree` aliases, and naturality uses
`MilnorKRing.map_symbolList`, `map_symbol`, `map_k2Symbol`,
`symbolTuple_mapDegree`, and `symbolMultilinear_mapDegree`.  For `symbolList`
a cast by `List.length_map` aligns the dependent degree indices.

This module retains only the canonical `map_*` orientation for naturality
lemmas (e.g. `map_symbol`, `map_symbolTuple`, `map_symbolMultilinear`). Alias
forms with the symbol name first, such as `symbolTuple_map` and
`symbolMultilinear_map`, are deliberately omitted: they would be exact
restatements with no independent rewrite or API value and have no repository
consumers.

## Main results
* `MilnorK.map_symbolList`: `map f` sends `symbolList F xs` to `symbolList K`
  of the pointwise image under `Units.map`.
* `MilnorK.map_symbol`: `map f` sends `{a}` to `{f(a)}` in degree one.
* `MilnorK.map_k2Symbol`: `map f` sends `{a, b}` to `{f(a), f(b)}` in degree two.
* `MilnorK.map_symbolTuple`: `map f` sends `symbolTuple F n v` to
  `symbolTuple K n` with `v` post-composed by `Units.map`.
* `MilnorK.map_symbolMultilinear`: the additive/multilinear variant.
-/

@[expose] public section

namespace MilnorK

variable {F K : Type*} [Field F] [Field K]

/-- The functorial map sends `symbolList F xs = {xs}` to `symbolList K`
of the pointwise image `xs.map (Units.map f)`, up to a `length_map` cast. -/
theorem map_symbolList (f : F →+* K) (xs : List Fˣ) :
    map f xs.length (symbolList F xs) =
      cast (congrArg (fun n => MilnorK K n)
        (List.length_map (f := Units.map f.toMonoidHom) (as := xs)))
        (symbolList K (xs.map (Units.map f.toMonoidHom))) := by
  have h_len : (xs.map (Units.map f.toMonoidHom)).length = xs.length :=
    List.length_map (f := Units.map f.toMonoidHom) (as := xs)
  apply Subtype.ext
  calc (map f xs.length (symbolList F xs) : MilnorKRing K)
      = MilnorKRing.map f (symbolList F xs : MilnorKRing F) := by
        simp only [map, MilnorKRing.mapDegree_apply]
    _ = MilnorKRing.map f (MilnorKRing.symbolList F xs) := rfl
    _ = MilnorKRing.symbolList K (xs.map (Units.map f.toMonoidHom)) :=
        MilnorKRing.map_symbolList f xs
    _ = (symbolList K (xs.map (Units.map f.toMonoidHom)) : MilnorKRing K) := rfl
    _ = ((MilnorKRing.degreeCastEquiv K h_len
          (symbolList K (xs.map (Units.map f.toMonoidHom))) : MilnorK K xs.length) :
          MilnorKRing K) := by
        exact (MilnorKRing.degreeCastEquiv_val (F := K) h_len
          (symbolList K (xs.map (Units.map f.toMonoidHom)))).symm
    _ = ((cast (congrArg (fun n => MilnorK K n) h_len)
          (symbolList K (xs.map (Units.map f.toMonoidHom))) : MilnorK K xs.length) :
          MilnorKRing K) := by
        rw [← MilnorKRing.degreeCastEquiv_apply (F := K) h_len]

/-- The functorial map `MilnorK.map f 1` sends the degree-one symbol `{a}`
to `{f(a)}`, i.e. `symbol F a` maps to `symbol K (Units.map f a)`. -/
@[simp]
theorem map_symbol (f : F →+* K) (a : Fˣ) :
    map f 1 (symbol F a) = symbol K (Units.map f.toMonoidHom a) := by
  apply Subtype.ext
  calc (map f 1 (symbol F a) : MilnorKRing K)
      = MilnorKRing.map f (symbol F a : MilnorKRing F) := by
        simp only [map, MilnorKRing.mapDegree_apply]
    _ = MilnorKRing.map f (MilnorKRing.symbol F a) := rfl
    _ = MilnorKRing.symbol K (Units.map f.toMonoidHom a) :=
        MilnorKRing.map_symbol f a
    _ = (symbol K (Units.map f.toMonoidHom a) : MilnorKRing K) := rfl

/-- The functorial map `MilnorK.map f 2` sends the degree-two symbol
`{a, b}` to `{f(a), f(b)}`, i.e. `k2Symbol F a b` maps to the symbol with both
entries pushed forward by `Units.map f`. -/
@[simp]
theorem map_k2Symbol (f : F →+* K) (a b : Fˣ) :
    map f 2 (k2Symbol F a b) =
      k2Symbol K (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := by
  apply Subtype.ext
  calc (map f 2 (k2Symbol F a b) : MilnorKRing K)
      = MilnorKRing.map f (k2Symbol F a b : MilnorKRing F) := by
        simp only [map, MilnorKRing.mapDegree_apply]
    _ = MilnorKRing.map f (MilnorKRing.k2Symbol (F := F) a b) := rfl
    _ = MilnorKRing.k2Symbol (F := K) (Units.map f.toMonoidHom a)
          (Units.map f.toMonoidHom b) :=
        MilnorKRing.map_k2Symbol f a b
    _ = (k2Symbol K (Units.map f.toMonoidHom a)
          (Units.map f.toMonoidHom b) : MilnorKRing K) := rfl

/-- The functorial map sends `symbolTuple F n v = {v 0, …, v (n-1)}` to
`symbolTuple K n` with each component mapped by `Units.map f.toMonoidHom`. -/
@[simp]
theorem map_symbolTuple (f : F →+* K) (n : ℕ) (v : Fin n → Fˣ) :
    map f n (symbolTuple F n v) =
      symbolTuple K n (fun i => Units.map f.toMonoidHom (v i)) :=
  MilnorKRing.symbolTuple_mapDegree F f n v

/-- The multilinear symbol is functorial: `MilnorK.map f n` sends
`symbolMultilinear F n v` to `symbolMultilinear K n` with each additive unit
entry transformed by `MilnorKRing.unitsAddHom f`, i.e. `Additive.ofMul`
composed with `Units.map f`. -/
theorem map_symbolMultilinear (f : F →+* K) (n : ℕ) (v : Fin n → Additive Fˣ) :
    map f n (symbolMultilinear F n v) =
      symbolMultilinear K n (fun i => MilnorKRing.unitsAddHom f (v i)) :=
  MilnorKRing.symbolMultilinear_mapDegree F f n v

end MilnorK
