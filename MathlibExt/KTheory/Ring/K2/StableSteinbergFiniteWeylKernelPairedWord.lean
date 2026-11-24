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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylKernelMonomial
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylPermutationTrivial
public import MathlibExt.KTheory.Ring.K2.StableSteinbergFiniteWeylHurwitzTrace

/-! # Finite central-kernel paired-word bridge

For `n : ℕ` and `[Field F]`, every
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` is the head-left
`weightedWeylProd` of a paired word `wc : List (SwapLabel n × Fˣ)` whose label
projection has permutation product one.

The proof reuses the accepted bounded `List.ofFn` Weyl representation and
monomial product-one fact from
`finiteCentralKernel_list_monomial_prod_eq_one`, then the accepted
`Matrix.GeneralLinearGroup.finiteWeyl_monomial_perm_prod_eq_one` for the
corresponding swap product. Endpoints are packaged as `SwapLabel n` at
`⟨a k, ha k⟩`, `⟨b k, hb k⟩` with distinctness
`fun h => hab k (congrArg Fin.val h)`, and the paired word is
`List.ofFn fun k => (label k, u k)`. Pointwise `weylOfSwapLabel` and
`swapDenote` identifications are definitional/proof-irrelevant; orientation is
head-left throughout. Empty `m = 0` and ranks `n = 0, 1` are uniform.

Nonclaims: only the formal paired-word bridge; no finite-torus containment,
kernel generation, `ker ⊓ finiteStage`, TWT, inverse, naturality, normal-form,
or Matsumoto claim.
-/

@[expose] public section

namespace AlgebraicKTheory

universe u

/-- Recursive `wordProd` equals the `List.prod` of the mapped denotations. -/
private theorem wordProd_eq_prod_map {n : ℕ} (w : List (SwapLabel n)) :
    wordProd w = (w.map swapDenote).prod := by
  induction w with
  | nil => simp [wordProd]
  | cons x xs ih => simp [wordProd, ih]

/-- First projection of a paired `List.ofFn` word simplifies by `List.map_ofFn`. -/
private theorem map_fst_paired_ofFn {F : Type u} [Field F] {m n : ℕ}
    (label : Fin m → SwapLabel n) (u : Fin m → Fˣ) :
    (List.ofFn fun k => (label k, u k)).map Prod.fst = List.ofFn label := by
  rw [List.map_ofFn]
  rfl

/-- Finite central-kernel elements yield paired words with trivial label product.

Purpose: formal paired-word bridge for the Matsumoto comparison: from
`g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n` over `[Field F]`,
exhibit `wc : List (SwapLabel n × Fˣ)` with `g = weightedWeylProd wc` and
`wordProd (wc.map Prod.fst) = 1`. Orientation is head-left throughout,
matching `weightedWeylProd`, `wordProd`, and the accepted `List.ofFn` order.
The empty word gives `1 = 1 ∧ wordProd [] = 1`, uniform in ranks `n = 0, 1`.

Nonclaims: bridge only; no finite-torus containment, kernel generation,
`ker ⊓ finiteStage`, TWT, inverse, naturality, normal-form, or Matsumoto claim. -/
public theorem finiteCentralKernel_exists_paired_word
    {F : Type u} [Field F] (n : ℕ) (g : StableSteinberg F)
    (hg : g ∈ StableSteinberg.finiteCentralKernelSubgroup (R := F) n) :
    ∃ wc : List (SwapLabel n × Fˣ),
      g = weightedWeylProd wc ∧ wordProd (wc.map Prod.fst) = 1 := by
  obtain ⟨m, a, b, ha, hb, hab, u, hrepr, hmono⟩ :=
    finiteCentralKernel_list_monomial_prod_eq_one (F := F) n g hg
  have hperm : List.prod (List.ofFn (fun k : Fin m =>
      Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n))) = 1 :=
    Matrix.GeneralLinearGroup.finiteWeyl_monomial_perm_prod_eq_one
      a b ha hb hab u hmono
  let label : Fin m → SwapLabel n := fun k =>
    ⟨(⟨a k, ha k⟩, ⟨b k, hb k⟩), fun h => hab k (congrArg Fin.val h)⟩
  have hweyl_point : ∀ k : Fin m, weylOfSwapLabel (label k) (u k) =
      StableSteinberg.weyl (a k) (b k) (hab k) (u k) :=
    fun k => rfl
  have hswap_point : ∀ k : Fin m, swapDenote (label k) =
      Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n) :=
    fun k => rfl
  have hfun_weyl : (fun p : SwapLabel n × Fˣ => weylOfSwapLabel p.1 p.2) ∘
      (fun k : Fin m => (label k, u k)) =
      (fun k : Fin m => StableSteinberg.weyl (a k) (b k) (hab k) (u k)) :=
    funext fun k => hweyl_point k
  have hW : weightedWeylProd (List.ofFn fun k : Fin m => (label k, u k)) =
      (List.ofFn fun k : Fin m =>
        StableSteinberg.weyl (a k) (b k) (hab k) (u k)).prod := by
    unfold weightedWeylProd
    rw [List.map_ofFn, hfun_weyl]
  have hfun_swap : (swapDenote ∘ label) =
      (fun k : Fin m =>
        Equiv.swap (⟨a k, ha k⟩ : Fin n) (⟨b k, hb k⟩ : Fin n)) :=
    funext fun k => hswap_point k
  have hfst : (List.ofFn fun k : Fin m => (label k, u k)).map Prod.fst =
      List.ofFn label :=
    map_fst_paired_ofFn label u
  have hword : wordProd ((List.ofFn fun k : Fin m => (label k, u k)).map Prod.fst) = 1 := by
    rw [hfst, wordProd_eq_prod_map, List.map_ofFn, hfun_swap]
    exact hperm
  exact ⟨List.ofFn fun k : Fin m => (label k, u k), hrepr.trans hW.symm, hword⟩

end AlgebraicKTheory

end
