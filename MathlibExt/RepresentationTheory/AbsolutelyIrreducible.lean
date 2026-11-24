/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Representation_AbsolutelyIrreducible.lean`
and
`Theorems/Thm_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible.lean`
and
`P2M/Sol/S_Representation_injective_liftBaseChange_of_isAbsolutelyIrreducible.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

open scoped TensorProduct

namespace Representation

universe uK u v w x

variable {k : Type u} [Field k] {G : Type v} [Group G] {V : Type w} [AddCommGroup V]
  [Module k V]

/-- The base change of a representation `ρ` of `G` on a `k`-module `V` to a
`k`-algebra `k'`: the representation of `G` on `k' ⊗[k] V` whose action is
the base change of each linear map `ρ g`. -/
def baseChange (k' : Type x) [CommRing k'] [Algebra k k'] (ρ : Representation k G V) :
    Representation k' G (k' ⊗[k] V) where
  toFun g := LinearMap.baseChange k' (ρ g)
  map_one' := by simp
  map_mul' := by
    intro g h
    simp [map_mul, LinearMap.baseChange_mul]

/-- The base-changed representation acts on a pure tensor by acting on the
module factor. -/
@[simp]
theorem baseChange_tmul (k' : Type x) [CommRing k'] [Algebra k k']
    (ρ : Representation k G V) (g : G) (a : k') (v : V) :
    baseChange k' ρ g (a ⊗ₜ[k] v) = a ⊗ₜ[k] (ρ g v) :=
  LinearMap.baseChange_tmul (ρ g) a v

variable {W : Type w} [AddCommGroup W] [Module k W]

/-- A representation `ρ` over a field `k` is absolutely irreducible if its
base change to every field extension `k'` (in the universe `Type uK`) is
irreducible. -/
class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible :
    ∀ k' : Type uK, ∀ _ : Field k', ∀ _ : Algebra k k', IsIrreducible (baseChange k' ρ)

variable {F : Type u} [Field F] {k₂ : Type u} [Field k₂] [Algebra F k₂]
  {G₂ : Type v} [Group G₂] {V₂ : Type w} [AddCommGroup V₂] [Module F V₂]
  {W₂ : Type x} [AddCommGroup W₂] [Module k₂ W₂] [Module F W₂] [IsScalarTower F k₂ W₂]

/-- If `ρ` is absolutely irreducible and `ι : V → W` is an injective map
intertwining `ρ` with a representation `τ` over a field extension, then the
base change of `ι` to that extension is injective. -/
theorem injective_liftBaseChange_of_isAbsolutelyIrreducible
    (ρ : Representation F G₂ V₂) [IsAbsolutelyIrreducible.{u} ρ]
    (τ : Representation k₂ G₂ W₂)
    (ι : V₂ →ₗ[F] W₂) (hι : Function.Injective ι)
    (hιG : ∀ (g : G₂) (v : V₂), ι (ρ g v) = τ g (ι v)) :
    Function.Injective (ι.liftBaseChange k₂) := by
  have hcomm : ∀ (g : G₂) (y : k₂ ⊗[F] V₂),
      ι.liftBaseChange k₂ ((ρ g).baseChange k₂ y) = τ g (ι.liftBaseChange k₂ y) := by
    intro g y
    induction y using TensorProduct.inductionOn with
    | tmul c v => simp [hιG]
    | add y z hy hz => simp [hy, hz]
  obtain ⟨f, hf⟩ : ∃ f : IntertwiningMap (baseChange k₂ ρ) τ,
      (⇑f : k₂ ⊗[F] V₂ → W₂) = ⇑(ι.liftBaseChange k₂) :=
    ⟨(ι.liftBaseChange k₂).intertwiningMap_of_isIntertwiningMap (baseChange k₂ ρ) τ
        (fun g y => hcomm g y), rfl⟩
  haveI : IsIrreducible (baseChange k₂ ρ) :=
    IsAbsolutelyIrreducible.absolutelyIrreducible k₂ inferInstance inferInstance
  rw [← hf]
  rcases IsIrreducible.injective_or_eq_zero f with h | h
  · exact h
  · have hV : ∀ v : V₂, v = 0 := fun v => hι (by
      have h1 := congrFun hf ((1 : k₂) ⊗ₜ[F] v)
      rw [h] at h1
      simpa using h1.symm)
    haveI : Subsingleton V₂ := ⟨fun a b => (hV a).trans (hV b).symm⟩
    exact Function.injective_of_subsingleton _

end Representation
