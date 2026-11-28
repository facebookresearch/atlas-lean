/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Precomposition and postcomposition of simplicial homotopies

Let `H` be a simplicial homotopy from `f : X→Y` to `g : X→Y`, with cylinder map `H.h : X ⊗
Δ[1] → Y`. Precomposing by `k : W→X` gives a homotopy from `k≫f` to `k≫g`, with cylinder `(k ⊗
𝟙 Δ[1])≫H.h`.

Postcomposing by `q : Y→Z` gives a homotopy from `f≫q` to `g≫q`, with cylinder `H.h≫q`. These
operations apply to arbitrary simplicial sets at a common universe.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

variable {W X Y Z : SSet.{u}} {f g : X ⟶ Y}

/-- Let `W,X,Y : SSet.{u}`, `f,g : X→Y`, and `H : SSet.Homotopy f g`. For `k : W→X`, `H.precomp k`
is a homotopy from `k≫f` to `k≫g`, obtained by precomposing the cylinder map with `k ⊗ 𝟙
Δ[1]`. -/
noncomputable def Homotopy.precomp (H : SSet.Homotopy f g)
    (k : W ⟶ X) : SSet.Homotopy (k ≫ f) (k ≫ g) := by
  let R := SSet.RelativeMorphism.Homotopy.precomp H
    (SSet.RelativeMorphism.botEquiv.symm k)
    (φψ := SSet.Subcomplex.isInitialBot.to _) (Subsingleton.elim _ _)
  exact
    { h := R.h
      h₀ := R.h₀
      h₁ := R.h₁
      rel := R.rel }

/-- For `H : SSet.Homotopy f g` between maps `X→Y` and `k : W→X`, `(H.precomp k).h = (k ▷ Δ[1]) ≫
H.h`. Here `k ▷ Δ[1]` is `k ⊗ 𝟙 Δ[1] : W ⊗ Δ[1] → X ⊗ Δ[1]`. -/
@[simp]
theorem Homotopy.precomp_h (H : SSet.Homotopy f g)
    (k : W ⟶ X) :
    (H.precomp k).h = (k ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
  rfl

/-- Let `X,Y,Z : SSet.{u}`, `f,g : X→Y`, and `H : SSet.Homotopy f g`. For `q : Y→Z`, `H.postcomp
q` is a homotopy from `f≫q` to `g≫q`, obtained by postcomposing its cylinder with `q`. -/
noncomputable def Homotopy.postcomp (H : SSet.Homotopy f g)
    (q : Y ⟶ Z) : SSet.Homotopy (f ≫ q) (g ≫ q) := by
  let R := SSet.RelativeMorphism.Homotopy.postcomp H
    (SSet.RelativeMorphism.botEquiv.symm q)
    (φψ := SSet.Subcomplex.isInitialBot.to _) (Subsingleton.elim _ _)
  exact
    { h := R.h
      h₀ := R.h₀
      h₁ := R.h₁
      rel := R.rel }

/-- For `H : SSet.Homotopy f g` between maps `X→Y` and `q : Y→Z`, `(H.postcomp q).h = H.h ≫ q` as
maps `X ⊗ Δ[1] → Z`. -/
@[simp]
theorem Homotopy.postcomp_h (H : SSet.Homotopy f g)
    (q : Y ⟶ Z) :
    (H.postcomp q).h = H.h ≫ q :=
  rfl

end SSet
