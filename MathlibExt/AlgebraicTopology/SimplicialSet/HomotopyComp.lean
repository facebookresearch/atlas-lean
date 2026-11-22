/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Whiskering of simplicial homotopies

The canonical precomposition and postcomposition (whiskering) operations
for ordinary simplicial homotopies `SSet.Homotopy`, obtained from the
relative whiskering operations `SSet.RelativeMorphism.Homotopy.precomp`
and `SSet.RelativeMorphism.Homotopy.postcomp` over the bottom
subcomplexes:

Both cylinder formulas hold definitionally (`rfl`).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

variable {W X Y Z : SSet.{u}} {f g : X ⟶ Y}

/-- Precompose an ordinary simplicial homotopy in its source. -/
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

/-- The cylinder of a precomposed ordinary homotopy is obtained by
whiskering the source map with the simplicial interval. -/
@[simp]
theorem Homotopy.precomp_h (H : SSet.Homotopy f g)
    (k : W ⟶ X) :
    (H.precomp k).h = (k ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
  rfl

/-- Postcompose an ordinary simplicial homotopy with a map of its
target. -/
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

/-- The cylinder of a postcomposed ordinary homotopy is the original
cylinder followed by the map. -/
@[simp]
theorem Homotopy.postcomp_h (H : SSet.Homotopy f g)
    (q : Y ⟶ Z) :
    (H.postcomp q).h = H.h ≫ q :=
  rfl

end SSet
