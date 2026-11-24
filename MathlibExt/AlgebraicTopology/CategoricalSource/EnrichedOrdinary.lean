/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

/-
Completed proof port; original Apache 2.0 author/license header retained.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Enriched/Ordinary/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only import paths and the TauCeti helper namespace are adapted.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Constant maps into enriched hom-objects

Let `C` be an ordinary category enriched over a Cartesian monoidal category `V`. A morphism
`f : a ⟶ b` of `C` gives, for every object `X` of `V`, the map `X ⟶ (a ⟶[V] b)` which is constant
at `f`, namely `toUnit X ≫ eHomEquiv V f`. This file shows that enriched composition of two such
constant maps is the constant map at the composite.

## Main declarations

* `CategoryTheory.toUnit_eHomEquiv_tensorHom_comp_eComp`: enriched composition of the constant
  maps at `f` and `g` is the constant map at `f ≫ g`.
-/

public section

universe v' v u' u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace CategoryTheory

variable {V : Type u'} [Category.{v'} V] [CartesianMonoidalCategory V] {C : Type u}
  [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Tensoring two maps which are constant at morphisms `f` and `g` and then composing gives the
map which is constant at `f ≫ g`. -/
@[reassoc]
lemma toUnit_eHomEquiv_tensorHom_comp_eComp {X Y : V} {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    ((toUnit X ≫ eHomEquiv V f) ⊗ₘ (toUnit Y ≫ eHomEquiv V g)) ≫ eComp V a b c =
      toUnit _ ≫ eHomEquiv V (f ≫ g) := by
  have : toUnit X ⊗ₘ toUnit Y = toUnit _ ≫ (λ_ (𝟙_ V)).inv :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (toUnit_unique _ _)
  rw [← tensorHom_comp_tensorHom_assoc, this, eHomEquiv_comp, Category.assoc]

end CategoryTheory
