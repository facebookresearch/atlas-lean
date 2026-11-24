/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Toskua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Toskua
-/
module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Null-difference homotopy constructor

Thin adapter that turns a null-homotopy for `f - g` into a homotopy `f ~ g`.
It packages `Homotopy.nullHomotopy` with `Homotopy.equivSubZero`.
-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory HomologicalComplex

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {c : ComplexShape ι} {C D : HomologicalComplex V c}
variable {f g : C ⟶ D}

namespace Homotopy

/-- Adapter: a null-homotopy for `f - g` yields a homotopy `f ~ g`. -/
def ofNullHomotopicMapEqSub
    (hom : ∀ i j, C.X i ⟶ D.X j)
    (zero : ∀ i j, ¬c.Rel j i → hom i j = 0)
    (h_eq : _root_.Homotopy.nullHomotopicMap hom = f - g) :
    Homotopy f g :=
  _root_.Homotopy.equivSubZero.symm (h_eq ▸ _root_.Homotopy.nullHomotopy hom zero)

end Homotopy

/-- Homotopic maps are quasi-isomorphisms simultaneously. -/
lemma Homotopy.quasiIso_iff (ho : Homotopy f g)
    [∀ i, C.HasHomology i] [∀ i, D.HasHomology i] :
    QuasiIso f ↔ QuasiIso g := by
  simp only [_root_.quasiIso_iff, _root_.quasiIsoAt_iff_isIso_homologyMap, ho.homologyMap_eq]
