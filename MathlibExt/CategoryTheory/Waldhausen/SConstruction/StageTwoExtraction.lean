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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.LowDegree
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

/-!
# Stage-two extraction to cofiber sequences

Minimal functor `Stage C 2 ⥤ CofiberSequenceCategory C` from the accepted
central `(0, 1, 2)` data: objects use the public `horiz`/`vert` legs with
`ComposableArrows.mk₂` and `Stage.cofiber_zero_one_two`; morphisms use
`ComposableArrows.homMk₂` with the two stage naturality squares.

Reuses `FiniteStage.interval/horiz/vert`, `Stage`, `LowDegree`,
`CofiberSequenceCategory`, `ComposableArrows.mk₂/homMk₂`, and
`ObjectProperty.FullSubcategory.lift`. No inverse, equivalence, reindexing,
nerve, realization, Q/S comparison, or K/G-theory.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Let `C` have a zero object and a Waldhausen structure without gluing.
The functor `Stage C 2 ⥤ CofiberSequenceCategory C` sends a stage diagram
`A` to its three values `A(0,1) ⟶ A(0,2) ⟶ A(1,2)`. Write
`h01 : (0 : Fin 3) ≤ 1` and `h12 : (1 : Fin 3) ≤ 2` for the order proofs.
Its two legs are `A.obj.map (horiz h01 h12)` and
`A.obj.map (vert h01 h12)`. A stage morphism `φ` is sent to the three
components of `φ.hom` at `interval 0 1 h01`, `interval 0 2 (h01.trans h12)`,
and `interval 1 2 h12`, with the two naturality squares. Here `A(i,j)`
denotes the value of `A.obj` on the interval `(i,j)`. This is extraction
of the supplied diagram, not a claimed inverse or equivalence. -/
def stageTwoExtraction : Stage C 2 ⥤ CofiberSequenceCategory C :=
  (cofiberSequenceProperty C).lift
    ((⟨fun A => ComposableArrows.mk₂
        (A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
          (show (1 : Fin 3) ≤ 2 by decide)))
        (A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
          (show (1 : Fin 3) ≤ 2 by decide))),
      fun φ => ComposableArrows.homMk₂
        (φ.hom.app (interval (0 : Fin 3) 1 (by decide)))
        (φ.hom.app (interval (0 : Fin 3) 2 (by decide)))
        (φ.hom.app (interval (1 : Fin 3) 2 (by decide)))
        (by exact φ.hom.naturality _)
        (by exact φ.hom.naturality _),
      fun A => by ext <;> rfl,
      fun φ ψ => by ext <;> rfl⟩ :
      Stage C 2 ⥤ ComposableArrows C 2))
    (fun A => Stage.cofiber_zero_one_two C A)

/-- Object `0 → 1` leg recovers the source `horiz` map. -/
@[simp]
theorem stageTwoExtraction_map'_zero_one (A : Stage C 2) :
    ComposableArrows.map' ((CofiberSequenceCategory.forget C).obj
      ((stageTwoExtraction C).obj A)) 0 1 =
      A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)) := rfl

/-- Object `1 → 2` leg recovers the source `vert` map. -/
@[simp]
theorem stageTwoExtraction_map'_one_two (A : Stage C 2) :
    ComposableArrows.map' ((CofiberSequenceCategory.forget C).obj
      ((stageTwoExtraction C).obj A)) 1 2 =
      A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)) := rfl

/-- Morphism component at `0` recovers the `(0, 1)` interval component. -/
@[simp]
theorem stageTwoExtraction_app_zero {A B : Stage C 2} (φ : A ⟶ B) :
    ComposableArrows.app' ((CofiberSequenceCategory.forget C).map
      ((stageTwoExtraction C).map φ)) 0 =
      φ.hom.app (interval (0 : Fin 3) 1 (by decide)) := rfl

/-- Morphism component at `1` recovers the `(0, 2)` interval component. -/
@[simp]
theorem stageTwoExtraction_app_one {A B : Stage C 2} (φ : A ⟶ B) :
    ComposableArrows.app' ((CofiberSequenceCategory.forget C).map
      ((stageTwoExtraction C).map φ)) 1 =
      φ.hom.app (interval (0 : Fin 3) 2 (by decide)) := rfl

/-- Morphism component at `2` recovers the `(1, 2)` interval component. -/
@[simp]
theorem stageTwoExtraction_app_two {A B : Stage C 2} (φ : A ⟶ B) :
    ComposableArrows.app' ((CofiberSequenceCategory.forget C).map
      ((stageTwoExtraction C).map φ)) 2 =
      φ.hom.app (interval (1 : Fin 3) 2 (by decide)) := rfl

end CategoryTheory.Waldhausen.SConstruction
