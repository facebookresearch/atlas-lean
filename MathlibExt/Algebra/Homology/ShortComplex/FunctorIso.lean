/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.Basic

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [Limits.HasZeroMorphisms D]
variable {E : Type u₃} [Category.{v₃} E] [Limits.HasZeroMorphisms E]

/-- Transport a natural isomorphism through `mapShortComplex`. -/
def mapShortComplexNatIso {F G : C ⥤ D} [PreservesZeroMorphisms F]
    [PreservesZeroMorphisms G] (e : F ≅ G) :
    F.mapShortComplex ≅ G.mapShortComplex :=
  NatIso.ofComponents (fun S => S.mapNatIso e) fun {S T} f => by
    apply ShortComplex.hom_ext
    · exact e.hom.naturality f.τ₁
    · exact e.hom.naturality f.τ₂
    · exact e.hom.naturality f.τ₃

/-- `mapShortComplex` preserves composition up to isomorphism. -/
def mapShortComplexCompIso (F : C ⥤ D) (G : D ⥤ E) [PreservesZeroMorphisms F]
    [PreservesZeroMorphisms G] [PreservesZeroMorphisms (F ⋙ G)] :
    F.mapShortComplex ⋙ G.mapShortComplex ≅ (F ⋙ G).mapShortComplex :=
  NatIso.ofComponents (fun S => Iso.refl _) fun {S T} f => by
    apply ShortComplex.hom_ext <;> simp [Functor.mapShortComplex]

end CategoryTheory.Functor
