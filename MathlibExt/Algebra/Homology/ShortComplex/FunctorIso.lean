/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Functor isomorphisms on short complexes

For categories with zero morphisms, a zero-preserving functor acts on the
three objects and two maps of a short complex. A natural isomorphism
between two such functors gives the corresponding natural isomorphism on
short complexes. Successive application of two zero-preserving functors
agrees, up to the identity component isomorphisms, with application of their
zero-preserving composite. All category object and morphism universes are
independent.
-/

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Limits.HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [Limits.HasZeroMorphisms D]
variable {E : Type u₃} [Category.{v₃} E] [Limits.HasZeroMorphisms E]

/-- Let C and D have zero morphisms, F,G:C → D preserve zero morphisms,
and e:F ≅ G be a natural isomorphism. The induced natural isomorphism
between the functors on short complexes that apply F and G to all three
terms and maps, with components e at the three terms. -/
def mapShortComplexNatIso {F G : C ⥤ D} [PreservesZeroMorphisms F]
    [PreservesZeroMorphisms G] (e : F ≅ G) :
    F.mapShortComplex ≅ G.mapShortComplex :=
  NatIso.ofComponents (fun S => S.mapNatIso e) fun {S T} f => by
    apply ShortComplex.hom_ext
    · exact e.hom.naturality f.τ₁
    · exact e.hom.naturality f.τ₂
    · exact e.hom.naturality f.τ₃

/-- Let C,D,E have zero morphisms and F:C → D, G:D → E and G∘F preserve
zero morphisms. Successive application of F and G to short complexes
is naturally isomorphic to application of G∘F; its components are the
identity identifications of the three objects G(F(Sₐ)). -/
def mapShortComplexCompIso (F : C ⥤ D) (G : D ⥤ E) [PreservesZeroMorphisms F]
    [PreservesZeroMorphisms G] [PreservesZeroMorphisms (F ⋙ G)] :
    F.mapShortComplex ⋙ G.mapShortComplex ≅ (F ⋙ G).mapShortComplex :=
  NatIso.ofComponents (fun S => Iso.refl _) fun {S T} f => by
    apply ShortComplex.hom_ext <;> simp [Functor.mapShortComplex]

end CategoryTheory.Functor
