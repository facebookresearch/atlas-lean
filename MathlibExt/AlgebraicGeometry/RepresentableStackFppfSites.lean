/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RepresentableStackFppfModels
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# The actual small fppf site of a fibred stack

The Hom type is exactly the quotient of cartesian triangles by their
compatible two-isomorphisms. Identity/composition are fixed to the
preceding native recipes. Coverings are the original representable
flat/LFP maps, jointly surjective on their scheme test fibres. General
site arrows are allowed without a flatness hypothesis.

Source: Talpo--Vistoli arXiv:1410.1164v2, Section4.1 and Definition6.2.
The canonical Kfl functor and its sheaf adjunction are separate operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RepresentableStackFppfSites

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open _root_.AlgebraicGeometry.StackCycleGeometry _root_.AlgebraicGeometry.StackFibreModels
open RepresentableStackFppfModels

variable {S : Scheme.{0}}

/-- The ordinary categorical realization has the literal quotient Hom
type, with every identity/composite fixed by the native raw triangles. -/
structure NativeSiteCategory (R : Stack S) where
  operations : RawOperations R
  category : Category.{1} (Chart R)
  hom_eq : letI := category
    ∀ A B : Chart R, (A ⟶ B) = QuotientHom A B
  identity_eq : letI := category
    ∀ A : Chart R, Equiv.cast (hom_eq A A) (𝟙 A) = Quot.mk _ (operations.identity A)
  composition_eq : letI := category
    ∀ {A B C : Chart R} (f : A ⟶ B) (g : B ⟶ C),
    Equiv.cast (hom_eq A C) (f ≫ g) =
      Quot.mk _ (operations.compose
        (Quot.out (Equiv.cast (hom_eq A B) f)) (Quot.out (Equiv.cast (hom_eq B C) g)))

variable {R : Stack S} (N : NativeSiteCategory R)

def rawArrow {A B : Chart R} : letI := N.category; (A ⟶ B) → RawHom A B := by
  letI := N.category
  exact fun f => Quot.out (Equiv.cast (N.hom_eq A B) f)

/-- Coverings use all actual represented test fibres, including nilpotents. -/
def IsCover {ι : Type 3} (A : Chart R) (B : ι → Chart R) :
    letI := N.category; (∀ i, B i ⟶ A) → Prop := by
  letI := N.category
  exact fun f => ∀ (T : Over S) (y : A.domain.Fibre T),
    ∃ m : ∀ i, SchemeFibreModel (rawArrow N (f i)).map T y,
      (∀ i, Flat (m i).scheme.hom ∧ LocallyOfFinitePresentation (m i).scheme.hom) ∧
      ∀ x : T.left, ∃ (i : ι) (z : (m i).scheme.left), (m i).scheme.hom z = x

def precoverage : letI := N.category; Precoverage (Chart R) := by
  letI := N.category
  exact {
    coverings A := {s | ∃ (ι : Type 3) (B : ι → Chart R) (f : ∀ i, B i ⟶ A),
      IsCover N A B f ∧ s = Presieve.ofArrows B f} }

def topology : letI := N.category; GrothendieckTopology (Chart R) := by
  letI := N.category
  exact (precoverage N).toGrothendieck

end MathlibExt.AlgebraicGeometry.RepresentableStackFppfSites
