/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ProductSymmetry
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingZeroUnit
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The genuine Cartesian closed structure on the original marked carrier

The chosen products are the literal original marked products and their
original two projections. The unit is the maximally marked original
point. The native finite-product construction supplies all coherence
laws; the closed structure reuses the original marked internal Hom and
adjunction. These structures are named choices, not new global
instances. No marked-model Cartesian compatibility is asserted.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

namespace SSet.Marked

/-- The actual marked two-coordinate product cone has its full native universal property. -/
def prodIsLimit (X Y : Marked.{u}) : IsLimit (BinaryFan.mk (prodFst X Y) (prodSnd X Y)) :=
  BinaryFan.isLimitMk
    (fun s => prodLift s.fst s.snd)
    (fun _ => Hom.ext rfl)
    (fun _ => Hom.ext rfl)
    (fun s m hm₀ hm₁ => (prodHomEquiv s.pt X Y).injective (by
      apply Prod.ext
      · exact hm₀
      · exact hm₁))

/-- Native chosen finite products make the original marked carrier Cartesian monoidal without a
  global instance registration. -/
@[instance_reducible]
def cartesianMonoidalCategory : CartesianMonoidalCategory Marked.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    { cone := asEmptyCone (max (Δ[0] : SSet.{u}))
      isLimit := parameterZeroIsTerminal .maximal }
    (fun X Y => { cone := BinaryFan.mk (prodFst X Y) (prodSnd X Y), isLimit := prodIsLimit X Y })

attribute [local instance] cartesianMonoidalCategory

/-- The chosen tensor keeps the same original marked product object. -/
@[simp]
theorem cartesianMonoidal_tensor (X Y : Marked.{u}) : X ⊗ Y = prod X Y := rfl

/-- Its original tensor map is exactly the existing native simultaneous marked product map. -/
@[simp]
theorem cartesianMonoidal_tensorHom {X X' Y Y' : Marked.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    f ⊗ₘ g = prodMap f g := by
  apply Hom.ext
  rfl

/-- The chosen tensor unit is the original maximally marked zero simplex. -/
@[simp]
theorem cartesianMonoidal_unit : 𝟙_ Marked.{u} = max (Δ[0] : SSet.{u}) := rfl

/-- The same original marked internal Hom supplies the native closed structure, with no global
  instance registration. -/
@[instance_reducible]
def monoidalClosed : MonoidalClosed Marked.{u} where
  closed X :=
    { rightAdj := internalHomFunctor X
      adj := by
        change prodLeft X ⊣ internalHomFunctor X
        exact leftProductAdjunction X }

end SSet.Marked
