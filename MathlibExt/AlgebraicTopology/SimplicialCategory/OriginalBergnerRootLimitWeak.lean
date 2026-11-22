/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFilteredBergnerRootWeak
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous

/-!
# The SAME original root is weak at a genuine original limit stage

The actual complete under-root limit cocone is preserved. Its original
cofibration transitions and genuine earlier weak root maps specialize
the proved original full filtered comparison without reducing native
factorization coordinates in the specialization.
-/

noncomputable section
universe u v
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.OriginalFilteredRoot
attribute [local instance] IsFiltered.isConnected

/-- Genuine original continuity and earlier original weak maps give the SAME weak root at a limit stage. -/
theorem weak_at_limit {C : Carrier.{u}} {J : Type v}
    [LinearOrder J] [OrderBot J] [UnivLE.{v, u}]
    (U : J ⥤ Under C) [U.IsWellOrderContinuous] (j : J) (hj : Order.IsSuccLimit j)
    (hC : ∀ {i k : J} (g : i ⟶ k), Bergner.cofibrations (U.map g).right)
    (hU : ∀ i, i < j → EnrichedDwyerKan.weakEquivalences (U.obj i).hom) :
    EnrichedDwyerKan.weakEquivalences (U.obj j).hom := by
  let _ : Nonempty (Set.Iio j) := ⟨⟨⊥, Order.IsSuccLimit.bot_lt hj⟩⟩
  let V : Set.Iio j ⥤ Under C := (Set.principalSegIio j).monotone.functor ⋙ U
  let s : Cocone V := (Set.principalSegIio j).cocone U
  have hs : IsColimit s := U.isColimitOfIsWellOrderContinuous j hj
  have hV {a b : Set.Iio j} (g : a ⟶ b) : Bergner.cofibrations (V.map g).right :=
    hC ((Set.principalSegIio j).monotone.functor.map g)
  let catV : Category.{v} (Set.Iio j) := inferInstance
  let filV : IsFiltered (Set.Iio j) := inferInstance
  let boundV : UnivLE.{v, u} := inferInstance
  let boundH : UnivLE.{v, u} := inferInstance
  have hW : EnrichedDwyerKan.weakEquivalences s.pt.hom :=
    @weak_of_cofibrations.{u, v, v} C (Set.Iio j) catV filV boundV boundH V s hs
      (fun {_a _b} g => hV g) (fun i => hU i.1 i.2)
  change EnrichedDwyerKan.weakEquivalences s.pt.hom
  exact hW

end CategoryTheory.SimplicialEnrichment.OriginalFilteredRoot
