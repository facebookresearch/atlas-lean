/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomLift
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFiberEdge
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Internal-hom pullback fibration and edge transport

For `i : A ⟶ B` a monomorphism and `p : X ⟶ Y` a Kan fibration, the
comparison `ihomToPullback i p` is a fibration by the SM7/pushout-product
principle `SSet.fibration_pullbackObjObjπ`. As a consequence, existence of a
diagonal lift for a commuting square is constant along edges in the pullback
target, via `hasLift_iff_fiber_ihomToPullback_ne_bot` and
`fiber_neq_bot_iff_of_edge`.

No `KanComplex`, fibrancy, weak-equivalence, or anodyne assumptions are used.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial SSet HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {A B X Y : SSet.{u}}

/-- The internal-hom/pullback SM7 comparison map: for a mono `i : A ⟶ B`
and a Kan fibration `p : X ⟶ Y`, the pullback-hom `ihomToPullback i p`
is a fibration. Only the monomorphism and fibration hypotheses are required. -/
theorem fibration_ihomToPullback (i : A ⟶ B) (p : X ⟶ Y) [Mono i] [Fibration p] :
    Fibration (ihomToPullback i p) := by
  have h_eq :
      ihomToPullback i p =
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p).π :=
    rfl
  rw [h_eq]
  exact SSet.fibration_pullbackObjObjπ _

end SSet

namespace SSet.CommSq

variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
variable {t₀ : A ⟶ X} {b₀ : B ⟶ Y} {t₁ : A ⟶ X} {b₁ : B ⟶ Y}

/-- Edge transport of lift existence in the pullback target: given an edge
`e` oriented from `ihomToPullbackTgt₀Mk sq₀` to `ihomToPullbackTgt₀Mk sq₁` in
`pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y)`, lift existence
is transported between the two associated target vertices,
`sq₀.HasLift ↔ sq₁.HasLift`. -/
theorem hasLift_iff_of_edge_ihomToPullbackTgt
    [Mono i] [Fibration p]
    (sq₀ : CommSq t₀ i p b₀) (sq₁ : CommSq t₁ i p b₁)
    (e : (pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y) : SSet.{u}).Edge
      (ihomToPullbackTgt₀Mk sq₀) (ihomToPullbackTgt₀Mk sq₁)) :
    sq₀.HasLift ↔ sq₁.HasLift := by
  have h_fib : Fibration (ihomToPullback i p) := SSet.fibration_ihomToPullback i p
  calc sq₀.HasLift
      ↔ SSet.Subcomplex.fiber (ihomToPullback i p) (ihomToPullbackTgt₀Mk sq₀) ≠ ⊥ :=
        SSet.hasLift_iff_fiber_ihomToPullback_ne_bot sq₀
    _ ↔ SSet.Subcomplex.fiber (ihomToPullback i p) (ihomToPullbackTgt₀Mk sq₁) ≠ ⊥ :=
        SSet.Subcomplex.fiber_neq_bot_iff_of_edge (ihomToPullback i p) e
    _ ↔ sq₁.HasLift :=
        (SSet.hasLift_iff_fiber_ihomToPullback_ne_bot sq₁).symm

end SSet.CommSq
