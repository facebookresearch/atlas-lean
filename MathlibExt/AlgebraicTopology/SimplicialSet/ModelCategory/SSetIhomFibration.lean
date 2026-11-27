/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetIhomLift
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetFiberEdge
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Internal-hom fibrations and transport of lifting problems

For a monomorphism `i : A → B` of simplicial sets and a Kan fibration `p : X → Y`,
the internal-hom comparison
`Map(B,X) → Map(A,X) ×_(Map(A,Y)) Map(B,Y)` is a Kan fibration.

A commuting square with left map `i` and right map `p` determines a vertex of this
pullback target. Along an edge connecting two such vertices, existence of a diagonal
lift is equivalent for the two squares. All simplicial sets lie in the same universe;
the hypotheses concern the maps `i` and `p`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial SSet HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

variable {A B X Y : SSet.{u}}

/--
For a monomorphism `i : A → B` and a Kan fibration `p : X → Y`, the comparison
`Map(B,X) → Map(A,X) ×_(Map(A,Y)) Map(B,Y)` is a Kan fibration.
-/
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

/--
For two commuting squares with the same monomorphism `i` and Kan fibration `p`,
an edge between their vertices in the internal-hom pullback target makes their
existence of diagonal lifts equivalent.
-/
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
