/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontOperators

/-!
# Actual injected right-join ordinal embeddings

A genuinely injective original front operator has an injective right
join, with the original last vertex retained. The same whole lifted
map is an order embedding. This is geometric input for the actual cube
face range, without a supplied quotient injectivity outcome.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeOrdinalEmbedding
open PathMaximumOperators
variable {n m : ℕ}

/-- An injective monotone map between actual linear orders is its genuine order embedding. -/
def ofInjective {J : Type u} {K : Type v} [LinearOrder J] [LinearOrder K]
    (f : J →o K) (hf : Function.Injective f) : J ↪o K where
  toFun := f
  inj' := hf
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      by_contra hab
      have hba : b ≤ a := le_of_lt (not_le.mp hab)
      have he : a = b := hf (le_antisymm h (f.monotone hba))
      exact hab (he ▸ le_rfl)
    · intro h
      exact f.monotone h

/-- The actual original right-join extension of a genuinely injective front operator is
injective. -/
theorem extension_injective (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) :
    Function.Injective (extension θ).toOrderHom := by
  intro a b hab
  cases a using Fin.lastCases with
  | last =>
    cases b using Fin.lastCases with
    | last => rfl
    | cast j =>
      have h : Fin.last (m + 1) = (θ.toOrderHom j).castSucc :=
        (extension_last θ).symm.trans (hab.trans (extension_front θ j))
      exact False.elim ((ne_of_lt (Fin.castSucc_lt_last _)) h.symm)
  | cast i =>
    cases b using Fin.lastCases with
    | last =>
      have h : (θ.toOrderHom i).castSucc = Fin.last (m + 1) :=
        (extension_front θ i).symm.trans (hab.trans (extension_last θ))
      exact False.elim ((ne_of_lt (Fin.castSucc_lt_last _)) h)
    | cast j =>
      have h : (θ.toOrderHom i).castSucc = (θ.toOrderHom j).castSucc :=
        (extension_front θ i).symm.trans (hab.trans (extension_front θ j))
      exact congrArg Fin.castSucc (hθ (Fin.castSucc_injective _ h))

/-- The genuine finite right-join order embedding of the same original operator. -/
def rightJoin (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) : Fin (n + 2) ↪o Fin (m + 2) :=
  ofInjective (extension θ).toOrderHom (extension_injective θ hθ)

/-- The whole original lifted right-join embedding on the actual path labels. -/
def lifted (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom) :
    ULift.{u} (Fin (n + 2)) ↪o ULift.{u} (Fin (m + 2)) where
  toFun x := ULift.up ((rightJoin θ hθ) x.down)
  inj' _ _ h := ULift.ext ((rightJoin θ hθ).injective (congrArg ULift.down h))
  map_rel_iff' := (rightJoin θ hθ).map_rel_iff'

/-- The actual lifted order embedding is the very same original right-join path-label
function used by the
  quotient operator. -/
theorem lifted_apply (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    (x : ULift.{u} (Fin (n + 2))) : lifted θ hθ x = (extension θ).toOrderHom.uliftMap x := rfl

end CategoryTheory.CoherentRealization.RightCubeOrdinalEmbedding
