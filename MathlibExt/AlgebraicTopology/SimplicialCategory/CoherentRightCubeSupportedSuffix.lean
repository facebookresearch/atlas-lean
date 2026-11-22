/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeSupport
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeOrdinalEmbedding
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOrderEmbeddingFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport

/-!
# Actual original supported suffix preimages of right-cube faces

When the retained original support lies in an injected front range,
the original suffix chain has a genuine embedding preimage. Its two
individual endpoint witnesses and every scalar path subset are retained.
The construction reuses the actual coherent embedding-face inverse.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeSupportedSuffix
open PathLastMaximum PathMaximumOperators RightCubeReduction RightCubeSupport
  RightCubeIntervalCuts RightCubeOrdinalEmbedding
variable {n m : ℕ}

/-- The whole original retained suffix lies in the same actual injected right-join range. -/
theorem suffix_in_range (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (hp : support p ⊆ Set.range θ.toOrderHom) (k : Fin (q.unop.len + 1)) :
    (suffix (initialMaximum p) (p.obj k) (initialMaximum_mem p k)).I ⊆ Set.range (lifted.{u} θ hθ) := by
  intro x hx
  change x ∈ (p.obj k).I ∧ ULift.up.{u} (initialMaximum p).castSucc ≤ x at hx
  cases x with
  | up x =>
    cases x using Fin.lastCases with
    | last => exact ⟨ULift.up.{u} (Fin.last (n + 1)), lifted_last θ⟩
    | cast j =>
      obtain ⟨i, hi⟩ := hp ⟨(p.map (homOfLE (Fin.le_last k))).hom.down.down hx.1, hx.2⟩
      exact ⟨ULift.up.{u} i.castSucc,
        (lifted_front θ i).trans (congrArg (fun j : Fin (m + 1) => ULift.up.{u} j.castSucc) hi)⟩

/-- The actual supported suffix chain is retargeted to the supplied original embedding endpoint witnesses. -/
def retargeted (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (i : Fin (n + 1)) (hi : θ.toOrderHom i = initialMaximum p) :
    (nerve (SimplicialThickening.Path (lifted.{u} θ hθ (ULift.up i.castSucc))
      (lifted.{u} θ hθ (ULift.up (Fin.last (n + 1)))))).obj q :=
  suffixChain (initialMaximum p) p (initialMaximum_mem p) ⋙ PathEndpointTransport.retarget
    ((lifted_front θ i).trans (congrArg (fun j : Fin (m + 1) => ULift.up.{u} j.castSucc) hi)).symm
    (lifted_last θ).symm

/-- The genuine whole original suffix preimage at the supplied original front label and literal source last vertex. -/
def preimage (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (i : Fin (n + 1)) (hi : θ.toOrderHom i = initialMaximum p)
    (hp : support p ⊆ Set.range θ.toOrderHom) : (nerve (LastPath.{u} i)).obj q :=
  OrderEmbeddingFace.preimageChain (lifted.{u} θ hθ) (ULift.up i.castSucc) (ULift.up (Fin.last (n + 1)))
    ⟨retargeted θ hθ p i hi, fun k => suffix_in_range θ hθ p hp k⟩

/-- The whole original preimage path is exactly the actual inverse-image subset of that same retained suffix. -/
theorem preimage_I (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (i : Fin (n + 1)) (hi : θ.toOrderHom i = initialMaximum p)
    (hp : support p ⊆ Set.range θ.toOrderHom) (k : Fin (q.unop.len + 1)) :
    ((preimage θ hθ p i hi hp).obj k).I = (lifted.{u} θ hθ) ⁻¹'
      (suffix (initialMaximum p) (p.obj k) (initialMaximum_mem p k)).I := rfl

/-- The actual original supported suffix is recovered as a whole path subset after its genuine embedding preimage. -/
theorem image_I (θ : ⦋n⦌ ⟶ ⦋m⦌) (hθ : Function.Injective θ.toOrderHom)
    {q : SimplexCategoryᵒᵖ} (p : (nerve (LastPath.{u} (0 : Fin (m + 1)))).obj q)
    (i : Fin (n + 1)) (hi : θ.toOrderHom i = initialMaximum p)
    (hp : support p ⊆ Set.range θ.toOrderHom) (k : Fin (q.unop.len + 1)) :
    (lifted.{u} θ hθ) '' ((preimage θ hθ p i hi hp).obj k).I =
      (suffix (initialMaximum p) (p.obj k) (initialMaximum_mem p k)).I :=
  Set.image_preimage_eq_of_subset (suffix_in_range θ hθ p hp k)

end CategoryTheory.CoherentRealization.RightCubeSupportedSuffix
