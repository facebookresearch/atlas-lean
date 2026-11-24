/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathFlagComparison
import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal

/-!
# Actual simplex operators on original last-front path maxima

The right join of a front simplex operator and the identity of the last
vertex acts by the original path direct image. Its maximum is the image
of the same original front maximum, for faces and degeneracies alike.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.PathMaximumOperators
open PathLastMaximum
variable {n m : ℕ}

/-- The actual ordinal-sum operator, fixing the last vertex and applying the supplied
operator to the front. -/
abbrev extension (θ : ⦋n⦌ ⟶ ⦋m⦌) : ⦋n + 1⦌ ⟶ ⦋m + 1⦌ :=
  AugmentedSimplexCategory.tensorHomOf θ (𝟙 ⦋0⦌)

/-- The genuine join operator sends each original front vertex to its supplied front image. -/
theorem extension_front (θ : ⦋n⦌ ⟶ ⦋m⦌) (j : Fin (n + 1)) :
    (extension θ).toOrderHom j.castSucc = (θ.toOrderHom j).castSucc := by
  change Fin.addCases (fun j => (θ.toOrderHom j).castAdd 1)
    (fun j : Fin 1 => j.natAdd (m + 1)) (j.castAdd 1) = (θ.toOrderHom j).castAdd 1
  exact Fin.addCases_left j

/-- The genuine right join operator retains the actual last vertex. -/
theorem extension_last (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    (extension θ).toOrderHom (Fin.last (n + 1)) = Fin.last (m + 1) := by
  change Fin.addCases (fun j => (θ.toOrderHom j).castAdd 1)
    (fun j : Fin 1 => j.natAdd (m + 1)) ((0 : Fin 1).natAdd (n + 1)) = (0 : Fin 1).natAdd (m + 1)
  exact Fin.addCases_right 0

/-- The lifted right join operator sends the same actual original front label to its lifted
image. -/
theorem lifted_front (θ : ⦋n⦌ ⟶ ⦋m⦌) (j : Fin (n + 1)) :
    (extension θ).toOrderHom.uliftMap (ULift.up.{u} j.castSucc) =
      ULift.up.{u} (θ.toOrderHom j).castSucc :=
  congrArg ULift.up (extension_front θ j)

/-- The lifted right join operator retains the same actual last endpoint. -/
theorem lifted_last (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    (extension θ).toOrderHom.uliftMap (ULift.up.{u} (Fin.last (n + 1))) =
      ULift.up.{u} (Fin.last (m + 1)) :=
  congrArg ULift.up (extension_last θ)

/-- The original direct-image last path under the actual right join simplex operator. -/
def image (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) (p : LastPath.{u} i) :
    LastPath.{u} (θ.toOrderHom i) where
  I := (extension θ).toOrderHom.uliftMap '' p.I
  left := by
    have h := Set.mem_image_of_mem (extension θ).toOrderHom.uliftMap p.left
    rw [lifted_front] at h
    exact h
  right := by
    have h := Set.mem_image_of_mem (extension θ).toOrderHom.uliftMap p.right
    rw [lifted_last] at h
    exact h
  left_le k := by
    rintro ⟨l, hl, rfl⟩
    have h := (extension θ).toOrderHom.uliftMap.monotone (p.left_le l hl)
    rw [lifted_front] at h
    exact h
  le_right k := by
    rintro ⟨l, hl, rfl⟩
    have h := (extension θ).toOrderHom.uliftMap.monotone (p.le_right l hl)
    rw [lifted_last] at h
    exact h

/-- The actual image retains the same whole path direct-image subset. -/
theorem image_I (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) (p : LastPath.{u} i) :
    (image θ i p).I = (extension θ).toOrderHom.uliftMap '' p.I := rfl

/-- The original front maximum commutes with every actual simplex operator, including
noninjective degeneracies. -/
theorem maximum_image (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) (p : LastPath.{u} i) :
    maximum (θ.toOrderHom i) (image θ i p) = θ.toOrderHom (maximum i p) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    have hJ := (mem_frontSet _ (image θ i p) j).mp hj
    obtain ⟨l, hl, hEq⟩ := hJ
    by_cases hL : l.down = Fin.last (n + 1)
    · have h : l = ULift.up.{u} (Fin.last (n + 1)) := ULift.ext hL
      subst l
      have hV := congrArg ULift.down hEq
      change (extension θ).toOrderHom (Fin.last (n + 1)) = j.castSucc at hV
      rw [extension_last] at hV
      exact False.elim ((ne_of_lt (Fin.castSucc_lt_last j)) hV.symm)
    · let k := l.down.castPred hL
      have hK : ULift.up.{u} k.castSucc = l := ULift.ext (Fin.castSucc_castPred _ hL)
      have hk : k ∈ frontSet i p := (mem_frontSet i p k).mpr (hK.symm ▸ hl)
      have hV := congrArg ULift.down hEq
      rw [← hK] at hV
      change (extension θ).toOrderHom k.castSucc = j.castSucc at hV
      rw [extension_front] at hV
      have hjK : θ.toOrderHom k = j := Fin.castSucc_injective _ hV
      rw [← hjK]
      exact θ.toOrderHom.monotone (le_maximum i p k hk)
  · apply le_maximum _ (image θ i p) (θ.toOrderHom (maximum i p))
    apply (mem_frontSet _ (image θ i p) _).mpr
    refine ⟨ULift.up.{u} (maximum i p).castSucc, (mem_frontSet i p _).mp (maximum_mem i p), ?_⟩
    exact congrArg ULift.up (extension_front θ (maximum i p))

/-- The whole original direct-image path functor for the actual right join operator. -/
def imageFunctor (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    LastPath.{u} i ⥤ LastPath.{u} (θ.toOrderHom i) where
  obj := image θ i
  map f := ⟨homOfLE (Set.image_mono f.hom.down.down)⟩

/-- The actual maximum functor is natural for every original front simplex operator. -/
theorem maximumFunctor_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    imageFunctor θ i ⋙ maximumFunctor (θ.toOrderHom i) =
      maximumFunctor i ⋙ θ.toOrderHom.uliftMap.monotone.functor := by
  refine Functor.ext (fun p => ULift.ext (maximum_image θ i p)) ?_
  intro p q f
  exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.PathMaximumOperators
