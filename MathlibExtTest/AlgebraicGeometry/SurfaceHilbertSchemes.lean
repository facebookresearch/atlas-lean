/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

universe u

variable {k : Type u} [Field k] {X T : Over (Spec (.of k))}

-- The re-exported names are the definitions of `ProjectiveSpace`.
example : @SurfaceHilbertSchemes.projectiveSpace = @ProjectiveSpace.projectiveSpace := rfl
example : @SurfaceHilbertSchemes.IsProjective = @ProjectiveSpace.IsProjective := rfl

-- The length is the rank at every point: a family of length zero is empty.
example (Z : PointSubscheme X T 0) : IsEmpty Z.Z := by
  refine ⟨fun z ↦ ?_⟩
  have h := (Z.i ≫ (prod.snd : prod X T ⟶ T).left).one_le_finrank_map z
  rw [Z.length] at h
  exact Nat.not_succ_le_zero 0 h

-- A family of positive length surjects onto its parameter scheme.
example {n : ℕ} (Z : PointSubscheme X T n) (hn : 0 < n) :
    Surjective (Z.i ≫ (prod.snd : prod X T ⟶ T).left) :=
  (Scheme.Hom.one_le_finrank_iff_surjective _).mp fun t ↦ by
    rw [Z.length t]
    exact hn

-- The length condition is not vacuous on parameter schemes without rational
-- points (such as `Spec ℂ` over `ℝ`): over any nonempty parameter scheme, the
-- empty closed subscheme only has length zero.
example [Nonempty T.left] {n : ℕ} (Z : PointSubscheme X T n) [IsEmpty Z.Z] :
    n = 0 := by
  by_contra hn
  have : Surjective (Z.i ≫ (prod.snd : prod X T ⟶ T).left) :=
    (Scheme.Hom.one_le_finrank_iff_surjective _).mp fun t ↦ by
      rw [Z.length t]
      exact Nat.one_le_iff_ne_zero.mpr hn
  obtain ⟨z, -⟩ :=
    (Z.i ≫ (prod.snd : prod X T ⟶ T).left).surjective (Classical.arbitrary T.left)
  exact isEmptyElim z

-- The universal property classifies families over every parameter scheme, with no
-- finite-type restriction on the test scheme.
example {n : ℕ} (M : HilbertPointsModel X n) (Z : PointSubscheme X T n) :
    ∃! f : T ⟶ M.H, ∃ a : Z.Z ⟶ M.universalFamily.Z,
      IsPullback a Z.i M.universalFamily.i (prod.map (𝟙 X) f).left :=
  M.universal T Z
