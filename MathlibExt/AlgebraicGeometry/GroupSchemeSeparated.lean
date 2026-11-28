/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Group schemes over a field are separated

* `CategoryTheory.GrpObj.isPullback_lift_id_id`: in a cartesian monoidal category, the diagonal
  `G ⟶ G ⊗ G` of a group object `G` is the pullback of its unit `η : 𝟙_ C ⟶ G` along the division
  map `(a, b) ↦ a * b⁻¹`.
* `AlgebraicGeometry.isSeparated_of_grpObj_of_isClosedImmersion`: a group scheme over a scheme `S`
  whose identity section is a closed immersion is separated over `S` (one direction of the Stacks
  project, Groupoid Schemes, Lemma 39.6.1, Tag 047G).
* `AlgebraicGeometry.isSeparated_of_grpObj`: a group scheme over a field `k` is separated over
  `k` (Stacks project, Groupoid Schemes, Lemma 39.7.3, Tag 047L).

The proof is the one of the Stacks project: the identity section `e : Spec k ⟶ G` is a section of
the structure morphism to the one-point scheme `Spec k`, hence a closed immersion, and the
diagonal of `G` is its base change along the division map (Groupoid Schemes, Lemma 39.6.1,
Tag 047G).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

namespace CategoryTheory

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- In a cartesian monoidal category, the diagonal `lift (𝟙 G) (𝟙 G) : G ⟶ G ⊗ G` of a group
object `G` is the pullback of the unit `η : 𝟙_ C ⟶ G` along the division map
`lift (fst G G) (snd G G ≫ ι) ≫ μ`, that is, `(a, b) ↦ a * b⁻¹`. -/
theorem GrpObj.isPullback_lift_id_id :
    IsPullback (lift (𝟙 G) (𝟙 G)) (toUnit G) (lift (fst G G) (snd G G ≫ ι) ≫ μ) η[G] := by
  have hdiv (T : C) (a : T ⟶ G ⊗ G) :
      a ≫ lift (fst G G) (snd G G ≫ ι) ≫ μ = (a ≫ fst G G) * (a ≫ snd G G)⁻¹ := by
    rw [Hom.mul_def, Hom.inv_def, comp_lift_assoc, Category.assoc]
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst ≫ fst G G) ?_ ?_ ?_⟩⟩
  · rw [hdiv, lift_fst, lift_snd, mul_inv_cancel, Hom.one_def]
  · intro s
    have h : (s.fst ≫ fst G G) * (s.fst ≫ snd G G)⁻¹ = 1 := by
      rw [← hdiv, s.condition, Hom.one_def, toUnit_unique s.snd (toUnit _)]
    have h' : s.fst ≫ fst G G = s.fst ≫ snd G G := mul_inv_eq_one.1 h
    ext
    · simp
    · simp [h']
  · intro s
    exact toUnit_unique _ _
  · intro s m hm _
    rw [← hm, Category.assoc, lift_fst, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry

/-- A group scheme over a scheme `S` (`f : G ⟶ S` with a group object structure on `Over.mk f`)
whose identity section `S ⟶ G` is a closed immersion is separated over `S`: the diagonal of `G`
is the base change of the identity section along the division map
(`CategoryTheory.GrpObj.isPullback_lift_id_id`).

This is the "if" direction, for separatedness, of the Stacks project, Groupoid Schemes,
Lemma 39.6.1 (Tag 047G): "Let `S` be a scheme. Let `G` be a group scheme over `S`. Then `G → S` is
separated (resp. quasi-separated) if and only if the identity morphism `e : S → G` is a closed
immersion (resp. quasi-compact)." -/
theorem isSeparated_of_grpObj_of_isClosedImmersion {S G : Scheme.{u}} (f : G ⟶ S)
    [GrpObj (Over.mk f)] [IsClosedImmersion η[Over.mk f].left] : IsSeparated f := by
  have h := (GrpObj.isPullback_lift_id_id (Over.mk f)).map (Over.forget _)
  have hΔ : IsClosedImmersion (lift (𝟙 (Over.mk f)) (𝟙 (Over.mk f))).left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip ‹_›
  rw [Over.lift_left] at hΔ
  exact ⟨hΔ⟩

/-- **Group schemes over a field are separated.** Let `k` be a field and `G` a group scheme over
`k` (`f : G ⟶ Spec k` with a group object structure on `Over.mk f`). Then `f` is separated.

This is the Stacks project, Groupoid Schemes, Lemma 39.7.3 (Tag 047L): "Let `G` be a group scheme
over a field. Then `G` is a separated scheme." Its identity section is a section of the structure
morphism to the one-point scheme `Spec k`, hence a closed immersion
(`AlgebraicGeometry.isClosedImmersion_of_comp_eq_id`). -/
theorem isSeparated_of_grpObj {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] : IsSeparated f :=
  have : IsClosedImmersion η[Over.mk f].left :=
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of k)) f _ (Over.w η[Over.mk f])
  isSeparated_of_grpObj_of_isClosedImmersion f

end AlgebraicGeometry
