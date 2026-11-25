/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Comonad.CobarCosimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataRev
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented

/-!
# Comonad bar resolutions

For a comonad `G` on a category `C` and an object `A`, this file constructs
the canonical augmented simplicial object with degree `n` object
`G^(n+1) A`. Its faces and degeneracies are the source-ordered counit and
comultiplication insertions, and its augmentation is the counit `G A ⟶ A`.

The construction uses the existing comonad insertion calculus and the generic
conversion from simplicial data. It assumes no comodule structure on `A`.

Mathematical source: Charles A. Weibel, *An Introduction to Homological
Algebra*, §8.6.4.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory Opposite

namespace CategoryTheory.Comonad

variable {C : Type u} [Category.{v} C]

/-- Iterated comonad powers add on objects. -/
theorem comonadPow_add_obj (G : Comonad C) (m n : ℕ) (A : C) :
    (comonadPow G (m + n)).obj A =
      (comonadPow G m).obj ((comonadPow G n).obj A) := by
  induction m generalizing A with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add]
      change (comonadPow G (m + n)).obj (G.toFunctor.obj A) =
        (comonadPow G m).obj
          (G.toFunctor.obj ((comonadPow G n).obj A))
      rw [ih (G.toFunctor.obj A), comonadPow_obj_G_comm G n A]

/-- Raw simplicial data on the iterated comonad. Raw insertion positions are
reversed in `resolutionData` to obtain Weibel's source ordering. -/
noncomputable def resolutionRawData (G : Comonad C) (A : C) :
    SimplicialObject.Data C where
  obj n := (comonadPow G (n + 1)).obj A
  δ i := epsilonAtPos G (i := i) _ A
  σ i := deltaAtPos G _ i A
  δ_comp_δ := by
    intro n i j h
    exact (epsilonAtPos_deg_deg G (n + 1) i j h A).symm
  δ_comp_σ_of_le := by
    intro n i j h
    exact deltaAtPos_epsilonAtPos_succ_castSucc_of_le
      G (n + 1) j i h A
  δ_comp_σ_self := by
    intro n i
    exact deltaAtPos_epsilonAtPos_castSucc G (n + 1) i A
  δ_comp_σ_succ := by
    intro n i
    exact deltaAtPos_epsilonAtPos_succ G (n + 1) i A
  δ_comp_σ_of_gt := by
    intro n i j h
    exact deltaAtPos_epsilonAtPos_castSucc_succ_of_lt
      G (n + 1) j i h A
  σ_comp_σ := by
    intro n i j h
    exact (deltaAtPos_face_face G (n + 1) i j h A).symm

/-- Source-ordered simplicial data of the comonad resolution. -/
noncomputable def resolutionData (G : Comonad C) (A : C) :
    SimplicialObject.Data C :=
  (resolutionRawData G A).rev

@[simp]
theorem resolutionData_obj (G : Comonad C) (A : C) (n : ℕ) :
    (resolutionData G A).obj n = (comonadPow G (n + 1)).obj A :=
  rfl

/-- Faces are the source-ordered counit insertions. -/
@[simp]
theorem resolutionData_δ (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 2)) :
    (resolutionData G A).δ i = cobarEpsilonAtPos G (n + 1) i A :=
  rfl

/-- Degeneracies are the source-ordered comultiplication insertions. -/
@[simp]
theorem resolutionData_σ (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 1)) :
    (resolutionData G A).σ i = cobarDeltaAtPos G (n + 1) i A :=
  rfl

/-- The simplicial bar resolution associated to a comonad and an object. -/
noncomputable def resolutionBar (G : Comonad C) (A : C) :
    SimplicialObject C :=
  (resolutionData G A).toSimplicialObject

@[simp]
theorem resolutionBar_obj (G : Comonad C) (A : C) (n : ℕ) :
    (resolutionBar G A).obj (op (SimplexCategory.mk n)) =
      (comonadPow G (n + 1)).obj A :=
  rfl

/-- Canonical level identification of the bar resolution with the iterated
comonad power. -/
noncomputable def resolutionBarObjIso (G : Comonad C) (A : C) (n : ℕ) :
    (resolutionBar G A).obj (op (SimplexCategory.mk n)) ≅
      (comonadPow G (n + 1)).obj A := by
  change (comonadPow G (n + 1)).obj A ≅
    (comonadPow G (n + 1)).obj A
  exact Iso.refl _

/-- Face maps of the bar resolution use Weibel's ordering. -/
@[simp]
theorem resolutionBar_map_δ_op (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 2)) :
    (resolutionBar G A).map (SimplexCategory.δ i).op =
      cobarEpsilonAtPos G (n + 1) i A := by
  exact SimplicialObject.Data.toSimplicialObject_map_δ
    (resolutionData G A) i

/-- Degeneracy maps of the bar resolution use Weibel's ordering. -/
@[simp]
theorem resolutionBar_map_σ_op (G : Comonad C) (A : C) {n : ℕ}
    (i : Fin (n + 1)) :
    (resolutionBar G A).map (SimplexCategory.σ i).op =
      cobarDeltaAtPos G (n + 1) i A := by
  exact SimplicialObject.Data.toSimplicialObject_map_σ
    (resolutionData G A) i

/-- The level identifications intertwine every face with the source-ordered
counit insertion. -/
@[reassoc]
theorem resolutionBarObjIso_hom_face (G : Comonad C) (A : C)
    (n : ℕ) (i : Fin (n + 2)) :
    (resolutionBarObjIso G A (n + 1)).hom ≫
        cobarEpsilonAtPos G (n + 1) i A =
      (resolutionBar G A).map (SimplexCategory.δ i).op ≫
        (resolutionBarObjIso G A n).hom := by
  rw [resolutionBar_map_δ_op]
  simp [resolutionBarObjIso]

/-- The level identifications intertwine every degeneracy with the
source-ordered comultiplication insertion. -/
@[reassoc]
theorem resolutionBarObjIso_hom_degeneracy (G : Comonad C) (A : C)
    (n : ℕ) (i : Fin (n + 1)) :
    (resolutionBarObjIso G A n).hom ≫
        cobarDeltaAtPos G (n + 1) i A =
      (resolutionBar G A).map (SimplexCategory.σ i).op ≫
        (resolutionBarObjIso G A (n + 1)).hom := by
  rw [resolutionBar_map_σ_op]
  simp [resolutionBarObjIso]

/-- In degree one, the zeroth face is `ε_(G A)`. -/
theorem resolutionBar_face_zero_degree_one (G : Comonad C) (A : C) :
    (resolutionBar G A).map
      (SimplexCategory.δ (0 : Fin 2)).op =
        G.ε.app (G.toFunctor.obj A) := by
  rw [resolutionBar_map_δ_op]
  rfl

/-- In degree one, the first face is `G(ε_A)`. -/
theorem resolutionBar_face_one_degree_one (G : Comonad C) (A : C) :
    (resolutionBar G A).map
      (SimplexCategory.δ (1 : Fin 2)).op =
        G.toFunctor.map (G.ε.app A) := by
  rw [resolutionBar_map_δ_op]
  rfl

/-- The degree-zero degeneracy is the comultiplication `δ_A`. -/
theorem resolutionBar_degeneracy_zero (G : Comonad C) (A : C) :
    (resolutionBar G A).map
      (SimplexCategory.σ (0 : Fin 1)).op = G.δ.app A := by
  rw [resolutionBar_map_σ_op]
  rfl

/-- The counit equalizes the two degree-one faces. -/
theorem resolutionData_counit_isBalanced (G : Comonad C) (A : C) :
    SimplicialObject.Data.IsBalanced
      (X := resolutionData G A) (G.ε.app A) := by
  change G.ε.app (G.toFunctor.obj A) ≫ G.ε.app A =
    G.toFunctor.map (G.ε.app A) ≫ G.ε.app A
  exact (G.ε.naturality (G.ε.app A)).symm

/-- The augmented simplicial data of the comonad resolution. -/
noncomputable def resolutionAugmentedData (G : Comonad C) (A : C) :
    SimplicialObject.Data.Augmented C :=
  SimplicialObject.Data.Augmented.augment
    (resolutionData G A) A (G.ε.app A)
      (resolutionData_counit_isBalanced G A)

/-- A map of carrier objects induces a morphism of raw resolution data. -/
noncomputable def resolutionRawHom (G : Comonad C) {A B : C}
    (f : A ⟶ B) : resolutionRawData G A ⟶ resolutionRawData G B where
  app n := (comonadPow G (n + 1)).map f
  w_δ i := epsilonAtPos_naturality G _ i f
  w_σ i := deltaAtPos_naturality G _ i f

/-- A map of carrier objects induces a morphism of source-ordered data. -/
noncomputable def resolutionDataHom (G : Comonad C) {A B : C}
    (f : A ⟶ B) : resolutionData G A ⟶ resolutionData G B :=
  SimplicialObject.Data.revHom (resolutionRawHom G f)

@[simp]
theorem resolutionDataHom_app (G : Comonad C) {A B : C}
    (f : A ⟶ B) (n : ℕ) :
    (resolutionDataHom G f).app n = (comonadPow G (n + 1)).map f :=
  rfl

@[simp]
theorem resolutionDataHom_id (G : Comonad C) (A : C) :
    resolutionDataHom G (𝟙 A) = 𝟙 (resolutionData G A) := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp

theorem resolutionDataHom_comp (G : Comonad C) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) :
    resolutionDataHom G (f ≫ g) =
      resolutionDataHom G f ≫ resolutionDataHom G g := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp

/-- A carrier map induces a morphism of augmented resolution data. -/
noncomputable def resolutionAugmentedDataHom (G : Comonad C) {A B : C}
    (f : A ⟶ B) :
    resolutionAugmentedData G A ⟶ resolutionAugmentedData G B where
  left := resolutionDataHom G f
  right := f
  w := by
    apply SimplicialObject.Data.hom_eq_of_app_zero_eq
    change G.toFunctor.map f ≫ G.ε.app B = G.ε.app A ≫ f
    exact G.ε.naturality f

@[simp]
theorem resolutionAugmentedDataHom_id (G : Comonad C) (A : C) :
    resolutionAugmentedDataHom G (𝟙 A) =
      𝟙 (resolutionAugmentedData G A) := by
  apply Comma.hom_ext
  · exact resolutionDataHom_id G A
  · rfl

theorem resolutionAugmentedDataHom_comp (G : Comonad C) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) :
    resolutionAugmentedDataHom G (f ≫ g) =
      resolutionAugmentedDataHom G f ≫
        resolutionAugmentedDataHom G g := by
  apply Comma.hom_ext
  · exact resolutionDataHom_comp G f g
  · rfl

/-- The augmented comonad resolution as a functor of the carrier object. -/
noncomputable def resolutionAugmentedDataFunctor (G : Comonad C) :
    C ⥤ SimplicialObject.Data.Augmented C where
  obj A := resolutionAugmentedData G A
  map f := resolutionAugmentedDataHom G f
  map_id A := resolutionAugmentedDataHom_id G A
  map_comp f g := resolutionAugmentedDataHom_comp G f g

/-- The genuine augmented comonad resolution functor. -/
noncomputable def resolutionAugmentedFunctor (G : Comonad C) :
    C ⥤ SimplicialObject.Augmented C :=
  resolutionAugmentedDataFunctor G ⋙
    SimplicialObject.Data.Augmented.toSimplicialFunctor

/-- The canonical augmented comonad resolution. -/
noncomputable def resolutionAugmented (G : Comonad C) (A : C) :
    SimplicialObject.Augmented C :=
  (resolutionAugmentedFunctor G).obj A

@[simp]
theorem resolutionAugmented_point (G : Comonad C) (A : C) :
    (resolutionAugmented G A).right = A := by
  unfold resolutionAugmented resolutionAugmentedFunctor
  exact SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_right
    (resolutionAugmentedData G A)

@[simp]
theorem resolutionAugmented_left (G : Comonad C) (A : C) :
    (resolutionAugmented G A).left = resolutionBar G A := by
  unfold resolutionAugmented resolutionAugmentedFunctor resolutionBar
  exact SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_left
    (resolutionAugmentedData G A)

/-- The degree-zero augmentation component is literally the counit. -/
@[simp]
theorem resolutionAugmented_hom_zero (G : Comonad C) (A : C) :
    (resolutionAugmented G A).hom.app
      (op (SimplexCategory.mk 0)) = G.ε.app A := by
  unfold resolutionAugmented resolutionAugmentedFunctor
  change (SimplicialObject.Data.Augmented.toSimplicialFunctor.obj
    (resolutionAugmentedData G A)).hom.app
      (op (SimplexCategory.mk 0)) = G.ε.app A
  rw [SimplicialObject.Data.Augmented.toSimplicialFunctor_obj_hom]
  exact SimplicialObject.Data.Augmented.toSimplicialAugmented_hom_app_mk
    (resolutionAugmentedData G A) 0

/-- The augmented resolution map induced by a morphism of carrier objects. -/
noncomputable def resolutionHom (G : Comonad C) {A B : C} (f : A ⟶ B) :
    resolutionAugmented G A ⟶ resolutionAugmented G B :=
  (resolutionAugmentedFunctor G).map f

@[simp]
theorem resolutionAugmentedFunctor_obj (G : Comonad C) (A : C) :
    (resolutionAugmentedFunctor G).obj A = resolutionAugmented G A :=
  rfl

@[simp]
theorem resolutionAugmentedFunctor_map (G : Comonad C) {A B : C}
    (f : A ⟶ B) :
    (resolutionAugmentedFunctor G).map f = resolutionHom G f :=
  rfl

@[simp]
theorem resolutionHom_id (G : Comonad C) (A : C) :
    resolutionHom G (𝟙 A) = 𝟙 (resolutionAugmented G A) :=
  (resolutionAugmentedFunctor G).map_id A

theorem resolutionHom_comp (G : Comonad C) {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) :
    resolutionHom G f ≫ resolutionHom G g = resolutionHom G (f ≫ g) :=
  ((resolutionAugmentedFunctor G).map_comp f g).symm

/-- The simplicial component of a resolution map is induced degreewise by
the corresponding comonad power. -/
@[simp]
theorem resolutionHom_left_app (G : Comonad C) {A B : C}
    (f : A ⟶ B) (n : ℕ) :
    (resolutionHom G f).left.app (op (SimplexCategory.mk n)) =
      (comonadPow G (n + 1)).map f :=
  rfl

/-- The target component of an augmented resolution map is the original map. -/
@[simp]
theorem resolutionHom_right (G : Comonad C) {A B : C} (f : A ⟶ B) :
    (resolutionHom G f).right = f :=
  rfl

end CategoryTheory.Comonad

end
