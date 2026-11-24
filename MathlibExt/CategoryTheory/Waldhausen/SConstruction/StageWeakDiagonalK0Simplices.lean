/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOne
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwo
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalVertex
import Mathlib.Tactic.FinCases

/-!
# Low-degree weak-stage diagonal simplices for Waldhausen K-zero

An object gives a canonical loop edge in the weak-stage diagonal, and a
cofiber sequence gives a diagonal `2`-simplex whose faces are the object
edges of source, quotient, and middle in the order `d₂ = X`, `d₀ = Z`,
`d₁ = Y`. Thus the realized direct `Y` edge is homotopic to the `X` edge
followed by the `Z` edge.

This file only constructs the generator and relation simplices. It makes no
K-zero comparison, generation, injectivity, surjectivity, additivity,
weak-equivalence, or model-category claim.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The canonical degree-one weak stage associated to an object. -/
noncomputable def stageOneWeakObj (X : C) : StageWeakCategory C 1 :=
  ⟨(stageOne C).obj X⟩

/-- Reindexing the object stage along either face gives the zero stage. -/
theorem stageOneWeakObj_reindex_delta (X : C) (i : Fin 2) :
    (reindexStageWeak C (SimplexCategory.δ i)).obj (stageOneWeakObj C X) =
      (⟨stageZero C⟩ : StageWeakCategory C 0) := by
  ext
  refine Functor.ext ?_ ?_
  · intro A
    have hA : A = diag (0 : Fin 1) := by
      obtain ⟨a, b, g, rfl⟩ := CategoryTheory.Arrow.mk_surjective A
      fin_cases a
      fin_cases b
      rfl
    subst A
    change ((stageOne C).obj X).obj.obj
        ((indexFunctor (SimplexCategory.δ i)).obj (diag (0 : Fin 1))) =
      (zeroDiagram C 0).obj (diag (0 : Fin 1))
    rw [indexFunctor_obj_diag, stageOne_obj_diag]
    rfl
  · intro A B φ
    have hA : A = diag (0 : Fin 1) := by
      obtain ⟨a, b, g, rfl⟩ := CategoryTheory.Arrow.mk_surjective A
      fin_cases a
      fin_cases b
      rfl
    have hZ : IsZero
        (((reindexStageWeak C (SimplexCategory.δ i)).obj
          (stageOneWeakObj C X)).obj.obj.obj A) := by
      rw [hA]
      change IsZero (((stageOne C).obj X).obj.obj
        ((indexFunctor (SimplexCategory.δ i)).obj (diag (0 : Fin 1))))
      rw [indexFunctor_obj_diag]
      exact ((stageOne C).obj X).property.diag_isZero _
    exact hZ.eq_of_src _ _

/-- The source face of the object stage is strictly the zero stage. -/
@[simp]
theorem stageOneWeakObj_reindex_d1 (X : C) :
    (⟨(reindexStage (C := C) (SimplexCategory.δ 1)).obj
      (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
      (⟨stageZero C⟩ : StageWeakCategory C 0) :=
  stageOneWeakObj_reindex_delta C X 1

/-- The target face of the object stage is strictly the zero stage. -/
@[simp]
theorem stageOneWeakObj_reindex_d0 (X : C) :
    (⟨(reindexStage (C := C) (SimplexCategory.δ 0)).obj
      (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
      (⟨stageZero C⟩ : StageWeakCategory C 0) :=
  stageOneWeakObj_reindex_delta C X 0

/-- Underlying diagonal degree-one simplex associated to an object. -/
noncomputable def stageWeakDiagonalObjectSimplex (X : C) :
    (stageWeakDiagonal C).obj (op ⦋1⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C X))

/-- Either diagonal face of the object simplex is the corresponding
reindexed degree-one stage vertex. -/
theorem stageWeakDiagonalObjectSimplex_face (X : C) (i : Fin 2) :
    (stageWeakDiagonal C).δ i (stageWeakDiagonalObjectSimplex C X) =
      ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ i)).obj (stageOneWeakObj C X)) := by
  change (stageWeakDiagonal C).map _ (stageWeakDiagonalObjectSimplex C X) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ i).op
      (stageWeakDiagonalObjectSimplex C X) =
      (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ i))).app
        (op ⦋0⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 1)).map
          (SimplexCategory.δ i).op)
          (ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C X)))) := rfl
  have hinner :
      ((CategoryTheory.nerve (StageWeakCategory C 1)).map
        (SimplexCategory.δ i).op)
        (ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C X))) =
      ComposableArrows.mk₀ (stageOneWeakObj C X) := by
    apply ComposableArrows.ext₀
    fin_cases i <;> rfl
  rw [hstep, hinner, CategoryTheory.nerveMap_app_mk₀]

/-- Canonical diagonal loop edge associated to an object. -/
noncomputable def stageWeakDiagonalObjectEdge (X : C) :
    (stageWeakDiagonal C).Edge
      (stageWeakDiagonalZeroVertex C) (stageWeakDiagonalZeroVertex C) := by
  refine SSet.Edge.ofEq (SSet.Edge.mk' (stageWeakDiagonalObjectSimplex C X)) ?_ ?_
  · rw [stageWeakDiagonalObjectSimplex_face]
    change ComposableArrows.mk₀
        (⟨(reindexStage (C := C) (SimplexCategory.δ 1)).obj
          (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
      (stageWeakDiagonalZeroVertex C : ComposableArrows (StageWeakCategory C 0) 0)
    have hFace := congrArg
      (fun A : StageWeakCategory C 0 => ComposableArrows.mk₀ A)
      (stageOneWeakObj_reindex_d1 C X)
    exact hFace
  · rw [stageWeakDiagonalObjectSimplex_face]
    change ComposableArrows.mk₀
        (⟨(reindexStage (C := C) (SimplexCategory.δ 0)).obj
          (stageOneWeakObj C X).obj⟩ : StageWeakCategory C 0) =
      (stageWeakDiagonalZeroVertex C : ComposableArrows (StageWeakCategory C 0) 0)
    have hFace := congrArg
      (fun A : StageWeakCategory C 0 => ComposableArrows.mk₀ A)
      (stageOneWeakObj_reindex_d0 C X)
    exact hFace

/-- The object edge is `mk₁` of the identity on its degree-one stage. -/
@[simp]
theorem stageWeakDiagonalObjectEdge_edge (X : C) :
    (stageWeakDiagonalObjectEdge C X).edge =
      ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C X)) :=
  rfl

/-- The source of the object edge is the diagonal zero vertex. -/
@[simp]
theorem stageWeakDiagonalObjectEdge_src (X : C) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (0 + 1))).obj (op ⦋0 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 0)).obj (op ⦋0⦌))
      ((stageWeakDiagonal C).δ 1)) (ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C X))) =
      stageWeakDiagonalZeroVertex C :=
  SSet.Edge.src_eq (stageWeakDiagonalObjectEdge C X)

/-- The target of the object edge is the diagonal zero vertex. -/
@[simp]
theorem stageWeakDiagonalObjectEdge_tgt (X : C) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (0 + 1))).obj (op ⦋0 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 0)).obj (op ⦋0⦌))
      ((stageWeakDiagonal C).δ 0)) (ComposableArrows.mk₁ (𝟙 (stageOneWeakObj C X))) =
      stageWeakDiagonalZeroVertex C :=
  SSet.Edge.tgt_eq (stageWeakDiagonalObjectEdge C X)

/-- The degree-two weak stage associated to a cofiber sequence. -/
noncomputable def stageTwoWeakObj {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) : StageWeakCategory C 2 :=
  ⟨stageTwo C X Y Z f g hSeq⟩

private theorem ar1_eq_diag_of_eq {A : Ar 1} (h : A.left = A.right) :
    A = diag A.left := by
  cases A with
  | mk l r hle =>
      have hlr : l = r := by simpa using h
      subst hlr
      have hh : hle = homOfLE le_rfl := Subsingleton.elim _ _
      subst hh
      rfl

private theorem stageTwoWeakObj_reindex_eq_stageOne
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) (i : Fin 3) (W : C)
    (hInterval :
      (stageTwo C X Y Z f g hSeq).obj.obj
          ((indexFunctor (SimplexCategory.δ i)).obj
            (interval (0 : Fin 2) 1 (by decide))) = W) :
    (reindexStageWeak C (SimplexCategory.δ i)).obj
        (stageTwoWeakObj C f g hSeq) = stageOneWeakObj C W := by
  ext
  refine Functor.ext ?_ ?_
  · intro A
    by_cases hA : A.left = A.right
    · have hdiag : A = diag A.left := ar1_eq_diag_of_eq hA
      rw [hdiag]
      change (stageTwo C X Y Z f g hSeq).obj.obj
          ((indexFunctor (SimplexCategory.δ i)).obj (diag _)) =
        ((stageOne C).obj W).obj.obj (diag _)
      rw [indexFunctor_obj_diag]
      change stageTwoDiagramObj C X Y Z (diag _) =
        stageOneDiagramObj C W (diag _)
      rw [stageTwoDiagramObj_diag,
        stageOneDiagramObj_of_eq C W (by rfl)]
    · have h01 : A = interval (0 : Fin 2) 1 (by decide) :=
        ar1_eq_interval01_of_ne hA
      subst A
      change (stageTwo C X Y Z f g hSeq).obj.obj
          ((indexFunctor (SimplexCategory.δ i)).obj (interval 0 1 _)) =
        ((stageOne C).obj W).obj.obj (interval 0 1 _)
      rw [hInterval, stageOne_obj_interval_zero_one]
  · intro A B φ
    by_cases hA : A.left = A.right
    · have hdiag : A = diag A.left := ar1_eq_diag_of_eq hA
      have hZ : IsZero
          (((reindexStageWeak C (SimplexCategory.δ i)).obj
            (stageTwoWeakObj C f g hSeq)).obj.obj.obj A) := by
        rw [hdiag]
        change IsZero ((stageTwo C X Y Z f g hSeq).obj.obj
          ((indexFunctor (SimplexCategory.δ i)).obj (diag _)))
        rw [indexFunctor_obj_diag]
        exact (stageTwo C X Y Z f g hSeq).property.diag_isZero _
      exact hZ.eq_of_src _ _
    · by_cases hB : B.left = B.right
      · have hdiag : B = diag B.left := ar1_eq_diag_of_eq hB
        have hZ : IsZero
            (((reindexStageWeak C (SimplexCategory.δ i)).obj
              (stageTwoWeakObj C f g hSeq)).obj.obj.obj B) := by
          rw [hdiag]
          change IsZero ((stageTwo C X Y Z f g hSeq).obj.obj
            ((indexFunctor (SimplexCategory.δ i)).obj (diag _)))
          rw [indexFunctor_obj_diag]
          exact (stageTwo C X Y Z f g hSeq).property.diag_isZero _
        exact hZ.eq_of_tgt _ _
      · have hA01 : A = interval (0 : Fin 2) 1 (by decide) :=
          ar1_eq_interval01_of_ne hA
        have hB01 : B = interval (0 : Fin 2) 1 (by decide) :=
          ar1_eq_interval01_of_ne hB
        subst A
        subst B
        have hφ : φ = 𝟙 (interval (0 : Fin 2) 1 (by decide)) :=
          Arrow.hom_ext _ _ (Subsingleton.elim _ _) (Subsingleton.elim _ _)
        rw [hφ]
        simp only [Functor.map_id, eqToHom_trans, eqToHom_refl,
          Category.id_comp]

/-- The second face of a cofiber stage is the object stage of its source. -/
@[simp]
theorem stageTwoWeakObj_reindex_d2 {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (⟨(reindexStage (C := C) (SimplexCategory.δ 2)).obj
        (stageTwoWeakObj C f g hSeq).obj⟩ : StageWeakCategory C 1) = stageOneWeakObj C X := by
  apply stageTwoWeakObj_reindex_eq_stageOne C f g hSeq 2 X
  rw [indexFunctor_obj_interval]
  exact stageTwo_obj_01 C X Y Z f g hSeq _

/-- The zeroth face of a cofiber stage is the object stage of its quotient. -/
@[simp]
theorem stageTwoWeakObj_reindex_d0 {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (⟨(reindexStage (C := C) (SimplexCategory.δ 0)).obj
        (stageTwoWeakObj C f g hSeq).obj⟩ : StageWeakCategory C 1) = stageOneWeakObj C Z := by
  apply stageTwoWeakObj_reindex_eq_stageOne C f g hSeq 0 Z
  rw [indexFunctor_obj_interval]
  exact stageTwo_obj_12 C X Y Z f g hSeq _

/-- The first face of a cofiber stage is the object stage of its middle. -/
@[simp]
theorem stageTwoWeakObj_reindex_d1 {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (⟨(reindexStage (C := C) (SimplexCategory.δ 1)).obj
        (stageTwoWeakObj C f g hSeq).obj⟩ : StageWeakCategory C 1) = stageOneWeakObj C Y := by
  apply stageTwoWeakObj_reindex_eq_stageOne C f g hSeq 1 Y
  rw [indexFunctor_obj_interval]
  exact stageTwo_obj_02 C X Y Z f g hSeq _

/-- Underlying diagonal `2`-simplex associated to a cofiber sequence. -/
noncomputable def stageWeakDiagonalCofiberSimplex
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (stageWeakDiagonal C).obj (op ⦋2⦌) := by
  rw [stageWeakDiagonal_obj, stageWeakNerve_obj]
  exact ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
    (𝟙 (stageTwoWeakObj C f g hSeq))

/-- The second diagonal face of the cofiber simplex is the source edge. -/
@[simp]
theorem stageWeakDiagonalCofiberSimplex_d2
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 2)) (stageWeakDiagonalCofiberSimplex C f g hSeq) =
      (stageWeakDiagonalObjectEdge C X).edge := by
  change (stageWeakDiagonal C).map _ (stageWeakDiagonalCofiberSimplex C f g hSeq) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 2).op
      (stageWeakDiagonalCofiberSimplex C f g hSeq) =
      (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ 2))).app
        (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 2).op)
          (ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
            (𝟙 (stageTwoWeakObj C f g hSeq)))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 2).op)
        (ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
          (𝟙 (stageTwoWeakObj C f g hSeq))) =
      ComposableArrows.mk₁ (𝟙 (stageTwoWeakObj C f g hSeq)) :=
    CategoryTheory.nerve.δ₂_mk₂_eq _ _
  rw [hstep, hface,
    CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  change ComposableArrows.mk₁
      (𝟙 (⟨(reindexStage (C := C) (SimplexCategory.δ 2)).obj
        (stageTwoWeakObj C f g hSeq).obj⟩ : StageWeakCategory C 1)) =
    ((stageWeakDiagonalObjectEdge C X).edge : ComposableArrows (StageWeakCategory C 1) 1)
  have hFace := congrArg
    (fun A : StageWeakCategory C 1 => ComposableArrows.mk₁ (𝟙 A))
    (stageTwoWeakObj_reindex_d2 C f g hSeq)
  exact hFace.trans (stageWeakDiagonalObjectEdge_edge C X).symm

/-- The zeroth diagonal face of the cofiber simplex is the quotient edge. -/
@[simp]
theorem stageWeakDiagonalCofiberSimplex_d0
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 0)) (stageWeakDiagonalCofiberSimplex C f g hSeq) =
      (stageWeakDiagonalObjectEdge C Z).edge := by
  change (stageWeakDiagonal C).map _ (stageWeakDiagonalCofiberSimplex C f g hSeq) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 0).op
      (stageWeakDiagonalCofiberSimplex C f g hSeq) =
      (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ 0))).app
        (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 0).op)
          (ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
            (𝟙 (stageTwoWeakObj C f g hSeq)))) := rfl
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 0).op)
        (ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
          (𝟙 (stageTwoWeakObj C f g hSeq))) =
      ComposableArrows.mk₁ (𝟙 (stageTwoWeakObj C f g hSeq)) :=
    CategoryTheory.nerve.δ₀_mk₂_eq _ _
  rw [hstep, hface,
    CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  change ComposableArrows.mk₁
      (𝟙 (⟨(reindexStage (C := C) (SimplexCategory.δ 0)).obj
        (stageTwoWeakObj C f g hSeq).obj⟩ : StageWeakCategory C 1)) =
    ((stageWeakDiagonalObjectEdge C Z).edge : ComposableArrows (StageWeakCategory C 1) 1)
  have hFace := congrArg
    (fun A : StageWeakCategory C 1 => ComposableArrows.mk₁ (𝟙 A))
    (stageTwoWeakObj_reindex_d0 C f g hSeq)
  exact hFace.trans (stageWeakDiagonalObjectEdge_edge C Z).symm

/-- The first diagonal face of the cofiber simplex is the middle edge. -/
@[simp]
theorem stageWeakDiagonalCofiberSimplex_d1
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve (StageWeakCategory C (1 + 1))).obj (op ⦋1 + 1⦌))
      (Y := (CategoryTheory.nerve (StageWeakCategory C 1)).obj (op ⦋1⦌))
      ((stageWeakDiagonal C).δ 1)) (stageWeakDiagonalCofiberSimplex C f g hSeq) =
      (stageWeakDiagonalObjectEdge C Y).edge := by
  change (stageWeakDiagonal C).map _ (stageWeakDiagonalCofiberSimplex C f g hSeq) = _
  have hstep : (stageWeakDiagonal C).map (SimplexCategory.δ 1).op
      (stageWeakDiagonalCofiberSimplex C f g hSeq) =
      (CategoryTheory.nerveMap (reindexStageWeak C (SimplexCategory.δ 1))).app
        (op ⦋1⦌)
        (((CategoryTheory.nerve (StageWeakCategory C 2)).map
          (SimplexCategory.δ 1).op)
          (ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
            (𝟙 (stageTwoWeakObj C f g hSeq)))) := rfl
  have hcomp : (𝟙 (stageTwoWeakObj C f g hSeq)) ≫
      𝟙 (stageTwoWeakObj C f g hSeq) = 𝟙 (stageTwoWeakObj C f g hSeq) := by simp
  have hface :
      ((CategoryTheory.nerve (StageWeakCategory C 2)).map
        (SimplexCategory.δ 1).op)
        (ComposableArrows.mk₂ (𝟙 (stageTwoWeakObj C f g hSeq))
          (𝟙 (stageTwoWeakObj C f g hSeq))) =
      ComposableArrows.mk₁
        ((𝟙 (stageTwoWeakObj C f g hSeq)) ≫
          𝟙 (stageTwoWeakObj C f g hSeq)) :=
    CategoryTheory.nerve.δ₁_mk₂_eq _ _
  rw [hstep, hface, hcomp,
    CategoryTheory.nerveMap_app_mk₁, Functor.map_id]
  change ComposableArrows.mk₁
      (𝟙 (⟨(reindexStage (C := C) (SimplexCategory.δ 1)).obj
        (stageTwoWeakObj C f g hSeq).obj⟩ : StageWeakCategory C 1)) =
    ((stageWeakDiagonalObjectEdge C Y).edge : ComposableArrows (StageWeakCategory C 1) 1)
  have hFace := congrArg
    (fun A : StageWeakCategory C 1 => ComposableArrows.mk₁ (𝟙 A))
    (stageTwoWeakObj_reindex_d1 C f g hSeq)
  exact hFace.trans (stageWeakDiagonalObjectEdge_edge C Y).symm

/-- The cofiber relation as a composition structure, oriented `X ; Z = Y`. -/
noncomputable def stageWeakDiagonalCofiberCompStruct
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    SSet.Edge.CompStruct (stageWeakDiagonalObjectEdge C X)
      (stageWeakDiagonalObjectEdge C Z) (stageWeakDiagonalObjectEdge C Y) :=
  SSet.Edge.CompStruct.mk (stageWeakDiagonalCofiberSimplex C f g hSeq)
    (stageWeakDiagonalCofiberSimplex_d2 C f g hSeq)
    (stageWeakDiagonalCofiberSimplex_d0 C f g hSeq)
    (stageWeakDiagonalCofiberSimplex_d1 C f g hSeq)

/-- The underlying simplex of the cofiber composition structure. -/
@[simp]
theorem stageWeakDiagonalCofiberCompStruct_simplex
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (stageWeakDiagonalCofiberCompStruct C f g hSeq).simplex =
      stageWeakDiagonalCofiberSimplex C f g hSeq :=
  rfl

/-- Realization of the cofiber relation: the direct middle edge is homotopic
to the source edge followed by the quotient edge, relative endpoints. -/
theorem stageWeakDiagonalCofiberRealizedHomotopic
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (TopCat.pathEquiv
      (SSet.realizedEdgePath (stageWeakDiagonalObjectEdge C Y))).Homotopic
      ((TopCat.pathEquiv
        (SSet.realizedEdgePath (stageWeakDiagonalObjectEdge C X))).trans
        (TopCat.pathEquiv
          (SSet.realizedEdgePath (stageWeakDiagonalObjectEdge C Z)))) :=
  SSet.realizedCompStructHomotopic
    (stageWeakDiagonalCofiberCompStruct C f g hSeq)

end CategoryTheory.Waldhausen.SConstruction

end
