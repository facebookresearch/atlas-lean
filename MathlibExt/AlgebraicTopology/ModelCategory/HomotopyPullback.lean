/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantCospanReplacement
public import MathlibExt.AlgebraicTopology.ModelCategory.Proper

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.AlgebraicTopology.ModelCategory.ProperSpanGluing
import MathlibExt.AlgebraicTopology.ModelCategory.Replacement
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks

/-!
# Functorial homotopy pullbacks

This file constructs functorial homotopy pullbacks of walking cospans and
compares them with ordinary cospan limits. It also relates the named
functorial construction to arbitrary fibrant cospan replacements by an
existential weak map under the common ordinary pullback.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

private abbrev CospanDiagram := WalkingCospan ⥤ C

private noncomputable def cospanInlComposite :
    CospanDiagram (C := C) ⥤ Arrow C where
  obj F := Arrow.mk
    (F.map WalkingCospan.Hom.inl ≫
      (fibrantReplacementUnit (C := C)).app
        (F.obj WalkingCospan.one))
  map {F G} η := Arrow.homMk
    (η.app WalkingCospan.left)
    ((fibrantReplacement (C := C)).map
      (η.app WalkingCospan.one)) (by
        calc
          η.app WalkingCospan.left ≫
                (G.map WalkingCospan.Hom.inl ≫
                  (fibrantReplacementUnit (C := C)).app
                    (G.obj WalkingCospan.one)) =
              (η.app WalkingCospan.left ≫
                G.map WalkingCospan.Hom.inl) ≫
                  (fibrantReplacementUnit (C := C)).app
                    (G.obj WalkingCospan.one) :=
            (Category.assoc _ _ _).symm
          _ = (F.map WalkingCospan.Hom.inl ≫
                η.app WalkingCospan.one) ≫
                  (fibrantReplacementUnit (C := C)).app
                    (G.obj WalkingCospan.one) := by
            rw [η.naturality WalkingCospan.Hom.inl]
          _ = F.map WalkingCospan.Hom.inl ≫
              η.app WalkingCospan.one ≫
                (fibrantReplacementUnit (C := C)).app
                  (G.obj WalkingCospan.one) := Category.assoc _ _ _
          _ = F.map WalkingCospan.Hom.inl ≫
              (fibrantReplacementUnit (C := C)).app
                  (F.obj WalkingCospan.one) ≫
                (fibrantReplacement (C := C)).map
                  (η.app WalkingCospan.one) := by
            simpa only [Functor.id_map, Category.assoc] using
              congrArg (fun k => F.map WalkingCospan.Hom.inl ≫ k)
                ((fibrantReplacementUnit (C := C)).naturality
                  (η.app WalkingCospan.one))
          _ = (F.map WalkingCospan.Hom.inl ≫
                (fibrantReplacementUnit (C := C)).app
                  (F.obj WalkingCospan.one)) ≫
              (fibrantReplacement (C := C)).map
                (η.app WalkingCospan.one) :=
            (Category.assoc _ _ _).symm)
  map_id F := by
    ext <;> simp
  map_comp η θ := by
    ext <;> simp

private noncomputable def cospanInrComposite :
    CospanDiagram (C := C) ⥤ Arrow C where
  obj F := Arrow.mk
    (F.map WalkingCospan.Hom.inr ≫
      (fibrantReplacementUnit (C := C)).app
        (F.obj WalkingCospan.one))
  map {F G} η := Arrow.homMk
    (η.app WalkingCospan.right)
    ((fibrantReplacement (C := C)).map
      (η.app WalkingCospan.one)) (by
        calc
          η.app WalkingCospan.right ≫
                (G.map WalkingCospan.Hom.inr ≫
                  (fibrantReplacementUnit (C := C)).app
                    (G.obj WalkingCospan.one)) =
              (η.app WalkingCospan.right ≫
                G.map WalkingCospan.Hom.inr) ≫
                  (fibrantReplacementUnit (C := C)).app
                    (G.obj WalkingCospan.one) :=
            (Category.assoc _ _ _).symm
          _ = (F.map WalkingCospan.Hom.inr ≫
                η.app WalkingCospan.one) ≫
                  (fibrantReplacementUnit (C := C)).app
                    (G.obj WalkingCospan.one) := by
            rw [η.naturality WalkingCospan.Hom.inr]
          _ = F.map WalkingCospan.Hom.inr ≫
              η.app WalkingCospan.one ≫
                (fibrantReplacementUnit (C := C)).app
                  (G.obj WalkingCospan.one) := Category.assoc _ _ _
          _ = F.map WalkingCospan.Hom.inr ≫
              (fibrantReplacementUnit (C := C)).app
                  (F.obj WalkingCospan.one) ≫
                (fibrantReplacement (C := C)).map
                  (η.app WalkingCospan.one) := by
            simpa only [Functor.id_map, Category.assoc] using
              congrArg (fun k => F.map WalkingCospan.Hom.inr ≫ k)
                ((fibrantReplacementUnit (C := C)).naturality
                  (η.app WalkingCospan.one))
          _ = (F.map WalkingCospan.Hom.inr ≫
                (fibrantReplacementUnit (C := C)).app
                  (F.obj WalkingCospan.one)) ≫
              (fibrantReplacement (C := C)).map
                (η.app WalkingCospan.one) :=
            (Category.assoc _ _ _).symm)
  map_id F := by
    ext <;> simp
  map_comp η θ := by
    ext <;> simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fibrantCospanReplacementFunctor :
    CospanDiagram (C := C) ⥤ CospanDiagram (C := C) where
  obj F := cospan
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      (cospanInlComposite (C := C) |>.obj F).hom).p
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      (cospanInrComposite (C := C) |>.obj F).hom).p
  map {F G} η := cospanHomMk
    ((fibrantReplacement (C := C)).map
      (η.app WalkingCospan.one))
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
      ((cospanInlComposite (C := C)).map η))
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
      ((cospanInrComposite (C := C)).map η))
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ_p
      ((cospanInlComposite (C := C)).map η)).symm
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ_p
      ((cospanInrComposite (C := C)).map η)).symm
  map_id F := by
    ext j
    rcases j with (_ | _ | _)
    · change (fibrantReplacement (C := C)).map
          ((CategoryStruct.id F).app WalkingCospan.one) =
        CategoryStruct.id _
      simp
    · change (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
          ((cospanInlComposite (C := C)).map
            (CategoryStruct.id F)) = CategoryStruct.id _
      rw [← (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ_id]
      exact congrArg (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
        ((cospanInlComposite (C := C)).map_id F)
    · change (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
          ((cospanInrComposite (C := C)).map
            (CategoryStruct.id F)) = CategoryStruct.id _
      rw [← (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ_id]
      exact congrArg (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
        ((cospanInrComposite (C := C)).map_id F)
  map_comp η θ := by
    ext j
    rcases j with (_ | _ | _)
    · change (fibrantReplacement (C := C)).map
          (η.app WalkingCospan.one ≫ θ.app WalkingCospan.one) =
        (fibrantReplacement (C := C)).map
            (η.app WalkingCospan.one) ≫
          (fibrantReplacement (C := C)).map
            (θ.app WalkingCospan.one)
      simp
    · change (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
          ((cospanInlComposite (C := C)).map (η ≫ θ)) =
        (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
            ((cospanInlComposite (C := C)).map η) ≫
          (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
            ((cospanInlComposite (C := C)).map θ)
      rw [Functor.map_comp,
          (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ_comp]
    · change (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
          ((cospanInrComposite (C := C)).map (η ≫ θ)) =
        (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
            ((cospanInrComposite (C := C)).map η) ≫
          (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ
            ((cospanInrComposite (C := C)).map θ)
      rw [Functor.map_comp,
          (functorialFactorizationData (trivialCofibrations C) (fibrations C)).mapZ_comp]

private noncomputable def fibrantCospanReplacementUnit :
    (𝟭 (CospanDiagram (C := C)) :
      CospanDiagram (C := C) ⥤ CospanDiagram (C := C)) ⟶
        fibrantCospanReplacementFunctor (C := C) where
  app F := cospanHomMk
    ((fibrantReplacementUnit (C := C)).app
      (F.obj WalkingCospan.one))
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      (cospanInlComposite (C := C) |>.obj F).hom).i
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      (cospanInrComposite (C := C) |>.obj F).hom).i
    (by
      change F.map WalkingCospan.Hom.inl ≫
          (fibrantReplacementUnit (C := C)).app
            (F.obj WalkingCospan.one) =
        ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
          (cospanInlComposite (C := C) |>.obj F).hom).i ≫
        ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
          (cospanInlComposite (C := C) |>.obj F).hom).p
      exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
          _).fac.symm)
    (by
      change F.map WalkingCospan.Hom.inr ≫
          (fibrantReplacementUnit (C := C)).app
            (F.obj WalkingCospan.one) =
        ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
          (cospanInrComposite (C := C) |>.obj F).hom).i ≫
        ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
          (cospanInrComposite (C := C) |>.obj F).hom).p
      exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
          _).fac.symm)
  naturality F G η := by
    ext j
    rcases j with (_ | _ | _)
    · exact (fibrantReplacementUnit (C := C)).naturality _
    · exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).i_mapZ
        ((cospanInlComposite (C := C)).map η)).symm
    · exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).i_mapZ
        ((cospanInrComposite (C := C)).map η)).symm

private theorem fibrantCospanReplacement_one_fibrant
    (F : CospanDiagram (C := C)) :
    IsFibrant
      ((fibrantCospanReplacementFunctor (C := C)).obj F |>.obj
        WalkingCospan.one) := by
  change IsFibrant
    ((fibrantReplacement (C := C)).obj
      (F.obj WalkingCospan.one))
  infer_instance

private theorem fibrantCospanReplacement_inl_fibration
    (F : CospanDiagram (C := C)) :
    Fibration
      ((fibrantCospanReplacementFunctor (C := C)).obj F |>.map
        WalkingCospan.Hom.inl) := by
  change Fibration
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      (cospanInlComposite (C := C) |>.obj F).hom).p
  rw [fibration_iff]
  exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      _).hp

private theorem fibrantCospanReplacement_inr_fibration
    (F : CospanDiagram (C := C)) :
    Fibration
      ((fibrantCospanReplacementFunctor (C := C)).obj F |>.map
        WalkingCospan.Hom.inr) := by
  change Fibration
    ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      (cospanInrComposite (C := C) |>.obj F).hom).p
  rw [fibration_iff]
  exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
      _).hp

private theorem fibrantCospanReplacementUnit_trivialCofibration
    (F : CospanDiagram (C := C)) (j : WalkingCospan) :
    trivialCofibrations C
      (((fibrantCospanReplacementUnit (C := C)).app F).app j) := by
  rcases j with (_ | _ | _)
  · change trivialCofibrations C
      ((fibrantReplacementUnit (C := C)).app
        (F.obj WalkingCospan.one))
    exact mem_trivialCofibrations _
  · change trivialCofibrations C
      ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
        (cospanInlComposite (C := C) |>.obj F).hom).i
    exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
        _).hi
  · change trivialCofibrations C
      ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
        (cospanInrComposite (C := C) |>.obj F).hom).i
    exact ((functorialFactorizationData (trivialCofibrations C) (fibrations C)).factorizationData
        _).hi

private noncomputable def functorialFibrantCospanReplacement
    (F : CospanDiagram (C := C)) : FibrantCospanReplacement F :=
  { P := (fibrantCospanReplacementFunctor (C := C)).obj F
    unit := (fibrantCospanReplacementUnit (C := C)).app F
    isFibrant_one := fibrantCospanReplacement_one_fibrant F
    fibration_inl := fibrantCospanReplacement_inl_fibration F
    fibration_inr := fibrantCospanReplacement_inr_fibration F
    unit_app_mem_trivialCofibrations :=
      fibrantCospanReplacementUnit_trivialCofibration F }

private theorem fibrantCospanReplacement_map_weakEquivalence
    {F G : CospanDiagram (C := C)} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j)) (j : WalkingCospan) :
    WeakEquivalence
      (((fibrantCospanReplacementFunctor (C := C)).map η).app j) := by
  have hF := (mem_trivialCofibrations_iff
    (((fibrantCospanReplacementUnit (C := C)).app F).app j)).1
      (fibrantCospanReplacementUnit_trivialCofibration F j)
  have hG := (mem_trivialCofibrations_iff
    (((fibrantCospanReplacementUnit (C := C)).app G).app j)).1
      (fibrantCospanReplacementUnit_trivialCofibration G j)
  let _ : WeakEquivalence
      (((fibrantCospanReplacementUnit (C := C)).app F).app j) := hF.2
  let _ : WeakEquivalence
      (((fibrantCospanReplacementUnit (C := C)).app G).app j) := hG.2
  let _ : WeakEquivalence (η.app j) := hη j
  have hfac :
      ((fibrantCospanReplacementUnit (C := C)).app F).app j ≫
          ((fibrantCospanReplacementFunctor (C := C)).map η).app j =
        η.app j ≫
          ((fibrantCospanReplacementUnit (C := C)).app G).app j := by
    simpa only [Functor.id_map, NatTrans.comp_app] using
      (congr_app
        ((fibrantCospanReplacementUnit (C := C)).naturality η) j).symm
  have : WeakEquivalence
      (((fibrantCospanReplacementUnit (C := C)).app F).app j ≫
        ((fibrantCospanReplacementFunctor (C := C)).map η).app j) := by
    rw [hfac]
    infer_instance
  exact weakEquivalence_of_precomp
    (((fibrantCospanReplacementUnit (C := C)).app F).app j)
    (((fibrantCospanReplacementFunctor (C := C)).map η).app j)

private noncomputable def cospanLimitIso (F : CospanDiagram (C := C)) :
    limit F ≅
      pullback (F.map WalkingCospan.Hom.inl)
        (F.map WalkingCospan.Hom.inr) :=
  HasLimit.isoOfNatIso (diagramIsoCospan F)

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem cospanLimitIso_left (F : CospanDiagram (C := C)) :
    (cospanLimitIso F).hom ≫
        pullback.fst (F.map WalkingCospan.Hom.inl)
          (F.map WalkingCospan.Hom.inr) =
      limit.π F WalkingCospan.left := by
  simp [cospanLimitIso]

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem cospanLimitIso_right (F : CospanDiagram (C := C)) :
    (cospanLimitIso F).hom ≫
        pullback.snd (F.map WalkingCospan.Hom.inl)
          (F.map WalkingCospan.Hom.inr) =
      limit.π F WalkingCospan.right := by
  simp [cospanLimitIso]

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem cospanLimit_isPullback (F : CospanDiagram (C := C)) :
    IsPullback
      (limit.π F WalkingCospan.left)
      (limit.π F WalkingCospan.right)
      (F.map WalkingCospan.Hom.inl)
      (F.map WalkingCospan.Hom.inr) := by
  exact IsPullback.of_iso_pullback
    ⟨(limit.w F WalkingCospan.Hom.inl).trans
      (limit.w F WalkingCospan.Hom.inr).symm⟩
    (cospanLimitIso F)
    (cospanLimitIso_left F)
    (cospanLimitIso_right F)

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem isCofibrant_op_of_isFibrant
    (X : C) [IsFibrant X] : IsCofibrant (Opposite.op X) := by
  apply (isCofibrant_iff_of_isInitial
    ((terminal.from X).op) terminalIsTerminal.op).2
  rw [cofibration_op_iff]
  infer_instance

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem weakEquivalence_limitMap_of_fibrant_cospans_inl
    {F G : CospanDiagram (C := C)} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j))
    [Fibration (F.map WalkingCospan.Hom.inl)]
    [Fibration (G.map WalkingCospan.Hom.inl)]
    [IsFibrant (F.obj WalkingCospan.one)]
    [IsFibrant (G.obj WalkingCospan.one)]
    [IsFibrant (F.obj WalkingCospan.right)]
    [IsFibrant (G.obj WalkingCospan.right)] :
    WeakEquivalence (lim.map η) := by
  let _ : Cofibration (F.map WalkingCospan.Hom.inl).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : Cofibration (G.map WalkingCospan.Hom.inl).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : IsCofibrant (Opposite.op (F.obj WalkingCospan.one)) :=
    isCofibrant_op_of_isFibrant _
  let _ : IsCofibrant (Opposite.op (G.obj WalkingCospan.one)) :=
    isCofibrant_op_of_isFibrant _
  let _ : IsCofibrant (Opposite.op (F.obj WalkingCospan.right)) :=
    isCofibrant_op_of_isFibrant _
  let _ : IsCofibrant (Opposite.op (G.obj WalkingCospan.right)) :=
    isCofibrant_op_of_isFibrant _
  let _ : WeakEquivalence (η.app WalkingCospan.one).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.one
  let _ : WeakEquivalence (η.app WalkingCospan.left).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.left
  let _ : WeakEquivalence (η.app WalkingCospan.right).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.right
  have h : WeakEquivalence (lim.map η).op := by
    exact weakEquivalence_map_of_isPushouts_of_cofibrant
      (cospanLimit_isPullback G).op.flip
      (cospanLimit_isPullback F).op.flip
      (by
        simpa only [op_comp] using
          congrArg Quiver.Hom.op
            (η.naturality WalkingCospan.Hom.inl).symm)
      (by
        simpa only [op_comp] using
          congrArg Quiver.Hom.op
            (η.naturality WalkingCospan.Hom.inr).symm)
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.left))
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.right))
  rwa [weakEquivalences_op_iff] at h

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem weakEquivalence_limitMap_of_fibrant_cospans_inr
    {F G : CospanDiagram (C := C)} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j))
    [Fibration (F.map WalkingCospan.Hom.inr)]
    [Fibration (G.map WalkingCospan.Hom.inr)]
    [IsFibrant (F.obj WalkingCospan.one)]
    [IsFibrant (G.obj WalkingCospan.one)]
    [IsFibrant (F.obj WalkingCospan.left)]
    [IsFibrant (G.obj WalkingCospan.left)] :
    WeakEquivalence (lim.map η) := by
  let _ : Cofibration (F.map WalkingCospan.Hom.inr).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : Cofibration (G.map WalkingCospan.Hom.inr).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : IsCofibrant (Opposite.op (F.obj WalkingCospan.one)) :=
    isCofibrant_op_of_isFibrant _
  let _ : IsCofibrant (Opposite.op (G.obj WalkingCospan.one)) :=
    isCofibrant_op_of_isFibrant _
  let _ : IsCofibrant (Opposite.op (F.obj WalkingCospan.left)) :=
    isCofibrant_op_of_isFibrant _
  let _ : IsCofibrant (Opposite.op (G.obj WalkingCospan.left)) :=
    isCofibrant_op_of_isFibrant _
  let _ : WeakEquivalence (η.app WalkingCospan.one).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.one
  let _ : WeakEquivalence (η.app WalkingCospan.left).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.left
  let _ : WeakEquivalence (η.app WalkingCospan.right).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.right
  have h : WeakEquivalence (lim.map η).op := by
    exact weakEquivalence_map_of_isPushouts_of_cofibrant
      (cospanLimit_isPullback G).op
      (cospanLimit_isPullback F).op
      (by
        simpa only [op_comp] using
          congrArg Quiver.Hom.op
            (η.naturality WalkingCospan.Hom.inr).symm)
      (by
        simpa only [op_comp] using
          congrArg Quiver.Hom.op
            (η.naturality WalkingCospan.Hom.inl).symm)
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.right))
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.left))
  rwa [weakEquivalences_op_iff] at h

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem isLeftProper_op_of_isRightProper
    [IsRightProper C] : IsLeftProper Cᵒᵖ where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro A B i hi
    constructor
    intro X Y j f' f sq hf
    have hiUnop : fibrations C i.unop := by
      rw [cofibrations_op] at hi
      exact hi
    have hfUnop : weakEquivalences C f.unop := by
      rw [weakEquivalences_op] at hf
      exact hf
    have hf'Unop : weakEquivalences C f'.unop :=
      (inferInstance :
          (weakEquivalences C).IsStableUnderBaseChangeAgainst
            (fibrations C))
        |>.isStableUnderBaseChangeAlong i.unop hiUnop
        |>.of_isPullback sq.unop hfUnop
    rw [weakEquivalences_op]
    exact hf'Unop

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
/-- A componentwise weak map of cospans induces a weak map of ordinary limits when both
original left legs are fibrations in a right-proper model category. -/
theorem weakEquivalence_limitMap_of_rightProper_inl
    [IsRightProper C]
    {F G : WalkingCospan ⥤ C} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j))
    [Fibration (F.map WalkingCospan.Hom.inl)]
    [Fibration (G.map WalkingCospan.Hom.inl)] :
    WeakEquivalence (lim.map η) := by
  let _ : IsLeftProper Cᵒᵖ := isLeftProper_op_of_isRightProper
  let _ : Cofibration (F.map WalkingCospan.Hom.inl).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : Cofibration (G.map WalkingCospan.Hom.inl).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : WeakEquivalence (η.app WalkingCospan.one).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.one
  let _ : WeakEquivalence (η.app WalkingCospan.left).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.left
  let _ : WeakEquivalence (η.app WalkingCospan.right).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.right
  have h : WeakEquivalence (lim.map η).op := by
    exact IsLeftProper.weakEquivalence_map_of_isPushouts_of_snd
      (cospanLimit_isPullback G).op
      (cospanLimit_isPullback F).op
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (η.naturality WalkingCospan.Hom.inr).symm)
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (η.naturality WalkingCospan.Hom.inl).symm)
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.right))
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.left))
  rwa [weakEquivalences_op_iff] at h

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem IsRightProper.weakEquivalence_limitMap_of_inr
    [IsRightProper C]
    {F G : CospanDiagram (C := C)} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j))
    [Fibration (F.map WalkingCospan.Hom.inr)]
    [Fibration (G.map WalkingCospan.Hom.inr)] :
    WeakEquivalence (lim.map η) := by
  let _ : IsLeftProper Cᵒᵖ := isLeftProper_op_of_isRightProper
  let _ : Cofibration (F.map WalkingCospan.Hom.inr).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : Cofibration (G.map WalkingCospan.Hom.inr).op := by
    rw [cofibration_op_iff]
    infer_instance
  let _ : WeakEquivalence (η.app WalkingCospan.one).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.one
  let _ : WeakEquivalence (η.app WalkingCospan.left).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.left
  let _ : WeakEquivalence (η.app WalkingCospan.right).op := by
    rw [weakEquivalences_op_iff]
    exact hη WalkingCospan.right
  have h : WeakEquivalence (lim.map η).op := by
    exact IsLeftProper.weakEquivalence_map_of_isPushouts_of_fst
      (cospanLimit_isPullback G).op
      (cospanLimit_isPullback F).op
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (η.naturality WalkingCospan.Hom.inr).symm)
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (η.naturality WalkingCospan.Hom.inl).symm)
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.right))
      (by
        simpa only [op_comp] using congrArg Quiver.Hom.op
          (limit.map_π η WalkingCospan.left))
  rwa [weakEquivalences_op_iff] at h

/-- The cospan limit after the chosen functorial fibrant cospan replacement. -/
@[no_expose]
noncomputable def homotopyPullback : (WalkingCospan ⥤ C) ⥤ C :=
  fibrantCospanReplacementFunctor (C := C) ⋙ lim

/-- The original cospan limit maps to its homotopy pullback through the replacement unit. -/
@[no_expose]
noncomputable def homotopyPullbackComparison :
    (lim : (WalkingCospan ⥤ C) ⥤ C) ⟶ homotopyPullback :=
  { app := fun F => lim.map
      ((fibrantCospanReplacementUnit (C := C)).app F)
    naturality := fun F G η => by
      change lim.map η ≫
          lim.map ((fibrantCospanReplacementUnit (C := C)).app G) =
        lim.map ((fibrantCospanReplacementUnit (C := C)).app F) ≫
          lim.map ((fibrantCospanReplacementFunctor (C := C)).map η)
      rw [← lim.map_comp, ← lim.map_comp]
      congr 1
      exact (fibrantCospanReplacementUnit (C := C)).naturality η }

theorem homotopyPullback_map_weakEquivalence
    {F G : WalkingCospan ⥤ C} (η : F ⟶ G)
    (hη : ∀ j, WeakEquivalence (η.app j)) :
    WeakEquivalence ((homotopyPullback (C := C)).map η) := by
  let PF := (fibrantCospanReplacementFunctor (C := C)).obj F
  let PG := (fibrantCospanReplacementFunctor (C := C)).obj G
  let ηP := (fibrantCospanReplacementFunctor (C := C)).map η
  let _ : Fibration (PF.map WalkingCospan.Hom.inl) :=
    fibrantCospanReplacement_inl_fibration F
  let _ : Fibration (PG.map WalkingCospan.Hom.inl) :=
    fibrantCospanReplacement_inl_fibration G
  let _ : IsFibrant (PF.obj WalkingCospan.one) :=
    fibrantCospanReplacement_one_fibrant F
  let _ : IsFibrant (PG.obj WalkingCospan.one) :=
    fibrantCospanReplacement_one_fibrant G
  let _ : Fibration (PF.map WalkingCospan.Hom.inr) :=
    fibrantCospanReplacement_inr_fibration F
  let _ : Fibration (PG.map WalkingCospan.Hom.inr) :=
    fibrantCospanReplacement_inr_fibration G
  let _ : IsFibrant (PF.obj WalkingCospan.right) :=
    isFibrant_of_fibration (PF.map WalkingCospan.Hom.inr)
  let _ : IsFibrant (PG.obj WalkingCospan.right) :=
    isFibrant_of_fibration (PG.map WalkingCospan.Hom.inr)
  change WeakEquivalence (lim.map ηP)
  exact weakEquivalence_limitMap_of_fibrant_cospans_inl ηP
    (fibrantCospanReplacement_map_weakEquivalence η hη)

theorem weakEquivalence_homotopyPullbackComparison_of_inl
    (F : WalkingCospan ⥤ C)
    [IsFibrant (F.obj WalkingCospan.one)]
    [IsFibrant (F.obj WalkingCospan.right)]
    [Fibration (F.map WalkingCospan.Hom.inl)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) := by
  let PF := (fibrantCospanReplacementFunctor (C := C)).obj F
  let η : F ⟶ PF := (fibrantCospanReplacementUnit (C := C)).app F
  let _ : Fibration (PF.map WalkingCospan.Hom.inl) :=
    fibrantCospanReplacement_inl_fibration F
  let _ : IsFibrant (PF.obj WalkingCospan.one) :=
    fibrantCospanReplacement_one_fibrant F
  let _ : Fibration (PF.map WalkingCospan.Hom.inr) :=
    fibrantCospanReplacement_inr_fibration F
  let _ : IsFibrant (PF.obj WalkingCospan.right) :=
    isFibrant_of_fibration (PF.map WalkingCospan.Hom.inr)
  change WeakEquivalence (lim.map η)
  exact weakEquivalence_limitMap_of_fibrant_cospans_inl η
    (fun j => ((mem_trivialCofibrations_iff (η.app j)).1
      (fibrantCospanReplacementUnit_trivialCofibration F j)).2)

theorem weakEquivalence_homotopyPullbackComparison_of_inr
    (F : WalkingCospan ⥤ C)
    [IsFibrant (F.obj WalkingCospan.one)]
    [IsFibrant (F.obj WalkingCospan.left)]
    [Fibration (F.map WalkingCospan.Hom.inr)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) := by
  let PF := (fibrantCospanReplacementFunctor (C := C)).obj F
  let η : F ⟶ PF := (fibrantCospanReplacementUnit (C := C)).app F
  let _ : Fibration (PF.map WalkingCospan.Hom.inr) :=
    fibrantCospanReplacement_inr_fibration F
  let _ : IsFibrant (PF.obj WalkingCospan.one) :=
    fibrantCospanReplacement_one_fibrant F
  let _ : Fibration (PF.map WalkingCospan.Hom.inl) :=
    fibrantCospanReplacement_inl_fibration F
  let _ : IsFibrant (PF.obj WalkingCospan.left) :=
    isFibrant_of_fibration (PF.map WalkingCospan.Hom.inl)
  change WeakEquivalence (lim.map η)
  exact weakEquivalence_limitMap_of_fibrant_cospans_inr η
    (fun j => ((mem_trivialCofibrations_iff (η.app j)).1
      (fibrantCospanReplacementUnit_trivialCofibration F j)).2)

theorem weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
    [IsRightProper C] (F : WalkingCospan ⥤ C)
    [Fibration (F.map WalkingCospan.Hom.inl)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) := by
  let PF := (fibrantCospanReplacementFunctor (C := C)).obj F
  let η : F ⟶ PF := (fibrantCospanReplacementUnit (C := C)).app F
  let _ : Fibration (PF.map WalkingCospan.Hom.inl) :=
    fibrantCospanReplacement_inl_fibration F
  change WeakEquivalence (lim.map η)
  exact weakEquivalence_limitMap_of_rightProper_inl η
    (fun j => ((mem_trivialCofibrations_iff (η.app j)).1
      (fibrantCospanReplacementUnit_trivialCofibration F j)).2)

theorem weakEquivalence_homotopyPullbackComparison_of_rightProper_inr
    [IsRightProper C] (F : WalkingCospan ⥤ C)
    [Fibration (F.map WalkingCospan.Hom.inr)] :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app F) := by
  let PF := (fibrantCospanReplacementFunctor (C := C)).obj F
  let η : F ⟶ PF := (fibrantCospanReplacementUnit (C := C)).app F
  let _ : Fibration (PF.map WalkingCospan.Hom.inr) :=
    fibrantCospanReplacement_inr_fibration F
  change WeakEquivalence (lim.map η)
  exact IsRightProper.weakEquivalence_limitMap_of_inr η
    (fun j => ((mem_trivialCofibrations_iff (η.app j)).1
      (fibrantCospanReplacementUnit_trivialCofibration F j)).2)

/-- An arbitrary fibrant cospan replacement admits a weak comparison from
the named functorial homotopy pullback under the ordinary cospan limit. -/
theorem FibrantCospanReplacement.exists_weakEquivalence_from_homotopyPullback
    {D : WalkingCospan ⥤ C} (R : FibrantCospanReplacement D) :
    ∃ f : (homotopyPullback (C := C)).obj D ⟶ R.pullbackObj,
      WeakEquivalence f ∧
        (homotopyPullbackComparison (C := C)).app D ≫ f =
          R.fromPullback := by
  let S := functorialFibrantCospanReplacement (C := C) D
  obtain ⟨f, hf, hfac⟩ :=
    FibrantCospanReplacement.exists_weakEquivalence_pullbackObj R S
  exact ⟨f, hf, hfac⟩

/-- Weakness of the named homotopy-pullback comparison is equivalent to
weakness for any arbitrary fibrant cospan replacement. -/
theorem FibrantCospanReplacement.weakEquivalence_homotopyPullbackComparison_iff
    {D : WalkingCospan ⥤ C} (R : FibrantCospanReplacement D) :
    WeakEquivalence ((homotopyPullbackComparison (C := C)).app D) ↔
      WeakEquivalence R.fromPullback := by
  let S := functorialFibrantCospanReplacement (C := C) D
  have h := FibrantCospanReplacement.weakEquivalence_fromPullback_iff S R
  change WeakEquivalence S.fromPullback ↔ WeakEquivalence R.fromPullback
  exact h

/-- The chosen fibrant cospan replacement functor used by `homotopyPullback`. -/
@[no_expose]
noncomputable abbrev homotopyPullbackReplacementFunctor :
    (WalkingCospan ⥤ C) ⥤ (WalkingCospan ⥤ C) :=
  fibrantCospanReplacementFunctor (C := C)

/-- The unit of the chosen replacement used by `homotopyPullback`. -/
@[no_expose]
noncomputable abbrev homotopyPullbackReplacementUnit :
    (𝟭 (WalkingCospan ⥤ C) :
      (WalkingCospan ⥤ C) ⥤ (WalkingCospan ⥤ C)) ⟶
        homotopyPullbackReplacementFunctor (C := C) :=
  fibrantCospanReplacementUnit (C := C)

/-- The actual fibrant cospan replacement used by the canonical homotopy pullback. -/
@[no_expose]
noncomputable abbrev homotopyPullbackReplacement (F : WalkingCospan ⥤ C) :
    FibrantCospanReplacement F :=
  functorialFibrantCospanReplacement (C := C) F

/-- The replacement record stores the object of the chosen replacement functor. -/
theorem homotopyPullbackReplacement_P (F : WalkingCospan ⥤ C) :
    (homotopyPullbackReplacement (C := C) F).P =
      (homotopyPullbackReplacementFunctor (C := C)).obj F := by
  with_unfolding_all rfl

/-- The replacement record stores the component of the chosen replacement unit. -/
theorem homotopyPullbackReplacement_unit (F : WalkingCospan ⥤ C) :
    (homotopyPullbackReplacement (C := C) F).unit ≫
      eqToHom (homotopyPullbackReplacement_P (C := C) F) =
        (homotopyPullbackReplacementUnit (C := C)).app F := by
  with_unfolding_all exact (Category.comp_id
    ((homotopyPullbackReplacementUnit (C := C)).app F))

/-- The canonical homotopy pullback is the limit of its actual replacement diagram. -/
theorem homotopyPullback_obj (F : WalkingCospan ⥤ C) :
    (homotopyPullback (C := C)).obj F =
      limit ((homotopyPullbackReplacementFunctor (C := C)).obj F) := by
  with_unfolding_all rfl

/-- The canonical homotopy pullback map is the limit map of its actual replacement,
with the source and target identified by `homotopyPullback_obj`. -/
theorem homotopyPullback_map {F G : WalkingCospan ⥤ C} (η : F ⟶ G) :
    (homotopyPullback (C := C)).map η =
      eqToHom (homotopyPullback_obj (C := C) F) ≫
        lim.map ((homotopyPullbackReplacementFunctor (C := C)).map η) ≫
          eqToHom (homotopyPullback_obj (C := C) G).symm := by
  with_unfolding_all change (lim.map ((fibrantCospanReplacementFunctor (C := C)).map η) =
    (𝟙 _) ≫ lim.map ((fibrantCospanReplacementFunctor (C := C)).map η) ≫ 𝟙 _)
  simp only [Category.id_comp, Category.comp_id]

/-- The canonical homotopy-pullback comparison retains the exact chosen replacement unit. -/
theorem homotopyPullbackComparison_replacement (F : WalkingCospan ⥤ C) :
    (homotopyPullbackComparison (C := C)).app F ≫
      eqToHom (homotopyPullback_obj (C := C) F) =
        lim.map ((homotopyPullbackReplacementUnit (C := C)).app F) := by
  with_unfolding_all change (lim.map ((fibrantCospanReplacementUnit (C := C)).app F) ≫ (𝟙 _) =
    lim.map ((fibrantCospanReplacementUnit (C := C)).app F))
  exact Category.comp_id _

end HomotopicalAlgebra
