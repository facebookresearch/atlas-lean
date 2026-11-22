/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCoreEndpointDiagonalHomotopyFibre
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The original zero-power core and its actual diagonal pair base

The Rezk 6.1 comparison is flattened using Raw20's actual zero-power Iso and
the diagonal's actual binary-product comparison. The base map is the original
raw coaugmentation on BOTH object factors. No Raw-base Kan, diagonal fibration,
core weakness or completion outcome is a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw

private theorem pairMap_comp_fst {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (prod.map f f ≫ prod.map g g) ≫ prod.fst = prod.fst ≫ f ≫ g := by
  rw [Category.assoc, prod.map_fst, ← Category.assoc, prod.map_fst, Category.assoc]

private theorem pairMap_comp_snd {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (prod.map f f ≫ prod.map g g) ≫ prod.snd = prod.snd ≫ f ≫ g := by
  rw [Category.assoc, prod.map_snd, ← Category.assoc, prod.map_snd, Category.assoc]

private theorem coreEndpoint_naturality {A B : SimplicialSpace.{u}}
    (f : A ⟶ B) (hA : segalSpaces A) (hB : segalSpaces B) :
    SegalHomotopy.equivalenceMap f hA hB ≫ SegalHomotopy.coreEndpoint B hB =
      SegalHomotopy.coreEndpoint A hA ≫ prod.map (f.hom.app (op ⦋0⦌)) (f.hom.app (op ⦋0⦌)) := by
  apply prod.hom_ext
  · simp only [SegalHomotopy.coreEndpoint,
      Category.assoc, prod.lift_fst, prod.lift_fst_assoc, prod.map_fst]
    exact SegalHomotopy.equivalenceSource_naturality f hA hB
  · simp only [SegalHomotopy.coreEndpoint,
      Category.assoc, prod.lift_snd, prod.lift_snd_assoc, prod.map_snd]
    exact SegalHomotopy.equivalenceTarget_naturality f hA hB

set_option linter.unusedVariables false in
/-- The first projection of every actual ordered coefficient-power pair. -/
def originalCorePairFst (W : SimplicialSpace.{u}) :
    originalCorePairDiagram W ⟶ rowPowerDiagram W (op ⦋0⦌) where
  app n := prod.fst
  naturality n m f := prod.map_fst _ _

set_option linter.unusedVariables false in
/-- The second projection retains the same coefficient and all operators. -/
def originalCorePairSnd (W : SimplicialSpace.{u}) :
    originalCorePairDiagram W ⟶ rowPowerDiagram W (op ⦋0⦌) where
  app n := prod.snd
  naturality n m f := prod.map_snd _ _

/-- The actual pair diagram is a binary product, proved by both evaluations. -/
def originalCorePairIsLimit (W : SimplicialSpace.{u}) :
    IsLimit (BinaryFan.mk (originalCorePairFst W) (originalCorePairSnd W)) :=
  evaluationJointlyReflectsLimits _ fun n =>
    (isLimitMapConeBinaryFanEquiv ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj n)
      (originalCorePairFst W) (originalCorePairSnd W)).symm
      (prodIsProd _ _)

/-- The preserved binary fan uses the actual diagonal maps of BOTH legs. -/
def originalCorePairDiagonalIsLimit (W : SimplicialSpace.{u}) :
    IsLimit (BinaryFan.mk
      (SSet.simplicialDiagonalFunctor.map (originalCorePairFst W))
      (SSet.simplicialDiagonalFunctor.map (originalCorePairSnd W))) :=
  mapIsLimitOfPreservesOfIsLimit SSet.simplicialDiagonalFunctor
    (originalCorePairFst W) (originalCorePairSnd W) (originalCorePairIsLimit W)

/-- The original pair diagonal is canonically Raw(W)₀ × Raw(W)₀. -/
def originalCorePairDiagonalIso (W : SimplicialSpace.{u}) :
    SSet.simplicialDiagonalFunctor.obj (originalCorePairDiagram W) ≅
      (rawCompletion W).diagram _⦋0⦌ ⨯ (rawCompletion W).diagram _⦋0⦌ :=
  IsLimit.conePointUniqueUpToIso
    (t := BinaryFan.mk (prod.fst : (rawCompletion W).diagram _⦋0⦌ ⨯
      (rawCompletion W).diagram _⦋0⦌ ⟶ (rawCompletion W).diagram _⦋0⦌) prod.snd)
    (originalCorePairDiagonalIsLimit W)
    (prodIsProd ((rawCompletion W).diagram _⦋0⦌) ((rawCompletion W).diagram _⦋0⦌))

/-- All four native binary-product projection equations are retained. -/
theorem originalCorePairDiagonalIso_legs (W : SimplicialSpace.{u}) :
    (originalCorePairDiagonalIso W).hom ≫ prod.fst =
        SSet.simplicialDiagonalFunctor.map (originalCorePairFst W) ∧
      (originalCorePairDiagonalIso W).hom ≫ prod.snd =
        SSet.simplicialDiagonalFunctor.map (originalCorePairSnd W) ∧
      (originalCorePairDiagonalIso W).inv ≫
          SSet.simplicialDiagonalFunctor.map (originalCorePairFst W) = prod.fst ∧
      (originalCorePairDiagonalIso W).inv ≫
          SSet.simplicialDiagonalFunctor.map (originalCorePairSnd W) = prod.snd :=
  ⟨IsLimit.conePointUniqueUpToIso_hom_comp (originalCorePairDiagonalIsLimit W)
      (prodIsProd ((rawCompletion W).diagram _⦋0⦌) ((rawCompletion W).diagram _⦋0⦌))
      (Discrete.mk WalkingPair.left),
    IsLimit.conePointUniqueUpToIso_hom_comp (originalCorePairDiagonalIsLimit W)
      (prodIsProd ((rawCompletion W).diagram _⦋0⦌) ((rawCompletion W).diagram _⦋0⦌))
      (Discrete.mk WalkingPair.right),
    IsLimit.conePointUniqueUpToIso_inv_comp (originalCorePairDiagonalIsLimit W)
      (prodIsProd ((rawCompletion W).diagram _⦋0⦌) ((rawCompletion W).diagram _⦋0⦌))
      (Discrete.mk WalkingPair.left),
    IsLimit.conePointUniqueUpToIso_inv_comp (originalCorePairDiagonalIsLimit W)
      (prodIsProd ((rawCompletion W).diagram _⦋0⦌) ((rawCompletion W).diagram _⦋0⦌))
      (Discrete.mk WalkingPair.right)⟩

/-- Raw20's original zero-power Iso in any original outer row. -/
def originalZeroPowerRowIso (W : SimplicialSpace.{u}) (k : SimplexCategoryᵒᵖ) :
    (rowPowerDiagram W k).obj (op ⦋0⦌) ≅ W.diagram.obj k :=
  (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj k).mapIso (powerZeroUnitIso W)

/-- The zero-row map followed by its actual inverse is the original raw unit,
in every scalar degree; this is not merely a vertex identification. -/
theorem originalZeroPowerRowIso_inv_rowVertex (W : SimplicialSpace.{u})
    (k : SimplexCategoryᵒᵖ) :
    (originalZeroPowerRowIso W k).inv ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W k) ⦋0⦌ 0 =
      (rawCompletionUnit W).hom.app k := by
  apply NatTrans.ext
  funext n
  simp only [NatTrans.comp_app, SSet.EquifibredDiagonal.rowVertexToDiagonal_app]
  change (((powerZeroUnitIso W).inv.hom.app k).app n) ≫
      ((((powerDiagram W).map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom.app k).app n) =
    ((((constantPowerSection W).app n).hom.app k).app n)
  have h := (constantPowerSection W).naturality
    (SimplexCategory.const n.unop ⦋0⦌ 0).op
  have h' : (powerZeroUnitIso W).inv ≫
      (powerDiagram W).map (SimplexCategory.const n.unop ⦋0⦌ 0).op =
      (constantPowerSection W).app n := by
    rw [← constantPowerSection_zero_eq_inverse]
    exact h.symm.trans (Category.id_comp _)
  exact congrArg (fun f : W ⟶ (powerDiagram W).obj n => (f.hom.app k).app n) h'

/-- Both directions of the actual zero-row Iso identify the raw unit. -/
theorem originalZeroPowerRowIso_rowVertex (W : SimplicialSpace.{u})
    (k : SimplexCategoryᵒᵖ) :
    SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W k) ⦋0⦌ 0 =
      (originalZeroPowerRowIso W k).hom ≫ (rawCompletionUnit W).hom.app k := by
  calc
    _ = (originalZeroPowerRowIso W k).hom ≫
        ((originalZeroPowerRowIso W k).inv ≫
          SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W k) ⦋0⦌ 0) := by
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = _ := by rw [originalZeroPowerRowIso_inv_rowVertex]; rfl

/-- The genuine zero-power Iso on BOTH ordered object factors. -/
def originalZeroCorePairIso (W : SimplicialSpace.{u}) :
    (originalCorePairDiagram W).obj (op ⦋0⦌) ≅
      (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) :=
  prod.mapIso (originalZeroPowerRowIso W (op ⦋0⦌))
    (originalZeroPowerRowIso W (op ⦋0⦌))

/-- The original raw unit on the source-first and target-second factors. -/
def originalRawUnitPair (W : SimplicialSpace.{u}) :
    (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶
      (rawCompletion W).diagram _⦋0⦌ ⨯ (rawCompletion W).diagram _⦋0⦌ :=
  prod.map ((rawCompletionUnit W).hom.app (op ⦋0⦌))
    ((rawCompletionUnit W).hom.app (op ⦋0⦌))

/-- The actual row-zero pair map is the original raw unit twice, through
the true product and zero-power Isos, with both ordered legs preserved. -/
theorem originalCorePair_rowZero_rawUnit (W : SimplicialSpace.{u}) :
    SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) ⦋0⦌ 0 ≫
        (originalCorePairDiagonalIso W).hom =
      (originalZeroCorePairIso W).hom ≫ originalRawUnitPair W := by
  apply prod.hom_ext
  · rw [Category.assoc, (originalCorePairDiagonalIso_legs W).1]
    have hn : SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) ⦋0⦌ 0 ≫
        SSet.simplicialDiagonalFunctor.map (originalCorePairFst W) =
      (originalCorePairFst W).app (op ⦋0⦌) ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋0⦌)) ⦋0⦌ 0 :=
      SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality (originalCorePairFst W) ⦋0⦌ 0
    refine hn.trans ?_
    change prod.fst ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋0⦌)) ⦋0⦌ 0 = _
    rw [originalZeroPowerRowIso_rowVertex]
    exact (pairMap_comp_fst (originalZeroPowerRowIso W (op ⦋0⦌)).hom
      ((rawCompletionUnit W).hom.app (op ⦋0⦌))).symm
  · rw [Category.assoc, (originalCorePairDiagonalIso_legs W).2.1]
    have hn : SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) ⦋0⦌ 0 ≫
        SSet.simplicialDiagonalFunctor.map (originalCorePairSnd W) =
      (originalCorePairSnd W).app (op ⦋0⦌) ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋0⦌)) ⦋0⦌ 0 :=
      SSet.EquifibredDiagonal.rowVertexToDiagonal_naturality (originalCorePairSnd W) ⦋0⦌ 0
    refine hn.trans ?_
    change prod.snd ≫
        SSet.EquifibredDiagonal.rowVertexToDiagonal (rowPowerDiagram W (op ⦋0⦌)) ⦋0⦌ 0 = _
    rw [originalZeroPowerRowIso_rowVertex]
    exact (pairMap_comp_snd (originalZeroPowerRowIso W (op ⦋0⦌)).hom
      ((rawCompletionUnit W).hom.app (op ⦋0⦌))).symm

/-- The original raw core endpoint, before the fixed baseline β-pair map. -/
def originalRawCoreEndpoint (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    coreDiagonal W hW ⟶
      (rawCompletion W).diagram _⦋0⦌ ⨯ (rawCompletion W).diagram _⦋0⦌ :=
  coreDiagonalInclusion W hW ≫ mappingEndpoint (rawCompletion W)

/-- The endpoint diagonal retains BOTH actual original face maps. -/
theorem originalCoreEndpointDiagonal_pair (W : SimplicialSpace.{u})
    (hW : segalSpaces W) :
    SSet.simplicialDiagonalFunctor.map (originalCoreEndpointDiagram W hW) ≫
        (originalCorePairDiagonalIso W).hom = originalRawCoreEndpoint W hW := by
  apply prod.hom_ext
  · rw [Category.assoc, (originalCorePairDiagonalIso_legs W).1]
    let d : rowPowerDiagram W (op ⦋1⦌) ⟶ rowPowerDiagram W (op ⦋0⦌) :=
      SimplicialObject.δ ((powerDiagram W ⋙ forget).flip) (1 : Fin 2)
    have hd : SSet.simplicialDiagonalFunctor.map d =
        (rawCompletion W).diagram.δ (1 : Fin 2) := by rfl
    have hf : originalCoreEndpointDiagram W hW ≫ originalCorePairFst W =
        corePowerInclusion W hW ≫ d := by
      apply NatTrans.ext
      funext n
      change SegalHomotopy.coreEndpoint ((powerDiagram W).obj n)
          (powerDiagram_segal W hW n) ≫ prod.fst =
        (SegalHomotopy.equivalenceSubcomplex ((powerDiagram W).obj n)
          (powerDiagram_segal W hW n)).ι ≫ ((powerDiagram W).obj n).diagram.δ (1 : Fin 2)
      simp [SegalHomotopy.coreEndpoint, SegalHomotopy.equivalenceSource]
    have hc := (SSet.simplicialDiagonalFunctor.map_comp (originalCoreEndpointDiagram W hW)
      (originalCorePairFst W)).symm
    refine hc.trans ((congrArg SSet.simplicialDiagonalFunctor.map hf).trans ?_)
    rw [SSet.simplicialDiagonalFunctor.map_comp, hd]
    change coreDiagonalInclusion W hW ≫ (rawCompletion W).diagram.δ (1 : Fin 2) =
      originalRawCoreEndpoint W hW ≫ prod.fst
    unfold originalRawCoreEndpoint
    rw [Category.assoc, mappingEndpoint_fst]
  · rw [Category.assoc, (originalCorePairDiagonalIso_legs W).2.1]
    let d : rowPowerDiagram W (op ⦋1⦌) ⟶ rowPowerDiagram W (op ⦋0⦌) :=
      SimplicialObject.δ ((powerDiagram W ⋙ forget).flip) (0 : Fin 2)
    have hd : SSet.simplicialDiagonalFunctor.map d =
        (rawCompletion W).diagram.δ (0 : Fin 2) := by rfl
    have hf : originalCoreEndpointDiagram W hW ≫ originalCorePairSnd W =
        corePowerInclusion W hW ≫ d := by
      apply NatTrans.ext
      funext n
      change SegalHomotopy.coreEndpoint ((powerDiagram W).obj n)
          (powerDiagram_segal W hW n) ≫ prod.snd =
        (SegalHomotopy.equivalenceSubcomplex ((powerDiagram W).obj n)
          (powerDiagram_segal W hW n)).ι ≫ ((powerDiagram W).obj n).diagram.δ (0 : Fin 2)
      simp [SegalHomotopy.coreEndpoint, SegalHomotopy.equivalenceTarget]
    have hc := (SSet.simplicialDiagonalFunctor.map_comp (originalCoreEndpointDiagram W hW)
      (originalCorePairSnd W)).symm
    refine hc.trans ((congrArg SSet.simplicialDiagonalFunctor.map hf).trans ?_)
    rw [SSet.simplicialDiagonalFunctor.map_comp, hd]
    change coreDiagonalInclusion W hW ≫ (rawCompletion W).diagram.δ (0 : Fin 2) =
      originalRawCoreEndpoint W hW ≫ prod.snd
    unfold originalRawCoreEndpoint
    rw [Category.assoc, mappingEndpoint_snd]

/-- Restrict the actual Raw20 zero-power Iso to the complete equivalence core. -/
def originalZeroCoreIso (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (corePowerDiagram W hW).obj (op ⦋0⦌) ≅
        (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) where
  hom := SegalHomotopy.equivalenceMap (powerZeroUnitIso W).hom
    (powerDiagram_segal W hW (op ⦋0⦌)) hW
  inv := SegalHomotopy.equivalenceMap (powerZeroUnitIso W).inv
    hW (powerDiagram_segal W hW (op ⦋0⦌))
  hom_inv_id := by
    have hc := SegalHomotopy.equivalenceMap_comp (powerZeroUnitIso W).hom (powerZeroUnitIso W).inv
      (powerDiagram_segal W hW (op ⦋0⦌)) hW (powerDiagram_segal W hW (op ⦋0⦌))
    have he := congrArg (fun f => SegalHomotopy.equivalenceMap f
      (powerDiagram_segal W hW (op ⦋0⦌)) (powerDiagram_segal W hW (op ⦋0⦌)))
      (powerZeroUnitIso W).hom_inv_id
    exact hc.symm.trans (he.trans (SegalHomotopy.equivalenceMap_id _ _))
  inv_hom_id := by
    have hc := SegalHomotopy.equivalenceMap_comp (powerZeroUnitIso W).inv (powerZeroUnitIso W).hom
      hW (powerDiagram_segal W hW (op ⦋0⦌)) hW
    have he := congrArg (fun f => SegalHomotopy.equivalenceMap f hW hW)
        (powerZeroUnitIso W).inv_hom_id
    exact hc.symm.trans (he.trans (SegalHomotopy.equivalenceMap_id _ _))

/-- Its source and target legs are the original ordered endpoint square. -/
theorem originalZeroCoreIso_endpoint (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (originalZeroCoreIso W hW).hom ≫ SegalHomotopy.coreEndpoint W hW =
      (originalCoreEndpointDiagram W hW).app (op ⦋0⦌) ≫
        (originalZeroCorePairIso W).hom := by
  exact coreEndpoint_naturality (powerZeroUnitIso W).hom
    (powerDiagram_segal W hW (op ⦋0⦌)) hW

/-- The native cospan Iso uses the actual raw endpoint, row-zero pair and
the unchanged whole core diagonal. -/
def originalCoreZeroRawCospanIso (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    cospan (SSet.simplicialDiagonalFunctor.map (originalCoreEndpointDiagram W hW))
        (SSet.EquifibredDiagonal.rowVertexToDiagonal (originalCorePairDiagram W) ⦋0⦌ 0) ≅
      cospan (originalRawCoreEndpoint W hW) (originalRawUnitPair W) :=
  cospanIsoMk (originalCorePairDiagonalIso W) (Iso.refl _) (originalZeroCorePairIso W)
    (by exact (originalCoreEndpointDiagonal_pair W hW).trans (Category.id_comp _).symm)
    (originalCorePair_rowZero_rawUnit W)

/-- The complete original core maps to the native HP over the ORIGINAL raw
unit pair. Both genuine Isos surround the actual Rezk 6.1 kappa. -/
def originalCoreToRawUnitHomotopyPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) ⟶
      (homotopyPullback (C := SSet.{u})).obj
        (cospan (originalRawCoreEndpoint W hW) (originalRawUnitPair W)) :=
  (originalZeroCoreIso W hW).inv ≫
    SSet.RezkOriginal61.kappa (originalCoreEndpointDiagram W hW) ⦋0⦌ 0 ≫
      ((homotopyPullback (C := SSet.{u})).mapIso (originalCoreZeroRawCospanIso W hW)).hom

/-- This actual whole HP comparison is weak by derived Rezk 6.1 and genuine
Isos. RawW₀ Kan, a global core WE and the desired completion are not inputs. -/
theorem originalCoreToRawUnitHomotopyPullback_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) : WeakEquivalence (originalCoreToRawUnitHomotopyPullback W hW) := by
  have hk := (originalCoreEndpointDiagram_all_simplex_and_homotopy_pullback W hW).2.2 ⦋0⦌ 0
  let : WeakEquivalence
      (SSet.RezkOriginal61.kappa (originalCoreEndpointDiagram W hW) ⦋0⦌ 0) := hk
  unfold originalCoreToRawUnitHomotopyPullback
  infer_instance

end SimplicialSpace.RezkCompletionCoreDiagonal
