/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.WeaklyPointedLoopComponentsWeakHomotopy
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0RealizationNaturality
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagLoopNaturality
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagLoopWeakEquivalence

set_option linter.style.longLine false

/-!
# Group-level naturality for the Quillen Q/S zigzag

Pointwise loop naturality descends to path components and fundamental
groups.  Since both legs of the Quillen Q/S loop zigzag are weak homotopy
equivalences, their component maps and fundamental-group homomorphisms are
bijective.  Inverting the Q leg algebraically and following the Stage leg
therefore gives natural Q-to-Stage comparisons, and the existing Stage
comparison identifies them naturally with Waldhausen `K₀`.

The component comparison is an `Equiv`, not an `AddEquiv`: no group
structure is installed on loop components.  The inverse of the Q leg is
only algebraic.  This file constructs no direct continuous, pointed, or
homotopy inverse, strict loop-map equality, spectrum map, or infinite-loop
comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open ContinuousMap.WeaklyPointed

universe v u

namespace AlgebraicKTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The Waldhausen structure derived from the source exact category, used in
the original Quillen/Stage group comparison. -/
local instance quillenQSZigzagGroupNaturalityWaldhausenC :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The Waldhausen structure derived from the target exact category, used in
the original Quillen/Stage group comparison. -/
local instance quillenQSZigzagGroupNaturalityWaldhausenD :
    WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

namespace QuillenQSZigzagGroupNaturality.Internal

/-- Component map induced by the Q-side weakly pointed leg. -/
noncomputable def quillenStageGridToNQPiZeroMap (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (quillenStageGridDiagonalKSpace C) →
      ZerothHomotopy (NQKSpace C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact (quillenStageGridToNQWeaklyPointed (C := C)).loopComponentsMap

/-- Component map induced by the Stage-side weakly pointed leg. -/
noncomputable def quillenStageGridToStagePiZeroMap (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (quillenStageGridDiagonalKSpace C) →
      ZerothHomotopy (stageWeakDiagonalKSpace C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact (quillenStageGridToStageWeaklyPointed (C := C)).loopComponentsMap

/-- Component map induced by the realized exact-functor Stage-grid map. -/
noncomputable def quillenStageGridDiagonalKSpacePiZeroMap :
    ZerothHomotopy (quillenStageGridDiagonalKSpace C) →
      ZerothHomotopy (quillenStageGridDiagonalKSpace D) :=
  (quillenStageGridDiagonalRealMapWeaklyPointed F
    (quillenStageGridZeroComparisonCoherence F).rootPath).loopComponentsMap

end QuillenQSZigzagGroupNaturality.Internal

open QuillenQSZigzagGroupNaturality.Internal

/-- Component map on the Quillen loop-space model induced by an additive
exact functor. -/
noncomputable def NQKSpacePiZeroMap :
    ZerothHomotopy (NQKSpace C) → ZerothHomotopy (NQKSpace D) :=
  (NQRealMapWeaklyPointed F).loopComponentsMap

namespace QuillenQSZigzagGroupNaturality.Internal

/-- Naturality of the Q-side component map, with the map-first route on the
left. -/
theorem quillenStageGridToNQPiZeroMap_naturality
    (q : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    quillenStageGridToNQPiZeroMap D
        (quillenStageGridDiagonalKSpacePiZeroMap F q) =
      NQKSpacePiZeroMap F (quillenStageGridToNQPiZeroMap C q) := by
  induction q using ZerothHomotopy.rec with
  | mk gamma =>
      simp only [quillenStageGridToNQPiZeroMap,
        quillenStageGridDiagonalKSpacePiZeroMap, NQKSpacePiZeroMap,
        ContinuousMap.WeaklyPointed.loopComponentsMap_mk]
      exact zerothHomotopy_mk_eq_of_pathHomotopic
        ((loopMap_comp_homotopic
            (quillenStageGridDiagonalRealMapWeaklyPointed F
              (quillenStageGridZeroComparisonCoherence F).rootPath)
            (quillenStageGridToNQWeaklyPointed (C := D)) gamma).symm.trans
          ((quillenStageGridToNQLoopMap_naturality F gamma).trans
            (loopMap_comp_homotopic
              (quillenStageGridToNQWeaklyPointed (C := C))
              (NQRealMapWeaklyPointed F) gamma)))

/-- Naturality of the Stage-side component map, with the map-first route on
the left. -/
theorem quillenStageGridToStagePiZeroMap_naturality
    (q : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    quillenStageGridToStagePiZeroMap D
        (quillenStageGridDiagonalKSpacePiZeroMap F q) =
      stageWeakDiagonalKSpacePiZeroMap C D F
        (quillenStageGridToStagePiZeroMap C q) := by
  induction q using ZerothHomotopy.rec with
  | mk gamma =>
      simp only [quillenStageGridToStagePiZeroMap,
        quillenStageGridDiagonalKSpacePiZeroMap,
        ContinuousMap.WeaklyPointed.loopComponentsMap_mk]
      exact zerothHomotopy_mk_eq_of_pathHomotopic
        ((loopMap_comp_homotopic
            (quillenStageGridDiagonalRealMapWeaklyPointed F
              (quillenStageGridZeroComparisonCoherence F).rootPath)
            (quillenStageGridToStageWeaklyPointed (C := D)) gamma).symm.trans
          ((quillenStageGridToStageLoopMap_naturality F gamma).trans
            (loopMap_comp_homotopic
              (quillenStageGridToStageWeaklyPointed (C := C))
              (stageWeakDiagonalRealMapWeaklyPointed C D F) gamma)))

/-- Fundamental-group homomorphism induced by the Q-side weakly pointed
leg. -/
noncomputable def quillenStageGridToNQFundamentalMap (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    FundamentalGroup (quillenStageGridDiagonalReal C)
        (quillenStageGridDiagonalReal.basepoint C) →*
      FundamentalGroup (NQReal C) (NQReal.basepoint C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact basedFundamentalGroupMap
    (quillenStageGridToNQWeaklyPointed (C := C)).hom
    (quillenStageGridToNQWeaklyPointed (C := C)).rootPath

/-- Fundamental-group homomorphism induced by the Stage-side weakly pointed
leg. -/
noncomputable def quillenStageGridToStageFundamentalMap (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    FundamentalGroup (quillenStageGridDiagonalReal C)
        (quillenStageGridDiagonalReal.basepoint C) →*
      FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact basedFundamentalGroupMap
    (quillenStageGridToStageWeaklyPointed (C := C)).hom
    (quillenStageGridToStageWeaklyPointed (C := C)).rootPath

/-- Fundamental-group homomorphism induced by the realized exact-functor
Stage-grid map. -/
noncomputable def quillenStageGridDiagonalFundamentalMap :
    FundamentalGroup (quillenStageGridDiagonalReal C)
        (quillenStageGridDiagonalReal.basepoint C) →*
      FundamentalGroup (quillenStageGridDiagonalReal D)
        (quillenStageGridDiagonalReal.basepoint D) :=
  basedFundamentalGroupMap
    (quillenStageGridDiagonalRealMapWeaklyPointed F
      (quillenStageGridZeroComparisonCoherence F).rootPath).hom
    (quillenStageGridZeroComparisonCoherence F).rootPath

end QuillenQSZigzagGroupNaturality.Internal

/-- Fundamental-group homomorphism on the Quillen realization induced by an
additive exact functor. -/
noncomputable def NQTopologicalFundamentalMap :
    FundamentalGroup (NQReal C) (NQReal.basepoint C) →*
      FundamentalGroup (NQReal D) (NQReal.basepoint D) :=
  basedFundamentalGroupMap
    (NQRealMapWeaklyPointed F).hom (NQRealMapWeaklyPointed F).rootPath

namespace QuillenQSZigzagGroupNaturality.Internal

/-- Naturality of the Q-side fundamental-group homomorphism, with the
map-first route on the left. -/
theorem quillenStageGridToNQFundamentalMap_naturality
    (g : FundamentalGroup (quillenStageGridDiagonalReal C)
      (quillenStageGridDiagonalReal.basepoint C)) :
    quillenStageGridToNQFundamentalMap D
        (quillenStageGridDiagonalFundamentalMap F g) =
      NQTopologicalFundamentalMap F
        (quillenStageGridToNQFundamentalMap C g) := by
  rcases g with ⟨g⟩
  obtain ⟨gamma, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  simp only [quillenStageGridToNQFundamentalMap,
    quillenStageGridDiagonalFundamentalMap, NQTopologicalFundamentalMap,
    basedFundamentalGroupMap_mk]
  apply End.ext
  apply Path.Homotopic.Quotient.eq.mpr
  exact (loopMap_comp_homotopic
      (quillenStageGridDiagonalRealMapWeaklyPointed F
        (quillenStageGridZeroComparisonCoherence F).rootPath)
      (quillenStageGridToNQWeaklyPointed (C := D)) gamma).symm.trans
    ((quillenStageGridToNQLoopMap_naturality F gamma).trans
      (loopMap_comp_homotopic
        (quillenStageGridToNQWeaklyPointed (C := C))
        (NQRealMapWeaklyPointed F) gamma))

/-- Naturality of the Stage-side fundamental-group homomorphism, with the
map-first route on the left. -/
theorem quillenStageGridToStageFundamentalMap_naturality
    (g : FundamentalGroup (quillenStageGridDiagonalReal C)
      (quillenStageGridDiagonalReal.basepoint C)) :
    quillenStageGridToStageFundamentalMap D
        (quillenStageGridDiagonalFundamentalMap F g) =
      stageWeakDiagonalTopologicalFundamentalMap C D F
        (quillenStageGridToStageFundamentalMap C g) := by
  rcases g with ⟨g⟩
  obtain ⟨gamma, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  simp only [quillenStageGridToStageFundamentalMap,
    quillenStageGridDiagonalFundamentalMap,
    stageWeakDiagonalTopologicalFundamentalMap,
    basedFundamentalGroupMap_mk]
  apply End.ext
  apply Path.Homotopic.Quotient.eq.mpr
  exact (loopMap_comp_homotopic
      (quillenStageGridDiagonalRealMapWeaklyPointed F
        (quillenStageGridZeroComparisonCoherence F).rootPath)
      (quillenStageGridToStageWeaklyPointed (C := D)) gamma).symm.trans
    ((quillenStageGridToStageLoopMap_naturality F gamma).trans
      (loopMap_comp_homotopic
        (quillenStageGridToStageWeaklyPointed (C := C))
        (stageWeakDiagonalRealMapWeaklyPointed C D F) gamma))

/-- Multiplicative equivalence induced by the Q-side leg. -/
noncomputable def quillenStageGridToNQFundamentalMulEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    FundamentalGroup (quillenStageGridDiagonalReal C)
        (quillenStageGridDiagonalReal.basepoint C) ≃*
      FundamentalGroup (NQReal C) (NQReal.basepoint C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact fundamentalGroupMulEquivOfLoopMapWeakEquivalence
    (quillenStageGridToNQWeaklyPointed (C := C))
    (quillenStageGridToNQLoopMap_mem_weakHomotopyEquivalences (C := C))

/-- Multiplicative equivalence induced by the Stage-side leg. -/
noncomputable def quillenStageGridToStageFundamentalMulEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    FundamentalGroup (quillenStageGridDiagonalReal C)
        (quillenStageGridDiagonalReal.basepoint C) ≃*
      FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact fundamentalGroupMulEquivOfLoopMapWeakEquivalence
    (quillenStageGridToStageWeaklyPointed (C := C))
    (quillenStageGridToStageLoopMap_mem_weakHomotopyEquivalences (C := C))

end QuillenQSZigzagGroupNaturality.Internal

/-- Algebraic Q-to-Stage comparison on topological fundamental groups:
invert the Q leg and then follow the Stage leg. -/
noncomputable def quillenQStageFundamentalMulEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    FundamentalGroup (NQReal C) (NQReal.basepoint C) ≃*
      FundamentalGroup (stageWeakDiagonalReal C)
        (stageWeakDiagonalReal.basepoint C) :=
  (quillenStageGridToNQFundamentalMulEquiv C).symm.trans
    (quillenStageGridToStageFundamentalMulEquiv C)

/-- The algebraic Q-to-Stage fundamental-group comparison is natural for
additive exact functors. -/
theorem quillenQStageFundamentalMulEquiv_naturality
    (q : FundamentalGroup (NQReal C) (NQReal.basepoint C)) :
    quillenQStageFundamentalMulEquiv D
        (NQTopologicalFundamentalMap F q) =
      stageWeakDiagonalTopologicalFundamentalMap C D F
        (quillenQStageFundamentalMulEquiv C q) := by
  let qC := quillenStageGridToNQFundamentalMulEquiv C
  let qD := quillenStageGridToNQFundamentalMulEquiv D
  let g := qC.symm q
  have hq : qD (quillenStageGridDiagonalFundamentalMap F g) =
      NQTopologicalFundamentalMap F q := by
    dsimp only [qD, quillenStageGridToNQFundamentalMulEquiv,
      fundamentalGroupMulEquivOfLoopMapWeakEquivalence]
    change quillenStageGridToNQFundamentalMap D
        (quillenStageGridDiagonalFundamentalMap F g) = _
    rw [quillenStageGridToNQFundamentalMap_naturality]
    change NQTopologicalFundamentalMap F (qC g) = _
    rw [show qC g = q from qC.apply_symm_apply q]
  change quillenStageGridToStageFundamentalMulEquiv D
      ((quillenStageGridToNQFundamentalMulEquiv D).symm
        (NQTopologicalFundamentalMap F q)) =
    stageWeakDiagonalTopologicalFundamentalMap C D F
      (quillenStageGridToStageFundamentalMulEquiv C
        ((quillenStageGridToNQFundamentalMulEquiv C).symm q))
  rw [← hq,
    (quillenStageGridToNQFundamentalMulEquiv D).symm_apply_apply]
  dsimp only [quillenStageGridToStageFundamentalMulEquiv,
    fundamentalGroupMulEquivOfLoopMapWeakEquivalence]
  change quillenStageGridToStageFundamentalMap D
      (quillenStageGridDiagonalFundamentalMap F g) = _
  rw [quillenStageGridToStageFundamentalMap_naturality]
  rfl

namespace QuillenQSZigzagGroupNaturality.Internal

/-- Naturality of the realized Stage fundamental-group comparison with
Waldhausen `K₀`, obtained from the combinatorial and realization squares. -/
theorem stageWeakDiagonalRealizedFundamentalK0MulEquiv_naturality
    (g : FundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C)) :
    stageWeakDiagonalRealizedFundamentalK0MulEquiv D
        (stageWeakDiagonalTopologicalFundamentalMap C D F g) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd
            (stageWeakDiagonalRealizedFundamentalK0MulEquiv C g))) := by
  let eC := stageWeakDiagonalRealizationFundamentalMulEquiv C
  let eD := stageWeakDiagonalRealizationFundamentalMulEquiv D
  let a := eC.symm g
  have htop :=
    stageWeakDiagonalRealizationFundamentalMulEquiv_naturality C D F a
  change stageWeakDiagonalFundamentalK0MulEquiv D
      (eD.symm (stageWeakDiagonalTopologicalFundamentalMap C D F g)) = _
  have htransport :
      eD.symm (stageWeakDiagonalTopologicalFundamentalMap C D F g) =
        stageWeakDiagonalFundamentalMap C D F a := by
    rw [← show eC a = g from eC.apply_symm_apply g, ← htop,
      eD.symm_apply_apply]
  rw [htransport]
  exact stageWeakDiagonalFundamentalK0MulEquiv_naturality C D F a

end QuillenQSZigzagGroupNaturality.Internal

/-- Natural multiplicative comparison between the topological Quillen
fundamental group and Waldhausen `K₀`. -/
noncomputable def NQRealizedFundamentalK0MulEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    FundamentalGroup (NQReal C) (NQReal.basepoint C) ≃*
      Multiplicative (WaldhausenKTheory.K0 C) :=
  (quillenQStageFundamentalMulEquiv C).trans
    (stageWeakDiagonalRealizedFundamentalK0MulEquiv C)

/-- Naturality of the topological Quillen fundamental-group comparison with
Waldhausen `K₀`. -/
theorem NQRealizedFundamentalK0MulEquiv_naturality
    (q : FundamentalGroup (NQReal C) (NQReal.basepoint C)) :
    NQRealizedFundamentalK0MulEquiv D
        (NQTopologicalFundamentalMap F q) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd
            (NQRealizedFundamentalK0MulEquiv C q))) := by
  change stageWeakDiagonalRealizedFundamentalK0MulEquiv D
      (quillenQStageFundamentalMulEquiv D
        (NQTopologicalFundamentalMap F q)) = _
  rw [quillenQStageFundamentalMulEquiv_naturality]
  exact stageWeakDiagonalRealizedFundamentalK0MulEquiv_naturality F
    (quillenQStageFundamentalMulEquiv C q)

namespace QuillenQSZigzagGroupNaturality.Internal

/-- Component equivalence induced by the Q-side leg. -/
noncomputable def quillenStageGridToNQPiZeroEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (quillenStageGridDiagonalKSpace C) ≃
      ZerothHomotopy (NQKSpace C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact Equiv.ofBijective (quillenStageGridToNQPiZeroMap C)
    (loopComponentsMap_bijective_of_loopMap_weakEquivalence
      (quillenStageGridToNQWeaklyPointed (C := C))
      (quillenStageGridToNQLoopMap_mem_weakHomotopyEquivalences (C := C)))

/-- Component equivalence induced by the Stage-side leg. -/
noncomputable def quillenStageGridToStagePiZeroEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (quillenStageGridDiagonalKSpace C) ≃
      ZerothHomotopy (stageWeakDiagonalKSpace C) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  exact Equiv.ofBijective (quillenStageGridToStagePiZeroMap C)
    (loopComponentsMap_bijective_of_loopMap_weakEquivalence
      (quillenStageGridToStageWeaklyPointed (C := C))
      (quillenStageGridToStageLoopMap_mem_weakHomotopyEquivalences (C := C)))

end QuillenQSZigzagGroupNaturality.Internal

/-- Algebraic Q-to-Stage comparison on loop-space path components: invert
the Q leg and then follow the Stage leg. -/
noncomputable def quillenQStageKSpacePiZeroEquiv (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (NQKSpace C) ≃
      ZerothHomotopy (stageWeakDiagonalKSpace C) :=
  (quillenStageGridToNQPiZeroEquiv C).symm.trans
    (quillenStageGridToStagePiZeroEquiv C)

/-- The algebraic Q-to-Stage component comparison is natural for additive
exact functors. -/
theorem quillenQStageKSpacePiZeroEquiv_naturality
    (q : ZerothHomotopy (NQKSpace C)) :
    quillenQStageKSpacePiZeroEquiv D (NQKSpacePiZeroMap F q) =
      stageWeakDiagonalKSpacePiZeroMap C D F
        (quillenQStageKSpacePiZeroEquiv C q) := by
  let qC := quillenStageGridToNQPiZeroEquiv C
  let qD := quillenStageGridToNQPiZeroEquiv D
  let g := qC.symm q
  have hq : qD (quillenStageGridDiagonalKSpacePiZeroMap F g) =
      NQKSpacePiZeroMap F q := by
    change quillenStageGridToNQPiZeroMap D
        (quillenStageGridDiagonalKSpacePiZeroMap F g) = _
    rw [quillenStageGridToNQPiZeroMap_naturality]
    change NQKSpacePiZeroMap F (qC g) = _
    rw [show qC g = q from qC.apply_symm_apply q]
  change quillenStageGridToStagePiZeroEquiv D
      ((quillenStageGridToNQPiZeroEquiv D).symm
        (NQKSpacePiZeroMap F q)) =
    stageWeakDiagonalKSpacePiZeroMap C D F
      (quillenStageGridToStagePiZeroEquiv C
        ((quillenStageGridToNQPiZeroEquiv C).symm q))
  rw [← hq, (quillenStageGridToNQPiZeroEquiv D).symm_apply_apply]
  change quillenStageGridToStagePiZeroMap D
      (quillenStageGridDiagonalKSpacePiZeroMap F g) = _
  rw [quillenStageGridToStagePiZeroMap_naturality]
  rfl

/-- Natural equivalence from Quillen loop-space components to Waldhausen
`K₀`. -/
noncomputable def NQKSpacePiZeroEquivK0 (C : Type u)
    [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] :
    ZerothHomotopy (NQKSpace C) ≃ WaldhausenKTheory.K0 C :=
  (quillenQStageKSpacePiZeroEquiv C).trans
    (stageWeakDiagonalKSpacePiZeroEquivK0 C)

/-- Naturality of the Quillen component comparison with Waldhausen `K₀`. -/
theorem NQKSpacePiZeroEquivK0_naturality
    (q : ZerothHomotopy (NQKSpace C)) :
    NQKSpacePiZeroEquivK0 D (NQKSpacePiZeroMap F q) =
      WaldhausenKTheory.K0.map F (NQKSpacePiZeroEquivK0 C q) := by
  let qC := quillenStageGridToNQPiZeroEquiv C
  let qD := quillenStageGridToNQPiZeroEquiv D
  let sC := quillenStageGridToStagePiZeroEquiv C
  let sD := quillenStageGridToStagePiZeroEquiv D
  let g := qC.symm q
  have hq : qD (quillenStageGridDiagonalKSpacePiZeroMap F g) =
      NQKSpacePiZeroMap F q := by
    change quillenStageGridToNQPiZeroMap D
        (quillenStageGridDiagonalKSpacePiZeroMap F g) = _
    rw [quillenStageGridToNQPiZeroMap_naturality]
    change NQKSpacePiZeroMap F (qC g) = _
    rw [show qC g = q from qC.apply_symm_apply q]
  have hqInv : qD.symm (NQKSpacePiZeroMap F q) =
      quillenStageGridDiagonalKSpacePiZeroMap F g := by
    rw [← hq, qD.symm_apply_apply]
  change stageWeakDiagonalKSpacePiZeroEquivK0 D
      (sD (qD.symm (NQKSpacePiZeroMap F q))) =
    WaldhausenKTheory.K0.map F
      (stageWeakDiagonalKSpacePiZeroEquivK0 C (sC (qC.symm q)))
  rw [hqInv]
  change stageWeakDiagonalKSpacePiZeroEquivK0 D
      (quillenStageGridToStagePiZeroMap D
        (quillenStageGridDiagonalKSpacePiZeroMap F g)) = _
  rw [quillenStageGridToStagePiZeroMap_naturality]
  rw [stageWeakDiagonalKSpacePiZeroEquivK0_naturality]
  rfl

end AlgebraicKTheory


public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction

universe uK vK

namespace AlgebraicKTheory

variable (C : Type uK) [Category.{vK} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The original Q-leg equivalence has the actual weakly pointed component map as forward map. -/
theorem quillenStageGridToNQPiZeroEquiv_apply
    (g : ZerothHomotopy (quillenStageGridDiagonalKSpace C)) :
    QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToNQPiZeroEquiv C g =
      (quillenStageGridToNQWeaklyPointed (C := C)).loopComponentsMap g := rfl

/-- The original Stage-leg equivalence has the actual weakly pointed component map as forward map. -/
theorem quillenStageGridToStagePiZeroEquiv_apply
    (g : (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      ZerothHomotopy (quillenStageGridDiagonalKSpace C))) :
    letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
    QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToStagePiZeroEquiv C g =
      (quillenStageGridToStageWeaklyPointed (C := C)).loopComponentsMap g := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  rfl

/-- The original Q/K-zero comparison retains the algebraic inverse of its Q leg. -/
theorem NQKSpacePiZeroEquivK0_apply (a : ZerothHomotopy (NQKSpace C)) :
    letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
    NQKSpacePiZeroEquivK0 C a =
      stageWeakDiagonalKSpacePiZeroEquivK0 C
        (QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToStagePiZeroEquiv C
          ((QuillenQSZigzagGroupNaturality.Internal.quillenStageGridToNQPiZeroEquiv C).symm a)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  rfl

end AlgebraicKTheory

end
