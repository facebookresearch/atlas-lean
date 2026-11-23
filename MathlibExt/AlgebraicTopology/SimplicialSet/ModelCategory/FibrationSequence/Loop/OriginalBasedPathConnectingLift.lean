/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.HomotopyFunctors
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWHomotopy
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Original based-path lifts and the actual all-degree connecting function

The same original constant-path point inclusion is a split monomorphism
and a genuine trivial cofibration in the existing Kan-Quillen model.
CM4 constructs a full simplicial lift of the original based-path
projection through every actual original pointed fibration sequence.
The literal induced loop-to-fiber map therefore gives the SAME original
connecting function in every degree, including all degree-zero components.
Both original points, the entire projection and every pointed sequence
map naturality on homotopy are retained. No functorial choice of strict
lifts or incoming connecting/action/loop interchange law is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial Opposite
open scoped Simplicial SSet.modelCategoryQuillen

private theorem originalConstantMapAtZero {X Y : SSet.{u}} (y : Y _⦋0⦌) (x : X _⦋0⦌) :
    (SSet.const y).app _ x = y := by
  change Y.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op y = y
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ :=
    Subsingleton.elim _ _
  rw [h, op_id, Y.map_id]
  rfl

private theorem originalPointKan : SSet.KanComplex (Δ[0] : SSet.{u}) :=
  (HomotopicalAlgebra.isFibrant_iff_of_isTerminal
    (𝟙 (Δ[0] : SSet.{u})) SSet.stdSimplex.isTerminalObj₀).mpr inferInstance

namespace SSet.OriginalBasedPathConnectingGeometry

open SSet.LoopShiftOriginalGeometry (originalLoopPoint loopConnectingEquiv)

/-- The original constant-path vertex defines the full actual point inclusion. -/
def basedPathPointMap (X : SSet.{u}) (x : X _⦋0⦌) : (Δ[0] : SSet.{u}) ⟶ basedPath X x :=
  SSet.const (basedPathPoint X x)

/-- The whole original point inclusion retains its original constant-path vertex. -/
theorem basedPathPointMap_point (X : SSet.{u}) (x : X _⦋0⦌) (z : (Δ[0] : SSet.{u}) _⦋0⦌) :
    (basedPathPointMap X x).app _ z = basedPathPoint X x :=
  originalConstantMapAtZero (basedPathPoint X x) z

/-- The entire original point inclusion has its genuine original terminal retraction. -/
def basedPathPointMapSplitMono (X : SSet.{u}) (x : X _⦋0⦌) :
    SplitMono (basedPathPointMap X x) where
  retraction := stdSimplex.isTerminalObj₀.from (basedPath X x)
  id := stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Every whole original constant-path point inclusion is a genuine monomorphism. -/
theorem basedPathPointMap_mono (X : SSet.{u}) (x : X _⦋0⦌) : Mono (basedPathPointMap X x) := by
  let : IsSplitMono (basedPathPointMap X x) := IsSplitMono.mk' (basedPathPointMapSplitMono X x)
  infer_instance

/-- The SAME original contraction proves the full original point inclusion is Kan weak. -/
theorem basedPathPointMap_kanWeak (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    KanComplex.W (basedPathPointMap X x) := by
  let : KanComplex (Δ[0] : SSet.{u}) := originalPointKan
  let q : basedPath X x ⟶ (Δ[0] : SSet.{u}) :=
    stdSimplex.isTerminalObj₀.from (basedPath X x)
  apply KanComplex.W.of_homotopy (basedPathPointMap X x) q
  · have h : basedPathPointMap X x ≫ q = 𝟙 (Δ[0] : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h]
    change RelativeMorphism.Homotopy (RelativeMorphism.botEquiv.symm _)
      (RelativeMorphism.botEquiv.symm _)
    exact RelativeMorphism.Homotopy.refl _
  · change SSet.Homotopy (SSet.const (basedPathPoint X x)) (𝟙 (basedPath X x))
    exact basedPathContraction X x

/-- The same actual original point inclusion is a weak equivalence in the existing model. -/
theorem basedPathPointMap_weakEquivalence (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    WeakEquivalence (basedPathPointMap X x) := by
  let : KanComplex (Δ[0] : SSet.{u}) := originalPointKan
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    ((KanComplex.W_iff_realizationWeakEquivalence _).mp (basedPathPointMap_kanWeak X x))

/-- The same actual original point inclusion is a cofibration in the existing model. -/
theorem basedPathPointMap_cofibration (X : SSet.{u}) (x : X _⦋0⦌) :
    Cofibration (basedPathPointMap X x) := by
  let : Mono (basedPathPointMap X x) := basedPathPointMap_mono X x
  exact SSet.modelCategoryQuillen.cofibration_of_mono _

/-- The whole original endpoint projection retains its exact actual original base point map. -/
theorem basedPathPointMap_projection (X : SSet.{u}) (x : X _⦋0⦌) :
    basedPathPointMap X x ≫ basedPathProj X x = SSet.const (X := Δ[0]) x :=
  (SSet.const_comp (basedPathPoint X x) (basedPathProj X x)).trans
    (congrArg (fun y => SSet.const (X := Δ[0]) y) (basedPathProj_basedPathPoint X x))

/-- The entire original based-path lifting square keeps the same four original maps. -/
theorem basedPathLiftSquare (S : SSet.FibrationSequence.{u}) :
    CommSq (SSet.const (X := Δ[0]) S.e) (basedPathPointMap S.B S.b) S.p
      (basedPathProj S.B S.b) := by
  have hLeft : SSet.const (X := Δ[0]) S.e ≫ S.p = SSet.const (X := Δ[0]) S.b :=
    (SSet.const_comp S.e S.p).trans (congrArg (fun y => SSet.const (X := Δ[0]) y) S.hb)
  exact ⟨hLeft.trans (basedPathPointMap_projection S.B S.b).symm⟩

/-- The SAME actual existing Kan model gives a full lift of the entire original square. -/
theorem basedPathLiftSquare_hasLift (S : SSet.FibrationSequence.{u}) :
    (basedPathLiftSquare S).HasLift := by
  let : Cofibration (basedPathPointMap S.B S.b) := basedPathPointMap_cofibration S.B S.b
  let : WeakEquivalence (basedPathPointMap S.B S.b) :=
    basedPathPointMap_weakEquivalence S.B S.b
  let : Fibration S.p := S.fibration_p
  infer_instance

/-- A full actual original simplicial based-path lift is chosen from its genuine original square. -/
def basedPathLift (S : SSet.FibrationSequence.{u}) : basedPath S.B S.b ⟶ S.E := by
  letI := basedPathLiftSquare_hasLift S
  exact (basedPathLiftSquare S).lift

/-- The entire original lift retains the literal original projection map. -/
theorem basedPathLift_projection (S : SSet.FibrationSequence.{u}) :
    basedPathLift S ≫ S.p = basedPathProj S.B S.b := by
  let := basedPathLiftSquare_hasLift S
  exact (basedPathLiftSquare S).fac_right

/-- The entire original lift retains the original full constant total point map. -/
theorem basedPathLift_point_map (S : SSet.FibrationSequence.{u}) :
    basedPathPointMap S.B S.b ≫ basedPathLift S = SSet.const (X := Δ[0]) S.e := by
  let := basedPathLiftSquare_hasLift S
  exact (basedPathLiftSquare S).fac_left

/-- The entire actual original lift preserves the SAME original chosen total vertex. -/
theorem basedPathLift_point (S : SSet.FibrationSequence.{u}) :
    (basedPathLift S).app _ (basedPathPoint S.B S.b) = S.e := by
  let z : (Δ[0] : SSet.{u}) _⦋0⦌ := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have h := ConcreteCategory.congr_hom (congr_app (basedPathLift_point_map S) (op ⦋0⦌)) z
  change (basedPathLift S).app _ ((basedPathPointMap S.B S.b).app _ z) =
    (SSet.const (X := Δ[0]) S.e).app _ z at h
  exact (congrArg ((basedPathLift S).app _) (basedPathPointMap_point S.B S.b z)).symm.trans
    (h.trans (originalConstantMapAtZero S.e z))

/-- Every original actual fibration has the whole original based-path-to-fibration sequence map. -/
def basedPathLiftSequenceHom (S : SSet.FibrationSequence.{u}) :
    SSet.FibrationSequenceHom (loopFibrationSequence S.B S.b) S where
  totalMap := basedPathLift S
  baseMap := 𝟙 S.B
  comm := (basedPathLift_projection S).trans (Category.comp_id (basedPathProj S.B S.b)).symm
  total_pt := basedPathLift_point S
  base_pt := rfl

/-- The complete original sequence map keeps its SAME original chosen whole lift as total map. -/
theorem basedPathLiftSequenceHom_total (S : SSet.FibrationSequence.{u}) :
    (basedPathLiftSequenceHom S).totalMap = basedPathLift S := rfl

/-- The complete original sequence map keeps the SAME original base identity map. -/
theorem basedPathLiftSequenceHom_base (S : SSet.FibrationSequence.{u}) :
    (basedPathLiftSequenceHom S).baseMap = 𝟙 S.B := rfl

/-- The full original loop-to-fiber map is the original fiber map of the actual whole lift
square. -/
def connectingLoopMap (S : SSet.FibrationSequence.{u}) : loopSpace S.B S.b ⟶ S.fiber :=
  (basedPathLiftSequenceHom S).fiberMap

/-- The whole original loop-to-fiber map preserves the exact original loop and fiber points. -/
theorem connectingLoopMap_point (S : SSet.FibrationSequence.{u}) :
    (connectingLoopMap S).app _ (originalLoopPoint S.B S.b) = S.fiberPoint :=
  (basedPathLiftSequenceHom S).fiberMap_app_basePoint

/-- The entire original loop-to-fiber map keeps the full original lift and projection square. -/
theorem connectingLoopMap_projection (S : SSet.FibrationSequence.{u}) :
    connectingLoopMap S ≫ S.fiberIncl =
      (loopFibrationSequence S.B S.b).fiberIncl ≫ basedPathLift S :=
  (basedPathLiftSequenceHom S).fiberMap_ι

/-- The SAME original connecting function is the full loop-to-fiber map after original loop
shift. -/
theorem connectingLoopMap_pi_then_shift (S : SSet.FibrationSequence.{u}) (n : ℕ)
    (q : SSet.KanComplex.π (n + 1) S.B S.b) :
    SSet.KanComplex.π.map (connectingLoopMap S) (connectingLoopMap_point S) n
        (loopConnectingEquiv n S.B S.b q) = S.connectingMap n q := by
  have h := SSet.FibrationSequence.connectingMap_naturality
    (basedPathLiftSequenceHom S) q
  exact h.trans (congrArg (S.connectingMap n) (SSet.KanComplex.π.map_id_apply q))

/-- The full original connecting function retains the actual inverse original loop comparison. -/
theorem connectingLoopMap_pi (S : SSet.FibrationSequence.{u}) (n : ℕ)
    (q : SSet.KanComplex.π n (loopSpace S.B S.b) (originalLoopPoint S.B S.b)) :
    SSet.KanComplex.π.map (connectingLoopMap S) (connectingLoopMap_point S) n q =
      S.connectingMap n ((loopConnectingEquiv n S.B S.b).symm q) :=
  (congrArg (SSet.KanComplex.π.map (connectingLoopMap S) (connectingLoopMap_point S) n)
    ((loopConnectingEquiv n S.B S.b).apply_symm_apply q).symm).trans
      (connectingLoopMap_pi_then_shift S n ((loopConnectingEquiv n S.B S.b).symm q))

/-- The entire original all-degree connecting/loop-map function is retained in full. -/
theorem connectingLoopMap_pi_function (S : SSet.FibrationSequence.{u}) (n : ℕ) :
    SSet.KanComplex.π.map (connectingLoopMap S) (connectingLoopMap_point S) n =
      S.connectingMap n ∘ (loopConnectingEquiv n S.B S.b).symm :=
  funext (connectingLoopMap_pi S n)

/-- Every whole original pointed fibration square preserves the full loop-to-fiber homotopy map. -/
theorem connectingLoopMap_pi_naturality {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) (n : ℕ)
    (q : SSet.KanComplex.π n (loopSpace S.B S.b) (originalLoopPoint S.B S.b)) :
    SSet.KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n
        (SSet.KanComplex.π.map (connectingLoopMap S) (connectingLoopMap_point S) n q) =
      SSet.KanComplex.π.map (connectingLoopMap T) (connectingLoopMap_point T) n
        (SSet.KanComplex.π.map (loopSpaceMap f.baseMap f.base_pt)
          (loopSpaceMap_app_point f.baseMap f.base_pt) n q) := by
  let r := (loopConnectingEquiv n S.B S.b).symm q
  have hOriginal := SSet.FibrationSequence.connectingMap_naturality f r
  have hSource := congrArg (SSet.KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n)
    (connectingLoopMap_pi S n q)
  have hTarget := connectingLoopMap_pi T n
    (SSet.KanComplex.π.map (loopSpaceMap f.baseMap f.base_pt)
      (loopSpaceMap_app_point f.baseMap f.base_pt) n q)
  exact hSource.trans (hOriginal.trans ((congrArg (T.connectingMap n)
    (SSet.LoopShiftOriginalGeometry.loopConnectingEquiv_symm_naturality
      f.baseMap f.base_pt n q)).trans hTarget.symm))

end SSet.OriginalBasedPathConnectingGeometry
