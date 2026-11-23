/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.EndpointBoundary
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeBoundedColimit
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeBoundedProjectionSquare

/-!
# The actual endpoint-retuning boundary of the original bounded telescope

The original full bounded inclusion supplies the actual monomorphism.
Its original interval-boundary pushout map is therefore an ordinary
Hurewicz and model cofibration on the SAME original bounded carriers.
Only the Ring and the actual bound are outer data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Semiring R]

/-- The ORIGINAL full bounded transition determines the actual
endpoint-boundary pushout, with literal I×original-later-stage target. -/
public def finiteBGLTelescopeBoundedEndpointBoundaryArrow (n : ℕ) :
    Arrow TopCat.{u} :=
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun _ hX => hX.trans (Nat.le_succ n))
  SSet.realizedEndpointBoundaryArrow (nerveMap B)

/-- The actual target is the literal inner interval times the SAME
original later bounded telescope realization. -/
public theorem finiteBGLTelescopeBoundedEndpointBoundaryArrow_right (n : ℕ) :
    (finiteBGLTelescopeBoundedEndpointBoundaryArrow R n).right =
      TopCat.of (unitInterval × SSet.toTop.obj
        (nerve (FiniteBGLTelescopeBoundedCategory R (n + 1)))) := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun X hX => hX.trans (Nat.le_succ n))
  change (SSet.realizedEndpointBoundaryArrow (nerveMap B)).right = _
  exact SSet.realizedEndpointBoundaryArrow_right (nerveMap B)

/-- The entire ORIGINAL endpoint-boundary pushout map has the actual
Hurewicz extension property, derived from the original bounded Mono. -/
public theorem finiteBGLTelescopeBoundedEndpointBoundary_isHurewiczCofibration (n : ℕ) :
    TopCat.IsHurewiczCofibration
      (finiteBGLTelescopeBoundedEndpointBoundaryArrow R n).hom := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun X hX => hX.trans (Nat.le_succ n))
  let _ : Mono (nerveMap B) := by
    change Mono ((finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n)))
    exact finiteBGLTelescopeBoundedNerveTransition_mono R (homOfLE (Nat.le_succ n))
  exact @SSet.realizedEndpointBoundary_isHurewiczCofibration.{u}
    (nerve (FiniteBGLTelescopeBoundedCategory R n))
    (nerve (FiniteBGLTelescopeBoundedCategory R (n + 1)))
    (nerveMap B) inferInstance

/-- The SAME original endpoint-boundary map is a model cofibration,
with no caller-provided Mono, NDR, family or lifting witness. -/
public theorem finiteBGLTelescopeBoundedEndpointBoundary_cofibration (n : ℕ) :
    Cofibration (finiteBGLTelescopeBoundedEndpointBoundaryArrow R n).hom := by
  let B := ObjectProperty.ιOfLE
    (show finiteBGLTelescopeBound R n ≤ finiteBGLTelescopeBound R (n + 1) from
      fun X hX => hX.trans (Nat.le_succ n))
  let _ : Mono (nerveMap B) := by
    change Mono ((finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n)))
    exact finiteBGLTelescopeBoundedNerveTransition_mono R (homOfLE (Nat.le_succ n))
  exact SSet.realizedEndpointBoundary_cofibration (nerveMap B)

end AlgebraicKTheory.StableGL

end


noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial ContinuousMap

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The original complete adjacent comparison and preceding ENTIRE correction
supply the actual original Hurewicz boundary family for the successor. -/
private theorem nonempty_originalBoundedStableCorrectionSucc (n : ℕ)
    (c : TopCat.EndpointFixedCorrection
      (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R n)) :
    let i := (finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n))
    Nonempty {d : TopCat.EndpointFixedCorrection
        (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R (n + 1)) //
      ∀ (s t : unitInterval)
        (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))),
        d.comparison (s, (t, SSet.toTop.map i x)) =
          ((finiteBGLTelescopeBoundedOriginalStableRowPrismHomotopy R n).trans
            c.comparison) (s, (t, x))} := by
  let i := (finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n))
  let _ : Mono i := finiteBGLTelescopeBoundedNerveTransition_mono R (homOfLE (Nat.le_succ n))
  let P := (finiteBGLTelescopeBoundedOriginalStableRowPrismHomotopy R n).trans c.comparison
  exact SSet.nonempty_endpointBoundaryCorrection i
    (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R (n + 1))
    c.corrected.toContinuousMap P

/-- The successor retains the ENTIRE endpoint-fixed Q and its WHOLE original
source restriction. Mono and the boundary comparison are derived internally. -/
public def finiteBGLTelescopeBoundedOriginalStableRowCorrectionSucc (n : ℕ)
    (c : TopCat.EndpointFixedCorrection
      (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R n)) :
    let i := (finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n))
    {d : TopCat.EndpointFixedCorrection
        (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R (n + 1)) //
      ∀ (s t : unitInterval)
        (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))),
        d.comparison (s, (t, SSet.toTop.map i x)) =
          ((finiteBGLTelescopeBoundedOriginalStableRowPrismHomotopy R n).trans
            c.comparison) (s, (t, x))} :=
  (nonempty_originalBoundedStableCorrectionSucc R n c).some

/-- The actual corrections start at the unchanged ORIGINAL H0 and recursively
retain each ENTIRE Q; all data are constructed from the original Ring alone. -/
public def finiteBGLTelescopeBoundedOriginalStableRowCorrection :
    (n : ℕ) → TopCat.EndpointFixedCorrection
      (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R n) :=
  Nat.rec
    (motive := fun n => TopCat.EndpointFixedCorrection
      (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R n))
    (TopCat.EndpointFixedCorrection.refl
      (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R 0))
    (fun n c => (finiteBGLTelescopeBoundedOriginalStableRowCorrectionSucc R n c).val)

/-- The entire original zero correction is the same reflexive rank-zero correction. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_zero :
    finiteBGLTelescopeBoundedOriginalStableRowCorrection R 0 =
      TopCat.EndpointFixedCorrection.refl
        (finiteBGLTelescopeBoundedOriginalStableRowHomotopy R 0) := by
  rfl

/-- The entire original successor correction uses the same original chosen successor. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_succ (n : ℕ) :
    finiteBGLTelescopeBoundedOriginalStableRowCorrection R (n + 1) =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrectionSucc R n
        (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n)).val := by
  rfl

/-- The original zero correction retains the entire unchanged rank-zero homotopy. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_zero_corrected :
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R 0).corrected =
      finiteBGLTelescopeBoundedOriginalStableRowHomotopy R 0 := by
  rfl

/-- EVERY successor Q retains its complete original two-parameter source fac. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_succ_comparison
    (n : ℕ) (s t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    let i := (finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n))
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R (n + 1)).comparison
        (s, (t, SSet.toTop.map i x)) =
      ((finiteBGLTelescopeBoundedOriginalStableRowPrismHomotopy R n).trans
        (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).comparison)
          (s, (t, x)) := by
  rw [finiteBGLTelescopeBoundedOriginalStableRowCorrection_succ]
  exact (finiteBGLTelescopeBoundedOriginalStableRowCorrectionSucc R n
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n)).property s t x

/-- The constructed original corrected families are LITERALLY compatible on
EVERY original adjacent bounded inclusion and every original inner time. -/
public theorem finiteBGLTelescopeBoundedOriginalStableRowCorrection_succ_compatible
    (n : ℕ) (t : unitInterval)
    (x : SSet.toTop.obj (nerve (FiniteBGLTelescopeBoundedCategory R n))) :
    let i := (finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n))
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R (n + 1)).corrected.toContinuousMap
        (t, SSet.toTop.map i x) =
      (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).corrected.toContinuousMap
        (t, x) := by
  let i := (finiteBGLTelescopeBoundedNerveDiagram R).map (homOfLE (Nat.le_succ n))
  let P := (finiteBGLTelescopeBoundedOriginalStableRowPrismHomotopy R n).trans
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R n).comparison
  have hQ :=
    (finiteBGLTelescopeBoundedOriginalStableRowCorrection R (n + 1)).comparison.apply_one
      (t, SSet.toTop.map i x)
  have hP := P.apply_one (t, x)
  exact hQ.symm.trans
    ((finiteBGLTelescopeBoundedOriginalStableRowCorrection_succ_comparison R n 1 t x).trans hP)

end AlgebraicKTheory.StableGL

end
