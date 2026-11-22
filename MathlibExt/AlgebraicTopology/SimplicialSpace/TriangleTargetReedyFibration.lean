/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.TriangleTargetShearFibration

/-!
# Reedy fibrancy of the original middle-last triangle shear
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.ReedyModel

open SimplicialSpace.SegalHomotopy
open scoped SSet.modelCategoryQuillen

private theorem targetHornComparison_fibration (W : SimplicialSpace.{u}) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → Fibration (outerHornTargetComparison W) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW
  let i := (SSet.horn 2 (2 : Fin 3) : (Δ[2] : SSet.{u}).Subcomplex).ι
  have : Mono i := by dsimp [i]; infer_instance
  have : Mono (SSet.simplicialSpaceDiscrete.map i) := by
    rw [NatTrans.mono_iff_mono_app]
    intro n
    rw [NatTrans.mono_iff_mono_app]
    intro k
    change Mono (i.app n)
    infer_instance
  let f := ofSimplicialObject.map (SSet.simplicialSpaceDiscrete.map i)
  have : Mono f := by dsimp [f]; infer_instance
  have hf : Cofibration f := (cofibration_iff f).2 inferInstance
  have hp := inner_precomp_fibration f W
    ((HomotopicalAlgebra.cofibration_iff f).1 hf) hW
  have : Fibration ((discreteSourceMapping W).map i.op) :=
    (HomotopicalAlgebra.fibration_iff _).2 hp
  rw [← outerHornTargetMappingIso_restriction W]
  infer_instance

/-- Reedy fibrancy alone makes the original middle-last triangle shear a Kan fibration. -/
theorem triangleTargetShear_fibration (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → Fibration (triangleTargetShear W x y z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW
  let _ : Fibration (outerHornTargetComparison W) := targetHornComparison_fibration W hW
  let _ : Fibration (triangleTargetShearPullbackPair W x y z) := by
    change Fibration (pullback.snd (outerHornTargetComparison W) (triangleTargetShearPair W x y z))
    infer_instance
  rw [← triangleTargetShearIso_hom_pair W x y z]
  infer_instance

/-- Every original positive horn has the lifting property against that same shear. -/
theorem triangleTargetShear_hasLiftingProperty (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → ∀ (n : ℕ), 1 ≤ n → ∀ (i : Fin (n + 1)),
      HasLiftingProperty (SSet.horn n i).ι (triangleTargetShear W x y z) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i
  let _ : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)⟩
  exact (SSet.modelCategoryQuillen.fibration_iff _).1
    (triangleTargetShear_fibration W x y z hW) _
    (SSet.modelCategoryQuillen.horn_ι_mem_J n i)

/-- A native diagonal for every original positive-horn square, with both factor equations. -/
def triangleTargetShearHornLift (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → ∀ (n : ℕ) (_ : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W y z)
      (sq : CommSq a (SSet.horn n i).ι (triangleTargetShear W x y z) b), sq.LiftStruct := by
  letI : ModelCategory SimplicialSpace.{u} := modelCategory
  letI : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  intro hW n hn i a b sq
  let hL : sq.HasLift := (triangleTargetShear_hasLiftingProperty W x y z hW n hn i).sq_hasLift sq
  exact hL.exists_lift.some

/-- The original horn followed by the native diagonal is the original top arrow. -/
theorem triangleTargetShearHornLift_fac_left (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    ∀ (hW : IsFibrant W) (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W y z)
      (sq : CommSq a (SSet.horn n i).ι (triangleTargetShear W x y z) b),
      (SSet.horn n i).ι ≫ (triangleTargetShearHornLift W x y z hW n hn i a b sq).l = a := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i a b sq
  exact (triangleTargetShearHornLift W x y z hW n hn i a b sq).fac_left

/-- The native diagonal followed by the same shear is the original bottom arrow. -/
theorem triangleTargetShearHornLift_fac_right (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    ∀ (hW : IsFibrant W) (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W y z)
      (sq : CommSq a (SSet.horn n i).ι (triangleTargetShear W x y z) b),
      (triangleTargetShearHornLift W x y z hW n hn i a b sq).l ≫
          triangleTargetShear W x y z = b := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i a b sq
  exact (triangleTargetShearHornLift W x y z hW n hn i a b sq).fac_right

/-- Every original positive-horn square admits a diagonal retaining both original legs. -/
theorem triangleTargetShear_original_hornLift (W : SimplicialSpace.{u})
    (x y z : (W.diagram _⦋0⦌) _⦋0⦌) :
    let _ : ModelCategory SimplicialSpace.{u} := modelCategory
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    IsFibrant W → ∀ (n : ℕ) (_ : 1 ≤ n) (i : Fin (n + 1))
      (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
      (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W y z)
      (_ : CommSq a (SSet.horn n i).ι (triangleTargetShear W x y z) b),
      ∃ l : (Δ[n] : SSet.{u}) ⟶ triangleSpace W x y z,
        (SSet.horn n i).ι ≫ l = a ∧ l ≫ triangleTargetShear W x y z = b := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  dsimp only
  intro hW n hn i a b sq
  let l := triangleTargetShearHornLift W x y z hW n hn i a b sq
  exact ⟨l.l, l.fac_left, l.fac_right⟩

/-- A given original horn filler transports with both legs at all prescribed vertices. -/
theorem triangleTargetShearHornLift_transport {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    {x y z : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' z' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap q x = x') (hy : mappingVertexMap q y = y')
    (hz : mappingVertexMap q z = z') (n : ℕ) (i : Fin (n + 1))
    (a : (Λ[n, i] : SSet.{u}) ⟶ triangleSpace W x y z)
    (b : (Δ[n] : SSet.{u}) ⟶ mappingFibre W x z ⨯ mappingFibre W y z)
    (sq : CommSq a (SSet.horn n i).ι (triangleTargetShear W x y z) b)
    (l : sq.LiftStruct) :
    (SSet.horn n i).ι ≫ (l.l ≫ triangleTargetTransport q hx hy hz) =
        a ≫ triangleTargetTransport q hx hy hz ∧
      (l.l ≫ triangleTargetTransport q hx hy hz) ≫ triangleTargetShear V x' y' z' =
        b ≫ prod.map (mappingFibre.map q hx hz) (mappingFibre.map q hy hz) := by
  constructor
  · rw [← Category.assoc, l.fac_left]
  · rw [Category.assoc, triangleTargetShear_natural, ← Category.assoc, l.fac_right]

end SimplicialSpace.ReedyModel
