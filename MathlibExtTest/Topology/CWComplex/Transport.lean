/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.CWComplex.Transport
public import MathlibExt.Topology.CWComplex.UniverseLift

/-!
# Consumers of classical CW transport in independent universes

The clients use the actual original cell identifiers and partial equivalences,
read back every CW field, and retain a chosen zero-cell point. The empty-space
client exercises an empty cell family without separation or cardinal bounds.
-/

public section
noncomputable section
set_option autoImplicit false
open Set Topology

universe u v

namespace CWTransportClients

/-- Same-universe transport retains the entire original cell identifier family. -/
theorem sameUniverseCells {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (cw : CWComplex (univ : Set X)) (h : X ≃ₜ Y) :
    (CWComplex.transport cw h).cell = cw.cell := rfl

/-- Independent upper-universe transport retains the literal lifted identifier family. -/
theorem upperUniverseCells {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (cw : CWComplex (univ : Set X)) (h : X ≃ₜ Y) :
    (CWComplex.transportULift cw h).cell = fun n => ULift.{v} (cw.cell n) := rfl

/-- The full characteristic partial equivalence, including its inverse, is the original postcomposition. -/
theorem upperUniverseCharacteristic {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (cw : CWComplex (univ : Set X)) (h : X ≃ₜ Y)
    (n : ℕ) (j : ULift.{v} (cw.cell n)) :
    (CWComplex.transportULift cw h).map n j = (cw.map n j.down).transEquiv h.toEquiv := rfl

/-- Every transported field is usable with only the original CW data and homeomorphism. -/
theorem upperUniverseFields {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (cw : CWComplex (univ : Set X)) (h : X ≃ₜ Y) (n : ℕ)
    (j : ULift.{v} (cw.cell n)) (A : Set Y)
    (hA : ∀ m k, IsClosed (A ∩ (CWComplex.transportULift cw h).map m k '' Metric.closedBall 0 1)) :
    ((CWComplex.transportULift cw h).map n j).source = Metric.ball 0 1 ∧
      ContinuousOn ((CWComplex.transportULift cw h).map n j) (Metric.closedBall 0 1) ∧
      ContinuousOn ((CWComplex.transportULift cw h).map n j).symm
        ((CWComplex.transportULift cw h).map n j).target ∧ IsClosed A := by
  let transported := CWComplex.transportULift cw h
  exact ⟨transported.source_eq n j, transported.continuousOn n j,
    transported.continuousOn_symm n j, transported.closed' A (Set.subset_univ _) hA⟩

/-- The same returned structure supplies disjoint cells, finite lower frontiers and covering. -/
theorem upperUniverseAttachmentFields {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (cw : CWComplex (univ : Set X)) (h : X ≃ₜ Y) (n : ℕ)
    (j : ULift.{v} (cw.cell n)) :
    (univ : Set (Σ m, (CWComplex.transportULift cw h).cell m)).PairwiseDisjoint
        (fun mi => (CWComplex.transportULift cw h).map mi.1 mi.2 '' Metric.ball 0 1) ∧
      (∃ I : Π m, Finset ((CWComplex.transportULift cw h).cell m),
        MapsTo ((CWComplex.transportULift cw h).map n j) (Metric.sphere 0 1)
          (⋃ (m < n) (k ∈ I m), (CWComplex.transportULift cw h).map m k '' Metric.closedBall 0 1)) ∧
      (⋃ (m : ℕ) (k : (CWComplex.transportULift cw h).cell m),
        (CWComplex.transportULift cw h).map m k '' Metric.closedBall 0 1) = univ := by
  let transported := CWComplex.transportULift cw h
  exact ⟨transported.pairwiseDisjoint', transported.mapsTo' n j, transported.union'⟩

/-- An original zero-cell point remains the transported point at every coordinate. -/
theorem upperUniverseZeroCell {X : Type u} {Y : Type (max u v)}
    [TopologicalSpace X] [TopologicalSpace Y]
    (cw : CWComplex (univ : Set X)) (h : X ≃ₜ Y) (x : X)
    (j : cw.cell 0) (hj : cw.map 0 j ![] = x) :
    ∀ z : Fin 0 → ℝ, (CWComplex.transportULift cw h).map 0 (ULift.up j) z = h x :=
  CWComplex.transportWithCells_zeroCell cw h (fun n => ULift.{v} (cw.cell n))
    (fun _ => Equiv.ulift.symm) j x hj

/-- The existing universe-lift API uses the same full characteristic partial equivalences. -/
theorem originalULiftCharacteristics (X : Type u) [TopologicalSpace X]
    [CWComplex (univ : Set X)] (n : ℕ)
    (j : ULift.{v} ((inferInstance : CWComplex (univ : Set X)).cell n)) :
    (CWComplex.uliftCWComplex X).map n j =
      ((inferInstance : CWComplex (univ : Set X)).map n j.down).transEquiv
        (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X).toEquiv := rfl

/-- The entire original lifted structure is the new generic upper-universe specialization. -/
theorem originalULiftStructure (X : Type u) [TopologicalSpace X]
    [CWComplex (univ : Set X)] :
    CWComplex.uliftCWComplex.{u, v} X =
      CWComplex.transportULift (inferInstance : CWComplex (univ : Set X))
        (Homeomorph.ulift.symm : X ≃ₜ ULift.{v} X) := rfl

/-- Empty classical cell families transport without any nonemptiness assumption. -/
theorem emptyCells (n : ℕ) :
    IsEmpty ((CWComplex.transport
      (CWComplex.ofDiscreteTopology : CWComplex (univ : Set PEmpty.{u + 1}))
      (Homeomorph.refl PEmpty.{u + 1})).cell n) := by
  cases n with
  | zero =>
    change IsEmpty (univ : Set PEmpty.{u + 1})
    infer_instance
  | succ n =>
    change IsEmpty PEmpty
    infer_instance

end CWTransportClients
