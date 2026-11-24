/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.OperatorUltraweak.Topology
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Infimum algebra for the actual operator ultraweak topology

The raw algebra is the infimum of all ultraweak closed subalgebras
containing the actual operator set. No algebra-existence or trace-dual
output is chosen. Containment, closedness, and leastness follow from the
actual infimum. Original source comparison theorems remain terminal statements.
-/

@[expose] public section
noncomputable section
namespace OperatorUltraweak

/-- The actual infimum of ultraweak closed subalgebras containing the original operator set. -/
def algebraGenerated {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Set (H →L[ℂ] H)) : Subalgebra ℂ (H →L[ℂ] H) :=
  sInf {A : Subalgebra ℂ (H →L[ℂ] H) | S ⊆ (A : Set (H →L[ℂ] H)) ∧
    IsClosedSet (A : Set (H →L[ℂ] H))}

/-- Every original generator belongs to the actual generated algebra. -/
theorem subset_algebraGenerated {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Set (H →L[ℂ] H)) : S ⊆ (algebraGenerated S : Set (H →L[ℂ] H)) := by
  intro T hT
  exact Algebra.mem_sInf.mpr fun A hA => hA.1 hT

/-- The actual generated algebra is closed in the coefficient-induced ultraweak topology. -/
theorem isClosedSet_algebraGenerated {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Set (H →L[ℂ] H)) : IsClosedSet (algebraGenerated S : Set (H →L[ℂ] H)) := by
  let : TopologicalSpace (H →L[ℂ] H) := topology H
  change IsClosed (algebraGenerated S : Set (H →L[ℂ] H))
  rw [algebraGenerated, Algebra.coe_sInf]
  exact isClosed_iInter fun A => isClosed_iInter fun hA => hA.2

/-- Any ultraweak closed algebra containing the generators contains the generated algebra. -/
theorem algebraGenerated_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : Set (H →L[ℂ] H)) (A : Subalgebra ℂ (H →L[ℂ] H))
    (hS : S ⊆ (A : Set (H →L[ℂ] H))) (hA : IsClosedSet (A : Set (H →L[ℂ] H))) :
    algebraGenerated S ≤ A :=
  sInf_le ⟨hS, hA⟩

end OperatorUltraweak
