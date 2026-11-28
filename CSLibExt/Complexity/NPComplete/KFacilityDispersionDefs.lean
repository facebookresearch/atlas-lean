/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# K-FACILITY DISPERSION: definitions

Source:
P. Crescenzi and V. Kann, *A compendium of NP optimization problems*, problem
MAXIMUM K-FACILITY DISPERSION;
S. S. Ravi, D. J. Rosenkrantz, and G. K. Tayi, "Heuristic and special case algorithms for
dispersion problems", Operations Research 42 (1994), 299-310, doi:10.1287/opre.42.2.299.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MetricKCenterDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KFacilityDispersion

open KCenter (KCenterInstance)
open MetricKCenter (distance)

/-- Well-formedness of an instance: METRIC K-CENTER's (a metric distance matrix, `0 < k ≤ |V|`,
`0 < K`) and `2 ≤ k`. -/
def WellFormed (i : KCenterInstance) : Prop :=
  MetricKCenter.WellFormed i ∧ 2 ≤ i.2.1

/-- Some set `F` of exactly `k` vertices has `d(f₁, f₂) ≥ K` for all distinct `f₁, f₂ ∈ F`,
i.e. the minimum distance between two facilities is at least `K`. -/
def KFacilityDispersionFeasible (i : KCenterInstance) : Prop :=
  ∃ F : Finset (Fin i.1.length), F.card = i.2.1 ∧
    ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ ≠ f₂ → i.2.2 ≤ distance i f₁ f₂

open Classical in
/-- K-FACILITY DISPERSION as a decision problem over bitstrings. -/
noncomputable def kFacilityDispersionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KCenterInstance) x with
  | some i => decide (WellFormed i ∧ KFacilityDispersionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KFacilityDispersion
