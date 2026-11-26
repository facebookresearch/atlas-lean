/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Native local semianalytic projections and subanalytic partitions

The predicates use finite Boolean formulas in actual real analytic
functions. A subanalytic germ is an actual projection of a relatively
compact semianalytic set. On a complex manifold these germs are checked
in its original coordinate charts. Strata are actual locally closed
subanalytic subsets, with an actual locally finite partition.

Source: DK arXiv:1311.2374v2, Sections 2.3--2.4, 4.9 and 5.1;
the standard local-projection definition of subanalytic sets.
Native analytic/chart APIs: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SubanalyticCoordinateModels

open TopologicalSpace Set

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite Boolean combinations of the original analytic zero/sign loci. -/
inductive SemianalyticFormula (W : Opens E) where
  | all
  | empty
  | zero (f : E → ℝ) (analytic : AnalyticOnNhd ℝ f W)
  | positive (f : E → ℝ) (analytic : AnalyticOnNhd ℝ f W)
  | intersection (P Q : SemianalyticFormula W)
  | union (P Q : SemianalyticFormula W)
  | complement (P : SemianalyticFormula W)

/-- The set is computed from those functions and finite Boolean operations. -/
def SemianalyticFormula.realization {W : Opens E} : SemianalyticFormula E W → Set E
  | .all => W
  | .empty => ∅
  | .zero f _ => (W : Set E) ∩ {x | f x = 0}
  | .positive f _ => (W : Set E) ∩ {x | 0 < f x}
  | .intersection P Q => P.realization ∩ Q.realization
  | .union P Q => P.realization ∪ Q.realization
  | .complement P => (W : Set E) \ P.realization

/-- The original relatively compact local projection, including all auxiliary dimensions. -/
def IsSubanalyticAt (S : Set E) (x : E) : Prop :=
  ∃ U : Opens E, x ∈ U ∧ ∃ (m : ℕ) (W : Opens (E × (Fin m → ℝ)))
    (P : SemianalyticFormula (E × (Fin m → ℝ)) W),
    IsCompact (closure P.realization) ∧ closure P.realization ⊆ W ∧
      S ∩ U = (Prod.fst '' P.realization) ∩ U

abbrev ComplexCoordinates (n : ℕ) := EuclideanSpace ℂ (Fin n)

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (ComplexCoordinates n) M]

/-- Subanalyticity refers to the actual source atlas, not a free property name. -/
def IsSubanalyticSubset (S : Set M) : Prop :=
  ∀ x : M, IsSubanalyticAt (ComplexCoordinates n)
    ((chartAt (ComplexCoordinates n) x) '' (S ∩ (chartAt (ComplexCoordinates n) x).source))
    ((chartAt (ComplexCoordinates n) x) x)

def IsLocallyClosedSubset (S : Set M) : Prop :=
  ∃ U : Opens M, ∃ Z : Set M, IsClosed Z ∧ S = (U : Set M) ∩ Z

/-- A locally finite subanalytic partition with its original subset inclusions. -/
structure SubanalyticPartition where
  index : Type
  stratum : index → Set M
  subanalytic : ∀ i, IsSubanalyticSubset n M (stratum i)
  locallyClosed : ∀ i, IsLocallyClosedSubset M (stratum i)
  disjoint : Pairwise (fun i j => Disjoint (stratum i) (stratum j))
  covers : (⋃ i, stratum i) = univ
  locallyFinite : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
    Set.Finite {i | (stratum i ∩ U).Nonempty}

end MathlibExt.AlgebraicGeometry.SubanalyticCoordinateModels
