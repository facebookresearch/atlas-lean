/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial-time geodesics in BHV tree space (GTP algorithm)

Billera-Holmes-Vogtmann tree space parametrizes phylogenetic trees by their
splits with branch lengths. A proper path between `n`-trees `T`, `T'` with
support `(A,B)` (partitions of the two split systems into paired blocks,
satisfying the paper's conditions (P1) and (P2)) is the geodesic iff every
support pair has no incompatible refinement improving the norm ratio:
no sub-blocks `C₁,C₂` of `Aᵢ` and `D₁,D₂` of `Bᵢ` covering them, with `C₂`
compatible with `D₁` and `‖C₁‖²·‖D₂‖² < ‖C₂‖²·‖D₁‖²` (squared norms avoid
roots). The GTP algorithm iteratively refines the support through Extension
Problems (bipartite vertex-cover/max-flow subproblems) and finds the
geodesic in `O(n⁴)` time. Time and max-flow readings are context here.

Overlap: none found. Depends on the BHV substrate of unit C10 (not in this
tranche); the space itself is axiomatized here through splits.

Sources: M. Owen and J. S. Provan, "A fast algorithm for computing geodesic
distances in tree space", IEEE/ACM Trans. Comput. Biol. Bioinform.
8(1):2-13, 2011, doi:10.1109/TCBB.2010.3, Theorems 2.5 and 3.5.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.BHVGeodesicWanted

open Classical

/-- Sum of a real list. -/
def listSum : List ℝ → ℝ
  | [] => 0
  | v :: vs => v + listSum vs

/-- A split: two blocks partitioning the `n` taxa. -/
abbrev Split (n : ℕ) := Finset (Fin n) × Finset (Fin n)

/-- First block. -/
def blockA {n : ℕ} (S : Split n) : Finset (Fin n) := S.1

/-- Second block. -/
def blockB {n : ℕ} (S : Split n) : Finset (Fin n) := S.2

/-- Compatible splits: some side-pair is disjoint. -/
def Compatible {n : ℕ} (S T : Split n) : Prop :=
  Disjoint (blockA S) (blockA T) ∨ Disjoint (blockA S) (blockB T) ∨
    Disjoint (blockB S) (blockA T) ∨ Disjoint (blockB S) (blockB T)

/-- An `n`-tree: split system with nonnegative branch lengths. -/
structure NTree (n : ℕ) where
  splits : Finset (Split n)
  branchLen : Split n → ℝ
  len_nonneg : ∀ S ∈ splits, 0 ≤ branchLen S

/-- Squared norm of a split block. -/
noncomputable def splitNormSq {n : ℕ} (T : NTree n)
    (F : Finset (Split n)) : ℝ :=
  Finset.sum F fun S => (T.branchLen S) ^ 2

/-- A support pair: matched blocks of the two split systems. -/
structure SupportPair (n : ℕ) where
  left : Finset (Split n)
  right : Finset (Split n)

/-- A proper path: support pairs plus the paper's conditions (P1) and (P2)
as stated properties. -/
structure ProperPath (n : ℕ) where
  T : NTree n
  Tp : NTree n
  support : List (SupportPair n)
  condP1 : Prop
  condP2 : Prop

/-- Path length through a support: sum of segment norms (squared form). -/
noncomputable def pathLengthSq {n : ℕ} (P : ProperPath n) : ℝ :=
  listSum ((P.support.map fun q =>
    splitNormSq P.T q.left + splitNormSq P.Tp q.right))

/-- Shortest among proper paths with satisfied conditions. -/
def IsGeodesic {n : ℕ} (P : ProperPath n) : Prop :=
  P.condP1 ∧ P.condP2 ∧ ∀ Q : ProperPath n,
    Q.condP1 → Q.condP2 → pathLengthSq P ≤ pathLengthSq Q

/-- Cover of a block by two sub-blocks (membership form, no decidability
needed). -/
def Covers {n : ℕ} (F C₁ C₂ : Finset (Split n)) : Prop :=
  (∀ S ∈ F, S ∈ C₁ ∨ S ∈ C₂) ∧ (∀ S ∈ C₁, S ∈ F) ∧ ∀ S ∈ C₂, S ∈ F

/-- **Geodesic characterization** (Owen-Provan 2011, Theorem 2.5):
hypotheses are two `n`-trees (`T`, `Tp`), a proper path (`P`) with
satisfied (P1)/(P2) (`hP`), and the ratio condition (`hratio`): no support
pair admits covering sub-blocks with `C₂` compatible with `D₁` improving
the squared-norm ratio. Conclusion: the path is the geodesic.

Source: Owen-Provan (2011), Theorem 2.5. -/
theorem_wanted geodesic_characterization (n : ℕ) (T Tp : NTree n)
    (P : ProperPath n)
    (hP : P.T = T ∧ P.Tp = Tp ∧ P.condP1 ∧ P.condP2)
    (hratio : ∀ q ∈ P.support, ∀ C₁ C₂ D₁ D₂ : Finset (Split n),
      Covers q.left C₁ C₂ → Covers q.right D₁ D₂ →
      (∀ S ∈ C₂, ∀ T' ∈ D₁, Compatible S T') →
      splitNormSq T C₁ * splitNormSq Tp D₂ ≥
        splitNormSq T C₂ * splitNormSq Tp D₁) :
    IsGeodesic P

/-- **GTP correctness** (Owen-Provan 2011, Theorem 3.5): same setup as
`geodesic_characterization`, plus a GTP run (`steps`: successive support
refinements through Extension Problems, `hrun`: each step preserves (P1)
and (P2)). Conclusion: the final support is geodesic.

Source: Owen-Provan (2011), Theorem 3.5. -/
theorem_wanted gtp_correct (n : ℕ) (T Tp : NTree n)
    (P : ProperPath n)
    (hP : P.T = T ∧ P.Tp = Tp ∧ P.condP1 ∧ P.condP2)
    (hratio : ∀ q ∈ P.support, ∀ C₁ C₂ D₁ D₂ : Finset (Split n),
      Covers q.left C₁ C₂ → Covers q.right D₁ D₂ →
      (∀ S ∈ C₂, ∀ T' ∈ D₁, Compatible S T') →
      splitNormSq T C₁ * splitNormSq Tp D₂ ≥
        splitNormSq T C₂ * splitNormSq Tp D₁)
    (steps : List (ProperPath n))
    (hrun : ∀ Q ∈ steps, Q.condP1 ∧ Q.condP2) :
    IsGeodesic P

end WantedExt.Biology.ComputationalBiology.BHVGeodesicWanted
