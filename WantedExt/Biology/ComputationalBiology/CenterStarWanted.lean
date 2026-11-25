/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Center-star multiple alignment is a (2 - 2/k)-approximation

For `k` strings and a pairwise scoring `s` on `Option α` (`none` is a gap)
with zero self-costs (`s x x = 0`, in particular `s none none = 0`), the triangle inequality,
and symmetry, let the center `X c` be an input string minimizing the total optimal-pairwise
distance `∑ⱼ D(X c, Xⱼ)` over the inputs (Gusfield's selection rule) and let `Ac` be
the center-star multiple alignment built from optimal pairwise alignments to
`X c`. With `V` the sum-of-pairs value and `A*` an optimal multiple alignment,
`k * V(Ac) ≤ 2 * (k - 1) * V(A*)`, i.e. `V(Ac) / V(A*) ≤ 2 * (k - 1) / k < 2`.
The symmetry of `s` and the zero self-costs (which give `D(X, X) = 0`) are used by the source
without being stated and are explicit hypotheses here.

Overlap: `CSLibExt/Algorithms/Lean/DynamicProgramming/MultipleSequenceAlignment.lean`
has the sum-of-pairs score as a sum of induced pairwise scores
(`msaScore_eq_sum_induced`) and the `msaScore_le_sum_nwScore` bound; the
center-star approximation bound is not stated there. Sum-of-pairs NP-hardness
is in the WantedExt NP catalog.

Sources: D. Gusfield, "Efficient methods for multiple sequence alignment with
guaranteed error bounds", Bulletin of Mathematical Biology 55(1):141-154,
1993, doi:10.1007/BF02460299, Lemma 3.1 and Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.CenterStarWanted


variable {α : Type*} [DecidableEq α]

/-- Sum of a real list (avoids big-operator imports for lists). -/
def listSum : List ℝ → ℝ
  | [] => 0
  | v :: vs => v + listSum vs

/-- A pairwise alignment: two equal-length rows over `Option α`. -/
structure PairAlignment (α : Type*) where
  left : List (Option α)
  right : List (Option α)
  len_eq : left.length = right.length

/-- Value of a pairwise alignment: sum of column scores. -/
def alignValue (s : Option α → Option α → ℝ) (A : PairAlignment α) : ℝ :=
  listSum ((A.left.zip A.right).map fun p => s p.1 p.2)

/-- Row erasure: deleting gaps recovers the string. -/
def erasesTo (l : List (Option α)) (X : List α) : Prop := l.filterMap id = X

/-- Validity: the rows erase to `X` and `Y`. -/
def IsPairAlignmentOf (A : PairAlignment α) (X Y : List α) : Prop :=
  erasesTo A.left X ∧ erasesTo A.right Y

/-- Optimal pairwise value: infimum of alignment values. Characterized by
`hD_le` (lower bound) and `hD_att` (attainment) in the theorems below. -/
noncomputable def pairDist (s : Option α → Option α → ℝ)
    (X Y : List α) : ℝ :=
  sInf {v | ∃ A : PairAlignment α, IsPairAlignmentOf A X Y ∧
    alignValue s A = v}

/-- A multiple alignment of `k` strings: columns of optional characters. -/
structure MSAlignment (α : Type*) (k : ℕ) where
  cols : List (Fin k → Option α)

/-- Row erasure for multiple alignments. -/
def msErasesTo {k : ℕ} (A : MSAlignment α k) (X : Fin k → List α) : Prop :=
  ∀ j, (A.cols.map fun c => c j).filterMap id = X j

/-- Induced pairwise value of rows `i`, `j`: column scores of the projection. -/
def inducedValue (s : Option α → Option α → ℝ) {k : ℕ}
    (A : MSAlignment α k) (i j : Fin k) : ℝ :=
  listSum (((A.cols.map fun c => c i).zip
    (A.cols.map fun c => c j)).map fun p => s p.1 p.2)

/-- Sum-of-pairs value over unordered row pairs. -/
def msaValue (s : Option α → Option α → ℝ) {k : ℕ}
    (A : MSAlignment α k) : ℝ :=
  Finset.sum ((Finset.univ : Finset (Fin k × Fin k)).filter
    fun p => p.1 < p.2) fun p => inducedValue s A p.1 p.2

/-- Center total: sum of optimal distances from a candidate center. -/
noncomputable def centerTotal (s : Option α → Option α → ℝ) {k : ℕ}
    (X : Fin k → List α) (C : List α) : ℝ :=
  Finset.sum Finset.univ fun j => pairDist s C (X j)

/-- **Center-star approximation** (Gusfield 1993, Theorem 3.1): hypotheses are
a gap scoring with `s none none = 0` (`hgap`) and zero self-costs `s x x = 0` for every
`x : Option α` (`hdiag`), the triangle inequality
(`htria`), explicit symmetry (`hsymm`), at least two strings (`hk`), the
`pairDist` characterization (`hD_le`, `hD_att`), a center index `c : Fin k`
whose input string minimizes the center total over the inputs,
`∑ j, D (X c) (X j) ≤ ∑ j, D (X i) (X j)` for every `i : Fin k` (`hcenter`, Gusfield's selection
rule), spoke alignments `P j` that are
valid and attain the pairwise optima (`hspoke`), a star alignment `Ac`
whose induced pairwise values obey the star triangle bound (`hstar`), and an
optimal alignment `Astar` valid for `X` and minimal (`hopt`). Conclusion:
`k * V(Ac) ≤ 2 * (k - 1) * V(Astar)`.

Source: Gusfield (1993), Theorem 3.1 (via Lemma 3.1). -/
theorem_wanted centerStar_bound (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (k : ℕ) (hk : 2 ≤ k)
    (X : Fin k → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin k)
    (hcenter : ∀ i : Fin k, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (P : Fin k → PairAlignment α)
    (hspoke : ∀ j, IsPairAlignmentOf (P j) (X c) (X j) ∧
      pairDist s (X c) (X j) = alignValue s (P j))
    (Ac : MSAlignment α k)
    (hac : msErasesTo Ac X)
    (hstar : ∀ i j, inducedValue s Ac i j ≤
      alignValue s (P i) + alignValue s (P j))
    (Astar : MSAlignment α k)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α k, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A') :
    (k : ℝ) * msaValue s Ac ≤ 2 * ((k : ℝ) - 1) * msaValue s Astar

/-- **Center-star ratio form** (Gusfield 1993, Theorem 3.1): same hypotheses
as `centerStar_bound` (including `s none none = 0` and zero self-costs `s x x = 0` for every
`x : Option α`, `hdiag`) plus positivity of the optimum (`hpos`). Conclusion:
`V(Ac) / V(Astar) ≤ 2 * (k - 1) / k < 2`.

Source: Gusfield (1993), Theorem 3.1. -/
theorem_wanted centerStar_ratio (s : Option α → Option α → ℝ)
    (hgap : s none none = 0)
    (hdiag : ∀ x : Option α, s x x = 0)
    (htria : ∀ x y z : Option α, s x z ≤ s x y + s y z)
    (hsymm : ∀ x y : Option α, s x y = s y x)
    (k : ℕ) (hk : 2 ≤ k)
    (X : Fin k → List α)
    (hD_le : ∀ (U V : List α) (A : PairAlignment α),
      IsPairAlignmentOf A U V → pairDist s U V ≤ alignValue s A)
    (hD_att : ∀ U V : List α, ∃ A : PairAlignment α,
      IsPairAlignmentOf A U V ∧ pairDist s U V = alignValue s A)
    (c : Fin k)
    (hcenter : ∀ i : Fin k, centerTotal s X (X c) ≤ centerTotal s X (X i))
    (P : Fin k → PairAlignment α)
    (hspoke : ∀ j, IsPairAlignmentOf (P j) (X c) (X j) ∧
      pairDist s (X c) (X j) = alignValue s (P j))
    (Ac : MSAlignment α k)
    (hac : msErasesTo Ac X)
    (hstar : ∀ i j, inducedValue s Ac i j ≤
      alignValue s (P i) + alignValue s (P j))
    (Astar : MSAlignment α k)
    (hastar : msErasesTo Astar X)
    (hopt : ∀ A' : MSAlignment α k, msErasesTo A' X →
      msaValue s Astar ≤ msaValue s A')
    (hpos : 0 < msaValue s Astar) :
    msaValue s Ac / msaValue s Astar ≤ 2 * ((k : ℝ) - 1) / k ∧
      2 * ((k : ℝ) - 1) / k < 2

end WantedExt.Biology.ComputationalBiology.CenterStarWanted
