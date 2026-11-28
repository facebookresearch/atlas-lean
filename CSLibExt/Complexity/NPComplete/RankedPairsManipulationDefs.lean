/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RANKED PAIRS MANIPULATION (single manipulator, co-winner): definitions

Source:
L. Xia, M. Zuckerman, A. D. Procaccia, V. Conitzer and J. S. Rosenschein, "Complexity of unweighted
coalitional manipulation under some common voting rules", Proceedings of the 21st International
Joint Conference on Artificial Intelligence (IJCAI 2009), 348-353, Section 2 (ranked pairs,
Definition 2.1 and the co-winner formulation) and Theorem 4.1;
L. Xia, V. Conitzer, A. D. Procaccia and J. S. Rosenschein, "Complexity of unweighted coalitional
manipulation under some common voting rules", 2nd International Workshop on Computational Social
Choice (COMSOC 2008), Theorem 2 and its proof ("The UCMU and UCMC problems under ranked pairs are
NP-complete, even when there is only one manipulator"),
https://research.illc.uva.nl/COMSOC/2008/papers/PDF/35-xia.pdf.
-/
module

public import Mathlib.Logic.Relation
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle
public import CSLibExt.Complexity.NPComplete.SecondOrderCopelandManipulationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RankedPairsManipulation

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (supporters)
open MetaMathlibExt.Complexity.NPComplete.SecondOrderCopelandManipulation
  (SecondOrderCopelandManipulationInstance WellFormed Candidate)

/-- An order of consideration allowed by ranked pairs on profile `P`: a list of ordered pairs of
distinct candidates with exactly one orientation of each pair of distinct candidates; each pair
`(a, b)` in it has at least as many votes ranking `a` ahead of `b` as `b` ahead of `a`; and the
number of votes ranking the first candidate ahead of the second never increases along the list. -/
def IsConsiderationOrder {Alt Voter : Type} [Fintype Voter] (P : Profile Alt Voter)
    (σ : List (Alt × Alt)) : Prop :=
  σ.Nodup ∧
    (∀ e ∈ σ, e.1 ≠ e.2 ∧ (e.2, e.1) ∉ σ ∧
      (supporters P e.2 e.1).card ≤ (supporters P e.1 e.2).card) ∧
    (∀ a b, a ≠ b → (a, b) ∈ σ ∨ (b, a) ∈ σ) ∧
    σ.Pairwise fun e f => (supporters P f.1 f.2).card ≤ (supporters P e.1 e.2).card

open Classical in
/-- The pairs that ranked pairs fixes when it considers the ordered pairs in the order `σ`: each
pair `(a, b)` is fixed (as `a ≻ b`) unless `b` is already above `a` through the pairs fixed
before it. -/
noncomputable def lockedPairs {Alt : Type} (σ : List (Alt × Alt)) : List (Alt × Alt) :=
  σ.foldl (fun F e => if Relation.TransGen (fun x y => (x, y) ∈ F) e.2 e.1 then F else F ++ [e])
    []

/-- `p` is at the top of the ranking that ranked pairs builds from the order `σ`: `p` is above
every other candidate through fixed pairs. -/
def IsTop {Alt : Type} (σ : List (Alt × Alt)) (p : Alt) : Prop :=
  ∀ q, q ≠ p → Relation.TransGen (fun x y => (x, y) ∈ lockedPairs σ) p q

/-- Some vote of the manipulator (the last voter) makes `p` a ranked-pairs winner, the other
voters voting their sincere orders (voter `k` prefers `a` to `b` exactly when `a` comes before
`b` in the `k`-th vote): `p` is at the top for some allowed order of consideration. -/
def RankedPairsManipulationFeasible (i : SecondOrderCopelandManipulationInstance) : Prop :=
  ∃ hp : i.2.2 ∈ i.1, ∃ P : Profile (Candidate i) (Fin (i.2.1.length + 1)),
    (∀ k : Fin i.2.1.length, ∀ a b : Candidate i,
      (P k.castSucc).lt a b ↔ (i.2.1.get k).idxOf a.1 < (i.2.1.get k).idxOf b.1) ∧
    ∃ σ, IsConsiderationOrder P σ ∧ IsTop σ ⟨i.2.2, hp⟩

open Classical in
/-- RANKED PAIRS MANIPULATION as a decision problem over bitstrings. -/
noncomputable def rankedPairsManipulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SecondOrderCopelandManipulationInstance) x with
  | some i => decide (WellFormed i ∧ RankedPairsManipulationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RankedPairsManipulation
