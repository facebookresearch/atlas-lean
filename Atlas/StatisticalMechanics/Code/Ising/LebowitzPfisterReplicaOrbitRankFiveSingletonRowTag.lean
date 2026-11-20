/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFullSources









namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveSingletonRowTagDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaCurrentSeamEdge_toFinset_eq_matchingSeamSource
    (sites : I -> V) (k : I) :
    (lpReplicaCurrentSeamEdge sites k).toFinset =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k := by
  have hne : lpReplicaCurrentLeft sites k ≠
      lpReplicaCurrentRight sites k := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  ext x
  simp only [lpReplicaCurrentSeamEdge, Sym2.mem_toFinset, Sym2.mem_iff,
    lpMatchingSeamSource, Finset.mem_symmDiff, Finset.mem_singleton]
  change (x = lpReplicaCurrentLeft sites k ∨
      x = lpReplicaCurrentRight sites k) ↔
    (x = lpReplicaCurrentLeft sites k ∧
        x ≠ lpReplicaCurrentRight sites k) ∨
      (x = lpReplicaCurrentRight sites k ∧
        x ≠ lpReplicaCurrentLeft sites k)
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hne⟩
    · exact Or.inr ⟨rfl, hne.symm⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
    · exact Or.inl hx
    · exact Or.inr hx



def lpReplicaSingletonFalseRowTag
    {C : Type*} [DecidableEq C] (c : C) : C -> LPReplicaRowTag :=
  fun e => if e = c then (false, false) else (true, false)

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_false_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) false false = {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_false_true
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) false true = ∅ := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_true_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) true false =
        Finset.univ \ {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaCurrentCopies_singletonFalse_true_true
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaCurrentCopies G sites m
      (lpReplicaSingletonFalseRowTag c) true true = ∅ := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaCurrentCopies, he]

@[simp] theorem lpReplicaRowCopies_singletonFalse_false
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaRowCopies G sites m
      (lpReplicaSingletonFalseRowTag c) false = {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaRowCopies, he]

@[simp] theorem lpReplicaRowCopies_singletonFalse_true
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    lpReplicaRowCopies G sites m
      (lpReplicaSingletonFalseRowTag c) true = Finset.univ \ {c} := by
  classical
  ext e
  by_cases he : e = c <;>
    simp [lpReplicaSingletonFalseRowTag, lpReplicaRowCopies, he]

end


end StatMech.Ising
