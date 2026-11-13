/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferCoverageHall
import Code.FrontierA.GrahamWeightedLemmaOneFiberClosure










namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



def CanonicalMaskOrbitCoverageNested
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      canonicalMaskOrbitCoverage ends m j k l zero p r ⊆
          canonicalMaskOrbitCoverage ends m j k l zero p s ∨
        canonicalMaskOrbitCoverage ends m j k l zero p s ⊆
          canonicalMaskOrbitCoverage ends m j k l zero p r



def CanonicalMaskOrbitCoverageNestedAllMarks
    (ends : I -> Sym2 W) (m : Finset I) : Prop :=
  ∀ j k l zero : W, j ≠ k -> k ≠ l -> k ≠ zero ->
    ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageNested ends m j k l zero p



def CanonicalMaskOrbitCoverageNoIncomparablePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      ¬ ∃ c d : leftMaskFiber ends m j k l zero p,
        c ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p s ∧
        d ∈ canonicalMaskOrbitCoverage ends m j k l zero p s ∧
        d ∉ canonicalMaskOrbitCoverage ends m j k l zero p r



theorem canonicalMaskOrbitCoverageNested_iff_noIncomparablePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalMaskOrbitCoverageNested ends m j k l zero p ↔
      CanonicalMaskOrbitCoverageNoIncomparablePair
        ends m j k l zero p := by
  classical
  constructor
  · intro hnested r s hrs hpair
    obtain ⟨c, d, hcR, hcS, hdS, hdR⟩ := hpair
    rcases hnested r s hrs with hRS | hSR
    · exact hcS (hRS hcR)
    · exact hdR (hSR hdS)
  · intro hno r s hrs
    by_cases hRS : canonicalMaskOrbitCoverage ends m j k l zero p r ⊆
        canonicalMaskOrbitCoverage ends m j k l zero p s
    · exact Or.inl hRS
    · right
      have hexclusive : ∃ c,
          c ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          c ∉ canonicalMaskOrbitCoverage ends m j k l zero p s := by
        by_contra h
        apply hRS
        intro c hcR
        by_contra hcS
        exact h ⟨c, hcR, hcS⟩
      obtain ⟨c, hcR, hcS⟩ := hexclusive
      intro d hdS
      by_contra hdR
      exact hno r s hrs ⟨c, d, hcR, hcS, hdS, hdR⟩



theorem canonicalMaskOrbitCoverageDirected_of_nested
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hnested : CanonicalMaskOrbitCoverageNested
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageDirected ends m j k l zero p := by
  intro r s hrs
  rcases hnested r s hrs with hrsSub | hsrSub
  · refine ⟨s, hrs, ?_⟩
    intro d hrd hworks
    rcases hworks with hworks | hworks
    · have hd : d ∈ canonicalMaskOrbitCoverage
          ends m j k l zero p r := by
        rw [mem_canonicalMaskOrbitCoverage_iff]
        exact ⟨hrd, hworks⟩
      exact ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p s d).mp (hrsSub hd)).2
    · exact hworks
  · refine ⟨r, canonicalMaskTransferOrbit_refl
      ends m j k l zero p r, ?_⟩
    intro d hrd hworks
    rcases hworks with hworks | hworks
    · exact hworks
    · have hsd : CanonicalMaskTransferOrbit ends m j k l zero p s d :=
        (canonicalMaskTransferOrbit_symm
          ends m j k l zero p hrs).trans hrd
      have hd : d ∈ canonicalMaskOrbitCoverage
          ends m j k l zero p s := by
        rw [mem_canonicalMaskOrbitCoverage_iff]
        exact ⟨hsd, hworks⟩
      exact ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p r d).mp (hsrSub hd)).2



theorem GrahamFiberMinor_of_canonicalMaskOrbitCoverageNested
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hnested : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero :=
  GrahamFiberMinor_of_canonicalMaskOrbitCoverageDirected
    ends m j k l zero hloop hjk hkl hk0
      (fun p => canonicalMaskOrbitCoverageDirected_of_nested
        ends m j k l zero p (hnested p))



theorem GrahamFiberMinor_of_canonicalMaskOrbitCoverageNoIncomparablePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hno : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageNoIncomparablePair
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero :=
  GrahamFiberMinor_of_canonicalMaskOrbitCoverageNested
    ends m j k l zero hloop hjk hkl hk0
      (fun p => (canonicalMaskOrbitCoverageNested_iff_noIncomparablePair
        ends m j k l zero p).mpr (hno p))



theorem rowDataRepairHall_of_canonicalMaskOrbitCoverageNested
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hnested : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
    RowDataRepairHall ends m j k l zero :=
  rowDataRepairHall_of_canonicalMaskOrbitCoverageDirected
    ends m j k l zero hloop hjk hkl hk0
      (fun p => canonicalMaskOrbitCoverageDirected_of_nested
        ends m j k l zero p (hnested p))


theorem GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageNested
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hnested : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageNested ends m j k l zero p) :
    GrahamWeightedRowMinor ends m j k l zero :=
  GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageDirected
    ends m j k l zero hloop hjk hkl hk0
      (fun p => canonicalMaskOrbitCoverageDirected_of_nested
        ends m j k l zero p (hnested p))

end StatMech.GrahamGHS.FourColor

namespace StatMech.FrontierA

open SimpleGraph
open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.GrahamGHS.FourColor

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNested
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (j k l m : V) (hjk : j ≠ k) (hkl : k ≠ l) (hkm : k ≠ m)
    (hnested : ∀ total : G.edgeFinset -> Nat,
      ∀ p : Finset (Copy G total) × Finset (Copy G total),
        CanonicalMaskOrbitCoverageNested
          (endsM G total) Finset.univ j k l m p) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m <=
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 := by
  apply grahamWeightedLemmaOne_of_rowDataRepairHall
    G beta J hbeta hJ j k l m
  intro total
  exact rowDataRepairHall_of_canonicalMaskOrbitCoverageNested
    (endsM G total) Finset.univ j k l m
      (fun i _ => endsM_not_isDiag G total i) hjk hkl hkm
      (hnested total)



theorem grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNestedAllMarks
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (j k l m : V) (hjk : j ≠ k) (hkl : k ≠ l) (hkm : k ≠ m)
    (hnested : ∀ total : G.edgeFinset -> Nat,
      CanonicalMaskOrbitCoverageNestedAllMarks
        (endsM G total) Finset.univ) :
    sourcePairDisconnSum G beta J {j, k} ∅ k m *
        sourcePairDisconnSum G beta J {k, l} ∅ k m <=
      sourcePairDisconnSum G beta J {j, k} {k, l} k m *
        currentSum G beta J ∅ ^ 2 :=
  grahamWeightedLemmaOne_of_canonicalMaskOrbitCoverageNested
    G beta J hbeta hJ j k l m hjk hkl hkm
      (fun total => hnested total j k l m hjk hkl hkm)

end StatMech.FrontierA
