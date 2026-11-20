/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferNormalization








open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem exists_coverage_exclusive_witnesses
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (ha : canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b)
    (hb : canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b) :
    (∃ c, c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b) ∧
      ∃ d, d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
        d ∉ canonicalMaskOrbitCoverage ends m j k l zero p a := by
  classical
  let A := canonicalMaskOrbitCoverage ends m j k l zero p a
  let B := canonicalMaskOrbitCoverage ends m j k l zero p b
  have ha' : A ≠ A ∪ B := by
    simpa only [A, B, canonicalMaskOrbitCoverageUnion] using ha
  have hb' : B ≠ A ∪ B := by
    simpa only [A, B, canonicalMaskOrbitCoverageUnion] using hb
  have hBA : ¬ B ⊆ A := by
    intro hBA
    apply ha'
    exact (Finset.union_eq_left.mpr hBA).symm
  have hAB : ¬ A ⊆ B := by
    intro hAB
    apply hb'
    exact (Finset.union_eq_right.mpr hAB).symm
  constructor
  · by_contra h
    apply hAB
    intro c hcA
    by_contra hcB
    exact h ⟨c, hcA, hcB⟩
  · by_contra h
    apply hBA
    intro d hdB
    by_contra hdA
    exact h ⟨d, hdB, hdA⟩

theorem canonicalMaskOrbitCoverageUnion_comm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitCoverageUnion ends m j k l zero p a b =
      canonicalMaskOrbitCoverageUnion ends m j k l zero p b a := by
  simp only [canonicalMaskOrbitCoverageUnion, Finset.union_comm]



def CanonicalMaskOrbitCoverageSmallerExclusiveJoin
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ a b : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    #(canonicalMaskOrbitCoverage ends m j k l zero p a) ≤
      #(canonicalMaskOrbitCoverage ends m j k l zero p b) ->
    ∀ c : leftMaskFiber ends m j k l zero p,
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ->
      c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ->
      canonicalMaskOrbitCoverage ends m j k l zero p c =
        canonicalMaskOrbitCoverageUnion ends m j k l zero p a b



theorem canonicalMaskOrbitCoverageUnionClosed_of_smallerExclusiveJoin
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hjoin : CanonicalMaskOrbitCoverageSmallerExclusiveJoin
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p := by
  intro a b hab
  let A := canonicalMaskOrbitCoverage ends m j k l zero p a
  let B := canonicalMaskOrbitCoverage ends m j k l zero p b
  let U := canonicalMaskOrbitCoverageUnion ends m j k l zero p a b
  by_cases ha : A = U
  · exact ⟨a, canonicalMaskTransferOrbit_refl ends m j k l zero p a, ha⟩
  by_cases hb : B = U
  · exact ⟨b, hab, hb⟩
  obtain ⟨⟨c, hcA, hcB⟩, ⟨d, hdB, hdA⟩⟩ :=
    exists_coverage_exclusive_witnesses ends m j k l zero p a b ha hb
  rcases le_total #A #B with hAB | hBA
  · have hcOrbit := (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p a c).mp hcA |>.1
    refine ⟨c, hcOrbit, ?_⟩
    exact hjoin a b hab ha hb hAB c hcA hcB
  · have hcomm := canonicalMaskOrbitCoverageUnion_comm
      ends m j k l zero p a b
    have ha' : A ≠
        canonicalMaskOrbitCoverageUnion ends m j k l zero p b a := by
      rwa [← hcomm]
    have hb' : B ≠
        canonicalMaskOrbitCoverageUnion ends m j k l zero p b a := by
      rwa [← hcomm]
    have hdOrbit := (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p b d).mp hdB |>.1
    refine ⟨d, hab.trans hdOrbit, ?_⟩
    have hdJoin := hjoin b a
      (canonicalMaskTransferOrbit_symm ends m j k l zero p hab)
      hb' ha' hBA d hdB hdA
    exact hdJoin.trans hcomm.symm

set_option maxHeartbeats 1000000 in


theorem mem_coverage_quadrangleCompletion_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero) :
    let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p a b c hdisc
    d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ↔
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a := by
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c hdisc
  have hdval : d.1.1 = canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1 := rfl
  constructor
  · intro hd
    have hd' := (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p b d).mp hd
    have hacWorks : CanonicalTransferWorks ends m k zero
        a.1.1 c.1.1 := by
      apply (canonicalTransferWorks_new_quadrangleCompletion_iff
        ends m k zero a.1.1 b.1.1 c.1.1).mp
      rw [← hdval]
      exact hd'.2
    have hcd := canonicalMaskTransferAdjacent_quadrangleCompletion
      hloop hjk hkl a b c hacWorks hdisc
    have hacOrbit : CanonicalMaskTransferOrbit ends m j k l zero p a c :=
      (hab.trans hd'.1).trans
        (Relation.ReflTransGen.single
          (canonicalMaskTransferAdjacent_symm
            ends m j k l zero p hcd))
    exact (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p a c).mpr ⟨hacOrbit, hacWorks⟩
  · intro hc
    have hc' := (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p a c).mp hc
    have hcd := canonicalMaskTransferAdjacent_quadrangleCompletion
      hloop hjk hkl a b c hc'.2 hdisc
    have hbdOrbit : CanonicalMaskTransferOrbit ends m j k l zero p b d :=
      ((canonicalMaskTransferOrbit_symm
          ends m j k l zero p hab).trans hc'.1).tail hcd
    have hbdWorks : CanonicalTransferWorks ends m k zero b.1.1 d.1.1 := by
      rw [hdval]
      exact (canonicalTransferWorks_new_quadrangleCompletion_iff
        ends m k zero a.1.1 b.1.1 c.1.1).mpr hc'.2
    exact (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p b d).mpr ⟨hbdOrbit, hbdWorks⟩

set_option maxHeartbeats 1000000 in


theorem quadrangleCompletion_mem_coverage_sdiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a)
    (hcb : c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b)
    (hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero) :
    let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p a b c hdisc
    d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
      d ∉ canonicalMaskOrbitCoverage ends m j k l zero p a := by
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c hdisc
  have hdB : d ∈ canonicalMaskOrbitCoverage ends m j k l zero p b :=
    (mem_coverage_quadrangleCompletion_iff
      hloop hjk hkl a b c hab hdisc).mpr hc
  refine ⟨hdB, ?_⟩
  intro hdA
  have hdA' := (mem_canonicalMaskOrbitCoverage_iff
    ends m j k l zero p a d).mp hdA
  have hdval : d.1.1 = canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1 := rfl
  have hbcOrbit : CanonicalMaskTransferOrbit ends m j k l zero p b c :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p hab).trans
      ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p a c).mp hc).1
  have hbcWorks : CanonicalTransferWorks ends m k zero b.1.1 c.1.1 := by
    apply (canonicalTransferWorks_quadrangleCompletion_iff
      ends m k zero a.1.1 b.1.1 c.1.1).mp
    rw [← hdval]
    exact hdA'.2
  exact hcb ((mem_canonicalMaskOrbitCoverage_iff
    ends m j k l zero p b c).mpr ⟨hbcOrbit, hbcWorks⟩)

end StatMech.GrahamGHS.FourColor
