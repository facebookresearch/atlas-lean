/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferCommonGood










open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalMaskOrbitCoverage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun d =>
    CanonicalMaskTransferOrbit ends m j k l zero p r d ∧
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1

@[simp] theorem mem_canonicalMaskOrbitCoverage_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r d ∧
        CanonicalTransferWorks ends m k zero r.1.1 d.1.1 := by
  classical
  simp [canonicalMaskOrbitCoverage]


noncomputable def canonicalMaskOrbitCoverageUnion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact canonicalMaskOrbitCoverage ends m j k l zero p r ∪
    canonicalMaskOrbitCoverage ends m j k l zero p s

@[simp] theorem mem_canonicalMaskOrbitCoverageUnion_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskOrbitCoverageUnion ends m j k l zero p r s ↔
      d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∨
        d ∈ canonicalMaskOrbitCoverage ends m j k l zero p s := by
  classical
  simp [canonicalMaskOrbitCoverageUnion]



def CanonicalMaskOrbitCoverageDirected
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      ∃ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r t ∧
          ∀ d : leftMaskFiber ends m j k l zero p,
            CanonicalMaskTransferOrbit ends m j k l zero p r d ->
            (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∨
              CanonicalTransferWorks ends m k zero s.1.1 d.1.1) ->
            CanonicalTransferWorks ends m k zero t.1.1 d.1.1


noncomputable def canonicalMaskOrbitMaxCoverageReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskTransferOrbitFinset ends m j k l zero p c).exists_max_image
      (fun r => #(canonicalMaskOrbitCoverage ends m j k l zero p r))
      (canonicalMaskTransferOrbitFinset_nonempty
        ends m j k l zero p c))

theorem canonicalMaskOrbitMaxCoverageReference_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitMaxCoverageReference ends m j k l zero p c ∈
        canonicalMaskTransferOrbitFinset ends m j k l zero p c ∧
      ∀ d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c,
        #(canonicalMaskOrbitCoverage ends m j k l zero p d) ≤
          #(canonicalMaskOrbitCoverage ends m j k l zero p
            (canonicalMaskOrbitMaxCoverageReference
              ends m j k l zero p c)) :=
  Classical.choose_spec
    ((canonicalMaskTransferOrbitFinset ends m j k l zero p c).exists_max_image
      (fun r => #(canonicalMaskOrbitCoverage ends m j k l zero p r))
      (canonicalMaskTransferOrbitFinset_nonempty
        ends m j k l zero p c))

theorem canonicalMaskOrbitMaxCoverageReference_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferOrbit ends m j k l zero p c
      (canonicalMaskOrbitMaxCoverageReference ends m j k l zero p c) := by
  rw [← mem_canonicalMaskTransferOrbitFinset_iff]
  exact (canonicalMaskOrbitMaxCoverageReference_spec
    ends m j k l zero p c).1

theorem canonicalMaskOrbitMaxCoverageReference_card_ge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    #(canonicalMaskOrbitCoverage ends m j k l zero p d) ≤
      #(canonicalMaskOrbitCoverage ends m j k l zero p
        (canonicalMaskOrbitMaxCoverageReference
          ends m j k l zero p c)) := by
  apply (canonicalMaskOrbitMaxCoverageReference_spec
    ends m j k l zero p c).2 d
  rwa [mem_canonicalMaskTransferOrbitFinset_iff]



theorem canonicalMaskOrbitHasCommonReference_of_coverageDirected
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hdirected : CanonicalMaskOrbitCoverageDirected
      ends m j k l zero p) :
    CanonicalMaskOrbitHasCommonReference ends m j k l zero p := by
  classical
  intro c
  let r := canonicalMaskOrbitMaxCoverageReference
    ends m j k l zero p c
  have hcr : CanonicalMaskTransferOrbit ends m j k l zero p c r :=
    canonicalMaskOrbitMaxCoverageReference_mem
      ends m j k l zero p c
  refine ⟨r, ?_⟩
  rw [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
  refine ⟨hcr, ?_⟩
  intro d hcd
  have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
    (canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcr).trans hcd
  obtain ⟨t, hrt, ht⟩ := hdirected r d hrd
  have hct : CanonicalMaskTransferOrbit ends m j k l zero p c t :=
    hcr.trans hrt
  have hsubset :
      canonicalMaskOrbitCoverage ends m j k l zero p r ⊆
        canonicalMaskOrbitCoverage ends m j k l zero p t := by
    intro x hx
    have hx' := (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p r x).mp hx
    rw [mem_canonicalMaskOrbitCoverage_iff]
    exact ⟨(canonicalMaskTransferOrbit_symm
        ends m j k l zero p hrt).trans hx'.1,
      ht x hx'.1 (Or.inl hx'.2)⟩
  have hcard : #(canonicalMaskOrbitCoverage ends m j k l zero p t) ≤
      #(canonicalMaskOrbitCoverage ends m j k l zero p r) := by
    simpa [r] using canonicalMaskOrbitMaxCoverageReference_card_ge
      ends m j k l zero p c t hct
  have heq : canonicalMaskOrbitCoverage ends m j k l zero p r =
      canonicalMaskOrbitCoverage ends m j k l zero p t :=
    Finset.eq_of_subset_of_card_le hsubset hcard
  have htd : CanonicalTransferWorks ends m k zero t.1.1 d.1.1 :=
    ht d hrd (Or.inr
      (canonicalTransferWorks_self hloop hjk hkl hk0 d))
  have hdmem : d ∈ canonicalMaskOrbitCoverage ends m j k l zero p t := by
    rw [mem_canonicalMaskOrbitCoverage_iff]
    exact ⟨(canonicalMaskTransferOrbit_symm
      ends m j k l zero p hrt).trans hrd, htd⟩
  rw [← heq, mem_canonicalMaskOrbitCoverage_iff] at hdmem
  exact hdmem.2


theorem GrahamFiberMinor_of_canonicalMaskOrbitCoverageDirected
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hdirected : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageDirected ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero :=
  GrahamFiberMinor_of_canonicalMaskOrbitCommonReference
    ends m j k l zero hloop hjk hkl
    (fun p => canonicalMaskOrbitHasCommonReference_of_coverageDirected
      ends m j k l zero hloop hjk hkl hk0 p (hdirected p))

end StatMech.GrahamGHS.FourColor
