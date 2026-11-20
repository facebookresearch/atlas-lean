/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferCoverageDirected











open Finset

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



def CanonicalMaskOrbitCoverageUnionClosed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r s : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r s ->
      ∃ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r t ∧
          canonicalMaskOrbitCoverage ends m j k l zero p t =
            canonicalMaskOrbitCoverageUnion ends m j k l zero p r s



noncomputable def canonicalMaskOrbitCoverageJoinCandidates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun t =>
    CanonicalMaskTransferOrbit ends m j k l zero p r t ∧
      canonicalMaskOrbitCoverage ends m j k l zero p t =
        canonicalMaskOrbitCoverageUnion ends m j k l zero p r s

@[simp] theorem mem_canonicalMaskOrbitCoverageJoinCandidates_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s t : leftMaskFiber ends m j k l zero p) :
    t ∈ canonicalMaskOrbitCoverageJoinCandidates ends m j k l zero p r s ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r t ∧
        canonicalMaskOrbitCoverage ends m j k l zero p t =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p r s := by
  classical
  simp [canonicalMaskOrbitCoverageJoinCandidates]

theorem canonicalMaskOrbitCoverageJoinCandidates_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    (canonicalMaskOrbitCoverageJoinCandidates
      ends m j k l zero p r s).Nonempty := by
  obtain ⟨t, hrt, ht⟩ := hclosed r s hrs
  refine ⟨t, ?_⟩
  rw [mem_canonicalMaskOrbitCoverageJoinCandidates_iff]
  exact ⟨hrt, ht⟩


noncomputable def canonicalMaskOrbitCoverageJoin
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskOrbitCoverageJoinCandidates
      ends m j k l zero p r s).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (canonicalMaskOrbitCoverageJoinCandidates_nonempty
          ends m j k l zero p hclosed r s hrs))

theorem canonicalMaskOrbitCoverageJoin_mem_candidates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    canonicalMaskOrbitCoverageJoin
        ends m j k l zero p hclosed r s hrs ∈
      canonicalMaskOrbitCoverageJoinCandidates
        ends m j k l zero p r s :=
  (Classical.choose_spec
    ((canonicalMaskOrbitCoverageJoinCandidates
      ends m j k l zero p r s).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (canonicalMaskOrbitCoverageJoinCandidates_nonempty
          ends m j k l zero p hclosed r s hrs))).1

theorem canonicalMaskOrbitCoverageJoin_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    CanonicalMaskTransferOrbit ends m j k l zero p r
      (canonicalMaskOrbitCoverageJoin
        ends m j k l zero p hclosed r s hrs) := by
  exact (mem_canonicalMaskOrbitCoverageJoinCandidates_iff
    ends m j k l zero p r s
      (canonicalMaskOrbitCoverageJoin
        ends m j k l zero p hclosed r s hrs)).mp
          (canonicalMaskOrbitCoverageJoin_mem_candidates
            ends m j k l zero p hclosed r s hrs) |>.1

theorem canonicalMaskOrbitCoverageJoin_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s)
    (d : leftMaskFiber ends m j k l zero p)
    (hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d)
    (hworks : CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∨
      CanonicalTransferWorks ends m k zero s.1.1 d.1.1) :
    CanonicalTransferWorks ends m k zero
      (canonicalMaskOrbitCoverageJoin
        ends m j k l zero p hclosed r s hrs).1.1 d.1.1 := by
  have hmem := canonicalMaskOrbitCoverageJoin_mem_candidates
    ends m j k l zero p hclosed r s hrs
  rw [mem_canonicalMaskOrbitCoverageJoinCandidates_iff] at hmem
  have hdmem : d ∈ canonicalMaskOrbitCoverage ends m j k l zero p
      (canonicalMaskOrbitCoverageJoin
        ends m j k l zero p hclosed r s hrs) := by
    rw [hmem.2, mem_canonicalMaskOrbitCoverageUnion_iff]
    rcases hworks with hworks | hworks
    · exact Or.inl ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p r d).mpr ⟨hrd, hworks⟩)
    · have hsd : CanonicalMaskTransferOrbit ends m j k l zero p s d :=
        (canonicalMaskTransferOrbit_symm
          ends m j k l zero p hrs).trans hrd
      exact Or.inr ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p s d).mpr ⟨hsd, hworks⟩)
  exact ((mem_canonicalMaskOrbitCoverage_iff ends m j k l zero p
    (canonicalMaskOrbitCoverageJoin
      ends m j k l zero p hclosed r s hrs) d).mp hdmem).2


theorem canonicalMaskOrbitCoverageDirected_of_unionClosed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hclosed : CanonicalMaskOrbitCoverageUnionClosed
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageDirected ends m j k l zero p := by
  intro r s hrs
  exact ⟨canonicalMaskOrbitCoverageJoin
      ends m j k l zero p hclosed r s hrs,
    canonicalMaskOrbitCoverageJoin_orbit
      ends m j k l zero p hclosed r s hrs,
    canonicalMaskOrbitCoverageJoin_works
      ends m j k l zero p hclosed r s hrs⟩


theorem GrahamFiberMinor_of_canonicalMaskOrbitCoverageUnionClosed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hclosed : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero :=
  GrahamFiberMinor_of_canonicalMaskOrbitCoverageDirected
    ends m j k l zero hloop hjk hkl hk0
    (fun p => canonicalMaskOrbitCoverageDirected_of_unionClosed
      ends m j k l zero p (hclosed p))

end StatMech.GrahamGHS.FourColor
