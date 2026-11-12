/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferCoverageDirected
import Code.FrontierA.GrahamRowDataMaskHall











namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem rowDataRepairHall_of_canonicalMaskOrbitCoverageDirected
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hdirected : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageDirected ends m j k l zero p) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskFiberEmbeddings
  intro p
  exact canonicalMaskCommonReferenceEmbedding
    ends m j k l zero hloop hjk hkl p
    (canonicalMaskOrbitHasCommonReference_of_coverageDirected
      ends m j k l zero hloop hjk hkl hk0 p (hdirected p))



theorem GrahamWeightedRowMinor_of_canonicalMaskOrbitCoverageDirected
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hdirected : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitCoverageDirected ends m j k l zero p) :
    GrahamWeightedRowMinor ends m j k l zero :=
  GrahamWeightedRowMinor_of_rowDataRepairHall ends m j k l zero
    (rowDataRepairHall_of_canonicalMaskOrbitCoverageDirected
      ends m j k l zero hloop hjk hkl hk0 hdirected)

end StatMech.GrahamGHS.FourColor
