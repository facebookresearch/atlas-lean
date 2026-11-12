/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferMatching












namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem canonicalMaskRightTightRootCutCoverageMerge_iff_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)] :
    CanonicalMaskRightTightRootCutCoverageMerge
        ends m j k l zero p ↔
      CanonicalMaskRightHall ends m j k l zero p := by
  constructor
  · exact canonicalMaskRightHall_of_tightRootCutCoverageMerge
      ends m j k l zero hloop hjk hkl hk0 p
  · intro hhall S _ htight
    have hle := hhall S
    omega



theorem canonicalMaskRightTightRootCutCoverageMerge_iff_exists_matching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)] :
    CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p ↔
      ∃ f : leftMaskFiber ends m j k l zero p ↪
          rightMaskFiber ends m j k l zero p,
        ∀ c, f c ∈ canonicalMaskRightImages ends m j k l zero p c := by
  rw [canonicalMaskRightTightRootCutCoverageMerge_iff_hall
    ends m j k l zero hloop hjk hkl hk0 p,
    canonicalMaskRightHall_iff_exists_matching]



theorem tightRootCutCoverageMerge_all_iff_canonicalMaskRightHall_all
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    (∀ p : Finset I × Finset I,
        CanonicalMaskRightTightRootCutCoverageMerge
          ends m j k l zero p) ↔
      ∀ p : Finset I × Finset I,
        CanonicalMaskRightHall ends m j k l zero p := by
  classical
  constructor <;> intro h p
  · exact (canonicalMaskRightTightRootCutCoverageMerge_iff_hall
      ends m j k l zero hloop hjk hkl hk0 p).mp (h p)
  · exact (canonicalMaskRightTightRootCutCoverageMerge_iff_hall
      ends m j k l zero hloop hjk hkl hk0 p).mpr (h p)

end StatMech.GrahamGHS.FourColor
