/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferOrbit










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



def CanonicalTransferWorks
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : Prop :=
  RowsDisconnect ends m
    (balancedSwap m
      (canonicalMiddleTransfer ends m r k zero)
      (canonicalOuterTransfer ends m r k zero) c) k zero



theorem canonicalTransferWorks_iff_rowSymmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ↔
      ¬ connK ends
          (rowClass m c.1.1 0 ∆
            canonicalTransferUnion ends m k zero r.1.1) k zero ∧
        ¬ connK ends
          (rowClass m c.1.1 1 ∆
            canonicalTransferUnion ends m k zero r.1.1) k zero := by
  have hv := canonicalTransfers_valid_on_sameMask
    hloop hjk hkl r c
  rw [CanonicalTransferWorks, RowsDisconnect,
    rowClass_balancedSwap_zero hv.1 hv.2.1,
    rowClass_balancedSwap_one hv.1 hv.2.1]
  rfl

theorem canonicalTransferWorks_self
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero c.1.1 c.1.1 :=
  canonicalBalancedSwap_disconnects hloop hjk hkl hk0 c.1.2



noncomputable def canonicalMaskOrbitCommonReferenceFinset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun r =>
    CanonicalMaskTransferOrbit ends m j k l zero p c r ∧
      ∀ d, CanonicalMaskTransferOrbit ends m j k l zero p c d ->
        CanonicalTransferWorks ends m k zero r.1.1 d.1.1

@[simp] theorem mem_canonicalMaskOrbitCommonReferenceFinset_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c r : leftMaskFiber ends m j k l zero p) :
    r ∈ canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c ↔
      CanonicalMaskTransferOrbit ends m j k l zero p c r ∧
        ∀ d, CanonicalMaskTransferOrbit ends m j k l zero p c d ->
          CanonicalTransferWorks ends m k zero r.1.1 d.1.1 := by
  classical
  simp [canonicalMaskOrbitCommonReferenceFinset]



def CanonicalMaskOrbitHasCommonReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : leftMaskFiber ends m j k l zero p,
    (canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c).Nonempty

theorem canonicalMaskOrbitCommonReferenceFinset_eq_of_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c =
      canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p d := by
  ext r
  simp only [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
  constructor
  · rintro ⟨hcr, hgood⟩
    refine ⟨(canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcd).trans hcr, ?_⟩
    intro x hdx
    exact hgood x (hcd.trans hdx)
  · rintro ⟨hdr, hgood⟩
    refine ⟨hcd.trans hdr, ?_⟩
    intro x hcx
    exact hgood x ((canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcd).trans hcx)



noncomputable def canonicalMaskOrbitCommonReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose
    ((canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (hcommon c))

theorem canonicalMaskOrbitCommonReference_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c : leftMaskFiber ends m j k l zero p) :
    canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c ∈
        canonicalMaskOrbitCommonReferenceFinset ends m j k l zero p c ∧
      ∀ r ∈ canonicalMaskOrbitCommonReferenceFinset
          ends m j k l zero p c,
        canonicalMaskOrbitScore ends m k zero p
            (canonicalMaskOrbitCommonReference
              ends m j k l zero p hcommon c) ≤
          canonicalMaskOrbitScore ends m k zero p r :=
  Classical.choose_spec
    ((canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c).exists_min_image
        (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l))
        (hcommon c))

theorem canonicalMaskOrbitCommonReference_eq_of_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalMaskOrbitCommonReference ends m j k l zero p hcommon c =
      canonicalMaskOrbitCommonReference ends m j k l zero p hcommon d := by
  let rc := canonicalMaskOrbitCommonReference
    ends m j k l zero p hcommon c
  let rd := canonicalMaskOrbitCommonReference
    ends m j k l zero p hcommon d
  have hrc := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon c).1
  have hrd := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon d).1
  have hrcSpec := (mem_canonicalMaskOrbitCommonReferenceFinset_iff
    ends m j k l zero p c rc).mp hrc
  have hrdSpec := (mem_canonicalMaskOrbitCommonReferenceFinset_iff
    ends m j k l zero p d rd).mp hrd
  have hrdc : rd ∈ canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p c := by
    rw [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
    refine ⟨hcd.trans hrdSpec.1, ?_⟩
    intro x hcx
    exact hrdSpec.2 x
      ((canonicalMaskTransferOrbit_symm
        ends m j k l zero p hcd).trans hcx)
  have hrcd : rc ∈ canonicalMaskOrbitCommonReferenceFinset
      ends m j k l zero p d := by
    rw [mem_canonicalMaskOrbitCommonReferenceFinset_iff]
    refine ⟨(canonicalMaskTransferOrbit_symm
      ends m j k l zero p hcd).trans hrcSpec.1, ?_⟩
    intro x hdx
    exact hrcSpec.2 x (hcd.trans hdx)
  have hle := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon c).2 rd hrdc
  have hge := (canonicalMaskOrbitCommonReference_spec
    ends m j k l zero p hcommon d).2 rc hrcd
  apply canonicalMaskOrbitScore_injective ends m j k l zero p
  exact le_antisymm hle hge

theorem canonicalMaskOrbitCommonReference_selector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
    IsCanonicalMaskOrbitSelector ends m j k l zero p
      (canonicalMaskOrbitCommonReference
        ends m j k l zero p hcommon) := by
  constructor
  · intro c
    exact (mem_canonicalMaskOrbitCommonReferenceFinset_iff
      ends m j k l zero p c
        (canonicalMaskOrbitCommonReference
          ends m j k l zero p hcommon c)).mp
            (canonicalMaskOrbitCommonReference_spec
              ends m j k l zero p hcommon c).1 |>.1
  · exact canonicalMaskOrbitCommonReference_eq_of_orbit
      ends m j k l zero p hcommon

theorem canonicalMaskOrbitCommonReference_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference ends m j k l zero p)
    (c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero
      (canonicalMaskOrbitCommonReference
        ends m j k l zero p hcommon c).1.1 c.1.1 := by
  have hspec := (mem_canonicalMaskOrbitCommonReferenceFinset_iff
    ends m j k l zero p c
      (canonicalMaskOrbitCommonReference
        ends m j k l zero p hcommon c)).mp
          (canonicalMaskOrbitCommonReference_spec
            ends m j k l zero p hcommon c).1
  exact hspec.2 c
    (canonicalMaskTransferOrbit_refl ends m j k l zero p c)



noncomputable def canonicalMaskCommonReferenceEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hcommon : CanonicalMaskOrbitHasCommonReference
      ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p :=
  canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p
    (canonicalMaskOrbitCommonReference ends m j k l zero p hcommon)
    (canonicalMaskOrbitCommonReference_selector
      ends m j k l zero p hcommon)
    (canonicalMaskOrbitCommonReference_works
      ends m j k l zero p hcommon)



theorem GrahamFiberMinor_of_canonicalMaskOrbitCommonReference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hcommon : ∀ p : Finset I × Finset I,
      CanonicalMaskOrbitHasCommonReference ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskwise
  intro p
  exact Fintype.card_le_of_injective
    (canonicalMaskCommonReferenceEmbedding
      ends m j k l zero hloop hjk hkl p (hcommon p))
    (canonicalMaskCommonReferenceEmbedding
      ends m j k l zero hloop hjk hkl p (hcommon p)).injective

end StatMech.GrahamGHS.FourColor
