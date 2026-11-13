/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferGF2












open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



noncomputable def canonicalCoveragePairScore
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b : ↑m -> Fin 4) : Nat :=
  #(rowClass m a 0 ∆ rowClass m b 0) * (#m + 1) +
    #(canonicalTransferUnion ends m k zero a ∆
      canonicalTransferUnion ends m k zero b)

private theorem symmDiff_subset_of_subsets_pair
    {A B S : Finset I} (hA : A ⊆ S) (hB : B ⊆ S) : A ∆ B ⊆ S := by
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hA hi.1
  · exact hB hi.1

theorem canonicalTransferSymmDiff_card_le_m
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b : leftMaskFiber ends m j k l zero p) :
    #(canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1) ≤ #m := by
  apply Finset.card_le_card
  exact symmDiff_subset_of_subsets_pair
    (canonicalTransferUnion_subset_m hloop hjk hkl a)
    (canonicalTransferUnion_subset_m hloop hjk hkl b)

private theorem nat_pair_encode_lt_iff
    {N x y u v : Nat} (hy : y ≤ N) (hv : v ≤ N) :
    x * (N + 1) + y < u * (N + 1) + v ↔
      x < u ∨ (x = u ∧ y < v) := by
  constructor
  · intro h
    by_cases hxu : x < u
    · exact Or.inl hxu
    have hux : u ≤ x := le_of_not_gt hxu
    by_cases heq : x = u
    · subst u
      exact Or.inr ⟨rfl, Nat.lt_of_add_lt_add_left h⟩
    have hult : u < x := lt_of_le_of_ne hux (Ne.symm heq)
    have hreverse : u * (N + 1) + v < x * (N + 1) + y := by
      calc
        u * (N + 1) + v ≤ u * (N + 1) + N :=
          Nat.add_le_add_left hv _
        _ < u * (N + 1) + (N + 1) := by omega
        _ = (u + 1) * (N + 1) := by rw [Nat.add_mul]; omega
        _ ≤ x * (N + 1) :=
          Nat.mul_le_mul_right (N + 1) (Nat.succ_le_iff.mpr hult)
        _ ≤ x * (N + 1) + y := Nat.le_add_right _ _
    exact False.elim (lt_asymm h hreverse)
  · rintro (hxu | ⟨rfl, hyv⟩)
    · calc
        x * (N + 1) + y ≤ x * (N + 1) + N :=
          Nat.add_le_add_left hy _
        _ < x * (N + 1) + (N + 1) := by omega
        _ = (x + 1) * (N + 1) := by rw [Nat.add_mul]; omega
        _ ≤ u * (N + 1) :=
          Nat.mul_le_mul_right (N + 1) (Nat.succ_le_iff.mpr hxu)
        _ ≤ u * (N + 1) + v := Nat.le_add_right _ _
    · exact Nat.add_lt_add_left hyv _



theorem canonicalCoveragePairScore_lt_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) :
    canonicalCoveragePairScore ends m k zero a.1.1 b.1.1 <
        canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 ↔
      #(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) <
          #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) ∨
        (#(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) =
            #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) ∧
          #(canonicalTransferUnion ends m k zero a.1.1 ∆
              canonicalTransferUnion ends m k zero b.1.1) <
            #(canonicalTransferUnion ends m k zero c.1.1 ∆
              canonicalTransferUnion ends m k zero d.1.1)) := by
  have hab := canonicalTransferSymmDiff_card_le_m hloop hjk hkl a b
  have hcd := canonicalTransferSymmDiff_card_le_m hloop hjk hkl c d
  unfold canonicalCoveragePairScore
  exact nat_pair_encode_lt_iff hab hcd




def CanonicalMaskOrbitCoveragePairExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ a b : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    ∃ c d : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p a c ∧
        CanonicalMaskTransferOrbit ends m j k l zero p a d ∧
        canonicalMaskOrbitCoverageUnion ends m j k l zero p c d =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ∧
        canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 >
          canonicalCoveragePairScore ends m k zero a.1.1 b.1.1




def CanonicalMaskOrbitCoveragePairProgress
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ a b : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p a ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    canonicalMaskOrbitCoverage ends m j k l zero p b ≠
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ->
    (∃ t : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p a t ∧
        canonicalMaskOrbitCoverage ends m j k l zero p t =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p a b) ∨
      ∃ c d : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p a c ∧
          CanonicalMaskTransferOrbit ends m j k l zero p a d ∧
          canonicalMaskOrbitCoverageUnion ends m j k l zero p c d =
            canonicalMaskOrbitCoverageUnion ends m j k l zero p a b ∧
          canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 >
            canonicalCoveragePairScore ends m k zero a.1.1 b.1.1

theorem canonicalMaskOrbitCoveragePairProgress_of_pairExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hexpand : CanonicalMaskOrbitCoveragePairExpansion
      ends m j k l zero p) :
    CanonicalMaskOrbitCoveragePairProgress ends m j k l zero p := by
  intro a b hab ha hb
  exact Or.inr (hexpand a b hab ha hb)



noncomputable def canonicalCoveragePairCandidates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p ×
      leftMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun ab =>
    CanonicalMaskTransferOrbit ends m j k l zero p r ab.1 ∧
      CanonicalMaskTransferOrbit ends m j k l zero p r ab.2 ∧
      canonicalMaskOrbitCoverageUnion ends m j k l zero p ab.1 ab.2 =
        canonicalMaskOrbitCoverageUnion ends m j k l zero p r s

@[simp] theorem mem_canonicalCoveragePairCandidates_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s a b : leftMaskFiber ends m j k l zero p) :
    (a, b) ∈ canonicalCoveragePairCandidates ends m j k l zero p r s ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r a ∧
        CanonicalMaskTransferOrbit ends m j k l zero p r b ∧
        canonicalMaskOrbitCoverageUnion ends m j k l zero p a b =
          canonicalMaskOrbitCoverageUnion ends m j k l zero p r s := by
  classical
  simp [canonicalCoveragePairCandidates]

theorem canonicalCoveragePairCandidates_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r s : leftMaskFiber ends m j k l zero p)
    (hrs : CanonicalMaskTransferOrbit ends m j k l zero p r s) :
    (canonicalCoveragePairCandidates ends m j k l zero p r s).Nonempty := by
  refine ⟨(r, s), ?_⟩
  rw [mem_canonicalCoveragePairCandidates_iff]
  exact ⟨canonicalMaskTransferOrbit_refl ends m j k l zero p r,
    hrs, rfl⟩



theorem canonicalMaskOrbitCoverageUnionClosed_of_pairProgress
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hprogress : CanonicalMaskOrbitCoveragePairProgress
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p := by
  intro r s hrs
  let S := canonicalCoveragePairCandidates ends m j k l zero p r s
  obtain ⟨ab, habS, habMax⟩ := S.exists_max_image
    (fun ab => canonicalCoveragePairScore ends m k zero ab.1.1.1 ab.2.1.1)
    (canonicalCoveragePairCandidates_nonempty
      ends m j k l zero p r s hrs)
  rcases ab with ⟨a, b⟩
  have hab := (mem_canonicalCoveragePairCandidates_iff
    ends m j k l zero p r s a b).mp habS
  have habOrbit : CanonicalMaskTransferOrbit ends m j k l zero p a b :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p hab.1).trans hab.2.1
  by_cases ha : canonicalMaskOrbitCoverage ends m j k l zero p a =
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b
  · exact ⟨a, hab.1, ha.trans hab.2.2⟩
  by_cases hb : canonicalMaskOrbitCoverage ends m j k l zero p b =
      canonicalMaskOrbitCoverageUnion ends m j k l zero p a b
  · exact ⟨b, hab.2.1, hb.trans hab.2.2⟩
  rcases hprogress a b habOrbit ha hb with
    ⟨t, hat, htCoverage⟩ | ⟨c, d, hac, had, hcdUnion, hscore⟩
  · exact ⟨t, hab.1.trans hat, htCoverage.trans hab.2.2⟩
  · have hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c :=
      hab.1.trans hac
    have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
      hab.1.trans had
    have hcdMem : (c, d) ∈ S := by
      rw [mem_canonicalCoveragePairCandidates_iff]
      exact ⟨hrc, hrd, hcdUnion.trans hab.2.2⟩
    have hle := habMax (c, d) hcdMem
    exact False.elim ((not_lt_of_ge hle) hscore)



theorem canonicalMaskOrbitCoverageUnionClosed_of_pairExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hexpand : CanonicalMaskOrbitCoveragePairExpansion
      ends m j k l zero p) :
    CanonicalMaskOrbitCoverageUnionClosed ends m j k l zero p :=
  canonicalMaskOrbitCoverageUnionClosed_of_pairProgress
    ends m j k l zero p
      (canonicalMaskOrbitCoveragePairProgress_of_pairExpansion
        ends m j k l zero p hexpand)

end StatMech.GrahamGHS.FourColor
