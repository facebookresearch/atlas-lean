/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCycleComponentExchange












open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

private theorem componentExchange_zeroComponent_source_empty
    {ends : I → Sym2 W} {m K : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag) (hKm : K ⊆ m)
    (hjk : j ≠ k)
    (hleft : LeftRowSupport ends m j k l zero K) :
    sources ends (edgeComponent ends K zero) = ∅ := by
  have hjkConn : connK ends K j k :=
    StatMech.Walls.gc6_pairingPath_abstract ends K K
      (fun i hi => hloop i (hKm hi)) Finset.Subset.rfl hleft.1 hjk
  rw [sources_edgeComponent, hleft.1]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
  rw [mem_compOf] at hcomp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hleft.2.2.1
      (connK_symm ends K (hcomp.trans hjkConn))
  · exact hleft.2.2.1 (connK_symm ends K hcomp)





noncomputable def componentExchangeSupportTag
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    leftRowSupportIndex ends m j k l zero →
      rightRowData ends m j k l zero := fun d => by
  classical
  let K := d.1
  let A := edgeComponent ends K zero
  let R := exchangeFirstRow ends K (m \ K) k zero
  have hmap := componentExchange_maps_leftRowSupport
    (ends := ends) (m := m) (K := K) (j := j) (k := k) (l := l)
    (zero := zero) hloop d.2.1 hjk hkl hk0 d.2.2
  have hRsub : R ⊆ m := by simpa only [R, K] using hmap.1
  have hRright : RightRowSupport ends m j k l zero R := by
    simpa only [R, K] using hmap.2
  have hAsubK : A ⊆ K := by
    intro i hi
    change i ∈ edgeComponent ends K zero at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hBsub : edgeComponent ends (m \ K) k ⊆ m \ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hPsub : K \ A ⊆ R := by
    intro i hi
    exact Finset.mem_union_left _ hi
  have hAsubCompl : A ⊆ m \ R := by
    intro i hiA
    refine Finset.mem_sdiff.mpr ⟨d.2.1 (hAsubK hiA), ?_⟩
    intro hiR
    rcases Finset.mem_union.mp hiR with hiKA | hiB
    · exact (Finset.mem_sdiff.mp hiKA).2 hiA
    · exact (Finset.mem_sdiff.mp (hBsub hiB)).2 (hAsubK hiA)
  have hAsrc : sources ends A = ∅ := by
    simpa only [A, K] using
      componentExchange_zeroComponent_source_empty hloop d.2.1 hjk d.2.2
  have hPsrc : sources ends (K \ A) = {j, k} := by
    rw [sources_sdiff_of_subset hAsubK, d.2.2.1, hAsrc]
    simp
  exact ⟨⟨R, hRsub, hRright⟩,
    ⟨⟨K \ A, hPsub, hPsrc⟩, ⟨A, hAsubCompl, hAsrc⟩⟩⟩



theorem componentExchangeSupportTag_injective
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    Function.Injective
      (componentExchangeSupportTag ends m j k l zero
        hloop hjk hkl hk0) := by
  classical
  intro d e hde
  have hP := congrArg (fun r => r.2.1.1) hde
  have hA := congrArg (fun r => r.2.2.1) hde
  apply Subtype.ext
  have hdsub : edgeComponent ends d.1 zero ⊆ d.1 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hesub : edgeComponent ends e.1 zero ⊆ e.1 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hdrecover : d.1 =
      (d.1 \ edgeComponent ends d.1 zero) ∪
        edgeComponent ends d.1 zero := by
    exact (Finset.sdiff_union_of_subset hdsub).symm
  have herecover : e.1 =
      (e.1 \ edgeComponent ends e.1 zero) ∪
        edgeComponent ends e.1 zero := by
    exact (Finset.sdiff_union_of_subset hesub).symm
  rw [hdrecover, herecover]
  dsimp only [componentExchangeSupportTag] at hP hA
  rw [hP, hA]



theorem card_leftRowSupportIndex_le_rightRowData
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    Fintype.card (leftRowSupportIndex ends m j k l zero) ≤
      Fintype.card (rightRowData ends m j k l zero) := by
  exact Fintype.card_le_of_injective
    (componentExchangeSupportTag ends m j k l zero hloop hjk hkl hk0)
    (componentExchangeSupportTag_injective
      ends m j k l zero hloop hjk hkl hk0)

end StatMech.GrahamGHS.FourColor
