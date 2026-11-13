/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Ising.AizenmanBarsky
import Code.Ising.GHSThreePoint
import Code.Ising.CorrelationRatio
import Code.Ising.CurrentWeight
import Code.Sharpness.GhostCurrentRep
import Code.Sharpness.ClaimIsingFull
import Code.Sharpness.BackbonePropsFull
import Code.Sharpness.Simon
import Code.Walls.gc10ghostfourpoint
import Code.Walls.ghc_urselleqgap
import Code.Walls.vbgtriangle
import Code.Walls.gc7ghosteven

open scoped BigOperators symmDiff
open Finset

namespace StatMech
namespace GrahamGHS

open Ising
open Sharpness







namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]








def boundarySector (ends : ι → Sym2 W) (S : Finset ι) (b : Finset W) :=
  {T : Finset ι // T ⊆ S ∧ Sharpness.RandomCurrent.sources ends T = b}

noncomputable instance instFintypeBoundarySector (ends : ι → Sym2 W) (S : Finset ι)
    (b : Finset W) : Fintype (boundarySector ends S b) := by
  classical
  exact Fintype.subtype (S.powerset.filter (fun T => Sharpness.RandomCurrent.sources ends T = b))
    (fun T => by simp [Finset.mem_powerset])



noncomputable def boundarySectorEquivCycle (ends : ι → Sym2 W) (S X : Finset ι)
    (b : Finset W) (hXsub : X ⊆ S) (hXsrc : Sharpness.RandomCurrent.sources ends X = b) :
    boundarySector ends S b ≃ boundarySector ends S ∅ := by
  classical
  let shift : Finset ι → Finset ι := fun T => T ∆ X
  refine
    { toFun := fun T => ⟨shift T.1, ?_⟩
      invFun := fun T => ⟨shift T.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro i hi
      rw [Finset.mem_symmDiff] at hi
      exact hi.elim (fun h => T.2.1 h.1) (fun h => hXsub h.1)
    · dsimp only [shift]
      rw [Sharpness.RandomCurrent.sources_symmDiff, T.2.2, hXsrc, symmDiff_self]
      rfl
  · constructor
    · intro i hi
      rw [Finset.mem_symmDiff] at hi
      exact hi.elim (fun h => T.2.1 h.1) (fun h => hXsub h.1)
    · dsimp only [shift]
      rw [Sharpness.RandomCurrent.sources_symmDiff, T.2.2, hXsrc]
      simp
  · intro T
    apply Subtype.ext
    simp [shift]
  · intro T
    apply Subtype.ext
    simp [shift]



theorem boundarySector_card_eq_cycle (ends : ι → Sym2 W) (S : Finset ι) (b : Finset W)
    (X : boundarySector ends S b) :
    Fintype.card (boundarySector ends S b) = Fintype.card (boundarySector ends S ∅) := by
  exact Fintype.card_congr
    (boundarySectorEquivCycle ends S X.1 b X.2.1 X.2.2)


def colorClass (m : Finset ι) (c : ↑m → Fin 4) (a : Fin 4) : Finset ι :=
  (m.attach.filter (fun i => c i = a)).map ⟨Subtype.val, Subtype.val_injective⟩

theorem colorClass_subset (m : Finset ι) (c : ↑m → Fin 4) (a : Fin 4) :
    colorClass m c a ⊆ m := by
  intro i hi
  simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hi
  obtain ⟨j, _, rfl⟩ := hi
  exact j.2

theorem colorClass_disjoint (m : Finset ι) (c : ↑m → Fin 4) {a b : Fin 4} (hab : a ≠ b) :
    Disjoint (colorClass m c a) (colorClass m c b) := by
  rw [Finset.disjoint_left]
  intro i hia hib
  simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hia hib
  obtain ⟨ia, ⟨_, hca⟩, hia⟩ := hia
  obtain ⟨ib, ⟨_, hcb⟩, hib⟩ := hib
  have hieq : ia = ib := Subtype.ext (hia.trans hib.symm)
  subst ib
  exact hab (hca.symm.trans hcb)

theorem connK_mono {ends : ι → Sym2 W} {K L : Finset ι} (hKL : K ⊆ L) {u v : W} :
    Sharpness.RandomCurrent.connK ends K u v → Sharpness.RandomCurrent.connK ends L u v := by
  apply Relation.ReflTransGen.mono
  rintro a b ⟨i, hi, ha, hb, hab⟩
  exact ⟨i, hKL hi, ha, hb, hab⟩


noncomputable def edgeComponent (ends : ι → Sym2 W) (K : Finset ι) (u : W) : Finset ι :=
  by
    classical
    exact K.filter (fun i => ∀ x ∈ ends i, Sharpness.RandomCurrent.connK ends K u x)

theorem mem_edgeComponent_of_endpoint {ends : ι → Sym2 W} {K : Finset ι}
    {u : W} {i : ι} (hi : i ∈ K) (hu : u ∈ ends i) :
    i ∈ edgeComponent ends K u := by
  classical
  rw [edgeComponent, Finset.mem_filter]
  refine ⟨hi, ?_⟩
  intro x hx
  by_cases hux : u = x
  · subst x
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨i, hi, hu, hx, hux⟩

theorem mem_edgeComponent_of_reachable_endpoint {ends : ι → Sym2 W} {K : Finset ι}
    {u x : W} {i : ι} (hux : Sharpness.RandomCurrent.connK ends K u x)
    (hi : i ∈ K) (hx : x ∈ ends i) : i ∈ edgeComponent ends K u := by
  classical
  rw [edgeComponent, Finset.mem_filter]
  refine ⟨hi, ?_⟩
  intro y hy
  by_cases hxy : x = y
  · simpa [hxy] using hux
  · exact hux.tail ⟨i, hi, hx, hy, hxy⟩



theorem degK_inter_edgeComponent_of_conn {ends : ι → Sym2 W} {T K : Finset ι}
    (hTK : T ⊆ K) {u x : W} (hux : Sharpness.RandomCurrent.connK ends K u x) :
    Sharpness.RandomCurrent.degK ends (T ∩ edgeComponent ends K u) x =
      Sharpness.RandomCurrent.degK ends T x := by
  classical
  unfold Sharpness.RandomCurrent.degK
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hiT, hxi⟩
    exact ⟨⟨hiT, mem_edgeComponent_of_reachable_endpoint hux (hTK hiT) hxi⟩, hxi⟩


theorem degK_inter_edgeComponent_of_not_conn {ends : ι → Sym2 W} {T K : Finset ι}
    {u x : W} (hux : ¬ Sharpness.RandomCurrent.connK ends K u x) :
    Sharpness.RandomCurrent.degK ends (T ∩ edgeComponent ends K u) x = 0 := by
  classical
  unfold Sharpness.RandomCurrent.degK
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_inter] at hi
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hux (hi.1.2.2 x hi.2)


theorem sources_inter_edgeComponent {ends : ι → Sym2 W} {T K : Finset ι}
    (hTK : T ⊆ K) (u : W) :
    Sharpness.RandomCurrent.sources ends (T ∩ edgeComponent ends K u) =
      Sharpness.RandomCurrent.sources ends T ∩
        Sharpness.RandomCurrent.compOf ends K u := by
  ext x
  simp only [Sharpness.RandomCurrent.mem_sources, Finset.mem_inter,
    Sharpness.RandomCurrent.mem_compOf]
  by_cases hux : Sharpness.RandomCurrent.connK ends K u x
  · rw [degK_inter_edgeComponent_of_conn hTK hux]
    simp only [hux, and_true]
  · rw [degK_inter_edgeComponent_of_not_conn hux]
    simp [hux]

theorem sources_union_of_disjoint {ends : ι → Sym2 W} {S T : Finset ι}
    (hST : Disjoint S T) :
    Sharpness.RandomCurrent.sources ends (S ∪ T) =
      Sharpness.RandomCurrent.sources ends S ∆ Sharpness.RandomCurrent.sources ends T := by
  have hu : S ∪ T = S ∆ T := by
    ext i
    simp only [Finset.mem_union, Finset.mem_symmDiff]
    rw [Finset.disjoint_left] at hST
    aesop
  rw [hu, Sharpness.RandomCurrent.sources_symmDiff]

theorem sources_sdiff_of_subset {ends : ι → Sym2 W} {S T : Finset ι} (hTS : T ⊆ S) :
    Sharpness.RandomCurrent.sources ends (S \ T) =
      Sharpness.RandomCurrent.sources ends S ∆ Sharpness.RandomCurrent.sources ends T := by
  have heq : S \ T = S ∆ T := by
    ext i
    have hmem := @hTS i
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
    aesop
  rw [heq, Sharpness.RandomCurrent.sources_symmDiff]

theorem sources_edgeComponent {ends : ι → Sym2 W} (K : Finset ι) (u : W) :
    Sharpness.RandomCurrent.sources ends (edgeComponent ends K u) =
      Sharpness.RandomCurrent.sources ends K ∩ Sharpness.RandomCurrent.compOf ends K u := by
  classical
  have hcap : K ∩ edgeComponent ends K u = edgeComponent ends K u := by
    ext i
    simp only [Finset.mem_inter]
    constructor
    · exact fun hi => hi.2
    · intro hi
      have hiK : i ∈ K := by
        rw [edgeComponent, Finset.mem_filter] at hi
        exact hi.1
      exact ⟨hiK, hi⟩
  rw [← hcap, sources_inter_edgeComponent Finset.Subset.rfl]

theorem not_connK_of_no_incident {ends : ι → Sym2 W} {K : Finset ι} {u v : W}
    (huv : u ≠ v) (hinc : ∀ i ∈ K, u ∉ ends i) :
    ¬ Sharpness.RandomCurrent.connK ends K u v := by
  intro huvconn
  have heq : ∀ x, Sharpness.RandomCurrent.connK ends K u x → x = u := by
    intro x hx
    induction hx with
    | refl => rfl
    | tail hab hstep ih =>
        rw [ih] at hstep
        rcases hstep with ⟨i, hi, hu, -, -⟩
        exact False.elim (hinc i hi hu)
  exact huv (heq v huvconn).symm



noncomputable def exchangeFirstRow (ends : ι → Sym2 W) (K L : Finset ι)
    (k zero : W) : Finset ι :=
  (K \ edgeComponent ends K zero) ∪ edgeComponent ends L k

noncomputable def exchangeSecondRow (ends : ι → Sym2 W) (K L : Finset ι)
    (k zero : W) : Finset ι :=
  (L \ edgeComponent ends L k) ∪ edgeComponent ends K zero



theorem componentExchange_disconnects {ends : ι → Sym2 W} {K L : Finset ι}
    {k zero : W} (hk0 : k ≠ zero)
    (hK : ¬ Sharpness.RandomCurrent.connK ends K k zero)
    (hL : ¬ Sharpness.RandomCurrent.connK ends L k zero) :
    ¬ Sharpness.RandomCurrent.connK ends (exchangeFirstRow ends K L k zero) k zero ∧
      ¬ Sharpness.RandomCurrent.connK ends (exchangeSecondRow ends K L k zero) k zero := by
  classical
  constructor
  · intro hkzero
    apply (not_connK_of_no_incident hk0.symm ?_)
      (Sharpness.RandomCurrent.connK_symm ends _ hkzero)
    intro i hi hzero
    rw [exchangeFirstRow, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rcases Finset.mem_sdiff.mp hi with ⟨hiK, hin⟩
      exact hin (mem_edgeComponent_of_endpoint hiK hzero)
    · rw [edgeComponent, Finset.mem_filter] at hi
      exact hL (hi.2 zero hzero)
  · apply not_connK_of_no_incident hk0
    intro i hi hk
    rw [exchangeSecondRow, Finset.mem_union] at hi
    rcases hi with hi | hi
    · rcases Finset.mem_sdiff.mp hi with ⟨hiL, hin⟩
      exact hin (mem_edgeComponent_of_endpoint hiL hk)
    · rw [edgeComponent, Finset.mem_filter] at hi
      have hz0k := hi.2 k hk
      exact hK (Sharpness.RandomCurrent.connK_symm ends K hz0k)



theorem componentExchange_boundaries {ends : ι → Sym2 W} {K L : Finset ι}
    {j k l zero : W} (hloopK : ∀ i ∈ K, ¬ (ends i).IsDiag)
    (hloopL : ∀ i ∈ L, ¬ (ends i).IsDiag) (hKL : Disjoint K L)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hsrcK : Sharpness.RandomCurrent.sources ends K = {j, k})
    (hsrcL : Sharpness.RandomCurrent.sources ends L = {k, l})
    (hdiscK : ¬ Sharpness.RandomCurrent.connK ends K k zero)
    (hdiscL : ¬ Sharpness.RandomCurrent.connK ends L k zero) :
    Sharpness.RandomCurrent.sources ends (exchangeFirstRow ends K L k zero) =
        {j, k} ∆ {k, l} ∧
      Sharpness.RandomCurrent.sources ends (exchangeSecondRow ends K L k zero) = ∅ := by
  classical
  have hjkConn : Sharpness.RandomCurrent.connK ends K j k := by
    exact Walls.gc6_pairingPath_abstract ends K K hloopK Finset.Subset.rfl hsrcK hjk
  have hklConn : Sharpness.RandomCurrent.connK ends L k l := by
    exact Walls.gc6_pairingPath_abstract ends L L hloopL Finset.Subset.rfl hsrcL hkl
  have hE0src : Sharpness.RandomCurrent.sources ends (edgeComponent ends K zero) = ∅ := by
    rw [sources_edgeComponent, hsrcK]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [Sharpness.RandomCurrent.mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hdiscK
        (Sharpness.RandomCurrent.connK_symm ends K (hcomp.trans hjkConn))
    · exact hdiscK (Sharpness.RandomCurrent.connK_symm ends K hcomp)
  have hE1src : Sharpness.RandomCurrent.sources ends (edgeComponent ends L k) = {k, l} := by
    rw [sources_edgeComponent, hsrcL]
    apply Finset.inter_eq_left.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Sharpness.RandomCurrent.mem_compOf]
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact hklConn
  have hE0sub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1sub : edgeComponent ends L k ⊆ L := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hdFirst : Disjoint (K \ edgeComponent ends K zero) (edgeComponent ends L k) :=
    hKL.mono Finset.sdiff_subset hE1sub
  have hdSecond : Disjoint (L \ edgeComponent ends L k) (edgeComponent ends K zero) :=
    hKL.symm.mono Finset.sdiff_subset hE0sub
  constructor
  · rw [exchangeFirstRow, sources_union_of_disjoint hdFirst,
      sources_sdiff_of_subset hE0sub, hsrcK, hE0src, hE1src]
    simp
  · rw [exchangeSecondRow, sources_union_of_disjoint hdSecond,
      sources_sdiff_of_subset hE1sub, hsrcL, hE1src, hE0src, symmDiff_self]
    rfl



def middleSwap (m : Finset ι) (c : ↑m → Fin 4) : ↑m → Fin 4 :=
  fun i => Equiv.swap (1 : Fin 4) 2 (c i)

theorem middleSwap_involutive (m : Finset ι) (c : ↑m → Fin 4) :
    middleSwap m (middleSwap m c) = c := by
  funext i
  simp [middleSwap]

theorem colorClass_middleSwap (m : Finset ι) (c : ↑m → Fin 4) (a : Fin 4) :
    colorClass m (middleSwap m c) a = colorClass m c (Equiv.swap (1 : Fin 4) 2 a) := by
  ext i
  by_cases hi : i ∈ m
  · simp [colorClass, middleSwap, Equiv.swap_apply_def, hi]
    aesop
  · simp [colorClass, hi]


def middleSwapOn (m : Finset ι) (X : Finset ι) (c : ↑m → Fin 4) : ↑m → Fin 4 :=
  fun i => if (i : ι) ∈ X then Equiv.swap (1 : Fin 4) 2 (c i) else c i

theorem middleSwapOn_involutive (m X : Finset ι) (c : ↑m → Fin 4) :
    middleSwapOn m X (middleSwapOn m X c) = c := by
  funext i
  by_cases hi : (i : ι) ∈ X <;> simp [middleSwapOn, hi]

theorem colorClass_middleSwapOn_zero (m X : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (middleSwapOn m X c) 0 = colorClass m c 0 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (1 : Fin 4) 2 x = 0 ↔ x = 0 := by
    intro x
    rw [← show Equiv.swap (1 : Fin 4) 2 0 = 0 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X <;> simp [colorClass, middleSwapOn, hi, hiX, im, hswap]
  · simp [colorClass, hi]

theorem colorClass_middleSwapOn_three (m X : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (middleSwapOn m X c) 3 = colorClass m c 3 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (1 : Fin 4) 2 x = 3 ↔ x = 3 := by
    intro x
    rw [← show Equiv.swap (1 : Fin 4) 2 3 = 3 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X <;> simp [colorClass, middleSwapOn, hi, hiX, im, hswap]
  · simp [colorClass, hi]



theorem colorClass_middleSwapOn_one (m X : Finset ι) (c : ↑m → Fin 4)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2) :
    colorClass m (middleSwapOn m X c) 1 = colorClass m c 1 ∆ X := by
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X
    · have hmid := hX hiX
      simp only [Finset.mem_union] at hmid
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hmid
      simp only [Finset.mem_symmDiff]
      simp [colorClass, middleSwapOn, Equiv.swap_apply_def, hi, hiX, im] at hmid ⊢
      aesop
    · simp [colorClass, middleSwapOn, hi, hiX, im, Finset.mem_symmDiff]
  · have hiX : i ∉ X := by
      intro h
      rcases Finset.mem_union.mp (hX h) with h1 | h2
      · exact hi (colorClass_subset m c 1 h1)
      · exact hi (colorClass_subset m c 2 h2)
    simp [colorClass, hi, hiX, Finset.mem_symmDiff]

theorem colorClass_middleSwapOn_two (m X : Finset ι) (c : ↑m → Fin 4)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2) :
    colorClass m (middleSwapOn m X c) 2 = colorClass m c 2 ∆ X := by
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    by_cases hiX : i ∈ X
    · have hmid := hX hiX
      simp only [Finset.mem_union] at hmid
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hmid
      simp only [Finset.mem_symmDiff]
      simp [colorClass, middleSwapOn, Equiv.swap_apply_def, hi, hiX, im] at hmid ⊢
      aesop
    · simp [colorClass, middleSwapOn, hi, hiX, im, Finset.mem_symmDiff]
  · have hiX : i ∉ X := by
      intro h
      rcases Finset.mem_union.mp (hX h) with h1 | h2
      · exact hi (colorClass_subset m c 1 h1)
      · exact hi (colorClass_subset m c 2 h2)
    simp [colorClass, hi, hiX, Finset.mem_symmDiff]


def outerSwapOn (m : Finset ι) (Y : Finset ι) (c : ↑m → Fin 4) : ↑m → Fin 4 :=
  fun i => if (i : ι) ∈ Y then Equiv.swap (0 : Fin 4) 3 (c i) else c i

theorem outerSwapOn_involutive (m Y : Finset ι) (c : ↑m → Fin 4) :
    outerSwapOn m Y (outerSwapOn m Y c) = c := by
  funext i
  by_cases hi : (i : ι) ∈ Y <;> simp [outerSwapOn, hi]

theorem colorClass_outerSwapOn_one (m Y : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (outerSwapOn m Y c) 1 = colorClass m c 1 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (0 : Fin 4) 3 x = 1 ↔ x = 1 := by
    intro x
    rw [← show Equiv.swap (0 : Fin 4) 3 1 = 1 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y <;> simp [colorClass, outerSwapOn, hi, hiY, hswap]
  · simp [colorClass, hi]

theorem colorClass_outerSwapOn_two (m Y : Finset ι) (c : ↑m → Fin 4) :
    colorClass m (outerSwapOn m Y c) 2 = colorClass m c 2 := by
  have hswap : ∀ x : Fin 4, Equiv.swap (0 : Fin 4) 3 x = 2 ↔ x = 2 := by
    intro x
    rw [← show Equiv.swap (0 : Fin 4) 3 2 = 2 by decide]
    exact Equiv.apply_eq_iff_eq _
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y <;> simp [colorClass, outerSwapOn, hi, hiY, hswap]
  · simp [colorClass, hi]

theorem colorClass_outerSwapOn_zero (m Y : Finset ι) (c : ↑m → Fin 4)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    colorClass m (outerSwapOn m Y c) 0 = colorClass m c 0 ∆ Y := by
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y
    · have hout := hY hiY
      simp only [Finset.mem_union] at hout
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hout
      simp only [Finset.mem_symmDiff]
      simp [colorClass, outerSwapOn, Equiv.swap_apply_def, hi, hiY] at hout ⊢
      aesop
    · simp [colorClass, outerSwapOn, hi, hiY, Finset.mem_symmDiff]
  · have hiY : i ∉ Y := by
      intro h
      rcases Finset.mem_union.mp (hY h) with h0 | h3
      · exact hi (colorClass_subset m c 0 h0)
      · exact hi (colorClass_subset m c 3 h3)
    simp [colorClass, hi, hiY, Finset.mem_symmDiff]

theorem colorClass_outerSwapOn_three (m Y : Finset ι) (c : ↑m → Fin 4)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    colorClass m (outerSwapOn m Y c) 3 = colorClass m c 3 ∆ Y := by
  ext i
  by_cases hi : i ∈ m
  · by_cases hiY : i ∈ Y
    · have hout := hY hiY
      simp only [Finset.mem_union] at hout
      simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hout
      simp only [Finset.mem_symmDiff]
      simp [colorClass, outerSwapOn, Equiv.swap_apply_def, hi, hiY] at hout ⊢
      aesop
    · simp [colorClass, outerSwapOn, hi, hiY, Finset.mem_symmDiff]
  · have hiY : i ∉ Y := by
      intro h
      rcases Finset.mem_union.mp (hY h) with h0 | h3
      · exact hi (colorClass_subset m c 0 h0)
      · exact hi (colorClass_subset m c 3 h3)
    simp [colorClass, hi, hiY, Finset.mem_symmDiff]



def balancedSwap (m X Y : Finset ι) (c : ↑m → Fin 4) : ↑m → Fin 4 :=
  outerSwapOn m Y (middleSwapOn m X c)

theorem balancedSwap_involutive (m X Y : Finset ι) (c : ↑m → Fin 4) :
    balancedSwap m X Y (balancedSwap m X Y c) = c := by
  funext i
  have hci : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  rcases hci with hci | hci | hci | hci <;>
    by_cases hiX : (i : ι) ∈ X <;> by_cases hiY : (i : ι) ∈ Y <;>
      simp [balancedSwap, middleSwapOn, outerSwapOn, hiX, hiY,
        Equiv.swap_apply_def, hci]


def rowClass (m : Finset ι) (c : ↑m → Fin 4) (r : Fin 2) : Finset ι :=
  if r = 0 then colorClass m c 0 ∪ colorClass m c 1
  else colorClass m c 2 ∪ colorClass m c 3

theorem rowClass_zero (m : Finset ι) (c : ↑m → Fin 4) :
    rowClass m c 0 = colorClass m c 0 ∪ colorClass m c 1 := by
  simp [rowClass]

theorem rowClass_one (m : Finset ι) (c : ↑m → Fin 4) :
    rowClass m c 1 = colorClass m c 2 ∪ colorClass m c 3 := by
  simp [rowClass]



noncomputable def canonicalMiddleTransfer (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (k zero : W) : Finset ι :=
  (colorClass m c 1 ∩ edgeComponent ends (rowClass m c 0) zero) ∪
    (colorClass m c 2 ∩ edgeComponent ends (rowClass m c 1) k)


noncomputable def canonicalOuterTransfer (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (k zero : W) : Finset ι :=
  (colorClass m c 0 ∩ edgeComponent ends (rowClass m c 0) zero) ∪
    (colorClass m c 3 ∩ edgeComponent ends (rowClass m c 1) k)


theorem rowClass_balancedSwap_zero {m X Y : Finset ι} {c : ↑m → Fin 4}
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    rowClass m (balancedSwap m X Y c) 0 = rowClass m c 0 ∆ (X ∪ Y) := by
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold balancedSwap
  rw [rowClass_zero, colorClass_outerSwapOn_zero m Y _ hY',
    colorClass_outerSwapOn_one, colorClass_middleSwapOn_zero,
    colorClass_middleSwapOn_one m X c hX, rowClass_zero]
  ext i
  by_cases hiX : i ∈ X
  · rcases Finset.mem_union.mp (hX hiX) with hi1 | hi2
    · have hi0 : i ∉ colorClass m c 0 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (1 : Fin 4) ≠ 0 by decide))) hi1
      have hi2' : i ∉ colorClass m c 2 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (1 : Fin 4) ≠ 2 by decide))) hi1
      have hi3 : i ∉ colorClass m c 3 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (1 : Fin 4) ≠ 3 by decide))) hi1
      have hiY : i ∉ Y := by
        intro hiY
        rcases Finset.mem_union.mp (hY hiY) with h | h
        · exact hi0 h
        · exact hi3 h
      simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
    · have hi0 : i ∉ colorClass m c 0 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (2 : Fin 4) ≠ 0 by decide))) hi2
      have hi1 : i ∉ colorClass m c 1 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (2 : Fin 4) ≠ 1 by decide))) hi2
      have hi3 : i ∉ colorClass m c 3 :=
        (Finset.disjoint_left.mp
          (colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide))) hi2
      have hiY : i ∉ Y := by
        intro hiY
        rcases Finset.mem_union.mp (hY hiY) with h | h
        · exact hi0 h
        · exact hi3 h
      simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
  · by_cases hiY : i ∈ Y
    · rcases Finset.mem_union.mp (hY hiY) with hi0 | hi3
      · have hi1 : i ∉ colorClass m c 1 :=
          (Finset.disjoint_left.mp
            (colorClass_disjoint m c (show (0 : Fin 4) ≠ 1 by decide))) hi0
        simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
      · have hi0 : i ∉ colorClass m c 0 :=
          (Finset.disjoint_left.mp
            (colorClass_disjoint m c (show (3 : Fin 4) ≠ 0 by decide))) hi3
        have hi1 : i ∉ colorClass m c 1 :=
          (Finset.disjoint_left.mp
            (colorClass_disjoint m c (show (3 : Fin 4) ≠ 1 by decide))) hi3
        simp [Finset.mem_symmDiff, hiX, hiY, hi0, hi1]
    · simp [Finset.mem_symmDiff, hiX, hiY]


theorem rowClass_one_eq_sdiff (m : Finset ι) (c : ↑m → Fin 4) :
    rowClass m c 1 = m \ rowClass m c 0 := by
  ext i
  by_cases hi : i ∈ m
  · let im : ↑m := ⟨i, hi⟩
    have him : (im : ι) = i := rfl
    have hc : c im = 0 ∨ c im = 1 ∨ c im = 2 ∨ c im = 3 := by
      omega
    simp only [rowClass_zero, rowClass_one, Finset.mem_union, Finset.mem_sdiff, hi, true_and]
    simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach]
    simp only [← him]
    aesop
  · have hca : ∀ a : Fin 4, i ∉ colorClass m c a := by
      intro a hmem
      exact hi (colorClass_subset m c a hmem)
    simp [rowClass_zero, rowClass_one, hi, hca]



def coloringOfRowData (m K P Q : Finset ι) : ↑m → Fin 4 := fun i =>
  if (i : ι) ∈ P then 0 else if (i : ι) ∈ K then 1 else if (i : ι) ∈ Q then 2 else 3

set_option maxHeartbeats 800000 in
theorem colorClasses_coloringOfRowData {m K P Q : Finset ι} (hKm : K ⊆ m)
    (hPK : P ⊆ K) (hQL : Q ⊆ m \ K) :
    colorClass m (coloringOfRowData m K P Q) 0 = P ∧
      colorClass m (coloringOfRowData m K P Q) 1 = K \ P ∧
      colorClass m (coloringOfRowData m K P Q) 2 = Q ∧
      colorClass m (coloringOfRowData m K P Q) 3 = (m \ K) \ Q := by
  classical
  have hPm : P ⊆ m := hPK.trans hKm
  have hQm : Q ⊆ m := hQL.trans Finset.sdiff_subset
  have hQK : Disjoint Q K := by
    rw [Finset.disjoint_left]
    intro i hiQ hiK
    exact (Finset.mem_sdiff.mp (hQL hiQ)).2 hiK
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i
  all_goals
    have hKm_i := @hKm i
    have hPK_i := @hPK i
    have hQL_i := @hQL i
    have hPm_i := @hPm i
    have hQm_i := @hQm i
    by_cases him : i ∈ m <;> by_cases hiK : i ∈ K <;>
      by_cases hiP : i ∈ P <;> by_cases hiQ : i ∈ Q <;>
        simp [colorClass, coloringOfRowData, him, hiK, hiP, hiQ] at hKm_i hPK_i hQL_i hPm_i hQm_i hQK ⊢

theorem rowClasses_coloringOfRowData {m K P Q : Finset ι} (hKm : K ⊆ m)
    (hPK : P ⊆ K) (hQL : Q ⊆ m \ K) :
    rowClass m (coloringOfRowData m K P Q) 0 = K ∧
      rowClass m (coloringOfRowData m K P Q) 1 = m \ K := by
  have hc := colorClasses_coloringOfRowData hKm hPK hQL
  constructor
  · rw [rowClass_zero, hc.1, hc.2.1, Finset.union_sdiff_of_subset hPK]
  · rw [rowClass_one, hc.2.2.1, hc.2.2.2]
    exact Finset.union_sdiff_of_subset hQL

theorem rowClass_balancedSwap_one {m X Y : Finset ι} {c : ↑m → Fin 4}
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    rowClass m (balancedSwap m X Y c) 1 = rowClass m c 1 ∆ (X ∪ Y) := by
  rw [rowClass_one_eq_sdiff, rowClass_one_eq_sdiff,
    rowClass_balancedSwap_zero hX hY]
  have hXY : X ∪ Y ⊆ m := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp (hX hi) with hi | hi
      · exact colorClass_subset m c 1 hi
      · exact colorClass_subset m c 2 hi
    · rcases Finset.mem_union.mp (hY hi) with hi | hi
      · exact colorClass_subset m c 0 hi
      · exact colorClass_subset m c 3 hi
  ext i
  have hiXYm : i ∈ X ∪ Y → i ∈ m := fun hi => hXY hi
  by_cases him : i ∈ m <;>
    by_cases hir : i ∈ rowClass m c 0 <;>
      by_cases hiXY : i ∈ X ∪ Y <;>
        simp [Finset.mem_symmDiff, him, hir, hiXY] at hiXYm ⊢


def RowsDisconnect (ends : ι → Sym2 W) (m : Finset ι) (c : ↑m → Fin 4)
    (u v : W) : Prop :=
  ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 0) u v ∧
    ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 1) u v



noncomputable def rowComponent (ends : ι → Sym2 W) (m : Finset ι) (c : ↑m → Fin 4)
    (r : Fin 2) (u : W) : Finset W :=
  Sharpness.RandomCurrent.compOf ends (rowClass m c r) u

theorem mem_rowComponent_iff (ends : ι → Sym2 W) (m : Finset ι) (c : ↑m → Fin 4)
    (r : Fin 2) (u x : W) :
    x ∈ rowComponent ends m c r u ↔
      Sharpness.RandomCurrent.connK ends (rowClass m c r) u x := by
  simp [rowComponent, Sharpness.RandomCurrent.mem_compOf]



theorem rowsDisconnect_iff_component (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (u v : W) :
    RowsDisconnect ends m c u v ↔
      v ∉ rowComponent ends m c 0 u ∧ v ∉ rowComponent ends m c 1 u := by
  simp only [RowsDisconnect, mem_rowComponent_iff]



theorem rowComponent_noCrossing (ends : ι → Sym2 W) (m : Finset ι)
    (c : ↑m → Fin 4) (r : Fin 2) (u : W) :
    Sharpness.RandomCurrent.NoCrossingK ends (rowClass m c r)
      (Sharpness.RandomCurrent.notConnCompK ends (rowClass m c r) u) := by
  apply Sharpness.RandomCurrent.noCrossingK_of_event ends (rowClass m c r)
      (Sharpness.RandomCurrent.notConnCompK ends (rowClass m c r) u) u
  · rw [Sharpness.RandomCurrent.mem_notConnCompK]
    exact not_not.mpr Relation.ReflTransGen.refl
  · rfl


def LeftPattern (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    (u v : W) (c : ↑m → Fin 4) : Prop :=
  Sharpness.RandomCurrent.sources ends (colorClass m c 0) = A ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 1) = ∅ ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 2) = B ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 3) = ∅ ∧
    RowsDisconnect ends m c u v


def RightPattern (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    (u v : W) (c : ↑m → Fin 4) : Prop :=
  Sharpness.RandomCurrent.sources ends (colorClass m c 0) = A ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 1) = B ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 2) = ∅ ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 3) = ∅ ∧
    RowsDisconnect ends m c u v




theorem rightPattern_of_middleTransfer {ends : ι → Sym2 W} {m X : Finset ι}
    {A B : Finset W} {u v : W} {c : ↑m → Fin 4}
    (hleft : LeftPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hsrc : Sharpness.RandomCurrent.sources ends X = B)
    (hdisc : RowsDisconnect ends m (middleSwapOn m X c) u v) :
    RightPattern ends m A B u v (middleSwapOn m X c) := by
  rcases hleft with ⟨h0, h1, h2, h3, -⟩
  refine ⟨?_, ?_, ?_, ?_, hdisc⟩
  · rw [colorClass_middleSwapOn_zero]
    exact h0
  · rw [colorClass_middleSwapOn_one m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h1, hsrc]
    simp
  · rw [colorClass_middleSwapOn_two m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h2, hsrc]
    simpa using (symmDiff_self B)
  · rw [colorClass_middleSwapOn_three]
    exact h3




theorem rightPattern_of_balancedTransfer {ends : ι → Sym2 W} {m X Y : Finset ι}
    {A B : Finset W} {u v : W} {c : ↑m → Fin 4}
    (hleft : LeftPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
    (hsrcX : Sharpness.RandomCurrent.sources ends X = B)
    (hsrcY : Sharpness.RandomCurrent.sources ends Y = ∅)
    (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
    RightPattern ends m A B u v (balancedSwap m X Y c) := by
  rcases hleft with ⟨h0, h1, h2, h3, -⟩
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold balancedSwap
  refine ⟨?_, ?_, ?_, ?_, hdisc⟩
  · rw [colorClass_outerSwapOn_zero m Y _ hY',
      Sharpness.RandomCurrent.sources_symmDiff, colorClass_middleSwapOn_zero, h0, hsrcY]
    simp
  · rw [colorClass_outerSwapOn_one, colorClass_middleSwapOn_one m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h1, hsrcX]
    simp
  · rw [colorClass_outerSwapOn_two, colorClass_middleSwapOn_two m X c hX,
      Sharpness.RandomCurrent.sources_symmDiff, h2, hsrcX]
    simpa using (symmDiff_self B)
  · rw [colorClass_outerSwapOn_three m Y _ hY',
      Sharpness.RandomCurrent.sources_symmDiff, colorClass_middleSwapOn_three, h3, hsrcY]
    simp




theorem leftPattern_sharedSource_connections {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    Sharpness.RandomCurrent.connK ends (colorClass m c 0) j k ∧
      Sharpness.RandomCurrent.connK ends (colorClass m c 2) k l := by
  constructor
  · apply Walls.gc6_pairingPath_abstract ends (colorClass m c 0) (colorClass m c 0)
    · intro i hi
      exact hloop i (colorClass_subset m c 0 hi)
    · exact Finset.Subset.rfl
    · exact h.1
    · exact hjk
  · apply Walls.gc6_pairingPath_abstract ends (colorClass m c 2) (colorClass m c 2)
    · intro i hi
      exact hloop i (colorClass_subset m c 2 hi)
    · exact Finset.Subset.rfl
    · exact h.2.2.1
    · exact hkl



theorem leftPattern_sharedSource_avoids_zero {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 0) j zero ∧
      ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 1) l zero := by
  have hp := leftPattern_sharedSource_connections hloop hjk hkl h
  rcases h with ⟨_, _, _, _, hdisc⟩
  have hjkRow : Sharpness.RandomCurrent.connK ends (rowClass m c 0) j k := by
    rw [rowClass_zero]
    exact connK_mono (Finset.subset_union_left) hp.1
  have hklRow : Sharpness.RandomCurrent.connK ends (rowClass m c 1) k l := by
    rw [rowClass_one]
    exact connK_mono (Finset.subset_union_left) hp.2
  constructor
  · intro hjzero
    exact hdisc.1 ((Sharpness.RandomCurrent.connK_symm ends _ hjkRow).trans hjzero)
  · intro hlzero
    exact hdisc.2 (hklRow.trans hlzero)



theorem canonicalTransfers_valid {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalMiddleTransfer ends m c k zero ⊆
        colorClass m c 1 ∪ colorClass m c 2 ∧
      canonicalOuterTransfer ends m c k zero ⊆
        colorClass m c 0 ∪ colorClass m c 3 ∧
      Sharpness.RandomCurrent.sources ends (canonicalMiddleTransfer ends m c k zero) =
        {k, l} ∧
      Sharpness.RandomCurrent.sources ends (canonicalOuterTransfer ends m c k zero) = ∅ := by
  classical
  have hconn := leftPattern_sharedSource_connections hloop hjk hkl h
  have hav := leftPattern_sharedSource_avoids_zero hloop hjk hkl h
  have hC0 : colorClass m c 0 ⊆ rowClass m c 0 := by
    rw [rowClass_zero]
    exact Finset.subset_union_left
  have hC1 : colorClass m c 1 ⊆ rowClass m c 0 := by
    rw [rowClass_zero]
    exact Finset.subset_union_right
  have hC2 : colorClass m c 2 ⊆ rowClass m c 1 := by
    rw [rowClass_one]
    exact Finset.subset_union_left
  have hC3 : colorClass m c 3 ⊆ rowClass m c 1 := by
    rw [rowClass_one]
    exact Finset.subset_union_right
  have hsrc1 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 1 ∩ edgeComponent ends (rowClass m c 0) zero) = ∅ := by
    rw [sources_inter_edgeComponent hC1, h.2.1]
    simp
  have hsrc2 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 2 ∩ edgeComponent ends (rowClass m c 1) k) = {k, l} := by
    rw [sources_inter_edgeComponent hC2, h.2.2.1]
    apply Finset.inter_eq_left.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Sharpness.RandomCurrent.mem_compOf]
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · rw [rowClass_one]
      exact connK_mono Finset.subset_union_left hconn.2
  have hsrc0 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 0 ∩ edgeComponent ends (rowClass m c 0) zero) = ∅ := by
    rw [sources_inter_edgeComponent hC0, h.1]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [Sharpness.RandomCurrent.mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hav.1 (Sharpness.RandomCurrent.connK_symm ends _ hcomp)
    · exact h.2.2.2.2.1 (Sharpness.RandomCurrent.connK_symm ends _ hcomp)
  have hsrc3 : Sharpness.RandomCurrent.sources ends
      (colorClass m c 3 ∩ edgeComponent ends (rowClass m c 1) k) = ∅ := by
    rw [sources_inter_edgeComponent hC3, h.2.2.2.1]
    simp
  have hd12 : Disjoint
      (colorClass m c 1 ∩ edgeComponent ends (rowClass m c 0) zero)
      (colorClass m c 2 ∩ edgeComponent ends (rowClass m c 1) k) :=
    (colorClass_disjoint m c (show (1 : Fin 4) ≠ 2 by decide)).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hd03 : Disjoint
      (colorClass m c 0 ∩ edgeComponent ends (rowClass m c 0) zero)
      (colorClass m c 3 ∩ edgeComponent ends (rowClass m c 1) k) :=
    (colorClass_disjoint m c (show (0 : Fin 4) ≠ 3 by decide)).mono
      Finset.inter_subset_left Finset.inter_subset_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).1
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).1
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).1
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).1
  · rw [canonicalMiddleTransfer, sources_union_of_disjoint hd12, hsrc1, hsrc2]
    simp
  · rw [canonicalOuterTransfer, sources_union_of_disjoint hd03, hsrc0, hsrc3]
    simp

theorem canonicalTransfers_union {ends : ι → Sym2 W} {m : Finset ι}
    {k zero : W} {c : ↑m → Fin 4} :
    canonicalMiddleTransfer ends m c k zero ∪ canonicalOuterTransfer ends m c k zero =
      edgeComponent ends (rowClass m c 0) zero ∪
        edgeComponent ends (rowClass m c 1) k := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi <;>
      rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).2
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp hi).2
    · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2
  · intro hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have hirow : i ∈ rowClass m c 0 := by
        rw [edgeComponent, Finset.mem_filter] at hi
        exact hi.1
      rw [rowClass_zero, Finset.mem_union] at hirow
      rcases hirow with hi0 | hi1
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi0, hi⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi1, hi⟩))
    · have hirow : i ∈ rowClass m c 1 := by
        rw [edgeComponent, Finset.mem_filter] at hi
        exact hi.1
      rw [rowClass_one, Finset.mem_union] at hirow
      rcases hirow with hi2 | hi3
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi2, hi⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi3, hi⟩))

theorem symmDiff_componentExchange_first {K L A B : Finset ι}
    (hA : A ⊆ K) (hB : B ⊆ L) (hKL : Disjoint K L) :
    K ∆ (A ∪ B) = (K \ A) ∪ B := by
  ext i
  have hAi := @hA i
  have hBi := @hB i
  rw [Finset.disjoint_left] at hKL
  simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  aesop

theorem symmDiff_componentExchange_second {K L A B : Finset ι}
    (hA : A ⊆ K) (hB : B ⊆ L) (hKL : Disjoint K L) :
    L ∆ (A ∪ B) = (L \ B) ∪ A := by
  rw [Finset.union_comm]
  exact symmDiff_componentExchange_first hB hA hKL.symm


theorem canonicalBalancedSwap_rows {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) 0 =
        exchangeFirstRow ends (rowClass m c 0) (rowClass m c 1) k zero ∧
      rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) 1 =
        exchangeSecondRow ends (rowClass m c 0) (rowClass m c 1) k zero := by
  classical
  have hv := canonicalTransfers_valid hloop hjk hkl h
  have hE0 : edgeComponent ends (rowClass m c 0) zero ⊆ rowClass m c 0 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1 : edgeComponent ends (rowClass m c 1) k ⊆ rowClass m c 1 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hrows : Disjoint (rowClass m c 0) (rowClass m c 1) := by
    rw [Finset.disjoint_left]
    intro i hi0 hi1
    rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
    exact hi1.2 hi0
  constructor
  · rw [rowClass_balancedSwap_zero hv.1 hv.2.1, canonicalTransfers_union,
      exchangeFirstRow]
    exact symmDiff_componentExchange_first hE0 hE1 hrows
  · rw [rowClass_balancedSwap_one hv.1 hv.2.1, canonicalTransfers_union,
      exchangeSecondRow]
    exact symmDiff_componentExchange_second hE0 hE1 hrows

theorem canonicalBalancedSwap_disconnects {ends : ι → Sym2 W} {m : Finset ι}
    {j k l zero : W} {c : ↑m → Fin 4} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    RowsDisconnect ends m
      (balancedSwap m (canonicalMiddleTransfer ends m c k zero)
        (canonicalOuterTransfer ends m c k zero) c) k zero := by
  rw [RowsDisconnect]
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl h
  rw [hrows.1, hrows.2]
  exact componentExchange_disconnects hk0 h.2.2.2.2.1 h.2.2.2.2.2



theorem leftPattern_componentExchange_disconnects {ends : ι → Sym2 W} {m : Finset ι}
    {A B : Finset W} {k zero : W} {c : ↑m → Fin 4} (hk0 : k ≠ zero)
    (h : LeftPattern ends m A B k zero c) :
    ¬ Sharpness.RandomCurrent.connK ends
        (exchangeFirstRow ends (rowClass m c 0) (rowClass m c 1) k zero) k zero ∧
      ¬ Sharpness.RandomCurrent.connK ends
        (exchangeSecondRow ends (rowClass m c 0) (rowClass m c 1) k zero) k zero :=
  componentExchange_disconnects hk0 h.2.2.2.2.1 h.2.2.2.2.2


theorem leftPattern_rowBoundaries {ends : ι → Sym2 W} {m : Finset ι} {A B : Finset W}
    {u v : W} {c : ↑m → Fin 4} (h : LeftPattern ends m A B u v c) :
    Sharpness.RandomCurrent.sources ends (rowClass m c 0) = A ∧
      Sharpness.RandomCurrent.sources ends (rowClass m c 1) = B := by
  rcases h with ⟨h0, h1, h2, h3, -⟩
  constructor
  · rw [rowClass_zero]
    have hd := colorClass_disjoint m c (show (0 : Fin 4) ≠ 1 by decide)
    have hu : colorClass m c 0 ∪ colorClass m c 1 = colorClass m c 0 ∆ colorClass m c 1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h0, h1]
    simp
  · rw [rowClass_one]
    have hd := colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide)
    have hu : colorClass m c 2 ∪ colorClass m c 3 = colorClass m c 2 ∆ colorClass m c 3 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h2, h3]
    simp


theorem rightPattern_rowBoundaries {ends : ι → Sym2 W} {m : Finset ι} {A B : Finset W}
    {u v : W} {c : ↑m → Fin 4} (h : RightPattern ends m A B u v c) :
    Sharpness.RandomCurrent.sources ends (rowClass m c 0) = A ∆ B ∧
      Sharpness.RandomCurrent.sources ends (rowClass m c 1) = ∅ := by
  rcases h with ⟨h0, h1, h2, h3, -⟩
  constructor
  · rw [rowClass_zero]
    have hd := colorClass_disjoint m c (show (0 : Fin 4) ≠ 1 by decide)
    have hu : colorClass m c 0 ∪ colorClass m c 1 = colorClass m c 0 ∆ colorClass m c 1 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h0, h1]
  · rw [rowClass_one]
    have hd := colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide)
    have hu : colorClass m c 2 ∪ colorClass m c 3 = colorClass m c 2 ∆ colorClass m c 3 := by
      ext i
      simp only [Finset.mem_union, Finset.mem_symmDiff]
      rw [Finset.disjoint_left] at hd
      aesop
    rw [hu, Sharpness.RandomCurrent.sources_symmDiff, h2, h3, symmDiff_self]
    rfl

def leftFiber (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W) (u v : W) :=
  {c : ↑m → Fin 4 // LeftPattern ends m A B u v c}

def rightFiber (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W) (u v : W) :=
  {c : ↑m → Fin 4 // RightPattern ends m A B u v c}

noncomputable instance instFintypeLeftFiber (ends : ι → Sym2 W) (m : Finset ι)
    (A B : Finset W) (u v : W) : Fintype (leftFiber ends m A B u v) := by
  classical
  exact Fintype.subtype (Finset.univ.filter (LeftPattern ends m A B u v))
    (fun _ => by simp)

noncomputable instance instFintypeRightFiber (ends : ι → Sym2 W) (m : Finset ι)
    (A B : Finset W) (u v : W) : Fintype (rightFiber ends m A B u v) := by
  classical
  exact Fintype.subtype (Finset.univ.filter (RightPattern ends m A B u v))
    (fun _ => by simp)




def FiberMinorCandidate (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    (u v : W) : Prop :=
  Fintype.card (leftFiber ends m A B u v) ≤ Fintype.card (rightFiber ends m A B u v)



def GrahamFiberMinor (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) : Prop :=
  Fintype.card (leftFiber ends m {j, k} {k, l} k zero)
    ≤ Fintype.card (rightFiber ends m {j, k} {k, l} k zero)


noncomputable def rowSupportWeight (ends : ι → Sym2 W) (m K : Finset ι) : ℕ :=
  Fintype.card (boundarySector ends K ∅) *
    Fintype.card (boundarySector ends (m \ K) ∅)

def LeftRowSupport (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W)
    (K : Finset ι) : Prop :=
  Sharpness.RandomCurrent.sources ends K = {j, k} ∧
    Sharpness.RandomCurrent.sources ends (m \ K) = {k, l} ∧
    ¬ Sharpness.RandomCurrent.connK ends K k zero ∧
    ¬ Sharpness.RandomCurrent.connK ends (m \ K) k zero

def RightRowSupport (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W)
    (K : Finset ι) : Prop :=
  Sharpness.RandomCurrent.sources ends K = {j, k} ∆ {k, l} ∧
    (∃ P : Finset ι, P ⊆ K ∧ Sharpness.RandomCurrent.sources ends P = {j, k}) ∧
    Sharpness.RandomCurrent.sources ends (m \ K) = ∅ ∧
    ¬ Sharpness.RandomCurrent.connK ends K k zero ∧
    ¬ Sharpness.RandomCurrent.connK ends (m \ K) k zero

noncomputable def leftRowSupports (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Finset (Finset ι) := by
  classical
  exact m.powerset.filter (LeftRowSupport ends m j k l zero)

noncomputable def rightRowSupports (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Finset (Finset ι) := by
  classical
  exact m.powerset.filter (RightRowSupport ends m j k l zero)



noncomputable def GrahamWeightedRowMinor (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Prop := by
  classical
  exact
    (∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K)
      ≤ ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K

def leftRowSupportIndex (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) :=
  {K : Finset ι // K ⊆ m ∧ LeftRowSupport ends m j k l zero K}

def leftRowData (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) :=
  Σ K : leftRowSupportIndex ends m j k l zero,
    boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) {k, l}

noncomputable instance instFintypeLeftRowSupportIndex (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Fintype (leftRowSupportIndex ends m j k l zero) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun K => K ⊆ m ∧ LeftRowSupport ends m j k l zero K))
    (fun K => by simp [leftRowSupportIndex])

noncomputable instance instFintypeLeftRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Fintype (leftRowData ends m j k l zero) := by
  classical
  unfold leftRowData
  infer_instance

noncomputable def leftFiberToRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : leftFiber ends m {j, k} {k, l} k zero →
      leftRowData ends m j k l zero := fun c => by
  classical
  let K := rowClass m c.1 0
  have hKm : K ⊆ m := by
    intro i hi
    dsimp only [K] at hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1 0 hi
    · exact colorClass_subset m c.1 1 hi
  have hrows := leftPattern_rowBoundaries c.2
  have hsupport : LeftRowSupport ends m j k l zero K := by
    unfold LeftRowSupport
    have hrow1 : m \ K = rowClass m c.1 1 := by
      dsimp only [K]
      rw [rowClass_one_eq_sdiff]
    exact ⟨hrows.1, hrow1 ▸ hrows.2, c.2.2.2.2.2.1,
      hrow1 ▸ c.2.2.2.2.2.2⟩
  have hC0 : colorClass m c.1 0 ⊆ K := by
    dsimp only [K]
    rw [rowClass_zero]
    exact Finset.subset_union_left
  have hC2 : colorClass m c.1 2 ⊆ m \ K := by
    dsimp only [K]
    rw [← rowClass_one_eq_sdiff, rowClass_one]
    exact Finset.subset_union_left
  exact ⟨⟨K, hKm, hsupport⟩,
    ⟨⟨colorClass m c.1 0, hC0, c.2.1⟩,
      ⟨colorClass m c.1 2, hC2, c.2.2.2.1⟩⟩⟩

noncomputable def rowDataToLeftFiber (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : leftRowData ends m j k l zero →
      leftFiber ends m {j, k} {k, l} k zero := fun d => by
  classical
  let K := d.1.1
  let P := d.2.1.1
  let Q := d.2.2.1
  let c := coloringOfRowData m K P Q
  have hc := colorClasses_coloringOfRowData d.1.2.1 d.2.1.2.1 d.2.2.2.1
  have hr := rowClasses_coloringOfRowData d.1.2.1 d.2.1.2.1 d.2.2.2.1
  refine ⟨c, ?_⟩
  unfold LeftPattern
  change Sharpness.RandomCurrent.sources ends (colorClass m c 0) = {j, k} ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 1) = ∅ ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 2) = {k, l} ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 3) = ∅ ∧
    RowsDisconnect ends m c k zero
  have hs := d.1.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.1]
    exact d.2.1.2.2
  · rw [hc.2.1, sources_sdiff_of_subset d.2.1.2.1, hs.1, d.2.1.2.2,
      symmDiff_self]
    rfl
  · rw [hc.2.2.1]
    exact d.2.2.2.2
  · rw [hc.2.2.2, sources_sdiff_of_subset d.2.2.2.1, hs.2.1, d.2.2.2.2,
      symmDiff_self]
    rfl
  · rw [RowsDisconnect, hr.1, hr.2]
    exact ⟨hs.2.2.1, hs.2.2.2⟩

theorem rowDataToLeftFiber_leftInverse (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (c : leftFiber ends m {j, k} {k, l} k zero) :
    rowDataToLeftFiber ends m j k l zero (leftFiberToRowData ends m j k l zero c) = c := by
  apply Subtype.ext
  funext i
  have hci : c.1 i = 0 ∨ c.1 i = 1 ∨ c.1 i = 2 ∨ c.1 i = 3 := by omega
  rcases hci with hci | hci | hci | hci <;>
    simp [rowDataToLeftFiber, leftFiberToRowData, coloringOfRowData, rowClass, colorClass, hci]

theorem rowDataToLeftFiber_injective (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Function.Injective (rowDataToLeftFiber ends m j k l zero) := by
  rintro ⟨dK, dP, dQ⟩ ⟨eK, eP, eQ⟩ hde
  have hc := congrArg Subtype.val hde
  change coloringOfRowData m dK.1 dP.1 dQ.1 =
    coloringOfRowData m eK.1 eP.1 eQ.1 at hc
  have hdcl := colorClasses_coloringOfRowData dK.2.1 dP.2.1 dQ.2.1
  have hecl := colorClasses_coloringOfRowData eK.2.1 eP.2.1 eQ.2.1
  have hdr := rowClasses_coloringOfRowData dK.2.1 dP.2.1 dQ.2.1
  have her := rowClasses_coloringOfRowData eK.2.1 eP.2.1 eQ.2.1
  have hK : dK.1 = eK.1 := by
    rw [← hdr.1, ← her.1, hc]
  have hK' : dK = eK := Subtype.ext hK
  subst eK
  have hP : dP.1 = eP.1 := by
    rw [← hdcl.1, ← hecl.1, hc]
  have hQ : dQ.1 = eQ.1 := by
    rw [← hdcl.2.2.1, ← hecl.2.2.1, hc]
  congr
  · exact Subtype.ext hP
  · exact Subtype.ext hQ

noncomputable def leftFiberEquivRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    leftFiber ends m {j, k} {k, l} k zero ≃ leftRowData ends m j k l zero :=
  Equiv.ofBijective (leftFiberToRowData ends m j k l zero) ⟨
    fun c d h => by
      rw [← rowDataToLeftFiber_leftInverse ends m j k l zero c,
        ← rowDataToLeftFiber_leftInverse ends m j k l zero d, h],
    fun d => by
      let c := rowDataToLeftFiber ends m j k l zero d
      exact ⟨c, rowDataToLeftFiber_injective ends m j k l zero
        (rowDataToLeftFiber_leftInverse ends m j k l zero c)⟩⟩

theorem leftRowData_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (leftRowData ends m j k l zero) =
      ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  classical
  calc
    Fintype.card (leftRowData ends m j k l zero) =
        ∑ K : leftRowSupportIndex ends m j k l zero, rowSupportWeight ends m K.1 := by
      change Fintype.card (Σ K : leftRowSupportIndex ends m j k l zero,
        boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) {k, l}) = _
      calc
        Fintype.card (Σ K : leftRowSupportIndex ends m j k l zero,
            boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) {k, l}) =
            ∑ K : leftRowSupportIndex ends m j k l zero,
              Fintype.card (boundarySector ends K.1 {j, k} ×
                boundarySector ends (m \ K.1) {k, l}) := Fintype.card_sigma
        _ = _ := by
          apply Finset.sum_congr rfl
          intro K _
          rw [Fintype.card_prod]
          have hKA : boundarySector ends K.1 {j, k} :=
            ⟨K.1, Finset.Subset.rfl, K.2.2.1⟩
          have hLB : boundarySector ends (m \ K.1) {k, l} :=
            ⟨m \ K.1, Finset.Subset.rfl, K.2.2.2.1⟩
          rw [boundarySector_card_eq_cycle ends K.1 {j, k} hKA,
            boundarySector_card_eq_cycle ends (m \ K.1) {k, l} hLB]
          rfl
    _ = ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
      symm
      exact Finset.sum_subtype _ (fun K => by simp [leftRowSupports, leftRowSupportIndex]) _

theorem leftFiber_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (leftFiber ends m {j, k} {k, l} k zero) =
      ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  rw [Fintype.card_congr (leftFiberEquivRowData ends m j k l zero),
    leftRowData_card_eq_weightedSum]

def rightRowSupportIndex (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) :=
  {K : Finset ι // K ⊆ m ∧ RightRowSupport ends m j k l zero K}

def rightRowData (ends : ι → Sym2 W) (m : Finset ι) (j k l zero : W) :=
  Σ K : rightRowSupportIndex ends m j k l zero,
    boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) ∅

noncomputable instance instFintypeRightRowSupportIndex (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Fintype (rightRowSupportIndex ends m j k l zero) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun K => K ⊆ m ∧ RightRowSupport ends m j k l zero K))
    (fun K => by simp)

noncomputable instance instFintypeRightRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Fintype (rightRowData ends m j k l zero) := by
  classical
  unfold rightRowData
  infer_instance

noncomputable def rightFiberToRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : rightFiber ends m {j, k} {k, l} k zero →
      rightRowData ends m j k l zero := fun c => by
  classical
  let K := rowClass m c.1 0
  have hKm : K ⊆ m := by
    intro i hi
    dsimp only [K] at hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1 0 hi
    · exact colorClass_subset m c.1 1 hi
  have hC0 : colorClass m c.1 0 ⊆ K := by
    dsimp only [K]
    rw [rowClass_zero]
    exact Finset.subset_union_left
  have hrows := rightPattern_rowBoundaries c.2
  have hsupport : RightRowSupport ends m j k l zero K := by
    unfold RightRowSupport
    have hrow1 : m \ K = rowClass m c.1 1 := by
      dsimp only [K]
      rw [rowClass_one_eq_sdiff]
    exact ⟨hrows.1, ⟨colorClass m c.1 0, hC0, c.2.1⟩,
      hrow1 ▸ hrows.2, c.2.2.2.2.2.1, hrow1 ▸ c.2.2.2.2.2.2⟩
  have hC2 : colorClass m c.1 2 ⊆ m \ K := by
    dsimp only [K]
    rw [← rowClass_one_eq_sdiff, rowClass_one]
    exact Finset.subset_union_left
  exact ⟨⟨K, hKm, hsupport⟩,
    ⟨⟨colorClass m c.1 0, hC0, c.2.1⟩,
      ⟨colorClass m c.1 2, hC2, c.2.2.2.1⟩⟩⟩

noncomputable def rowDataToRightFiber (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : rightRowData ends m j k l zero →
      rightFiber ends m {j, k} {k, l} k zero := fun d => by
  classical
  let K := d.1.1
  let P := d.2.1.1
  let Q := d.2.2.1
  let c := coloringOfRowData m K P Q
  have hc := colorClasses_coloringOfRowData d.1.2.1 d.2.1.2.1 d.2.2.2.1
  have hr := rowClasses_coloringOfRowData d.1.2.1 d.2.1.2.1 d.2.2.2.1
  refine ⟨c, ?_⟩
  unfold RightPattern
  have hs := d.1.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.1]
    exact d.2.1.2.2
  · rw [hc.2.1, sources_sdiff_of_subset d.2.1.2.1, hs.1, d.2.1.2.2]
    simp [symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
  · rw [hc.2.2.1]
    exact d.2.2.2.2
  · rw [hc.2.2.2, sources_sdiff_of_subset d.2.2.2.1, hs.2.2.1, d.2.2.2.2]
    rfl
  · rw [RowsDisconnect, hr.1, hr.2]
    exact ⟨hs.2.2.2.1, hs.2.2.2.2⟩

theorem rowDataToRightFiber_leftInverse (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (c : rightFiber ends m {j, k} {k, l} k zero) :
    rowDataToRightFiber ends m j k l zero (rightFiberToRowData ends m j k l zero c) = c := by
  apply Subtype.ext
  funext i
  have hci : c.1 i = 0 ∨ c.1 i = 1 ∨ c.1 i = 2 ∨ c.1 i = 3 := by omega
  rcases hci with hci | hci | hci | hci <;>
    simp [rowDataToRightFiber, rightFiberToRowData, coloringOfRowData, rowClass, colorClass, hci]

theorem rowDataToRightFiber_injective (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : Function.Injective (rowDataToRightFiber ends m j k l zero) := by
  rintro ⟨dK, dP, dQ⟩ ⟨eK, eP, eQ⟩ hde
  have hc := congrArg Subtype.val hde
  change coloringOfRowData m dK.1 dP.1 dQ.1 =
    coloringOfRowData m eK.1 eP.1 eQ.1 at hc
  have hdcl := colorClasses_coloringOfRowData dK.2.1 dP.2.1 dQ.2.1
  have hecl := colorClasses_coloringOfRowData eK.2.1 eP.2.1 eQ.2.1
  have hdr := rowClasses_coloringOfRowData dK.2.1 dP.2.1 dQ.2.1
  have her := rowClasses_coloringOfRowData eK.2.1 eP.2.1 eQ.2.1
  have hK : dK.1 = eK.1 := by rw [← hdr.1, ← her.1, hc]
  have hK' : dK = eK := Subtype.ext hK
  subst eK
  have hP : dP.1 = eP.1 := by rw [← hdcl.1, ← hecl.1, hc]
  have hQ : dQ.1 = eQ.1 := by rw [← hdcl.2.2.1, ← hecl.2.2.1, hc]
  congr
  · exact Subtype.ext hP
  · exact Subtype.ext hQ

noncomputable def rightFiberEquivRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    rightFiber ends m {j, k} {k, l} k zero ≃ rightRowData ends m j k l zero :=
  Equiv.ofBijective (rightFiberToRowData ends m j k l zero) ⟨
    fun c d h => by
      rw [← rowDataToRightFiber_leftInverse ends m j k l zero c,
        ← rowDataToRightFiber_leftInverse ends m j k l zero d, h],
    fun d => by
      let c := rowDataToRightFiber ends m j k l zero d
      exact ⟨c, rowDataToRightFiber_injective ends m j k l zero
        (rowDataToRightFiber_leftInverse ends m j k l zero c)⟩⟩

theorem rightRowData_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (rightRowData ends m j k l zero) =
      ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  classical
  calc
    Fintype.card (rightRowData ends m j k l zero) =
        ∑ K : rightRowSupportIndex ends m j k l zero, rowSupportWeight ends m K.1 := by
      change Fintype.card (Σ K : rightRowSupportIndex ends m j k l zero,
        boundarySector ends K.1 {j, k} × boundarySector ends (m \ K.1) ∅) = _
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro K _
      rw [Fintype.card_prod]
      obtain ⟨P, hPK, hPsrc⟩ := K.2.2.2.1
      have hKA : boundarySector ends K.1 {j, k} := ⟨P, hPK, hPsrc⟩
      have hL0 : boundarySector ends (m \ K.1) ∅ :=
        ⟨m \ K.1, Finset.Subset.rfl, K.2.2.2.2.1⟩
      rw [boundarySector_card_eq_cycle ends K.1 {j, k} hKA]
      rfl
    _ = ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
      symm
      exact Finset.sum_subtype _ (fun K => by simp [rightRowSupports]) _

theorem rightFiber_card_eq_weightedSum (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    Fintype.card (rightFiber ends m {j, k} {k, l} k zero) =
      ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
  rw [Fintype.card_congr (rightFiberEquivRowData ends m j k l zero),
    rightRowData_card_eq_weightedSum]

theorem GrahamFiberMinor_of_weightedRowMinor (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (h : GrahamWeightedRowMinor ends m j k l zero) :
    GrahamFiberMinor ends m j k l zero := by
  rw [GrahamFiberMinor, leftFiber_card_eq_weightedSum, rightFiber_card_eq_weightedSum]
  exact h

theorem GrahamFiberMinor_iff_weightedRowMinor (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) :
    GrahamFiberMinor ends m j k l zero ↔ GrahamWeightedRowMinor ends m j k l zero := by
  rw [GrahamFiberMinor, GrahamWeightedRowMinor, leftFiber_card_eq_weightedSum,
    rightFiber_card_eq_weightedSum]



theorem componentExchange_maps_leftRowSupport {ends : ι → Sym2 W} {m K : Finset ι}
    {j k l zero : W} (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag) (hKm : K ⊆ m)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hleft : LeftRowSupport ends m j k l zero K) :
    let K' := exchangeFirstRow ends K (m \ K) k zero
    K' ⊆ m ∧ RightRowSupport ends m j k l zero K' := by
  classical
  let L := m \ K
  let K' := exchangeFirstRow ends K L k zero
  let L' := exchangeSecondRow ends K L k zero
  have hLsub : L ⊆ m := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hKL : Disjoint K L := by
    rw [Finset.disjoint_left]
    intro i hiK hiL
    exact (Finset.mem_sdiff.mp hiL).2 hiK
  have hE0sub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1sub : edgeComponent ends L k ⊆ L := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hK'sub : K' ⊆ m := by
    intro i hi
    dsimp only [K', exchangeFirstRow] at hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hKm (Finset.mem_sdiff.mp hi).1
    · exact hLsub (hE1sub hi)
  have hcompl : m \ K' = L' := by
    ext i
    have hE0 := @hE0sub i
    have hE1 := @hE1sub i
    have hKi := @hKm i
    simp only [K', L', exchangeFirstRow, exchangeSecondRow, Finset.mem_sdiff,
      Finset.mem_union]
    dsimp only [L] at hE1 ⊢
    by_cases hiK : i ∈ K <;> by_cases him : i ∈ m <;>
      by_cases hiE0 : i ∈ edgeComponent ends K zero <;>
        by_cases hiE1 : i ∈ edgeComponent ends (m \ K) k <;>
          simp [hiK, him, hiE0, hiE1] at hE0 hE1 hKi ⊢
  have hjkConn : Sharpness.RandomCurrent.connK ends K j k :=
    Walls.gc6_pairingPath_abstract ends K K (fun i hi => hloop i (hKm hi))
      Finset.Subset.rfl hleft.1 hjk
  have hE0src : Sharpness.RandomCurrent.sources ends (edgeComponent ends K zero) = ∅ := by
    rw [sources_edgeComponent, hleft.1]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [Sharpness.RandomCurrent.mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hleft.2.2.1
        (Sharpness.RandomCurrent.connK_symm ends K (hcomp.trans hjkConn))
    · exact hleft.2.2.1 (Sharpness.RandomCurrent.connK_symm ends K hcomp)
  have hPsrc : Sharpness.RandomCurrent.sources ends (K \ edgeComponent ends K zero) =
      {j, k} := by
    rw [sources_sdiff_of_subset hE0sub, hleft.1, hE0src]
    simp
  have hPsub : K \ edgeComponent ends K zero ⊆ K' := by
    intro i hi
    dsimp only [K', exchangeFirstRow]
    exact Finset.mem_union_left _ hi
  have hbound := componentExchange_boundaries
    (K := K) (L := L) (j := j) (k := k) (l := l) (zero := zero)
    (fun i hi => hloop i (hKm hi)) (fun i hi => hloop i (hLsub hi)) hKL hjk hkl
    hleft.1 hleft.2.1 hleft.2.2.1 hleft.2.2.2
  have hdisc := componentExchange_disconnects hk0 hleft.2.2.1 hleft.2.2.2
  dsimp only
  refine ⟨hK'sub, ?_⟩
  unfold RightRowSupport
  change Sharpness.RandomCurrent.sources ends K' = {j, k} ∆ {k, l} ∧
    (∃ P, P ⊆ K' ∧ Sharpness.RandomCurrent.sources ends P = {j, k}) ∧
    Sharpness.RandomCurrent.sources ends (m \ K') = ∅ ∧
    ¬ Sharpness.RandomCurrent.connK ends K' k zero ∧
    ¬ Sharpness.RandomCurrent.connK ends (m \ K') k zero
  rw [hcompl]
  exact ⟨hbound.1, ⟨K \ edgeComponent ends K zero, hPsub, hPsrc⟩,
    hbound.2, hdisc.1, hdisc.2⟩





theorem GrahamFiberMinor_of_balancedSelector (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (σ : (↑m → Fin 4) → Finset ι × Finset ι)
    (hvalid : ∀ c, LeftPattern ends m {j, k} {k, l} k zero c →
      let X := (σ c).1
      let Y := (σ c).2
      X ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧
      Y ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧
      Sharpness.RandomCurrent.sources ends X = {k, l} ∧
      Sharpness.RandomCurrent.sources ends Y = ∅ ∧
      RowsDisconnect ends m (balancedSwap m X Y c) k zero)
    (hequiv : ∀ c,
      σ (balancedSwap m (σ c).1 (σ c).2 c) = σ c) :
    GrahamFiberMinor ends m j k l zero := by
  classical
  let f : leftFiber ends m {j, k} {k, l} k zero →
      rightFiber ends m {j, k} {k, l} k zero := fun c =>
    ⟨balancedSwap m (σ c.1).1 (σ c.1).2 c.1, by
      rcases hvalid c.1 c.2 with ⟨hX, hY, hsrcX, hsrcY, hdisc⟩
      exact rightPattern_of_balancedTransfer c.2 hX hY hsrcX hsrcY hdisc⟩
  apply Fintype.card_le_of_injective f
  intro c d hcd
  apply Subtype.ext
  have himage : balancedSwap m (σ c.1).1 (σ c.1).2 c.1 =
      balancedSwap m (σ d.1).1 (σ d.1).2 d.1 := congrArg Subtype.val hcd
  have hsigma : σ c.1 = σ d.1 := by
    rw [← hequiv c.1, ← hequiv d.1, himage]
  calc
    c.1 = balancedSwap m (σ c.1).1 (σ c.1).2
        (balancedSwap m (σ c.1).1 (σ c.1).2 c.1) :=
      (balancedSwap_involutive m (σ c.1).1 (σ c.1).2 c.1).symm
    _ = balancedSwap m (σ d.1).1 (σ d.1).2
        (balancedSwap m (σ d.1).1 (σ d.1).2 d.1) := by
      have himage' : balancedSwap m (σ d.1).1 (σ d.1).2 c.1 =
          balancedSwap m (σ d.1).1 (σ d.1).2 d.1 := by
        simpa [hsigma] using himage
      rw [hsigma]
      exact congrArg (balancedSwap m (σ d.1).1 (σ d.1).2) himage'
    _ = d.1 := balancedSwap_involutive m (σ d.1).1 (σ d.1).2 d.1



theorem FiberMinorCandidate_of_total_disconnected (ends : ι → Sym2 W) (m : Finset ι)
    (A B : Finset W) (u v : W) (hdisc : ¬ Sharpness.RandomCurrent.connK ends m u v) :
    FiberMinorCandidate ends m A B u v := by
  classical
  have hrows : ∀ c : ↑m → Fin 4, RowsDisconnect ends m c u v := by
    intro c
    constructor <;> intro hc
    · exact hdisc (connK_mono
        (Finset.union_subset (colorClass_subset m c 0) (colorClass_subset m c 1)) hc)
    · exact hdisc (connK_mono
        (Finset.union_subset (colorClass_subset m c 2) (colorClass_subset m c 3)) hc)
  let f : leftFiber ends m A B u v → rightFiber ends m A B u v := fun c =>
    ⟨middleSwap m c.1, by
      rcases c.2 with ⟨h0, h1, h2, h3, _⟩
      unfold RightPattern
      have e0 : colorClass m (middleSwap m c.1) 0 = colorClass m c.1 0 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 0
      have e1 : colorClass m (middleSwap m c.1) 1 = colorClass m c.1 2 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 1
      have e2 : colorClass m (middleSwap m c.1) 2 = colorClass m c.1 1 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 2
      have e3 : colorClass m (middleSwap m c.1) 3 = colorClass m c.1 3 := by
        simpa [Equiv.swap_apply_def] using colorClass_middleSwap m c.1 3
      refine ⟨?_, ?_, ?_, ?_, hrows _⟩
      · rw [e0]; exact h0
      · rw [e1]; exact h2
      · rw [e2]; exact h1
      · rw [e3]; exact h3⟩
  apply Fintype.card_le_of_injective f
  intro c d hcd
  apply Subtype.ext
  have hfun : middleSwap m c.1 = middleSwap m d.1 := congrArg Subtype.val hcd
  calc
    c.1 = middleSwap m (middleSwap m c.1) := (middleSwap_involutive m c.1).symm
    _ = middleSwap m (middleSwap m d.1) := congrArg (middleSwap m) hfun
    _ = d.1 := middleSwap_involutive m d.1



theorem GrahamFiberMinor_of_total_disconnected (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) (hdisc : ¬ Sharpness.RandomCurrent.connK ends m k zero) :
    GrahamFiberMinor ends m j k l zero :=
  FiberMinorCandidate_of_total_disconnected ends m {j, k} {k, l} k zero hdisc

end FourColor


end GrahamGHS
end StatMech

