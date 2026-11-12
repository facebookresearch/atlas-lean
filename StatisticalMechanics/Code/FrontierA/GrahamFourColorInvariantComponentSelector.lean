/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorInvariantMasks









open Finset
open Classical

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def invariantMiddleTransfer (ends : I -> Sym2 W)
    (m : Finset I) (c : ↑m -> Fin 4) (k : W) : Finset I :=
  edgeComponent ends (middleMask m c) k




noncomputable def invariantOuterTransfer (ends : I -> Sym2 W)
    (m : Finset I) (c : ↑m -> Fin 4) (j zero : W) : Finset I :=
  if connK ends (outerMask m c) zero j then ∅
  else edgeComponent ends (outerMask m c) zero

noncomputable def invariantComponentSelector (ends : I -> Sym2 W)
    (m : Finset I) (j k zero : W) (c : ↑m -> Fin 4) :
    Finset I × Finset I :=
  (invariantMiddleTransfer ends m c k,
    invariantOuterTransfer ends m c j zero)

theorem invariantMiddleTransfer_subset (ends : I -> Sym2 W)
    (m : Finset I) (c : ↑m -> Fin 4) (k : W) :
    invariantMiddleTransfer ends m c k ⊆ middleMask m c := by
  intro i hi
  rw [invariantMiddleTransfer, edgeComponent, Finset.mem_filter] at hi
  exact hi.1

theorem invariantOuterTransfer_subset (ends : I -> Sym2 W)
    (m : Finset I) (c : ↑m -> Fin 4) (j zero : W) :
    invariantOuterTransfer ends m c j zero ⊆ outerMask m c := by
  intro i hi
  unfold invariantOuterTransfer at hi
  split at hi
  · simp at hi
  · rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1

theorem invariantMiddleTransfer_sources
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {c : ↑m -> Fin 4}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    sources ends (invariantMiddleTransfer ends m c k) = {k, l} := by
  exact leftPattern_middleComponent_sources hloop hjk hkl hc

theorem invariantOuterTransfer_sources
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {c : ↑m -> Fin 4}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    sources ends (invariantOuterTransfer ends m c j zero) = ∅ := by
  classical
  unfold invariantOuterTransfer
  by_cases hzj : connK ends (outerMask m c) zero j
  · rw [if_pos hzj]
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK]
  · rw [if_neg hzj, sources_edgeComponent,
      leftPattern_outerMask_sources hc]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
    rw [mem_compOf] at hcomp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxj | hxk
    · subst x
      exact hzj hcomp
    · have hjkColor := (leftPattern_sharedSource_connections
          hloop hjk hkl hc).1
      have hjkOuter : connK ends (outerMask m c) j k := by
        apply connK_mono (K := colorClass m c 0)
          (L := outerMask m c)
        · intro i hi
          exact Finset.mem_union_left _ hi
        · exact hjkColor
      rw [hxk] at hcomp
      exact hzj (hcomp.trans (connK_symm ends _ hjkOuter))

@[simp] theorem invariantMiddleTransfer_balancedSwap
    (ends : I -> Sym2 W) (m X Y : Finset I) (c : ↑m -> Fin 4)
    (k : W) :
    invariantMiddleTransfer ends m (balancedSwap m X Y c) k =
      invariantMiddleTransfer ends m c k := by
  simp [invariantMiddleTransfer, middleMask_balancedSwap]

@[simp] theorem invariantOuterTransfer_balancedSwap
    (ends : I -> Sym2 W) (m X Y : Finset I) (c : ↑m -> Fin 4)
    (j zero : W) :
    invariantOuterTransfer ends m (balancedSwap m X Y c) j zero =
      invariantOuterTransfer ends m c j zero := by
  simp [invariantOuterTransfer, outerMask_balancedSwap]

@[simp] theorem invariantComponentSelector_balancedSwap
    (ends : I -> Sym2 W) (m X Y : Finset I) (j k zero : W)
    (c : ↑m -> Fin 4) :
    invariantComponentSelector ends m j k zero (balancedSwap m X Y c) =
      invariantComponentSelector ends m j k zero c := by
  simp [invariantComponentSelector]



theorem GrahamFiberMinor_of_invariantComponent_disconnects
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hdisc : ∀ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
        RowsDisconnect ends m
          (balancedSwap m
            (invariantMiddleTransfer ends m c k)
            (invariantOuterTransfer ends m c j zero) c) k zero) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_balancedSelector ends m j k l zero
    (invariantComponentSelector ends m j k zero)
  · intro c hc
    have hX := invariantMiddleTransfer_subset ends m c k
    have hY := invariantOuterTransfer_subset ends m c j zero
    have hsX := invariantMiddleTransfer_sources hloop hjk hkl hc
    have hsY := invariantOuterTransfer_sources hloop hjk hkl hc
    simpa only [invariantComponentSelector, middleMask, outerMask] using
      And.intro hX (And.intro hY (And.intro hsX (And.intro hsY (hdisc c hc))))
  · intro c
    exact invariantComponentSelector_balancedSwap ends m _ _ j k zero c

end StatMech.GrahamGHS.FourColor
