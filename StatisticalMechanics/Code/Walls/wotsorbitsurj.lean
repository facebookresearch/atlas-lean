/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Lattice.InterfaceConnected
import Code.Lattice.InterfaceConnectedGlobal
import Code.Lattice.KingFacts
import Code.Lattice.DartOrbit
import Code.Walls.wifinterfaceconn

open SimpleGraph Function

namespace StatMech

namespace Wots

open StatMech.Lattice
open StatMech.Wpb
open StatMech.Wcd
open StatMech.Euc











def wots_dartGraph (K : Set (Site 2)) : SimpleGraph {e : Dart // IsBoundaryDart K e} where
  Adj d1 d2 := d1 ≠ d2 ∧
    (KingAdj d1.1.head d2.1.head ∨ d1.1.head = d2.1.head) ∧
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩
  symm := by
    intro a b h
    refine ⟨h.1.symm, ?_, h.2.2.symm⟩
    rcases h.2.1 with hk | he
    · exact Or.inl hk.symm
    · exact Or.inr he.symm
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem wots_dartGraph_adj (K : Set (Site 2)) (d1 d2 : {e : Dart // IsBoundaryDart K e}) :
    (wots_dartGraph K).Adj d1 d2 ↔
      d1 ≠ d2 ∧
      (KingAdj d1.1.head d2.1.head ∨ d1.1.head = d2.1.head) ∧
      ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
        ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩ := Iff.rfl







def wots_LocalStepSameOrbit (K : Set (Site 2)) : Prop :=
  ∀ d1 d2 : {e : Dart // IsBoundaryDart K e},
    (wots_dartGraph K).Adj d1 d2 → SameOrbit K d1.1 d2.1



def wots_DartConnected (K : Set (Site 2)) : Prop :=
  ∀ d1 d2 : {e : Dart // IsBoundaryDart K e},
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩ →
    (wots_dartGraph K).Reachable d1 d2










theorem wots_reachable_sameOrbit (K : Set (Site 2)) (hstep : wots_LocalStepSameOrbit K)
    {d1 d2 : {e : Dart // IsBoundaryDart K e}}
    (h : (wots_dartGraph K).Reachable d1 d2) : SameOrbit K d1.1 d2.1 := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (a b : {e : Dart // IsBoundaryDart K e}), (wots_dartGraph K).Walk a b →
      SameOrbit K a.1 b.1 from H d1 d2 p
  intro a b q
  induction q with
  | nil => exact SameOrbit.refl K _
  | @cons a b c hadj q' ih => exact SameOrbit.trans (hstep a b hadj) ih







theorem wots_orbitTraceSurjective_of_reduction (K : Set (Site 2))
    (hstep : wots_LocalStepSameOrbit K) (hconn : wots_DartConnected K) :
    OrbitTraceSurjective K := by
  intro e f he hf hreach
  have hR : (wots_dartGraph K).Reachable ⟨e, he⟩ ⟨f, hf⟩ := hconn ⟨e, he⟩ ⟨f, hf⟩ hreach
  exact wots_reachable_sameOrbit K hstep hR










theorem wots_localStep_of_orbitTraceSurjective (K : Set (Site 2))
    (hOTS : OrbitTraceSurjective K) : wots_LocalStepSameOrbit K := by
  intro d1 d2 hadj
  exact hOTS d1.1 d2.1 d1.2 d2.2 hadj.2.2






theorem wots_dartNextSub_adj (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    (wots_dartGraph K).Adj d (dartNextSub K d) := by
  refine ⟨(dartNextSub_ne_self K d).symm, ?_, ?_⟩
  · rcases kf_dartNext_head_kingAdj_or_eq K d.1 with h | h
    · right; rw [dartNextSub_val]; exact h.symm
    · left; rw [dartNextSub_val]; exact h
  · have hso : SameOrbit K d.1 (dartNextSub K d).1 := ⟨1, by rw [dartNextSub_val]; rfl⟩
    exact sameComponent_of_sameOrbit K d.2 (dartNextSub K d).2 hso




theorem wots_reachable_of_sameOrbit (K : Set (Site 2))
    {d1 d2 : {e : Dart // IsBoundaryDart K e}} (h : SameOrbit K d1.1 d2.1) :
    (wots_dartGraph K).Reachable d1 d2 := by
  obtain ⟨n, hn⟩ := h
  have hval : ((dartNextSub K)^[n] d1).1 = d2.1 := by rw [dartNextSub_iterate_val]; exact hn
  have hsub : (dartNextSub K)^[n] d1 = d2 := Subtype.ext hval
  rw [← hsub]
  clear hsub hval hn
  induction n with
  | zero => exact Reachable.refl _
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (wots_dartNextSub_adj K _).reachable




theorem wots_dartConnected_of_orbitTraceSurjective (K : Set (Site 2))
    (hOTS : OrbitTraceSurjective K) : wots_DartConnected K := by
  intro d1 d2 hreach
  exact wots_reachable_of_sameOrbit K (hOTS d1.1 d2.1 d1.2 d2.2 hreach)










theorem wots_orbitTraceSurjective_iff_reduction (K : Set (Site 2)) :
    OrbitTraceSurjective K ↔ (wots_LocalStepSameOrbit K ∧ wots_DartConnected K) := by
  constructor
  · intro h
    exact ⟨wots_localStep_of_orbitTraceSurjective K h,
      wots_dartConnected_of_orbitTraceSurjective K h⟩
  · rintro ⟨hstep, hconn⟩
    exact wots_orbitTraceSurjective_of_reduction K hstep hconn



theorem wots_interfaceConnected_of_reduction (K : Set (Site 2))
    (hstep : wots_LocalStepSameOrbit K) (hconn : wots_DartConnected K) :
    InterfaceConnected K :=
  (orbitTraceSurjective_iff_interfaceConnected K).mp
    (wots_orbitTraceSurjective_of_reduction K hstep hconn)









theorem wots_reduction_singleton (c : Site 2) :
    wots_LocalStepSameOrbit ({c} : Set (Site 2)) ∧ wots_DartConnected ({c} : Set (Site 2)) :=
  (wots_orbitTraceSurjective_iff_reduction ({c} : Set (Site 2))).mp
    (ifg_orbitTraceSurjective_singleton c)



theorem wots_orbitTraceSurjective_singleton (c : Site 2) :
    OrbitTraceSurjective ({c} : Set (Site 2)) :=
  wots_orbitTraceSurjective_of_reduction ({c} : Set (Site 2))
    (wots_reduction_singleton c).1 (wots_reduction_singleton c).2










theorem wots_revCount_pm_one (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e})
    (hpf : WpbPinchFree K a)
    (hstep : wots_LocalStepSameOrbit K) (hconn : wots_DartConnected K)
    (hheads : ∀ d : Dart, (hd : IsBoundaryDart K d) →
      ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨a.1.head, a.2.2⟩ ⟨d.head, hd.2⟩)
    (hbuild : Euc.EucBuildable (wcd_toVtxFinset K hK)) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  Wif.wif_revCount_pm_one K hK a hpf (wots_interfaceConnected_of_reduction K hstep hconn) hheads
    hbuild

end Wots

end StatMech
