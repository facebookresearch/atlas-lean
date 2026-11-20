/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.EarRemoval
import Code.Lattice.EarExistence
import Code.Lattice.EarContraction
import Code.Lattice.BalanceContraction
import Code.Lattice.GaussBonnetEar

open SimpleGraph Function Set

namespace StatMech

namespace Lattice












theorem bpc_dartNext_agree (K K' : Set (Site 2)) (e : Dart)
    (h1 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
    (h2 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
    dartNext K' e = dartNext K e := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [dartNext_of_front_mem K' e (h1.mpr hA), dartNext_of_front_mem K e hA]
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [dartNext_of_side_mem K' e (fun hh => hA (h1.mp hh)) (h2.mpr hB),
          dartNext_of_side_mem K e hA hB]
    · rw [dartNext_of_corner K' e (fun hh => hA (h1.mp hh)) (fun hh => hB (h2.mp hh)),
          dartNext_of_corner K e hA hB]



theorem bpc_turnZ_agree (K K' : Set (Site 2)) (e : Dart)
    (h1 : (e.head + (-rot90Fun e.dir) ∈ K') ↔ (e.head + (-rot90Fun e.dir) ∈ K))
    (h2 : (e.tail + (-rot90Fun e.dir) ∈ K') ↔ (e.tail + (-rot90Fun e.dir) ∈ K)) :
    turnZ K' e = turnZ K e := by
  classical
  unfold turnZ
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · rw [if_pos (h1.mpr hA), if_pos hA]
  · rw [if_neg (fun hh => hA (h1.mp hh)), if_neg hA]
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · rw [if_pos (h2.mpr hB), if_pos hB]
    · rw [if_neg (fun hh => hB (h2.mp hh)), if_neg hB]










def bpc_NotProbed (c : Site 2) (e : Dart) : Prop :=
  e.head + (-rot90Fun e.dir) ≠ c ∧ e.tail + (-rot90Fun e.dir) ≠ c



theorem bpc_dartNext_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (h : bpc_NotProbed c e) :
    dartNext (K \ {c}) e = dartNext K e := by
  apply bpc_dartNext_agree
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.1
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.2


theorem bpc_turnZ_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (h : bpc_NotProbed c e) : turnZ (K \ {c}) e = turnZ K e := by
  apply bpc_turnZ_agree
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.1
  · constructor
    · intro hh; exact (Set.mem_diff _).mp hh |>.1
    · intro hh; refine (Set.mem_diff _).mpr ⟨hh, ?_⟩
      simp only [Set.mem_singleton_iff]; exact h.2





theorem bpc_iterate_dartNext_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] e)) (k : ℕ) :
    (dartNext (K \ {c}))^[k] e = (dartNext K)^[k] e := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact bpc_dartNext_diff_singleton K c ((dartNext K)^[n] e) (hnp n)











theorem bpc_isBoundaryDart_diff_singleton (K : Set (Site 2)) (c : Site 2) (e : Dart)
    (he : IsBoundaryDart K e) (hc : c ≠ e.tail) : IsBoundaryDart (K \ {c}) e := by
  refine ⟨⟨he.1, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff]; exact fun h => hc h.symm
  · intro hh; exact he.2 hh.1



theorem bpc_isPeriodicPt_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (K \ {c})) n a' ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  have key : (dartNext (K \ {c}))^[n] a'.1 = (dartNext K)^[n] a.1 := by
    rw [hval]; exact bpc_iterate_dartNext_diff_singleton K c a.1 hnp n
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [key, hval] at hv
    change ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]; exact hv
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    change ((dartNextSub (K \ {c}))^[n] a').1 = a'.1
    rw [dartNextSub_iterate_val, key, hval]; exact hv



theorem bpc_dartOrbitPeriod_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    dartOrbitPeriod (K \ {c}) a' = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact bpc_isPeriodicPt_diff_singleton K c a a' hval hnp n






theorem bpc_cornerBalance_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    cornerBalance (K \ {c}) a' = cornerBalance K a := by
  classical
  unfold cornerBalance
  rw [bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp]
  set p := dartOrbitPeriod K a with hp
  have hright : rightCornerCount (K \ {c}) a'.1 p = rightCornerCount K a.1 p := by
    unfold rightCornerCount
    congr 2
    apply Finset.filter_congr
    intro i _
    rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp i,
        bpc_turnZ_diff_singleton K c ((dartNext K)^[i] a.1) (hnp i)]
  have hleft : leftCornerCount (K \ {c}) a'.1 p = leftCornerCount K a.1 p := by
    unfold leftCornerCount
    congr 2
    apply Finset.filter_congr
    intro i _
    rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp i,
        bpc_turnZ_diff_singleton K c ((dartNext K)^[i] a.1) (hnp i)]
  rw [hright, hleft]












def bpc_orbitFootprint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set (Site 2) :=
  {x | ∃ i : ℕ,
    x = ((dartNext K)^[i] a.1).head + (-rot90Fun ((dartNext K)^[i] a.1).dir) ∨
    x = ((dartNext K)^[i] a.1).tail + (-rot90Fun ((dartNext K)^[i] a.1).dir) ∨
    x = ((dartNext K)^[i] a.1).tail}



theorem bpc_notProbed_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ bpc_orbitFootprint K a) (i : ℕ) :
    bpc_NotProbed c ((dartNext K)^[i] a.1) := by
  constructor
  · intro h; exact hc ⟨i, Or.inl h.symm⟩
  · intro h; exact hc ⟨i, Or.inr (Or.inl h.symm)⟩



theorem bpc_ne_tail_of_not_footprint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2)
    (hc : c ∉ bpc_orbitFootprint K a) : c ≠ a.1.tail := by
  intro h
  apply hc
  exact ⟨0, Or.inr (Or.inr (by rw [Function.iterate_zero_apply]; exact h))⟩








theorem bpc_contraction_of_not_saturating (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hcK : c ∈ K)
    (hc : c ∉ bpc_orbitFootprint K a) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  have hne_tail : c ≠ a.1.tail := bpc_ne_tail_of_not_footprint K a c hc
  have hbd : IsBoundaryDart (K \ {c}) a.1 :=
    bpc_isBoundaryDart_diff_singleton K c a.1 a.2 hne_tail
  refine ⟨K \ {c}, hK.subset Set.diff_subset, ⟨a.1.tail, hbd.1⟩, ⟨a.1, hbd⟩, ?_, ?_⟩
  · have hsub : (K \ {c}) ⊂ K := by
      rw [Set.ssubset_iff_of_subset Set.diff_subset]
      exact ⟨c, hcK, by simp⟩
    exact Set.ncard_lt_ncard hsub hK
  · exact bpc_cornerBalance_diff_singleton K c a ⟨a.1, hbd⟩ rfl
      (bpc_notProbed_of_not_footprint K a c hc)

















def bpc_BalanceSaturatingContraction : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a








theorem bpc_balancePreservingContraction_of_saturating
    (h : bpc_BalanceSaturatingContraction) : BalancePreservingContraction := by
  intro K hK hge a
  by_cases hsat : K ⊆ bpc_orbitFootprint K a
  · exact h K hK hge a hsat
  · 
    rw [Set.not_subset] at hsat
    obtain ⟨c, hcK, hc⟩ := hsat
    exact bpc_contraction_of_not_saturating K hK a c hcK hc
















theorem bpc_totalTurn_eq_four_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  gbe_totalTurn_eq_four_of_contraction K hSK hne a
    (bpc_balancePreservingContraction_of_saturating hsat)




theorem bpc_totalTurn_eq_four_value_of_saturating (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hsat : bpc_BalanceSaturatingContraction) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  bpc_totalTurn_eq_four_of_saturating K hSK hne a hsat












theorem bpc_domino_cornerBalance : cornerBalance domino dmBase = -4 := by
  rw [cornerBalance_eq_totalTurnZ]
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact domino_totalTurnZ_six


theorem bpc_domino_diff : domino \ {(![1, 0] : Site 2)} = unitCell := by
  ext v
  rw [Set.mem_diff, mem_domino_iff, Set.mem_singleton_iff]
  unfold unitCell
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | h, hne⟩
    · exact h
    · exact absurd h hne
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rw [h]
    intro hcon
    rw [funext_iff, Fin.forall_fin_two] at hcon
    norm_num at hcon






theorem bpc_domino_balanceSaturatingContraction_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase := by
  refine ⟨unitCell, unitCell_finite, ⟨![0, 0], origin_mem_unitCell⟩, ucBase, ?_, ?_⟩
  · 
    have h1 : unitCell.ncard = 1 := by
      unfold unitCell; exact Set.ncard_singleton _
    have h2 : domino.ncard = 2 := by
      unfold domino
      apply Set.ncard_pair
      intro hcon
      rw [funext_iff, Fin.forall_fin_two] at hcon; norm_num at hcon
    omega
  · 
    rw [bpc_domino_cornerBalance, unitCell_cornerBalance ucBase (Or.inl rfl)]










































end Lattice

end StatMech
