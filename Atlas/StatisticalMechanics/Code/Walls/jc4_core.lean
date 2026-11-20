/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































































import Mathlib
import Code.Walls.jc3_core
import Code.Walls.jc3_earfootprint
import Code.Walls.jc4_iteratecoincide
import Code.Walls.jc4_tailnotprobed
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice

































theorem jc4_align_lockstep_bdd (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' : ℕ)
    (hmerge : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1) (i : ℕ)
    (hconf : ∀ j, j < i → jc3_AvoidsEarFootprint r ((dartNext K)^[m + j] a.1)) :
    (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 := by
  induction i with
  | zero => simpa using hmerge
  | succ k ih =>
    have ihk := ih (fun j hj => hconf j (Nat.lt_succ_of_lt hj))
    rw [show m' + (k + 1) = (m' + k) + 1 by ring, show m + (k + 1) = (m + k) + 1 by ring,
        Function.iterate_succ_apply', Function.iterate_succ_apply', ihk]
    exact jc3_dartNext_eq_of_avoidsEarFootprint K r _ (hconf k (Nat.lt_succ_self k))











theorem jc4_align_lockstep (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' : ℕ)
    (hmerge : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
    (hconf : ∀ j, jc3_AvoidsEarFootprint r ((dartNext K)^[m + j] a.1)) (i : ℕ) :
    (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 :=
  jc4_align_lockstep_bdd K a r a' m m' hmerge i (fun j _ => hconf j)


























def jc4_MergeDatum (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∃ (_ : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e}) (m m' n : ℕ),
    dartOrbitPeriod K a = m + n ∧
    dartOrbitPeriod (K \ {r}) a' = m' + n ∧
    (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1 ∧
    (∀ i, i < n → jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1)) ∧
    jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m








theorem jc4_mergeDatum_of_reaches (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hne' : (K \ {r}).Nonempty) (a' : {e : Dart // IsBoundaryDart (K \ {r}) e})
    (m m' n : ℕ)
    (hp : dartOrbitPeriod K a = m + n)
    (hp' : dartOrbitPeriod (K \ {r}) a' = m' + n)
    (hreach : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
    (hconf : ∀ i, i < n → jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1))
    (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m) :
    jc4_MergeDatum K a r :=
  ⟨hne', a', m, m', n, hp, hp', hreach, hconf, hbal⟩
























theorem jc4_splice_of_merge (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (h : jc4_MergeDatum K a r) : jc3_OrbitSpliceDatum K a r := by
  obtain ⟨hne', a', m, m', n, hp, hp', hmerge, hconf, hbal⟩ := h
  refine ⟨hne', a', m, m', n, hp, hp', ?_, hbal⟩
  intro i hi
  refine ⟨jc4_align_lockstep_bdd K a r a' m m' hmerge i (fun j hj => hconf j (hj.trans hi)),
          jc3_notProbed_of_avoidsEarFootprint r _ (hconf i hi)⟩







theorem jc4_merge_strengthens_splice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    jc4_MergeDatum K a r → jc3_OrbitSpliceDatum K a r :=
  jc4_splice_of_merge K a r
















def jc4_SaturatingMerge : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      K ⊆ bpc_orbitFootprint K a →
      ∀ c len, jc2_RunFrame K c len → jc4_MergeDatum K a (c + ![len, 0])






theorem jc4_saturatingOrbitSplice_of_merge (h : jc4_SaturatingMerge) :
    jc3_SaturatingOrbitSplice := by
  intro K hK hge a hsat c len hframe
  exact jc4_splice_of_merge K a _ (h K hK hge a hsat c len hframe)





theorem jc4_saturatingEarMatch_of_merge (h : jc4_SaturatingMerge) :
    jc2_SaturatingEarMatch :=
  jc3_saturatingEarMatch_of_splice (jc4_saturatingOrbitSplice_of_merge h)



theorem jc4_balanceSaturatingContraction_of_merge (h : jc4_SaturatingMerge) :
    bpc_BalanceSaturatingContraction :=
  jc3_balanceSaturatingContraction_of_splice (jc4_saturatingOrbitSplice_of_merge h)



theorem jc4_balancePreservingContraction_of_merge (h : jc4_SaturatingMerge) :
    BalancePreservingContraction :=
  jc3_balancePreservingContraction_of_splice (jc4_saturatingOrbitSplice_of_merge h)





theorem jc4_starHull_totalTurn_eq_four_of_merge (h : jc4_SaturatingMerge)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨
      totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 :=
  jc3_starHull_totalTurn_eq_four_of_splice (jc4_saturatingOrbitSplice_of_merge h) K hSK hne a

























theorem jc4_degenerate_mergeDatum (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail)
    (hne' : (K \ {r}).Nonempty) :
    jc4_MergeDatum K a r := by
  have hnp : ∀ i, bpc_NotProbed r ((dartNext K)^[i] a.1) :=
    fun i => jc3_notProbed_of_avoidsEarFootprint r _ (hfoot i)
  refine ⟨hne', ⟨a.1, jc4_basepoint_survives K a r hne⟩, 0, 0, dartOrbitPeriod K a,
    by rw [Nat.zero_add], ?_, ?_, ?_, ?_⟩
  · 
    rw [Nat.zero_add]; exact jc4_period_eq K a r hnp hne
  · 
    simp
  · 
    intro i _; simpa using hfoot i
  · 
    rw [jc_windowTurn_eq, jc_windowTurn_eq, umEar_windowTurn_self, umEar_windowTurn_self]







theorem jc4_farCell_mergeDatum (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1))
    (hr : r ∉ bpc_orbitFootprint K a) (hne' : (K \ {r}).Nonempty) :
    jc4_MergeDatum K a r :=
  jc4_degenerate_mergeDatum K a r hfoot (bpc_ne_tail_of_not_footprint K a r hr) hne'















theorem jc4_degenerate_merge_gives_splice (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1)) (hne : r ≠ a.1.tail)
    (hne' : (K \ {r}).Nonempty) :
    jc3_OrbitSpliceDatum K a r :=
  jc4_splice_of_merge K a r (jc4_degenerate_mergeDatum K a r hfoot hne hne')


























































end Walls

end StatMech
