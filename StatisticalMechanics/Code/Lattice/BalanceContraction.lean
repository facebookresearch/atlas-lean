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
import Code.Lattice.GaussBonnet

open SimpleGraph Function

namespace StatMech

namespace Lattice




















theorem sum_range_cyclic_shift (g : ℕ → ℤ) (p : ℕ) (hcyc : g p = g 0) :
    ∑ i ∈ Finset.range p, g (i + 1) = ∑ i ∈ Finset.range p, g i := by
  have h1 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g (i + 1)) + g 0 :=
    Finset.sum_range_succ' g p
  have h2 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g i) + g p :=
    Finset.sum_range_succ g p
  rw [hcyc] at h2
  omega

















theorem dartOrbitPeriod_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod K (dartNextSub K a) = dartOrbitPeriod K a := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  unfold dartOrbitPeriod
  exact Function.minimalPeriod_apply ((dartNextSub_injective K).mem_periodicPts a)



theorem dartOrbitPeriod_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    dartOrbitPeriod K ((dartNextSub K)^[n] a) = dartOrbitPeriod K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', dartOrbitPeriod_dartNextSub K hK, ih]






















theorem totalTurnZ_period_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K (dartNextSub K a).1 (dartOrbitPeriod K (dartNextSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [dartOrbitPeriod_dartNextSub K hK a]
  set p := dartOrbitPeriod K a with hp
  set g := fun i => turnZ K ((dartNext K)^[i] a.1) with hg
  have hper : (dartNext K)^[p] a.1 = a.1 := orbit_iterate_period_eq K a
  have hcyc : g p = g 0 := by simp only [hg, hper, Function.iterate_zero_apply]
  unfold totalTurnZ
  rw [dartNextSub_val]
  have key : ∀ i, (dartNext K)^[i] (dartNext K a.1) = (dartNext K)^[i + 1] a.1 := by
    intro i; rw [Function.iterate_succ_apply]
  simp_rw [key]
  exact sum_range_cyclic_shift g p hcyc




theorem totalTurnZ_period_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    totalTurnZ K ((dartNextSub K)^[n] a).1 (dartOrbitPeriod K ((dartNextSub K)^[n] a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', totalTurnZ_period_dartNextSub K hK, ih]
















theorem cornerBalance_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K (dartNextSub K a) = cornerBalance K a := by
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ]
  exact totalTurnZ_period_dartNextSub K hK a



theorem cornerBalance_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    cornerBalance K ((dartNextSub K)^[n] a) = cornerBalance K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', cornerBalance_dartNextSub K hK, ih]





theorem cornerBalance_constant_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a b : {e : Dart // IsBoundaryDart K e}) (n : ℕ) (hb : b = (dartNextSub K)^[n] a) :
    cornerBalance K b = cornerBalance K a := by
  rw [hb]; exact cornerBalance_iterate_dartNextSub K hK a n









theorem revCount_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    revCount K (dartNextSub K a) = revCount K a := by
  unfold revCount
  rw [totalTurnZ_period_dartNextSub K hK a]



theorem revCount_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    revCount K ((dartNextSub K)^[n] a) = revCount K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', revCount_dartNextSub K hK, ih]





theorem eulerCharOne_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    EulerCharOne K (dartNextSub K a) ↔ EulerCharOne K a := by
  unfold EulerCharOne
  rw [revCount_dartNextSub K hK a, dartOrbitPeriod_dartNextSub K hK a]



theorem eulerCharOne_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    EulerCharOne K ((dartNextSub K)^[n] a) ↔ EulerCharOne K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', eulerCharOne_dartNextSub K hK, ih]




















theorem cornerBalance_eq_four_revCount (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K a = 4 * revCount K a := by
  rw [cornerBalance_eq_totalTurnZ, gaussBonnet_local_global]




theorem balanceIsFour_iff_revCount_pm_one (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    BalanceIsFour K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  unfold BalanceIsFour
  rw [cornerBalance_eq_four_revCount]
  constructor
  · rintro (h | h)
    · left; omega
    · right; omega
  · rintro (h | h)
    · left; rw [h]; ring
    · right; rw [h]; ring






theorem eulerCharOne_iff_balanceIsFour (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ BalanceIsFour K a := by
  rw [balanceIsFour_iff_simplePolygon, simplePolygonCornerBalance_iff,
    eulerCharOne_iff_turningIsFullRevolution K a hp]

















def BalancePreservingContractionRep : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      ∃ (n : ℕ) (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧
          cornerBalance K' a' = cornerBalance K ((dartNextSub K)^[n] a)








theorem balancePreservingContraction_of_rep (h : BalancePreservingContractionRep) :
    BalancePreservingContraction := by
  intro K hK hge a
  obtain ⟨n, K', hK', hne', a', hlt, hbal⟩ := h K hK hge a
  refine ⟨K', hK', hne', a', hlt, ?_⟩
  rw [hbal, cornerBalance_iterate_dartNextSub K hK a n]






theorem balancePreservingContractionRep_iff :
    BalancePreservingContractionRep ↔ BalancePreservingContraction := by
  constructor
  · exact balancePreservingContraction_of_rep
  · intro h K hK hge a
    obtain ⟨K', hK', hne', a', hlt, hbal⟩ := h K hK hge a
    exact ⟨0, K', hK', hne', a', hlt, by rw [Function.iterate_zero_apply]; exact hbal⟩










theorem unitCell_cornerBalance_dartNextSub :
    cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase :=
  cornerBalance_dartNextSub unitCell unitCell_finite ucBase




theorem domino_cornerBalance_dartNextSub :
    cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase :=
  cornerBalance_dartNextSub domino domino_finite dmBase




























end Lattice

end StatMech
