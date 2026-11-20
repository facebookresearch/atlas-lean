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

open SimpleGraph Function

namespace StatMech.Walls

open StatMech.Lattice



















theorem jc_sum_range_cyclic_shift (g : ℕ → ℤ) (p : ℕ) (hcyc : g p = g 0) :
    ∑ i ∈ Finset.range p, g (i + 1) = ∑ i ∈ Finset.range p, g i := by
  have h1 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g (i + 1)) + g 0 :=
    Finset.sum_range_succ' g p
  have h2 : ∑ i ∈ Finset.range (p + 1), g i = (∑ i ∈ Finset.range p, g i) + g p :=
    Finset.sum_range_succ g p
  rw [hcyc] at h2
  omega











theorem jc_dartOrbitPeriod_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod K (dartNextSub K a) = dartOrbitPeriod K a := by
  have hfin : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  unfold dartOrbitPeriod
  exact Function.minimalPeriod_apply ((dartNextSub_injective K).mem_periodicPts a)



theorem jc_dartOrbitPeriod_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    dartOrbitPeriod K ((dartNextSub K)^[n] a) = dartOrbitPeriod K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', jc_dartOrbitPeriod_dartNextSub K hK, ih]





















theorem jc_totalTurnZ_period_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K (dartNextSub K a).1 (dartOrbitPeriod K (dartNextSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [jc_dartOrbitPeriod_dartNextSub K hK a]
  set p := dartOrbitPeriod K a with hp
  set g := fun i => turnZ K ((dartNext K)^[i] a.1) with hg
  have hper : (dartNext K)^[p] a.1 = a.1 := orbit_iterate_period_eq K a
  have hcyc : g p = g 0 := by simp only [hg, hper, Function.iterate_zero_apply]
  unfold totalTurnZ
  rw [dartNextSub_val]
  have key : ∀ i, (dartNext K)^[i] (dartNext K a.1) = (dartNext K)^[i + 1] a.1 := by
    intro i; rw [Function.iterate_succ_apply]
  simp_rw [key]
  exact jc_sum_range_cyclic_shift g p hcyc




theorem jc_totalTurnZ_period_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    totalTurnZ K ((dartNextSub K)^[n] a).1 (dartOrbitPeriod K ((dartNextSub K)^[n] a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', jc_totalTurnZ_period_dartNextSub K hK, ih]













theorem jc_cornerBalance_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance K (dartNextSub K a) = cornerBalance K a := by
  rw [cornerBalance_eq_totalTurnZ, cornerBalance_eq_totalTurnZ]
  exact jc_totalTurnZ_period_dartNextSub K hK a



theorem jc_cornerBalance_iterate_dartNextSub (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    cornerBalance K ((dartNextSub K)^[n] a) = cornerBalance K a := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', jc_cornerBalance_dartNextSub K hK, ih]






theorem jc_cornerBalance_constant_on_orbit (K : Set (Site 2)) (hK : K.Finite)
    (a b : {e : Dart // IsBoundaryDart K e}) (n : ℕ) (hb : b = (dartNextSub K)^[n] a) :
    cornerBalance K b = cornerBalance K a := by
  rw [hb]; exact jc_cornerBalance_iterate_dartNextSub K hK a n
















def jc_BalancePreservingContractionRep : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (a : {e : Dart // IsBoundaryDart K e}),
      ∃ (n : ℕ) (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧
          cornerBalance K' a' = cornerBalance K ((dartNextSub K)^[n] a)








theorem jc_balancePreservingContraction_of_rep (h : jc_BalancePreservingContractionRep) :
    BalancePreservingContraction := by
  intro K hK hge a
  obtain ⟨n, K', hK', hne', a', hlt, hbal⟩ := h K hK hge a
  refine ⟨K', hK', hne', a', hlt, ?_⟩
  rw [hbal, jc_cornerBalance_iterate_dartNextSub K hK a n]









theorem jc_balancePreservingContractionRep_iff :
    jc_BalancePreservingContractionRep ↔ BalancePreservingContraction := by
  constructor
  · exact jc_balancePreservingContraction_of_rep
  · intro h K hK hge a
    obtain ⟨K', hK', hne', a', hlt, hbal⟩ := h K hK hge a
    exact ⟨0, K', hK', hne', a', hlt, by rw [Function.iterate_zero_apply]; exact hbal⟩

















def jc_BalancePreservingContractionExtreme : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → 2 ≤ K.ncard →
    ∀ (c : Site 2) (hc : IsExtremeCell K c),
      ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
        (a' : {e : Dart // IsBoundaryDart K' e}),
        K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K (extremeBase K c hc)




















theorem jc_balancePreservingContractionExtreme_of_rep
    (h : jc_BalancePreservingContractionExtreme) (K : Set (Site 2)) (hK : K.Finite)
    (hge : 2 ≤ K.ncard) (c : Site 2) (hc : IsExtremeCell K c) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧
        cornerBalance K' a' = cornerBalance K (extremeBase K c hc) :=
  h K hK hge c hc








theorem jc_balancePreservingContraction_at_orbit_of_extreme
    (h : jc_BalancePreservingContractionExtreme) (K : Set (Site 2)) (hK : K.Finite)
    (hge : 2 ≤ K.ncard) (c : Site 2) (hc : IsExtremeCell K c)
    (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ)
    (ha : a = (dartNextSub K)^[n] (extremeBase K c hc)) :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
  obtain ⟨K', hK', hne', a', hlt, hbal⟩ := h K hK hge c hc
  refine ⟨K', hK', hne', a', hlt, ?_⟩
  rw [hbal, ha, jc_cornerBalance_iterate_dartNextSub K hK (extremeBase K c hc) n]










theorem jc_unitCell_cornerBalance_dartNextSub :
    cornerBalance unitCell (dartNextSub unitCell ucBase) = cornerBalance unitCell ucBase :=
  jc_cornerBalance_dartNextSub unitCell unitCell_finite ucBase




theorem jc_domino_cornerBalance_dartNextSub :
    cornerBalance domino (dartNextSub domino dmBase) = cornerBalance domino dmBase :=
  jc_cornerBalance_dartNextSub domino domino_finite dmBase
























end StatMech.Walls
