/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.MonotoneAutomatonNearestConclusion

open Set
open scoped NNReal

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem siteOpenGraph_mono {eta eta' : ConfigSpace (Site d)} (h : eta ≤ eta') :
    siteOpenGraph eta ≤ siteOpenGraph eta' := by
  intro x y hxy
  refine ⟨hxy.1, ?_, ?_⟩
  · exact Bool.eq_true_of_true_le (hxy.2.1 ▸ h x)
  · exact Bool.eq_true_of_true_le (hxy.2.2 ▸ h y)


theorem le_raiseField (xi : NonnegativeField d) (x : Site d) (r : ℝ≥0) :
    xi ≤ raiseField xi x r := by
  intro y
  by_cases hy : y = x
  · subst y
    simp [raiseField]
  · simp [raiseField, hy]



theorem site_eq_true_of_siteCluster_infinite
    (eta : ConfigSpace (Site d)) (x : Site d)
    (hinf : (siteCluster eta x).Infinite) :
    eta x = true := by
  by_contra hx
  have hxfalse : eta x = false := by
    cases h : eta x
    · rfl
    · exact (hx h).elim
  have hsub : siteCluster eta x ⊆ ({x} : Set (Site d)) := by
    intro y hy
    rcases hy with ⟨w⟩
    cases w with
    | nil => simp
    | cons hadj w =>
        exfalso
        simpa [hxfalse] using hadj.2.1
  exact hinf (Set.finite_singleton x |>.subset hsub)



theorem siteCluster_raise_eq_of_infinite_of_not_mem
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (x y : Site d) (r : ℝ≥0)
    (hinf : (siteCluster (T (raiseField xi x r)) y).Infinite)
    (hx : x ∉ siteCluster (T (raiseField xi x r)) y) :
    siteCluster (T (raiseField xi x r)) y = siteCluster (T xi) y := by
  let etaRaised : ConfigSpace (Site d) := T (raiseField xi x r)
  let etaBase : ConfigSpace (Site d) := T xi
  have heta : etaBase ≤ etaRaised := T.monotone (le_raiseField xi x r)
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with ⟨w⟩
    have hvertexBase : ∀ a : Site d, a ∈ siteCluster etaRaised y →
        etaBase a = true := by
      intro a ha
      have hax : a ∉ siteCluster etaRaised x := by
        intro hxa
        apply hx
        exact ha.trans hxa.symm
      exact site_eq_true_of_siteCluster_infinite etaBase a
        (T.otherInfiniteClustersStable xi x r a hax (by
          rw [show siteCluster etaRaised a = siteCluster etaRaised y by
            ext z
            constructor
            · exact fun haz => ha.trans haz
            · exact fun hyz => ha.symm.trans hyz]
          exact hinf))
    have hwalk : ∀ {a b : Site d},
        (siteOpenGraph etaRaised).Walk a b →
        a ∈ siteCluster etaRaised y →
        (siteOpenGraph etaBase).Walk a b := by
      intro a b p
      induction p with
      | nil =>
          intro _
          exact SimpleGraph.Walk.nil
      | @cons a b c hab p ih =>
          intro ha
          have hb : b ∈ siteCluster etaRaised y :=
            ha.trans hab.reachable
          exact SimpleGraph.Walk.cons
            ⟨hab.1, hvertexBase a ha, hvertexBase b hb⟩ (ih hb)
    exact ⟨hwalk w (by exact ⟨SimpleGraph.Walk.nil⟩)⟩
  · intro z hz
    exact (SimpleGraph.Reachable.mono (siteOpenGraph_mono heta) hz)




def raiseFields (xi : NonnegativeField d) (S : Finset (Site d))
    (r : Site d → ℝ≥0) : NonnegativeField d :=
  fun y => if y ∈ S then max (r y) (xi y) else xi y

@[simp] theorem raiseFields_empty (xi : NonnegativeField d) (r : Site d → ℝ≥0) :
    raiseFields xi ∅ r = xi := by
  funext y
  simp [raiseFields]



theorem raiseFields_insert (xi : NonnegativeField d) (S : Finset (Site d))
    (r : Site d → ℝ≥0) {x : Site d} (hx : x ∉ S) :
    raiseFields xi (insert x S) r = raiseField (raiseFields xi S r) x (r x) := by
  funext y
  by_cases hyx : y = x
  · subst y
    simp [raiseFields, raiseField, hx]
  · by_cases hyS : y ∈ S
    · simp [raiseFields, raiseField, hyx, hyS]
    · simp [raiseFields, raiseField, hyx, hyS]


theorem le_raiseFields (xi : NonnegativeField d) (S : Finset (Site d))
    (r : Site d → ℝ≥0) :
    xi ≤ raiseFields xi S r := by
  intro y
  by_cases hy : y ∈ S
  · simp [raiseFields, hy]
  · simp [raiseFields, hy]


theorem raiseFields_mono_set (xi : NonnegativeField d) {S U : Finset (Site d)}
    (hSU : S ⊆ U) (r : Site d → ℝ≥0) :
    raiseFields xi S r ≤ raiseFields xi U r := by
  intro y
  by_cases hyS : y ∈ S
  · have hyU : y ∈ U := hSU hyS
    simp [raiseFields, hyS, hyU]
  · by_cases hyU : y ∈ U
    · simp [raiseFields, hyS, hyU]
    · simp [raiseFields, hyS, hyU]




theorem siteCluster_raiseFields_eq_of_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (r : Site d → ℝ≥0) (y : Site d)
    (hinf : (siteCluster (T xi) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T (raiseFields xi S r)) y) :
    siteCluster (T (raiseFields xi S r)) y = siteCluster (T xi) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      let xiS := raiseFields xi S r
      have hxiSFinal : xiS ≤ raiseFields xi (insert x S) r := by
        exact raiseFields_mono_set xi (Finset.subset_insert x S) r
      have hclusterMono : siteCluster (T xiS) y ⊆
          siteCluster (T (raiseFields xi (insert x S) r)) y := by
        intro z hz
        exact SimpleGraph.Reachable.mono
          (siteOpenGraph_mono (T.monotone hxiSFinal)) hz
      have havoidS : ∀ z ∈ S, z ∉ siteCluster (T xiS) y := by
        intro z hzS hzCluster
        exact havoid z (Finset.mem_insert_of_mem hzS) (hclusterMono hzCluster)
      have ihEq : siteCluster (T xiS) y = siteCluster (T xi) y :=
        ih havoidS
      have hinfS : (siteCluster (T xiS) y).Infinite := by
        rw [ihEq]
        exact hinf
      have hinfFinal :
          (siteCluster (T (raiseFields xi (insert x S) r)) y).Infinite :=
        hinfS.mono hclusterMono
      have hsingle := siteCluster_raise_eq_of_infinite_of_not_mem
        T xiS x y (r x)
      rw [← raiseFields_insert xi S r hx] at hsingle
      exact (hsingle hinfFinal (havoid x (Finset.mem_insert_self x S))).trans ihEq


def zeroFields (xi : NonnegativeField d) (S : Finset (Site d)) :
    NonnegativeField d :=
  fun y => if y ∈ S then 0 else xi y



theorem raiseFields_zeroFields (xi : NonnegativeField d) (S : Finset (Site d)) :
    raiseFields (zeroFields xi S) S xi = xi := by
  funext y
  by_cases hy : y ∈ S
  · simp [raiseFields, zeroFields, hy]
  · simp [raiseFields, zeroFields, hy]




theorem siteCluster_zeroFields_eq_of_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (y : Site d)
    (hinf : (siteCluster (T (zeroFields xi S)) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T xi) y) :
    siteCluster (T (zeroFields xi S)) y = siteCluster (T xi) y := by
  have h := siteCluster_raiseFields_eq_of_infinite_of_avoids
    T (zeroFields xi S) S xi y hinf
  rw [raiseFields_zeroFields] at h
  exact (h havoid).symm

end StatMech.FrontierA
