/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierA.MonotoneAutomatonAbsorptionReduction
import Code.FrontierA.FiniteEventMultivalued
import Code.Lattice.SegmentConn
import Code.Percolation.GridBoxConnected

open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}




theorem siteCluster_raiseFields_eq_of_final_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (r : Site d → ℝ≥0) (y : Site d)
    (hinf : (siteCluster (T (raiseFields xi S r)) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T (raiseFields xi S r)) y) :
    siteCluster (T (raiseFields xi S r)) y = siteCluster (T xi) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      let xiS := raiseFields xi S r
      have hsingle := siteCluster_raise_eq_of_infinite_of_not_mem
        T xiS x y (r x)
      rw [← raiseFields_insert xi S r hx] at hsingle
      have hfinalIntermediate :
          siteCluster (T (raiseFields xi (insert x S) r)) y =
            siteCluster (T xiS) y :=
        hsingle hinf (havoid x (Finset.mem_insert_self x S))
      have hinfS : (siteCluster (T xiS) y).Infinite := by
        rw [← hfinalIntermediate]
        exact hinf
      have havoidS : ∀ z ∈ S, z ∉ siteCluster (T xiS) y := by
        intro z hzS hz
        exact havoid z (Finset.mem_insert_of_mem hzS)
          (hfinalIntermediate.symm ▸ hz)
      exact hfinalIntermediate.trans (ih hinfS havoidS)




theorem siteCluster_zeroFields_eq_of_final_infinite_of_avoids
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (S : Finset (Site d)) (y : Site d)
    (hinf : (siteCluster (T xi) y).Infinite)
    (havoid : ∀ x ∈ S, x ∉ siteCluster (T xi) y) :
    siteCluster (T (zeroFields xi S)) y = siteCluster (T xi) y := by
  have h := siteCluster_raiseFields_eq_of_final_infinite_of_avoids
    T (zeroFields xi S) S xi y
  rw [raiseFields_zeroFields] at h
  exact (h hinf havoid).symm




def coordinateBetween (x y : Site d) : Set (Site d) :=
  {z | ∀ i, min (x i) (y i) ≤ z i ∧ z i ≤ max (x i) (y i)}

@[simp] theorem left_mem_coordinateBetween (x y : Site d) :
    x ∈ coordinateBetween x y := by
  intro i
  exact ⟨min_le_left _ _, le_max_left _ _⟩

@[simp] theorem right_mem_coordinateBetween (x y : Site d) :
    y ∈ coordinateBetween x y := by
  intro i
  exact ⟨min_le_right _ _, le_max_right _ _⟩

theorem coordinateBetween_l1dist_le {x y z : Site d}
    (hz : z ∈ coordinateBetween x y) :
    l1dist d x z ≤ l1dist d x y := by
  unfold l1dist
  apply Finset.sum_le_sum
  intro i hi
  have hzi := hz i
  rcases le_total (x i) (y i) with hxy | hyx
  · simp only [min_eq_left hxy, max_eq_right hxy] at hzi
    omega
  · simp only [min_eq_right hyx, max_eq_left hyx] at hzi
    omega



theorem eq_right_of_mem_coordinateBetween_of_l1dist_eq
    {x y z : Site d} (hz : z ∈ coordinateBetween x y)
    (heq : l1dist d x z = l1dist d x y) : z = y := by
  funext i
  have hzi := hz i
  by_contra hne
  have hstrictTerm : (x i - z i).natAbs < (x i - y i).natAbs := by
    rcases le_total (x i) (y i) with hxy | hyx
    · simp only [min_eq_left hxy, max_eq_right hxy] at hzi
      omega
    · simp only [min_eq_right hyx, max_eq_left hyx] at hzi
      omega
  have hleTerms : ∀ j, (x j - z j).natAbs ≤ (x j - y j).natAbs := by
    intro j
    have hzj := hz j
    rcases le_total (x j) (y j) with hxy | hyx
    · simp only [min_eq_left hxy, max_eq_right hxy] at hzj
      omega
    · simp only [min_eq_right hyx, max_eq_left hyx] at hzj
      omega
  have hsumStrict :
      (∑ j, (x j - z j).natAbs) < ∑ j, (x j - y j).natAbs := by
    exact Finset.sum_lt_sum (fun j _ => hleTerms j)
      ⟨i, Finset.mem_univ i, hstrictTerm⟩
  exact (ne_of_lt hsumStrict) heq

theorem coordinateBetween_finite (x y : Site d) :
    (coordinateBetween x y).Finite := by
  let D := l1dist d x y
  have hsub : coordinateBetween x y ⊆
      (fun w : Site d => x + w) '' box d D := by
    intro z hz
    refine ⟨z - x, ?_, by simp⟩
    intro i
    have hcoord : (z i - x i).natAbs ≤ D := by
      have hterm : (x i - z i).natAbs ≤ l1dist d x z := by
        unfold l1dist
        exact Finset.single_le_sum
          (f := fun j : Fin d => (x j - z j).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have habs : (z i - x i).natAbs = (x i - z i).natAbs := by
        rw [← Int.natAbs_neg]
        congr 1
        ring
      rw [habs]
      exact hterm.trans (coordinateBetween_l1dist_le hz)
    simpa [Pi.sub_apply] using hcoord
  exact ((box_finite d D).image (fun w : Site d => x + w)).subset hsub

theorem mixSite_mem_coordinateBetween (x y : Site d) (k : ℕ) :
    mixSite x y k ∈ coordinateBetween x y := by
  intro i
  simp only [mixSite]
  split_ifs
  · exact ⟨min_le_right _ _, le_max_right _ _⟩
  · exact ⟨min_le_left _ _, le_max_left _ _⟩




theorem coordinateBetween_update_reachable (x y u : Site d)
    (hu : u ∈ coordinateBetween x y) (j : Fin d) :
    ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable
      ⟨u, hu⟩
      ⟨Function.update u j (y j), by
        intro i
        by_cases hij : i = j
        · subst i
          simp
        · simpa [Function.update_of_ne hij] using hu i⟩ := by
  classical
  let v := Function.update u j (y j)
  have hv : v ∈ coordinateBetween x y := by
    intro i
    by_cases hij : i = j
    · subst i
      simp [v]
    · simpa [v, Function.update_of_ne hij] using hu i
  rcases le_total (u j) (y j) with hle | hle
  · obtain ⟨n, hn⟩ := Int.le.dest hle
    have hseg := segment_connectedWithin (coordinateBetween x y) j u n
      (fun t ht => by
        intro i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
          have huj := hu j
          omega
        · simpa [Function.update_of_ne hij] using hu i)
    have hend : Function.update u j (u j + (n : ℤ)) = v := by
      simp [v, hn]
    simpa [v, hend] using hseg
  · obtain ⟨n, hn⟩ := Int.le.dest hle
    have hseg := segment_connectedWithin (coordinateBetween x y) j v n
      (fun t ht => by
        intro i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self, v]
          have huj := hu j
          omega
        · simpa [v, Function.update_of_ne hij] using hu i)
    have hend : Function.update v j (v j + (n : ℤ)) = u := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [v, hn]
      · simp [v, Function.update_of_ne hij]
    have hrev := hseg.symm
    simpa only [Int.ofNat_zero, add_zero, Function.update_eq_self, hend] using hrev



theorem coordinateBetween_reachable (x y : Site d) :
    ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable
      ⟨x, left_mem_coordinateBetween x y⟩
      ⟨y, right_mem_coordinateBetween x y⟩ := by
  have hreach : ∀ k ≤ d,
      ((hypercubicLattice d).induce (coordinateBetween x y)).Reachable
        ⟨x, left_mem_coordinateBetween x y⟩
        ⟨mixSite x y k, mixSite_mem_coordinateBetween x y k⟩ := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa only [mixSite_zero] using
          (SimpleGraph.Reachable.refl
            (⟨x, left_mem_coordinateBetween x y⟩ : coordinateBetween x y))
    | succ k ih =>
        intro hk
        have hkd : k < d := by omega
        have hstep := coordinateBetween_update_reachable x y
          (mixSite x y k) (mixSite_mem_coordinateBetween x y k) ⟨k, hkd⟩
        have hmix : mixSite x y (k + 1) =
            Function.update (mixSite x y k) ⟨k, hkd⟩ (y ⟨k, hkd⟩) :=
          mixSite_succ hkd
        exact (ih (by omega)).trans (by simpa [hmix] using hstep)
  simpa using hreach d le_rfl



theorem connected_siteToBond_of_coordinateBetween
    (eta : ConfigSpace (Site d)) (x y : Site d)
    (hopen : ∀ z ∈ coordinateBetween x y, eta z = true) :
    Connected d (siteToBond eta) x y := by
  rw [connected_siteToBond_iff]
  let f : (hypercubicLattice d).induce (coordinateBetween x y) →g
      siteOpenGraph eta :=
    { toFun := fun z => z.1
      map_rel' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
        exact ⟨hab, hopen a ha, hopen b hb⟩ }
  exact (coordinateBetween_reachable x y).map f


noncomputable def contactForceSet (x y : Site d) : Finset (Site d) :=
  (coordinateBetween_finite x y).toFinset.erase y

@[simp] theorem mem_contactForceSet {x y z : Site d} :
    z ∈ contactForceSet x y ↔ z ∈ coordinateBetween x y ∧ z ≠ y := by
  classical
  simp only [contactForceSet, Set.Finite.mem_toFinset, Finset.mem_erase]
  tauto



theorem connected_siteToBond_of_contactForceSet
    (eta : ConfigSpace (Site d)) (x y : Site d)
    (hy : eta y = true)
    (hforce : ∀ z ∈ contactForceSet x y, eta z = true) :
    Connected d (siteToBond eta) x y := by
  apply connected_siteToBond_of_coordinateBetween eta x y
  intro z hz
  by_cases hzy : z = y
  · simpa [hzy] using hy
  · exact hforce z (mem_contactForceSet.mpr ⟨hz, hzy⟩)





noncomputable def zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) (q : FieldTriple d) : PairSiteConfig d :=
  pairSiteConfig (interpolatedSite T q) (T (zeroFields q.2.2 S))

@[simp] theorem pairSiteLeft_zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) (q : FieldTriple d) :
    pairSiteLeft (zeroHighPair T S q) = interpolatedSite T q := rfl

@[simp] theorem pairSiteRight_zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) (q : FieldTriple d) :
    pairSiteRight (zeroHighPair T S q) = T (zeroFields q.2.2 S) := rfl

theorem measurable_zeroFields (S : Finset (Site d)) :
    Measurable (fun xi : NonnegativeField d => zeroFields xi S) := by
  rw [measurable_pi_iff]
  intro x
  by_cases hx : x ∈ S
  · simp [zeroFields, hx]
  · simpa [zeroFields, hx] using
      (measurable_pi_apply x : Measurable (fun xi : NonnegativeField d => xi x))

theorem measurable_zeroHighPair (T : MonotoneAutomaton d)
    (S : Finset (Site d)) :
    Measurable (zeroHighPair T S : FieldTriple d → PairSiteConfig d) := by
  unfold zeroHighPair
  exact measurable_pairSiteConfig.comp
    ((measurable_interpolatedSite T).prodMk
      (T.measurable_toFun.comp
        ((measurable_zeroFields S).comp measurable_snd.snd)))



theorem measurableSet_pairHighCluster_eq_preimage
    (f g : FieldTriple d → PairSiteConfig d) (hf : Measurable f)
    (hg : Measurable g) (root : Site d) :
    MeasurableSet {q | pairHighCluster (f q) root =
      pairHighCluster (g q) root} := by
  have heq : {q : FieldTriple d | pairHighCluster (f q) root =
      pairHighCluster (g q) root} =
      ⋂ z : Site d,
        ((f ⁻¹' {omega | z ∈ pairHighCluster omega root}) ∩
          (g ⁻¹' {omega | z ∈ pairHighCluster omega root})) ∪
        ((f ⁻¹' {omega | z ∈ pairHighCluster omega root})ᶜ ∩
          (g ⁻¹' {omega | z ∈ pairHighCluster omega root})ᶜ) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union,
      Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · intro h z
      rw [h]
      by_cases hz : z ∈ pairHighCluster (g q) root
      · exact Or.inl ⟨hz, hz⟩
      · exact Or.inr ⟨hz, hz⟩
    · intro h
      ext z
      rcases h z with hz | hz
      · exact iff_of_true hz.1 hz.2
      · exact iff_of_false hz.1 hz.2
  rw [heq]
  apply MeasurableSet.iInter
  intro z
  have hfz := hf (measurableSet_pairHighConnected root z)
  have hgz := hg (measurableSet_pairHighConnected root z)
  exact (hfz.inter hgz).union (hfz.compl.inter hgz.compl)


noncomputable def step3Indices (N : ℕ) :
    Finset ((Finset (Site d) × Site d) × Site d) :=
  ((boxFinsetBK d N).powerset.product (boxFinsetBK d N)).product
    (boxFinsetBK d N)

def step3MaskMatches (T : MonotoneAutomaton d) (D N : ℕ)
    (M : Finset (Site d)) (q : FieldTriple d) : Prop :=
  ∀ z : Site d, z ∈ M ↔ z ∈ boxFinsetBK d N ∧
    ∃ a : Site d, a ∈ pairLowInfiniteVertices (zeroHighPair T M q) ∧
      l1dist d a z < D

theorem measurableSet_step3MaskMatches (T : MonotoneAutomaton d)
    (D N : ℕ) (M : Finset (Site d)) :
    MeasurableSet {q : FieldTriple d | step3MaskMatches T D N M q} := by
  have heq : {q : FieldTriple d | step3MaskMatches T D N M q} =
      ⋂ z : Site d, if z ∈ M then
        if z ∈ boxFinsetBK d N then
          ⋃ a : Site d, if l1dist d a z < D then
            (zeroHighPair T M) ⁻¹'
              {omega | a ∈ pairLowInfiniteVertices omega}
          else ∅
        else ∅
      else
        if z ∈ boxFinsetBK d N then
          (⋃ a : Site d, if l1dist d a z < D then
            (zeroHighPair T M) ⁻¹'
              {omega | a ∈ pairLowInfiniteVertices omega}
          else ∅)ᶜ
        else Set.univ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    unfold step3MaskMatches
    apply forall_congr'
    intro z
    by_cases hzM : z ∈ M
    · by_cases hzN : z ∈ boxFinsetBK d N
      · simp [hzM, hzN]
        aesop
      · simp [hzM, hzN]
    · by_cases hzN : z ∈ boxFinsetBK d N
      · simp [hzM, hzN]
        constructor
        · intro h i hi hmem
          exact (Nat.not_lt_of_ge (h i hmem)) hi
        · intro h x hx
          exact Nat.le_of_not_gt (fun hlt => h x hlt hx)
      · simp [hzM, hzN]
  rw [heq]
  apply MeasurableSet.iInter
  intro z
  split_ifs
  all_goals first
    | exact MeasurableSet.empty
    | exact MeasurableSet.univ
    | apply MeasurableSet.iUnion; intro a; split_ifs
      · exact (measurable_zeroHighPair T M)
          (measurableSet_pairLowInfinite a)
      · exact MeasurableSet.empty
    | apply MeasurableSet.compl; apply MeasurableSet.iUnion; intro a; split_ifs
      · exact (measurable_zeroHighPair T M)
          (measurableSet_pairLowInfinite a)
      · exact MeasurableSet.empty



def step3SourceEvent (T : MonotoneAutomaton d) (D N : ℕ)
    (i : (Finset (Site d) × Site d) × Site d) : Set (FieldTriple d) :=
  let M := i.1.1
  let x := i.1.2
  let y := i.2
  {q | step3MaskMatches T D N M q ∧
    (↑(contactForceSet x y) : Set (Site d)) ⊆ ↑M ∧
    l1dist d x y = D ∧
    x ∈ pairLowInfiniteVertices (zeroHighPair T M q) ∧
    y ∈ pairHighCluster (zeroHighPair T M q) 0 ∧
    zeroHighPair T (contactForceSet x y) q ∈
      pairDisjointInfiniteHighAt (0 : Site d) ∧
    pairHighCluster (zeroHighPair T (contactForceSet x y) q) 0 =
      pairHighCluster (zeroHighPair T M q) 0}

def step3TargetEvent (T : MonotoneAutomaton d) (D N : ℕ)
    (i : (Finset (Site d) × Site d) × Site d) : Set (FieldTriple d) :=
  step3SourceEvent T D N i ∩
    highThresholdOn T.threshold (contactForceSet i.1.2 i.2)

theorem measurableSet_step3SourceEvent (T : MonotoneAutomaton d)
    (D N : ℕ) (i : (Finset (Site d) × Site d) × Site d) :
    MeasurableSet (step3SourceEvent T D N i) := by
  let M := i.1.1
  let x := i.1.2
  let y := i.2
  by_cases hsub : (↑(contactForceSet x y) : Set (Site d)) ⊆ ↑M
  · by_cases hdist : l1dist d x y = D
    · have hmask := measurableSet_step3MaskMatches T D N M
      have hlow := (measurable_zeroHighPair T M)
        (measurableSet_pairLowInfinite x)
      have hhigh := (measurable_zeroHighPair T M)
        (measurableSet_pairHighConnected 0 y)
      have hdisjoint := (measurable_zeroHighPair T (contactForceSet x y))
        (measurableSet_pairDisjointInfiniteHighAt 0)
      have heq := measurableSet_pairHighCluster_eq_preimage
        (zeroHighPair T (contactForceSet x y)) (zeroHighPair T M)
        (measurable_zeroHighPair T (contactForceSet x y))
        (measurable_zeroHighPair T M) 0
      simpa only [step3SourceEvent, M, x, y, hsub, hdist, true_and] using
        hmask.inter (hlow.inter (hhigh.inter (hdisjoint.inter heq)))
    · have hempty : step3SourceEvent T D N i = ∅ := by
        ext q
        simp [step3SourceEvent, x, y, hdist]
      rw [hempty]
      exact MeasurableSet.empty
  · have hempty : step3SourceEvent T D N i = ∅ := by
      ext q
      simp [step3SourceEvent, M, x, y, hsub]
    rw [hempty]
    exact MeasurableSet.empty

theorem measurableSet_step3TargetEvent (T : MonotoneAutomaton d)
    (D N : ℕ) (i : (Finset (Site d) × Site d) × Site d) :
    MeasurableSet (step3TargetEvent T D N i) :=
  (measurableSet_step3SourceEvent T D N i).inter
    (measurableSet_highThresholdOn T.threshold (contactForceSet i.1.2 i.2))

theorem zeroFields_eq_of_eq_off (S : Finset (Site d))
    {xi xi' : NonnegativeField d}
    (h : ∀ z ∉ S, xi z = xi' z) : zeroFields xi S = zeroFields xi' S := by
  funext z
  by_cases hz : z ∈ S
  · simp [zeroFields, hz]
  · simp [zeroFields, hz, h z hz]

theorem zeroHighPair_eq_of_eq_off (T : MonotoneAutomaton d)
    (S : Finset (Site d)) {q q' : FieldTriple d}
    (hlow : q.1 = q'.1) (hmiddle : q.2.1 = q'.2.1)
    (hhigh : ∀ z ∉ S, q.2.2 z = q'.2.2 z) :
    zeroHighPair T S q = zeroHighPair T S q' := by
  unfold zeroHighPair
  congr 1
  · unfold interpolatedSite
    funext z
    rw [hlow, hmiddle]
  · rw [zeroFields_eq_of_eq_off S hhigh]



theorem step3SourceEvent_ignoresHigh (T : MonotoneAutomaton d) (D N : ℕ)
    (i : (Finset (Site d) × Site d) × Site d) :
    TripleEventIgnoresHighOn (contactForceSet i.1.2 i.2)
      (step3SourceEvent T D N i) := by
  intro q q' hlow hmiddle hhigh
  by_cases hsub : (↑(contactForceSet i.1.2 i.2) : Set (Site d)) ⊆ ↑i.1.1
  · have hforce : zeroHighPair T (contactForceSet i.1.2 i.2) q =
        zeroHighPair T (contactForceSet i.1.2 i.2) q' :=
      zeroHighPair_eq_of_eq_off T _ hlow hmiddle hhigh
    have hMoff : ∀ z ∉ i.1.1, q.2.2 z = q'.2.2 z := by
      intro z hzM
      apply hhigh z
      exact fun hzF => hzM (hsub hzF)
    have hbase : zeroHighPair T i.1.1 q = zeroHighPair T i.1.1 q' :=
      zeroHighPair_eq_of_eq_off T i.1.1 hlow hmiddle hMoff
    have hmask : step3MaskMatches T D N i.1.1 q ↔
        step3MaskMatches T D N i.1.1 q' := by
      unfold step3MaskMatches
      rw [hbase]
    simp only [step3SourceEvent, Set.mem_setOf_eq]
    rw [hforce, hbase]
    exact and_congr hmask Iff.rfl
  · have hq : q ∉ step3SourceEvent T D N i := by
      simp [step3SourceEvent, hsub]
    have hq' : q' ∉ step3SourceEvent T D N i := by
      simp [step3SourceEvent, hsub]
    exact iff_of_false hq hq'

@[simp] theorem pairLowInfiniteVertices_zeroHighPair
    (T : MonotoneAutomaton d) (S : Finset (Site d)) (q : FieldTriple d) :
    pairLowInfiniteVertices (zeroHighPair T S q) =
      pairLowInfiniteVertices (interpolatedHighPair T q) := rfl

theorem pairHighCluster_zeroHighPair_eq_siteCluster
    (T : MonotoneAutomaton d) (S : Finset (Site d))
    (q : FieldTriple d) (x : Site d) :
    pairHighCluster (zeroHighPair T S q) x =
      siteCluster (T (zeroFields q.2.2 S)) x := by
  ext z
  exact connected_siteToBond_iff _ _ _

theorem site_eq_true_of_pairHighCluster_infinite
    (omega : PairSiteConfig d) (x : Site d)
    (hinf : (pairHighCluster omega x).Infinite) :
    pairSiteRight omega x = true := by
  apply site_eq_true_of_siteCluster_infinite
  have heq : siteCluster (pairSiteRight omega) x =
      pairHighCluster omega x := by
    ext z
    exact (connected_siteToBond_iff (pairSiteRight omega) x z).symm
  rw [heq]
  exact hinf





theorem step3TargetEvent_forceSets_inter_nonempty
    (T : MonotoneAutomaton d) (D N : ℕ) (q : FieldTriple d)
    {i j : (Finset (Site d) × Site d) × Site d}
    (hi : q ∈ step3TargetEvent T D N i)
    (hj : q ∈ step3TargetEvent T D N j) :
    (contactForceSet i.1.2 i.2 ∩ contactForceSet j.1.2 j.2).Nonempty := by
  classical
  rcases hi with ⟨hiSource, hiThreshold⟩
  rcases hj with ⟨hjSource, hjThreshold⟩
  rcases hiSource with
    ⟨hiMask, hiSub, hiDist, hix, hiy, hiDisjoint, hiClusterEq⟩
  rcases hjSource with
    ⟨hjMask, hjSub, hjDist, hjx, hjy, hjDisjoint, hjClusterEq⟩
  by_contra hinter
  have hdisj : Disjoint (contactForceSet i.1.2 i.2)
      (contactForceSet j.1.2 j.2) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.mp hinter
  have hmaskEq : i.1.1 = j.1.1 := by
    ext z
    rw [hiMask z, hjMask z]
    simp only [pairLowInfiniteVertices_zeroHighPair]
  have hjy' : j.2 ∈
      pairHighCluster (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0 := by
    rw [hiClusterEq, hmaskEq]
    exact hjy
  have hinfI : (pairHighCluster
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0).Infinite :=
    hiDisjoint.1
  have hyCluster : pairHighCluster
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) j.2 =
      pairHighCluster
        (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0 :=
    pairHighCluster_eq_of_mem hjy'
  have hyOpen : T (zeroFields q.2.2 (contactForceSet i.1.2 i.2)) j.2 = true := by
    change pairSiteRight
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) j.2 = true
    apply site_eq_true_of_pairHighCluster_infinite
    rw [hyCluster]
    exact hinfI
  have hforceOpen : ∀ z ∈ contactForceSet j.1.2 j.2,
      T (zeroFields q.2.2 (contactForceSet i.1.2 i.2)) z = true := by
    intro z hzj
    apply T.occupationThreshold
    have hzi : z ∉ contactForceSet i.1.2 i.2 := by
      exact fun hzi => Finset.disjoint_left.mp hdisj hzi hzj
    simpa [zeroFields, hzi] using hjThreshold z hzj
  have hconn : Connected d
      (siteToBond (T (zeroFields q.2.2 (contactForceSet i.1.2 i.2))))
      j.1.2 j.2 :=
    connected_siteToBond_of_contactForceSet _ _ _ hyOpen hforceOpen
  have hxHigh : j.1.2 ∈
      pairHighCluster (zeroHighPair T (contactForceSet i.1.2 i.2) q) 0 := by
    exact hjy'.trans hconn.symm
  have hxLow : j.1.2 ∈ pairLowInfiniteVertices
      (zeroHighPair T (contactForceSet i.1.2 i.2) q) := by
    simpa only [pairLowInfiniteVertices_zeroHighPair] using hjx
  exact hiDisjoint.2 ⟨j.1.2, hxHigh, hxLow⟩



noncomputable def shiftedBoxFinset (z : Site d) (D : ℕ) : Finset (Site d) :=
  (boxFinsetBK d D).image fun w => z + w

theorem mem_shiftedBoxFinset_of_l1dist_le {z x : Site d} {D : ℕ}
    (h : l1dist d z x ≤ D) : x ∈ shiftedBoxFinset z D := by
  classical
  rw [shiftedBoxFinset, Finset.mem_image]
  refine ⟨x - z, ?_, by simp⟩
  rw [mem_boxFinsetBK_iff]
  intro k
  have hterm : (z k - x k).natAbs ≤ l1dist d z x := by
    unfold l1dist
    exact Finset.single_le_sum
      (f := fun j : Fin d => (z j - x j).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have habs : (x k - z k).natAbs = (z k - x k).natAbs := by
    rw [← Int.natAbs_neg]
    congr 1
    ring
  simpa [Pi.sub_apply, habs] using hterm.trans h

theorem shiftedBoxFinset_card_le (z : Site d) (D : ℕ) :
    (shiftedBoxFinset z D).card ≤ (boxFinsetBK d D).card := by
  classical
  exact Finset.card_image_le

theorem contactForceSet_card_le_box {x y : Site d} {D : ℕ}
    (hxy : l1dist d x y = D) :
    (contactForceSet x y).card ≤ (boxFinsetBK d D).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun z : Site d => z - x)
  · intro z hz
    change z - x ∈ boxFinsetBK d D
    rw [mem_boxFinsetBK_iff]
    have hzBetween := (mem_contactForceSet.mp hz).1
    have hdist : l1dist d x z ≤ D :=
      (coordinateBetween_l1dist_le hzBetween).trans_eq hxy
    intro k
    have hterm : (x k - z k).natAbs ≤ l1dist d x z := by
      unfold l1dist
      exact Finset.single_le_sum
        (f := fun j : Fin d => (x j - z j).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have habs : (z k - x k).natAbs = (x k - z k).natAbs := by
      rw [← Int.natAbs_neg]
      congr 1
      ring
    simpa [Pi.sub_apply, habs] using hterm.trans hdist
  · intro a ha b hb hab
    have h := congrArg (fun w : Site d => w + x) hab
    simpa using h



noncomputable def contactOverlapPairs
    (i : (Finset (Site d) × Site d) × Site d) (D : ℕ) :
    Finset (Site d × Site d) :=
  (contactForceSet i.1.2 i.2).biUnion fun z =>
    (shiftedBoxFinset z D).product (shiftedBoxFinset z D)

theorem contactOverlapPairs_card_le
    (i : (Finset (Site d) × Site d) × Site d) (D : ℕ)
    (hiDist : l1dist d i.1.2 i.2 = D) :
    (contactOverlapPairs i D).card ≤ (boxFinsetBK d D).card ^ 3 := by
  classical
  let B := (boxFinsetBK d D).card
  calc
    (contactOverlapPairs i D).card ≤
        ∑ z ∈ contactForceSet i.1.2 i.2,
          ((shiftedBoxFinset z D).product (shiftedBoxFinset z D)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ contactForceSet i.1.2 i.2, B * B := by
      apply Finset.sum_le_sum
      intro z hz
      calc
        ((shiftedBoxFinset z D).product
            (shiftedBoxFinset z D)).card =
            (shiftedBoxFinset z D).card *
              (shiftedBoxFinset z D).card :=
          Finset.card_product _ _
        _ ≤ B * B := by
          dsimp only [B]
          exact Nat.mul_le_mul (shiftedBoxFinset_card_le z D)
            (shiftedBoxFinset_card_le z D)
    _ = (contactForceSet i.1.2 i.2).card * (B * B) := by simp
    _ ≤ B * (B * B) := by
      gcongr
      exact contactForceSet_card_le_box hiDist
    _ = (boxFinsetBK d D).card ^ 3 := by
      simp only [B]
      ring

theorem step3TargetMultiplicity_le (T : MonotoneAutomaton d) (D N : ℕ)
    (q : FieldTriple d) :
    finiteEventMultiplicity (step3Indices (d := d) N)
      (step3TargetEvent T D N) q ≤ (boxFinsetBK d D).card ^ 3 := by
  classical
  let F := (step3Indices (d := d) N).filter fun i =>
    q ∈ step3TargetEvent T D N i
  change F.card ≤ (boxFinsetBK d D).card ^ 3
  by_cases hF : F.Nonempty
  · obtain ⟨i, hiF⟩ := hF
    have hiTarget : q ∈ step3TargetEvent T D N i :=
      (Finset.mem_filter.mp hiF).2
    have hiDist : l1dist d i.1.2 i.2 = D := hiTarget.1.2.2.1
    calc
      F.card ≤ (contactOverlapPairs i D).card := by
        apply (Finset.card_le_card_of_injOn
          (fun j : (Finset (Site d) × Site d) × Site d => (j.1.2, j.2))
          (s := F) (t := contactOverlapPairs i D))
        · intro j hjF
          have hjTarget : q ∈ step3TargetEvent T D N j :=
            (Finset.mem_filter.mp hjF).2
          obtain ⟨z, hz⟩ :=
            step3TargetEvent_forceSets_inter_nonempty T D N q hiTarget hjTarget
          have hzi : z ∈ contactForceSet i.1.2 i.2 :=
            (Finset.mem_inter.mp hz).1
          have hzj : z ∈ contactForceSet j.1.2 j.2 :=
            (Finset.mem_inter.mp hz).2
          change (j.1.2, j.2) ∈ contactOverlapPairs i D
          rw [contactOverlapPairs, Finset.mem_biUnion]
          refine ⟨z, hzi, ?_⟩
          apply Finset.mem_product.mpr
          have hzBetween := (mem_contactForceSet.mp hzj).1
          have hjDist : l1dist d j.1.2 j.2 = D := hjTarget.1.2.2.1
          constructor
          · apply mem_shiftedBoxFinset_of_l1dist_le
            rw [← l1dist_comm]
            exact (coordinateBetween_l1dist_le hzBetween).trans_eq hjDist
          · apply mem_shiftedBoxFinset_of_l1dist_le
            have hzSymm : z ∈ coordinateBetween j.2 j.1.2 := by
              intro k
              simpa [coordinateBetween, min_comm, max_comm] using hzBetween k
            rw [← l1dist_comm]
            exact (coordinateBetween_l1dist_le hzSymm).trans_eq
              ((l1dist_comm d j.2 j.1.2).trans hjDist)
        · intro j hjF k hkF heq
          have hjTarget : q ∈ step3TargetEvent T D N j :=
            (Finset.mem_filter.mp hjF).2
          have hkTarget : q ∈ step3TargetEvent T D N k :=
            (Finset.mem_filter.mp hkF).2
          have hcontacts : j.1.2 = k.1.2 ∧ j.2 = k.2 := by
            exact Prod.mk.inj heq
          have hmask : j.1.1 = k.1.1 := by
            ext z
            rw [hjTarget.1.1 z, hkTarget.1.1 z]
            simp only [pairLowInfiniteVertices_zeroHighPair]
          apply Prod.ext
          · apply Prod.ext
            · exact hmask
            · exact hcontacts.1
          · exact hcontacts.2
      _ ≤ (boxFinsetBK d D).card ^ 3 :=
        contactOverlapPairs_card_le i D hiDist
  · simp only [Finset.not_nonempty_iff_eq_empty] at hF
    rw [hF]
    simp



theorem highInsertionLowerBound_le_one
    (mu : Measure (FieldTriple d)) [IsProbabilityMeasure mu]
    (t : NNReal) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu t epsilon) : epsilon ≤ 1 := by
  have hignore : TripleEventIgnoresHighAt (0 : Site d)
      (Set.univ : Set (FieldTriple d)) := by
    intro q q' hlow hmiddle hhigh
    simp
  have h := hinsert (0 : Site d) Set.univ MeasurableSet.univ hignore
  have htarget : mu (Set.univ ∩
      {q : FieldTriple d | t ≤ q.2.2 (0 : Site d)}) ≤ 1 := by
    calc
      mu (Set.univ ∩ {q : FieldTriple d | t ≤ q.2.2 (0 : Site d)}) ≤
          mu Set.univ := measure_mono (Set.inter_subset_left)
      _ = 1 := measure_univ
  simpa only [measure_univ, mul_one] using h.trans htarget

theorem step3SourceTarget_transfer
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D N : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon)
    (i : (Finset (Site d) × Site d) × Site d) :
    epsilon ^ (boxFinsetBK d D).card * mu (step3SourceEvent T D N i) ≤
      mu (step3TargetEvent T D N i) := by
  by_cases hdist : l1dist d i.1.2 i.2 = D
  · have hcard : (contactForceSet i.1.2 i.2).card ≤
        (boxFinsetBK d D).card := contactForceSet_card_le_box hdist
    have hepsilon : epsilon ≤ 1 :=
      highInsertionLowerBound_le_one mu T.threshold epsilon hinsert
    have hpow : epsilon ^ (boxFinsetBK d D).card ≤
        epsilon ^ (contactForceSet i.1.2 i.2).card :=
      pow_le_pow_of_le_one (by positivity) hepsilon hcard
    calc
      epsilon ^ (boxFinsetBK d D).card *
          mu (step3SourceEvent T D N i) ≤
          epsilon ^ (contactForceSet i.1.2 i.2).card *
            mu (step3SourceEvent T D N i) := by gcongr
      _ ≤ mu (step3SourceEvent T D N i ∩
          highThresholdOn T.threshold (contactForceSet i.1.2 i.2)) :=
        highInsertionLowerBound_finset mu T.threshold epsilon hinsert _ _
          (measurableSet_step3SourceEvent T D N i)
          (step3SourceEvent_ignoresHigh T D N i)
      _ = mu (step3TargetEvent T D N i) := rfl
  · have hempty : step3SourceEvent T D N i = ∅ := by
      ext q
      simp [step3SourceEvent, hdist]
    rw [hempty]
    simp

theorem measurable_finiteEventMultiplicity_countable
    {Omega I : Type*} [MeasurableSpace Omega] [Countable I]
    (J : Finset I) (A : I → Set Omega)
    (hA : ∀ i ∈ J, MeasurableSet (A i)) :
    Measurable (finiteEventMultiplicity J A) := by
  classical
  let p : Omega → I → Prop := fun omega i => i ∈ J ∧ omega ∈ A i
  have hp : ∀ i, Measurable (fun omega => p omega i) := by
    intro i
    by_cases hi : i ∈ J
    · simpa [p, hi] using measurable_mem.mpr (hA i hi)
    · simp [p, hi]
  have hset : Measurable (fun omega : Omega => {i | p omega i}) :=
    measurable_setOf.comp (measurable_pi_lambda _ hp)
  have hncard : Measurable (fun omega : Omega => Set.ncard {i | p omega i}) :=
    measurable_ncard.comp hset
  convert hncard using 1
  funext omega
  unfold finiteEventMultiplicity
  let S : Set I := {i | p omega i}
  have hS : S.Finite := by
    apply J.finite_toSet.subset
    intro i hi
    exact hi.1
  rw [Set.ncard_eq_toFinset_card S hS]
  congr 1
  ext i
  simp [S, p]

theorem measurableSet_step3SourceDegree (T : MonotoneAutomaton d)
    (D N K : ℕ) : MeasurableSet {q : FieldTriple d |
      K ≤ finiteEventMultiplicity (step3Indices (d := d) N)
        (step3SourceEvent T D N) q} := by
  exact (measurable_finiteEventMultiplicity_countable
    (step3Indices (d := d) N) (step3SourceEvent T D N)
    (fun i _ => measurableSet_step3SourceEvent T D N i))
      measurableSet_Ici

theorem step3FiniteWindow_probability_bound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D N K : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon)
    (E : Set (FieldTriple d)) (hEmeas : MeasurableSet E)
    (hdegree : ∀ q ∈ E, K ≤ finiteEventMultiplicity
      (step3Indices (d := d) N) (step3SourceEvent T D N) q) :
    epsilon ^ (boxFinsetBK d D).card * K * mu E ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
  apply finiteEventMultivalued_probability_bound mu
    (step3Indices (d := d) N) (step3SourceEvent T D N)
    (step3TargetEvent T D N)
    (fun i _ => measurableSet_step3SourceEvent T D N i)
    (fun i _ => measurableSet_step3TargetEvent T D N i)
    E hEmeas (epsilon ^ (boxFinsetBK d D).card) K
    ((boxFinsetBK d D).card ^ 3) hdegree
    (step3TargetMultiplicity_le T D N)
  intro i hi
  exact step3SourceTarget_transfer T mu D N epsilon hinsert i





def pairStep3DistanceAt (root : Site d) (D : ℕ) : Set (PairSiteConfig d) :=
  pairStep3CoreAt root ∩
    {omega | ∀ y ∈ pairHighCluster omega root,
      ∀ x ∈ pairLowInfiniteVertices omega, D ≤ l1dist d y x} ∩
    {omega | ∃ y ∈ pairHighCluster omega root,
      ∃ x ∈ pairLowInfiniteVertices omega, l1dist d y x = D}

theorem measurableSet_pairStep3DistanceAt (root : Site d) (D : ℕ) :
    MeasurableSet (pairStep3DistanceAt root D) := by
  have hatLeast : MeasurableSet {omega : PairSiteConfig d |
      ∀ y ∈ pairHighCluster omega root,
      ∀ x ∈ pairLowInfiniteVertices omega, D ≤ l1dist d y x} := by
    have heq : {omega : PairSiteConfig d |
        ∀ y ∈ pairHighCluster omega root,
        ∀ x ∈ pairLowInfiniteVertices omega, D ≤ l1dist d y x} =
        ⋂ y : Site d, ⋂ x : Site d,
          if D ≤ l1dist d y x then Set.univ else
            {omega | y ∈ pairHighCluster omega root}ᶜ ∪
              {omega | x ∈ pairLowInfiniteVertices omega}ᶜ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h y x
        split_ifs with hD
        · trivial
        · by_cases hy : y ∈ pairHighCluster omega root
          · exact Or.inr (fun hx => hD (h y hy x hx))
          · exact Or.inl hy
      · intro h y hy x hx
        have := h y x
        split_ifs at this with hD
        · exact hD
        · exact (this.elim (fun hny => hny hy) (fun hnx => hnx hx)).elim
    rw [heq]
    exact MeasurableSet.iInter fun y => MeasurableSet.iInter fun x => by
      split_ifs
      · exact MeasurableSet.univ
      · exact (measurableSet_pairHighConnected root y).compl.union
          (measurableSet_pairLowInfinite x).compl
  have hattained : MeasurableSet {omega : PairSiteConfig d |
      ∃ y ∈ pairHighCluster omega root,
      ∃ x ∈ pairLowInfiniteVertices omega, l1dist d y x = D} := by
    have heq : {omega : PairSiteConfig d |
        ∃ y ∈ pairHighCluster omega root,
        ∃ x ∈ pairLowInfiniteVertices omega, l1dist d y x = D} =
        ⋃ y : Site d, ⋃ x : Site d,
          if l1dist d y x = D then
            {omega | y ∈ pairHighCluster omega root} ∩
              {omega | x ∈ pairLowInfiniteVertices omega}
          else ∅ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      aesop
    rw [heq]
    exact MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun x => by
      split_ifs
      · exact (measurableSet_pairHighConnected root y).inter
          (measurableSet_pairLowInfinite x)
      · exact MeasurableSet.empty
  exact ((measurableSet_pairStep3CoreAt root).inter hatLeast).inter hattained

theorem pairStep3CoreAt_eq_iUnion_distance (root : Site d) :
    pairStep3CoreAt root = ⋃ D : ℕ, pairStep3DistanceAt root D := by
  ext omega
  constructor
  · intro hcore
    have hnearest : (pairNearestHighSet omega root).Nonempty :=
      hcore.2.nonempty
    obtain ⟨y, hy⟩ := hnearest
    rcases hy with ⟨hyCluster, x, hxLow, hxy⟩
    apply Set.mem_iUnion.mpr
    refine ⟨l1dist d y x, ?_⟩
    refine ⟨⟨hcore, ?_⟩, y, hyCluster, x, hxLow, rfl⟩
    intro z hz a ha
    rw [hxy]
    exact Nat.sInf_le ⟨z, hz, a, ha, rfl⟩
  · intro h
    obtain ⟨D, hD⟩ := Set.mem_iUnion.mp h
    exact hD.1.1

def step3ContactEvent (T : MonotoneAutomaton d) (D : ℕ)
    (p : Site d × Site d) : Set (FieldTriple d) :=
  {q | p.1 ∈ pairLowInfiniteVertices (interpolatedHighPair T q) ∧
    p.2 ∈ pairNearestHighSet (interpolatedHighPair T q) 0 ∧
    l1dist d p.1 p.2 = D}

theorem measurableSet_step3ContactEvent (T : MonotoneAutomaton d)
    (D : ℕ) (p : Site d × Site d) :
    MeasurableSet (step3ContactEvent T D p) := by
  by_cases hdist : l1dist d p.1 p.2 = D
  · have heq : step3ContactEvent T D p =
        {q | p.1 ∈ pairLowInfiniteVertices (interpolatedHighPair T q)} ∩
          {q | p.2 ∈ pairNearestHighSet (interpolatedHighPair T q) 0} := by
      ext q
      simp [step3ContactEvent, hdist]
    rw [heq]
    exact ((measurable_interpolatedHighPair T)
      (measurableSet_pairLowInfinite p.1)).inter
        ((measurable_interpolatedHighPair T)
          (measurableSet_pairNearestHighSet 0 p.2))
  · have hempty : step3ContactEvent T D p = ∅ := by
      ext q
      simp [step3ContactEvent, hdist]
    rw [hempty]
    exact MeasurableSet.empty

noncomputable def step3WindowContacts (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) : Finset (Site d × Site d) :=
  by
    classical
    exact ((boxFinsetBK d N).product (boxFinsetBK d N)).filter fun p =>
      q ∈ step3ContactEvent T D p

def step3CoreWindowEvent (T : MonotoneAutomaton d) (D N K : ℕ) :
    Set (FieldTriple d) :=
  (interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D ∩
    {q | K ≤ (step3WindowContacts T D N q).card}

theorem measurableSet_step3CoreWindowEvent (T : MonotoneAutomaton d)
    (D N K : ℕ) : MeasurableSet (step3CoreWindowEvent T D N K) := by
  have hfirst := (measurable_interpolatedHighPair T)
    (measurableSet_pairStep3DistanceAt 0 D)
  have hmult : Measurable (fun q : FieldTriple d =>
      finiteEventMultiplicity
        ((boxFinsetBK d N).product (boxFinsetBK d N))
        (step3ContactEvent T D) q) :=
    measurable_finiteEventMultiplicity_countable _ _
      (fun p _ => measurableSet_step3ContactEvent T D p)
  have heq : (fun q : FieldTriple d => (step3WindowContacts T D N q).card) =
      finiteEventMultiplicity
        ((boxFinsetBK d N).product (boxFinsetBK d N))
        (step3ContactEvent T D) := by
    funext q
    classical
    rfl
  rw [step3CoreWindowEvent]
  apply hfirst.inter
  have hset : {q : FieldTriple d | K ≤ (step3WindowContacts T D N q).card} =
      {q | K ≤ finiteEventMultiplicity
        ((boxFinsetBK d N).product (boxFinsetBK d N))
        (step3ContactEvent T D) q} := by
    ext q
    exact (congrArg (fun f => K ≤ f q) heq).to_iff
  rw [hset]
  exact hmult measurableSet_Ici

theorem boxFinsetBK_mono {N M : ℕ} (hNM : N ≤ M) :
    boxFinsetBK d N ⊆ boxFinsetBK d M := by
  intro x hx
  rw [mem_boxFinsetBK_iff] at hx ⊢
  exact box_mono d hNM hx

theorem step3WindowContacts_card_mono (T : MonotoneAutomaton d)
    (D : ℕ) {N M : ℕ} (hNM : N ≤ M) (q : FieldTriple d) :
    (step3WindowContacts T D N q).card ≤
      (step3WindowContacts T D M q).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  change p ∈ step3WindowContacts T D N q at hp
  have hpMem : p ∈ ((boxFinsetBK d N).product
      (boxFinsetBK d N)).filter
        (fun p => q ∈ step3ContactEvent T D p) := by
    simpa [step3WindowContacts] using hp
  have hp' := Finset.mem_filter.mp hpMem
  have hpBox := Finset.mem_product.mp hp'.1
  rw [step3WindowContacts, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr
    ⟨boxFinsetBK_mono hNM hpBox.1, boxFinsetBK_mono hNM hpBox.2⟩, hp'.2⟩

theorem step3CoreWindowEvent_mono (T : MonotoneAutomaton d) (D K : ℕ) :
    Monotone (fun N => step3CoreWindowEvent T D N K) := by
  intro N M hNM q hq
  exact ⟨hq.1, hq.2.trans (step3WindowContacts_card_mono T D hNM q)⟩

theorem exists_low_contact_distance_of_mem_nearest
    {omega : PairSiteConfig d} {root y : Site d} {D : ℕ}
    (hD : omega ∈ pairStep3DistanceAt root D)
    (hy : y ∈ pairNearestHighSet omega root) :
    ∃ x ∈ pairLowInfiniteVertices omega, l1dist d x y = D := by
  rcases hy with ⟨hyCluster, x, hxLow, hxy⟩
  rcases hD.2 with ⟨z, hzCluster, a, haLow, hza⟩
  have hsetLe : setL1Distance (pairHighCluster omega root)
      (pairLowInfiniteVertices omega) ≤ D := by
    rw [← hza]
    exact Nat.sInf_le ⟨z, hzCluster, a, haLow, rfl⟩
  have hDLe : D ≤ setL1Distance (pairHighCluster omega root)
      (pairLowInfiniteVertices omega) := by
    rw [← hxy]
    exact hD.1.2 y hyCluster x hxLow
  refine ⟨x, hxLow, ?_⟩
  rw [l1dist_comm, hxy, le_antisymm hsetLe hDLe]

theorem step3Distance_preimage_eq_iUnion_windows
    (T : MonotoneAutomaton d) (D K : ℕ) :
    (interpolatedHighPair T) ⁻¹' pairStep3DistanceAt (0 : Site d) D =
      ⋃ N : ℕ, step3CoreWindowEvent T D N K := by
  classical
  ext q
  constructor
  · intro hq
    have hinf : (pairNearestHighSet (interpolatedHighPair T q) 0).Infinite :=
      hq.1.1.2
    obtain ⟨Y, hYsub, hYcard⟩ := hinf.exists_subset_card_eq K
    let xOf : Site d → Site d := fun y =>
      if hy : y ∈ Y then Classical.choose
        (exists_low_contact_distance_of_mem_nearest hq (hYsub hy)) else 0
    have hxOf (y : Site d) (hy : y ∈ Y) :
        xOf y ∈ pairLowInfiniteVertices (interpolatedHighPair T q) ∧
          l1dist d (xOf y) y = D := by
      dsimp only [xOf]
      rw [dif_pos hy]
      exact Classical.choose_spec
        (exists_low_contact_distance_of_mem_nearest hq (hYsub hy))
    let F : Finset (Site d) := Y.image xOf ∪ Y
    obtain ⟨N, hN⟩ := StatMech.Lattice.finite_subset_box
      (↑F : Set (Site d)) F.finite_toSet
    apply Set.mem_iUnion.mpr
    refine ⟨N, hq, ?_⟩
    rw [← hYcard]
    let G : Finset (Site d × Site d) := Y.image fun y => (xOf y, y)
    have hGcard : G.card = Y.card := by
      apply Finset.card_image_of_injective
      intro y z hyz
      exact congrArg Prod.snd hyz
    rw [← hGcard]
    apply Finset.card_le_card
    intro p hp
    change p ∈ Y.image (fun y => (xOf y, y)) at hp
    rw [Finset.mem_image] at hp
    obtain ⟨y, hyY, rfl⟩ := hp
    rw [step3WindowContacts, Finset.mem_filter]
    have hyF : y ∈ F := Finset.mem_union_right _ hyY
    have hxF : xOf y ∈ F :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem xOf hyY)
    have hyBox : y ∈ boxFinsetBK d N := by
      rw [mem_boxFinsetBK_iff]
      exact hN hyF
    have hxBox : xOf y ∈ boxFinsetBK d N := by
      rw [mem_boxFinsetBK_iff]
      exact hN hxF
    refine ⟨Finset.mem_product.mpr ⟨hxBox, hyBox⟩, ?_⟩
    exact ⟨(hxOf y hyY).1, hYsub hyY, (hxOf y hyY).2⟩
  · intro hq
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hq
    exact hN.1



noncomputable def step3WindowMask (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) : Finset (Site d) := by
  classical
  exact (boxFinsetBK d N).filter fun z => ∃ x : Site d,
    x ∈ pairLowInfiniteVertices (interpolatedHighPair T q) ∧
      l1dist d x z < D

theorem step3WindowMask_subset_box (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) :
    step3WindowMask T D N q ⊆ boxFinsetBK d N := by
  classical
  intro z hz
  exact (Finset.mem_filter.mp hz).1

theorem step3WindowMask_matches (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) :
    step3MaskMatches T D N (step3WindowMask T D N q) q := by
  classical
  intro z
  rw [step3WindowMask, Finset.mem_filter]
  simp only [pairLowInfiniteVertices_zeroHighPair]

theorem coordinateBetween_mem_box {x y z : Site d} {N : ℕ}
    (hx : x ∈ box d N) (hy : y ∈ box d N)
    (hz : z ∈ coordinateBetween x y) : z ∈ box d N := by
  intro k
  have hxk := hx k
  have hyk := hy k
  have hzk := hz k
  rcases le_total (x k) (y k) with hxy | hyx
  · simp only [min_eq_left hxy, max_eq_right hxy] at hzk
    push_cast at hxk hyk ⊢
    omega
  · simp only [min_eq_right hyx, max_eq_left hyx] at hzk
    push_cast at hxk hyk ⊢
    omega

theorem pairHighCluster_interpolatedHighPair_eq_siteCluster
    (T : MonotoneAutomaton d) (q : FieldTriple d) (x : Site d) :
    pairHighCluster (interpolatedHighPair T q) x = siteCluster (T q.2.2) x := by
  ext z
  exact connected_siteToBond_iff _ _ _

theorem step3Contact_forceSet_subset_mask
    (T : MonotoneAutomaton d) (D N : ℕ) (q : FieldTriple d)
    {x y : Site d}
    (hxBox : x ∈ boxFinsetBK d N) (hyBox : y ∈ boxFinsetBK d N)
    (hxLow : x ∈ pairLowInfiniteVertices (interpolatedHighPair T q))
    (hxy : l1dist d x y = D) :
    contactForceSet x y ⊆ step3WindowMask T D N q := by
  classical
  intro z hz
  rw [step3WindowMask, Finset.mem_filter]
  have hzBetween := (mem_contactForceSet.mp hz).1
  have hzne := (mem_contactForceSet.mp hz).2
  have hzLe : l1dist d x z ≤ D :=
    (coordinateBetween_l1dist_le hzBetween).trans_eq hxy
  have hzLt : l1dist d x z < D := by
    exact lt_of_le_of_ne hzLe (fun heq => hzne
      (eq_right_of_mem_coordinateBetween_of_l1dist_eq hzBetween
        (heq.trans hxy.symm)))
  have hx' := mem_boxFinsetBK_iff.mp hxBox
  have hy' := mem_boxFinsetBK_iff.mp hyBox
  exact ⟨mem_boxFinsetBK_iff.mpr (coordinateBetween_mem_box hx' hy' hzBetween),
    x, hxLow, hzLt⟩

theorem contactForceSet_l1dist_lt {x y z : Site d} {D : ℕ}
    (hxy : l1dist d x y = D) (hz : z ∈ contactForceSet x y) :
    l1dist d x z < D := by
  have hzBetween := (mem_contactForceSet.mp hz).1
  have hzne := (mem_contactForceSet.mp hz).2
  have hzLe : l1dist d x z ≤ D :=
    (coordinateBetween_l1dist_le hzBetween).trans_eq hxy
  exact lt_of_le_of_ne hzLe (fun heq => hzne
    (eq_right_of_mem_coordinateBetween_of_l1dist_eq hzBetween
      (heq.trans hxy.symm)))

theorem step3Deletion_cluster_eq_original
    (T : MonotoneAutomaton d) (D : ℕ) (q : FieldTriple d)
    (hD : interpolatedHighPair T q ∈ pairStep3DistanceAt (0 : Site d) D)
    (S : Finset (Site d))
    (hnear : ∀ z ∈ S, ∃ x ∈
      pairLowInfiniteVertices (interpolatedHighPair T q), l1dist d x z < D) :
    pairHighCluster (zeroHighPair T S q) 0 =
      pairHighCluster (interpolatedHighPair T q) 0 := by
  have hinfPair :
      (pairHighCluster (interpolatedHighPair T q) 0).Infinite :=
    hD.1.1.1.1
  have hinfSite : (siteCluster (T q.2.2) 0).Infinite := by
    rw [← pairHighCluster_interpolatedHighPair_eq_siteCluster]
    exact hinfPair
  have havoid : ∀ z ∈ S, z ∉ siteCluster (T q.2.2) 0 := by
    intro z hzS hzCluster
    obtain ⟨x, hxLow, hxz⟩ := hnear z hzS
    have hzPair : z ∈ pairHighCluster (interpolatedHighPair T q) 0 := by
      rw [pairHighCluster_interpolatedHighPair_eq_siteCluster]
      exact hzCluster
    have hlower := hD.1.2 z hzPair x hxLow
    exact (Nat.not_lt_of_ge hlower) (by simpa [l1dist_comm] using hxz)
  rw [pairHighCluster_zeroHighPair_eq_siteCluster,
    pairHighCluster_interpolatedHighPair_eq_siteCluster]
  exact siteCluster_zeroFields_eq_of_final_infinite_of_avoids
    T q.2.2 S 0 hinfSite havoid

theorem step3Contact_gives_source
    (T : MonotoneAutomaton d) (D N : ℕ) (q : FieldTriple d)
    (hD : interpolatedHighPair T q ∈ pairStep3DistanceAt (0 : Site d) D)
    {x y : Site d}
    (hcontact : (x, y) ∈ step3WindowContacts T D N q) :
    q ∈ step3SourceEvent T D N
      ((step3WindowMask T D N q, x), y) := by
  classical
  have hcontact' := Finset.mem_filter.mp hcontact
  have hboxes := Finset.mem_product.mp hcontact'.1
  rcases hcontact'.2 with ⟨hxLow, hyNearest, hxy⟩
  have hforceSub := step3Contact_forceSet_subset_mask T D N q
    hboxes.1 hboxes.2 hxLow hxy
  have hbaseEq := step3Deletion_cluster_eq_original T D q hD
    (step3WindowMask T D N q) (by
      intro z hz
      exact (Finset.mem_filter.mp hz).2)
  have hforceEq := step3Deletion_cluster_eq_original T D q hD
    (contactForceSet x y) (by
      intro z hz
      exact ⟨x, hxLow, contactForceSet_l1dist_lt hxy hz⟩)
  have hyOriginal : y ∈ pairHighCluster (interpolatedHighPair T q) 0 :=
    pairNearestHighSet_subset_cluster _ _ hyNearest
  have hforceDisjoint : zeroHighPair T (contactForceSet x y) q ∈
      pairDisjointInfiniteHighAt (0 : Site d) := by
    constructor
    · rw [hforceEq]
      exact hD.1.1.1.1
    · rw [hforceEq]
      simpa only [pairLowInfiniteVertices_zeroHighPair] using hD.1.1.1.2
  refine ⟨step3WindowMask_matches T D N q, hforceSub, hxy,
    ?_, ?_, hforceDisjoint, ?_⟩
  · simpa only [pairLowInfiniteVertices_zeroHighPair] using hxLow
  · rw [hbaseEq]
    exact hyOriginal
  · exact hforceEq.trans hbaseEq.symm

theorem step3CoreWindow_sourceDegree
    (T : MonotoneAutomaton d) (D N K : ℕ) (q : FieldTriple d)
    (hq : q ∈ step3CoreWindowEvent T D N K) :
    K ≤ finiteEventMultiplicity (step3Indices (d := d) N)
      (step3SourceEvent T D N) q := by
  classical
  let C := step3WindowContacts T D N q
  let M := step3WindowMask T D N q
  have hcard : K ≤ C.card := hq.2
  apply hcard.trans
  unfold finiteEventMultiplicity
  apply Finset.card_le_card_of_injOn
    (fun p : Site d × Site d => ((M, p.1), p.2))
  · intro p hp
    have hpC : p ∈ step3WindowContacts T D N q := hp
    have hp' := Finset.mem_filter.mp hpC
    have hpBoxes := Finset.mem_product.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · rw [step3Indices]
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_powerset.mpr (step3WindowMask_subset_box T D N q),
          hpBoxes.1⟩
      · exact hpBoxes.2
    · exact step3Contact_gives_source T D N q hq.1 hpC
  · intro p hp r hr heq
    exact Prod.ext (congrArg (fun i => i.1.2) heq)
      (congrArg (fun i => i.2) heq)



theorem step3CoreWindow_probability_bound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D N K : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    epsilon ^ (boxFinsetBK d D).card * K *
        mu (step3CoreWindowEvent T D N K) ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
  apply step3FiniteWindow_probability_bound T mu D N K epsilon hinsert
    (step3CoreWindowEvent T D N K)
    (measurableSet_step3CoreWindowEvent T D N K)
  intro q hq
  exact step3CoreWindow_sourceDegree T D N K q hq

theorem step3Distance_probability_bound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D K : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    epsilon ^ (boxFinsetBK d D).card * K *
        mu ((interpolatedHighPair T) ⁻¹'
          pairStep3DistanceAt (0 : Site d) D) ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
  let c : ℝ≥0∞ := epsilon ^ (boxFinsetBK d D).card * K
  have hmono := step3CoreWindowEvent_mono T D K
  have hN : ∀ N, c * mu (step3CoreWindowEvent T D N K) ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
    intro N
    exact step3CoreWindow_probability_bound T mu D N K epsilon hinsert
  rw [step3Distance_preimage_eq_iUnion_windows T D K,
    hmono.measure_iUnion]
  change c * (⨆ N, mu (step3CoreWindowEvent T D N K)) ≤ _
  rw [ENNReal.mul_iSup]
  exact iSup_le hN

theorem step3Distance_measure_zero
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D : ℕ) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    mu ((interpolatedHighPair T) ⁻¹'
      pairStep3DistanceAt (0 : Site d) D) = 0 := by
  let c : ℝ≥0∞ := epsilon ^ (boxFinsetBK d D).card
  let p : ℝ≥0∞ := mu ((interpolatedHighPair T) ⁻¹'
    pairStep3DistanceAt (0 : Site d) D)
  by_contra hp
  have hc : c ≠ 0 := by
    exact pow_ne_zero _ hepsilon
  have hcp : c * p ≠ 0 := mul_ne_zero hc hp
  let L : ℝ≥0∞ := (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞)
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_mul_gt
    (a := c * p) (b := L) hcp (by simp [L])
  have hbound := step3Distance_probability_bound
    T mu D K epsilon hinsert
  have hrewrite : c * (K : ℝ≥0∞) * p = (K : ℝ≥0∞) * (c * p) := by
    ring
  rw [hrewrite] at hbound
  exact (not_lt_of_ge hbound) hK



theorem interpolatedHighPair_step3Core_measure_zero
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    (interpolatedHighPairLaw T mu)
      (pairStep3CoreAt (0 : Site d)) = 0 := by
  have hpre : mu ((interpolatedHighPair T) ⁻¹'
      pairStep3CoreAt (0 : Site d)) = 0 := by
    rw [pairStep3CoreAt_eq_iUnion_distance,
      Set.preimage_iUnion]
    exact measure_iUnion_null fun D =>
      step3Distance_measure_zero T mu D epsilon hepsilon hinsert
  rw [interpolatedHighPairLaw,
    Measure.map_apply (measurable_interpolatedHighPair T)
      (measurableSet_pairStep3CoreAt 0)]
  exact hpre




theorem monotoneAutomaton_infiniteCluster_uniqueness
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d) (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsertMiddle : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hinsertHigh : HasHighInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (T q.1))} = 1) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
  apply highOutput_cluster_count_ae_le_one_of_step3Core
    T mu hd herg epsilon hepsilon hinsertMiddle hmono hlow
  exact interpolatedHighPair_step3Core_measure_zero
    T mu epsilon hepsilon hinsertHigh

end StatMech.FrontierA
