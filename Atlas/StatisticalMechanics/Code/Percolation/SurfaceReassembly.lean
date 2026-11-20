/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































import Code.Percolation.OffClusterIndep
import Code.Percolation.DctDifferentialFull

open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}




theorem measurableSet_of_dependsOn {E : Type*} [Countable E] [DecidableEq E]
    {A : Set (ConfigSpace E)} {F : Finset E}
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
    MeasurableSet A := by
  rw [eq_cylinder_restrict_image A F hA]
  exact MeasurableSet.cylinder F MeasurableSet.of_discrete


theorem coord_true_dependsOn {E : Type*} (e : E) :
    DependsOn (({ω : ConfigSpace E | ω e = true}).indicator (fun _ => (1 : ℝ)))
      ({e} : Set E) := by
  intro ω ω' h
  have he : ω e = ω' e := h e rfl
  by_cases hmem : ω ∈ {ω : ConfigSpace E | ω e = true}
  · rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (by simp only [Set.mem_setOf_eq, ← he]; exact hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq, ← he]; exact hmem)]



theorem coord_true_prob {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) (e : E) :
    (bernoulliProductMeasure (E := E) p hp).real {ω | ω e = true} = (p : ℝ) := by
  classical
  haveI hu : Unique ↥({e} : Finset E) := by
    refine ⟨⟨⟨e, by simp⟩⟩, ?_⟩
    intro a; obtain ⟨av, hav⟩ := a; simp only [Finset.mem_singleton] at hav; subst hav; rfl
  rw [realProb_cylinder_eq_finsum p hp _ ({e} : Finset E) (by simpa using coord_true_dependsOn e)]
  have hmemiff : ∀ η : ConfigSpace ↥({e} : Finset E),
      (η ∈ ({e} : Finset E).restrict '' {ω : ConfigSpace E | ω e = true}) ↔
        η default = true := by
    intro η
    constructor
    · rintro ⟨ω, hω, rfl⟩
      have hde : (default : ↥({e}:Finset E)) = ⟨e, by simp⟩ := Subsingleton.elim _ _
      simp only [Finset.restrict, hde]; exact hω
    · intro h
      refine ⟨fun a => if a = e then true else false, ?_, ?_⟩
      · simp [Set.mem_setOf_eq]
      · funext j
        have hde : (default : ↥({e}:Finset E)) = ⟨e, by simp⟩ := Subsingleton.elim _ _
        obtain ⟨jv, hjv⟩ := j
        simp only [Finset.mem_singleton] at hjv; subst hjv
        simp only [Finset.restrict, if_pos]
        rw [hde] at h; exact h.symm
  have hterm : ∀ η : ConfigSpace ↥({e} : Finset E),
      Set.indicator (({e}:Finset E).restrict '' {ω : ConfigSpace E | ω e = true})
          (fun _ => (1:ℝ)) η
        * ∏ a, (if η a then (p:ℝ) else 1 - p)
      = (if η default then (p:ℝ) else 0) := by
    intro η
    rw [Set.indicator_apply, Fintype.prod_unique]
    simp only [hmemiff]
    by_cases hb : η default = true <;> simp [hb]
  rw [Finset.sum_congr rfl (fun η _ => hterm η)]
  rw [Fintype.sum_equiv (Equiv.funUnique (↥({e}:Finset E)) Bool)
      (fun η => if η default then (p:ℝ) else 0) (fun b => if b then (p:ℝ) else 0) (fun η => rfl)]
  simp










theorem sum_natAbs_one {n : ℕ} (f : Fin n → ℕ) (h : ∑ j, f j = 1) :
    ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
  classical
  have hex : ∃ i, f i ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    simp only [hcon, Finset.sum_const_zero] at h
    exact absurd h (by norm_num)
  obtain ⟨i, hi⟩ := hex
  have hile : f i ≤ ∑ j, f j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [h] at hile
  have hfi : f i = 1 := by omega
  refine ⟨i, hfi, fun j hj => ?_⟩
  by_contra hjne
  have hbound2 : f i + f j ≤ ∑ k, f k := by
    have hje : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hbound : f j ≤ ∑ k ∈ Finset.univ.erase i, f k :=
      Finset.single_le_sum (fun k _ => Nat.zero_le _) hje
    have := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
    omega
  rw [h, hfi] at hbound2
  omega




theorem adj_coordShift_sr (x y : Site d) (hadj : (hypercubicLattice d).Adj x y) :
    ∃ (i : Fin d) (b : Bool), y = coordShift x i (stepSign b) := by
  rw [hypercubicLattice_adj] at hadj
  classical
  obtain ⟨i, hi1, hother⟩ := sum_natAbs_one (fun j => (x j - y j).natAbs) hadj
  refine ⟨i, decide ((y i - x i) = 1), ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    rw [coordShift, Function.update_self]
    have hpm : (x j - y j) = 1 ∨ (x j - y j) = -1 := by
      have : (x j - y j).natAbs = 1 := hi1
      omega
    unfold stepSign
    rcases hpm with h | h
    · have hyx : (y j - x j) = -1 := by omega
      rw [hyx]; simp; omega
    · have hyx : (y j - x j) = 1 := by omega
      rw [hyx]; simp; omega
  · rw [coordShift, Function.update_of_ne hj]
    have hz : (x j - y j).natAbs = 0 := hother j hj
    omega




theorem mem_boundaryEdges_of_adj (S : Finset (Site d)) {x y : Site d}
    (hxS : x ∈ S) (hyS : y ∉ S) (hadj : (hypercubicLattice d).Adj x y) :
    (x, y) ∈ boundaryEdges d S := by
  classical
  obtain ⟨i, b, hyc⟩ := adj_coordShift_sr x y hadj
  unfold boundaryEdges
  rw [Finset.mem_image]
  refine ⟨(x, i, b), ?_, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, and_true]; exact hxS
    · simp only; rw [← hyc]; exact hyS
  · simp only; rw [← hyc]



theorem boundaryEdges_outer {S : Finset (Site d)} {e : Site d × Site d}
    (he : e ∈ boundaryEdges d S) :
    ∃ (i : Fin d) (b : Bool), e.1 ∈ S ∧ e.2 ∉ S ∧ e.2 = coordShift e.1 i (stepSign b) := by
  classical
  unfold boundaryEdges at he
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product] at he
  obtain ⟨t, ⟨⟨ht1, _, _⟩, hnotin⟩, het⟩ := he
  refine ⟨t.2.1, t.2.2, ?_, ?_, ?_⟩
  · rw [show e.1 = t.1 from by rw [← het]]; exact ht1
  · rw [show e.2 = coordShift t.1 t.2.1 (stepSign t.2.2) from by rw [← het]]; exact hnotin
  · rw [show e.1 = t.1 from by rw [← het], show e.2 = coordShift t.1 t.2.1 (stepSign t.2.2) from by rw [← het]]




theorem boundaryEdges_snd_mem_box {S : Finset (Site d)} {L : ℕ} (hL : 1 ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) {e : Site d × Site d}
    (he : e ∈ boundaryEdges d S) : e.2 ∈ box d L := by
  classical
  obtain ⟨i, b, h1S, _, h2⟩ := boundaryEdges_outer he
  have ht1box : e.1 ∈ box d (L - 1) := hSbox (by exact_mod_cast h1S)
  rw [h2, mem_box]
  intro j
  by_cases hj : j = i
  · rw [hj, coordShift, Function.update_self]
    have hb := ht1box i
    unfold stepSign
    cases b
    · simp only [Bool.false_eq_true, if_false]; omega
    · simp only [if_true]; omega
  · rw [coordShift, Function.update_of_ne hj]
    have hb := ht1box j
    omega
















theorem withinConn_transfer_on_cluster {S : Set (Site d)} {K : Set (Site d)}
    {x : Site d} (hoS : origin d ∈ S)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hK : clusterWithin d ω S (origin d) = K)
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    (hconn : ω ∈ withinConnEvent d S (origin d) x) :
    ω' ∈ withinConnEvent d S (origin d) x := by
  obtain ⟨hoS', hxS, hconn⟩ := hconn
  obtain ⟨w⟩ := hconn
  have hagree' : ∀ e ∈ incidentWithin (clusterWithin d ω S (origin d)) S, ω e = ω' e := by
    rw [hK]; exact hagree
  have hoK : (origin d) ∈ clusterWithin d ω S (origin d) :=
    ⟨hoS, hoS, connectedWithin_refl ω S ⟨origin d, hoS⟩⟩
  obtain ⟨_, ⟨w'⟩⟩ := walk_transfer hagree' w hoK
  exact ⟨hoS', hxS, ⟨w'⟩⟩







theorem clusterInter_withinConn_dependsOn {S : Finset (Site d)} {K : Finset (Site d)}
    {x : Site d} (hoS : origin d ∈ (S : Set (Site d))) :
    DependsOn ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
        ∩ withinConnEvent d (S : Set (Site d)) (origin d) x).indicator (fun _ => (1 : ℝ)))
      (incidentWithinFinset K S : Set (Sym2 (Site d))) := by
  intro ω ω' h
  rw [incidentWithinFinset_coe] at h
  have hiff : (ω ∈ clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
        ∩ withinConnEvent d (S : Set (Site d)) (origin d) x) ↔
      (ω' ∈ clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
        ∩ withinConnEvent d (S : Set (Site d)) (origin d) x) := by
    constructor
    · rintro ⟨hcl, hwc⟩
      refine ⟨(clusterEvent_iff (K := (K : Set (Site d))) hoS (fun e he => h e he)).mp hcl, ?_⟩
      have hK : clusterWithin d ω (S : Set (Site d)) (origin d) = (K : Set (Site d)) := hcl
      exact withinConn_transfer_on_cluster hoS hK (fun e he => h e he) hwc
    · rintro ⟨hcl, hwc⟩
      refine ⟨(clusterEvent_iff (K := (K : Set (Site d))) hoS (fun e he => h e he)).mpr hcl, ?_⟩
      have hK : clusterWithin d ω' (S : Set (Site d)) (origin d) = (K : Set (Site d)) := hcl
      exact withinConn_transfer_on_cluster hoS hK (fun e he => (h e he).symm) hwc
  by_cases hmem : ω ∈ clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
      ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]















theorem lastExit_summand_factor (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (K : Finset (Site d)) (x y : Site d) (n : ℕ)
    (hxK : x ∈ K) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω})
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
            ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
            ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω} := by
  have hA : DependsOn (((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
        ∩ withinConnEvent d (S : Set (Site d)) (origin d) x)
        ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}).indicator (fun _ => (1 : ℝ)))
      ((incidentWithinFinset K S : Set (Sym2 (Site d))) ∪ ({s(x, y)} : Set (Sym2 (Site d)))) :=
    dependsOn_inter (clusterInter_withinConn_dependsOn hoS)
      (boundaryOpen_dependsOn (K : Set (Site d)) x y)
  refine indep_cylinder_inf p hp _ _ (incidentWithinFinset K S ∪ {s(x, y)})
    (boxOffCEdges d (K : Set (Site d)) n) ?_ ?_ (offClusterBoxCrossing_dependsOn _ _ _)
  · exact disjoint_boxOffC_incidentUnion K S x y n hxK
  · rw [Finset.coe_union, Finset.coe_singleton]
    exact hA




theorem boundaryEdge_disjoint_within (S : Finset (Site d)) (x y : Site d) (hyS : y ∉ S) :
    Disjoint (edgesWithinFinset S) ({s(x, y)} : Finset (Sym2 (Site d))) := by
  classical
  rw [Finset.disjoint_singleton_right]
  intro hmem
  rw [mem_edgesWithinFinset] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1; subst h2; exact hyS hb
  · subst h1; subst h2; exact hyS ha






theorem withinConn_edge_indep (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (x y : Site d) (hyS : y ∉ S) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | ω s(x, y) = true})
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) x) * (p : ℝ) := by
  classical
  rw [indep_cylinder_inf p hp _ _ (edgesWithinFinset S) ({s(x, y)} : Finset (Sym2 (Site d)))
      (boundaryEdge_disjoint_within S x y hyS) (withinConn_dependsOn S (origin d) x)
      (by simpa using coord_true_dependsOn (s(x, y) : Sym2 (Site d)))]
  rw [coord_true_prob p hp]














theorem crossingEvent_lastExit_finset (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
    crossingEvent d n ⊆
      ⋃ K ∈ S.powerset, ⋃ e ∈ boundaryEdges d S,
        (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1
          ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω}
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω}) := by
  classical
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  set C := clusterWithin d ω (S : Set (Site d)) (origin d) with hC
  have hoC : origin d ∈ C := ⟨hoS, hoS, connectedWithin_refl ω _ ⟨origin d, hoS⟩⟩
  have hCsub : C ⊆ (S : Set (Site d)) := fun z hz => hz.1
  have hvC : v ∉ C := fun hvc => hv (hSbox (hCsub hvc))
  have hCfin : C.Finite := (S.finite_toSet).subset hCsub
  set K := hCfin.toFinset with hK
  have hKC : (K : Set (Site d)) = C := by simp [hK]
  have hKsub : K ⊆ S := by
    intro z hz
    have hzC : z ∈ C := by rw [← hKC]; exact_mod_cast hz
    exact_mod_cast (hCsub hzC)
  obtain ⟨x, y, hx, hy, hopen, hwithin⟩ := lattice_lastExit ω C (origin d) v hoC hvC hconn
  have hxbox : x ∈ box d (n - 1) := hSbox (hCsub hx)
  have hadj : (hypercubicLattice d).Adj x y := hopen.1
  have hybox : y ∈ box d n := by
    have := adj_box_step hxbox hadj
    rwa [show n - 1 + 1 = n from by omega] at this
  have hxS : x ∈ S := by exact_mod_cast (hCsub hx)
  have hyS : y ∉ S := by
    intro hyS'
    exact hy (clusterWithin_closed hx (by exact_mod_cast hyS') hopen)
  obtain ⟨z, hz, _hzbox, hzconn⟩ := extract_box ω C y v n hn hy hvC hybox hv hwithin
  have hwc : ω ∈ withinConnEvent d (S : Set (Site d)) (origin d) x := by
    obtain ⟨hxS_, _, hconnx⟩ := hx
    exact ⟨hoS, hxS_, hconnx⟩
  rw [Set.mem_iUnion₂]
  refine ⟨K, Finset.mem_powerset.mpr hKsub, ?_⟩
  rw [Set.mem_iUnion₂]
  refine ⟨(x, y), mem_boundaryEdges_of_adj S hxS hyS hadj, ?_⟩
  refine ⟨⟨⟨?_, hwc⟩, ?_⟩, ?_⟩
  · show clusterWithin d ω (S : Set (Site d)) (origin d) = (K : Set (Site d))
    rw [hKC]
  · show boundaryOpen d (K : Set (Site d)) x y ω
    rw [hKC]; exact ⟨hx, hy, hopen⟩
  · show offClusterBoxCrossing d (K : Set (Site d)) y n ω
    rw [hKC]
    exact ⟨z, _hzbox, ⟨hybox, hy⟩, hz, hzconn⟩









theorem summand_per_K_le (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (K : Finset (Site d)) (x y : Site d)
    {L m n : ℕ} (hy : y ∈ box d L) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω})
      ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
            ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
            ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
        * crossProb d p hp m := by
  classical
  by_cases hxK : x ∈ K
  · rw [lastExit_summand_factor p hp S hoS K x y n hxK]
    exact mul_le_mul_of_nonneg_left
      (offClusterBox_crossProb_le p hp _ y hy hmLn hm) measureReal_nonneg
  · have hempty : (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hbo⟩, _⟩
      exact hxK hbo.1
    rw [hempty, measureReal_empty]
    exact mul_nonneg measureReal_nonneg (crossProb_nonneg d p hp m)






theorem sumK_explored_le (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (x y : Site d) :
    ∑ K ∈ S.powerset,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
      ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | ω s(x, y) = true}) := by
  classical
  set F := fun K : Finset (Site d) =>
    clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
      ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
      ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω} with hF
  have hmeas : ∀ K ∈ S.powerset, MeasurableSet (F K) := by
    intro K _
    have hdep : DependsOn ((F K).indicator (fun _ => (1:ℝ)))
        ((incidentWithinFinset K S : Set (Sym2 (Site d))) ∪ ({s(x, y)} : Set (Sym2 (Site d)))) :=
      dependsOn_inter (clusterInter_withinConn_dependsOn hoS) (boundaryOpen_dependsOn _ x y)
    rw [show ((incidentWithinFinset K S : Set (Sym2 (Site d)))
            ∪ ({s(x, y)} : Set (Sym2 (Site d))))
          = ((incidentWithinFinset K S ∪ {s(x, y)} : Finset (Sym2 (Site d)))
              : Set (Sym2 (Site d)))
        from by rw [Finset.coe_union, Finset.coe_singleton]] at hdep
    exact measurableSet_of_dependsOn hdep
  have hdisj : (S.powerset : Set (Finset (Site d))).PairwiseDisjoint F := by
    intro K _ K' _ hne
    simp only [Function.onFun, hF]
    rw [Set.disjoint_left]
    rintro ω ⟨⟨hcl, _⟩, _⟩ ⟨⟨hcl', _⟩, _⟩
    have h1 : clusterWithin d ω (S : Set (Site d)) (origin d) = (K : Set (Site d)) := hcl
    have h2 : clusterWithin d ω (S : Set (Site d)) (origin d) = (K' : Set (Site d)) := hcl'
    exact hne (by exact_mod_cast (h1 ▸ h2 : (K : Set (Site d)) = (K' : Set (Site d))))
  rw [← measureReal_biUnion_finset hdisj hmeas]
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_iUnion₂] at hω
  obtain ⟨K, _, ⟨_, hwc⟩, hbo⟩ := hω
  exact ⟨hwc, hbo.2.2.2⟩





theorem sumK_summand_le (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (x y : Site d) (hyS : y ∉ S)
    {L m n : ℕ} (hy : y ∈ box d L) (hmLn : m + L ≤ n) (hm : 1 ≤ m) :
    ∑ K ∈ S.powerset,
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
          ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω})
      ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) (origin d) x) * (p : ℝ) * crossProb d p hp m := by
  classical
  calc ∑ K ∈ S.powerset,
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
            ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
            ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
            ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω})
      ≤ ∑ K ∈ S.powerset,
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
              ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
              ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω})
          * crossProb d p hp m :=
        Finset.sum_le_sum (fun K _ => summand_per_K_le p hp S hoS K x y hy hmLn hm)
    _ = (∑ K ∈ S.powerset,
            (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
              (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
                ∩ withinConnEvent d (S : Set (Site d)) (origin d) x
                ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}))
          * crossProb d p hp m := by rw [Finset.sum_mul]
    _ ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | ω s(x, y) = true})
          * crossProb d p hp m :=
        mul_le_mul_of_nonneg_right (sumK_explored_le p hp S hoS x y) (crossProb_nonneg d p hp m)
    _ = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
            (withinConnEvent d (S : Set (Site d)) (origin d) x) * (p : ℝ) * crossProb d p hp m := by
        rw [withinConn_edge_indep p hp S x y hyS]















theorem subcritical_oneStep (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (L : ℕ) (hL : 1 ≤ L)
    (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) (k : ℕ) (hk : 1 ≤ k) :
    crossProb d p hp ((k + 1) * L) ≤ phi d p hp S * crossProb d p hp (k * L) := by
  classical
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp with hμ
  set n := (k + 1) * L with hn_def
  set m := k * L with hm_def
  have hn1 : 1 ≤ n := by rw [hn_def]; nlinarith [hk, hL]
  have hm1 : 1 ≤ m := by rw [hm_def]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmLn : m + L ≤ n := by rw [hm_def, hn_def]; nlinarith
  have hSn : (S : Set (Site d)) ⊆ box d (n - 1) := hSbox.trans (box_mono d (by omega))
  have hub : crossProb d p hp n ≤
      ∑ K ∈ S.powerset, ∑ e ∈ boundaryEdges d S,
        μ.real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1
          ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω}) := by
    unfold crossProb
    calc μ.real (crossingEvent d n)
        ≤ μ.real (⋃ K ∈ S.powerset, ⋃ e ∈ boundaryEdges d S,
            (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
              ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1
              ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω}
              ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω})) :=
          measureReal_mono (crossingEvent_lastExit_finset S hoS n hn1 hSn) (measure_ne_top _ _)
      _ ≤ ∑ K ∈ S.powerset, μ.real (⋃ e ∈ boundaryEdges d S,
            (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
              ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1
              ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω}
              ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω})) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ _ := Finset.sum_le_sum (fun K _ => measureReal_biUnion_finset_le _ _)
  rw [Finset.sum_comm] at hub
  have hpe : ∀ e ∈ boundaryEdges d S,
      ∑ K ∈ S.powerset,
        μ.real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
          ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1
          ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω})
          ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω})
      ≤ μ.real (withinConnEvent d (S : Set (Site d)) (origin d) e.1)
          * (p : ℝ) * crossProb d p hp m := by
    intro e he
    obtain ⟨_, _, _, h2S, _⟩ := boundaryEdges_outer he
    exact sumK_summand_le p hp S hoS e.1 e.2 h2S
      (boundaryEdges_snd_mem_box hL hSbox he) hmLn hm1
  calc crossProb d p hp n
      ≤ ∑ e ∈ boundaryEdges d S, ∑ K ∈ S.powerset,
          μ.real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d))
            ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1
            ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω})
            ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω}) := hub
    _ ≤ ∑ e ∈ boundaryEdges d S,
          μ.real (withinConnEvent d (S : Set (Site d)) (origin d) e.1)
            * (p : ℝ) * crossProb d p hp m :=
        Finset.sum_le_sum hpe
    _ = phi d p hp S * crossProb d p hp m := by
        unfold phi
        rw [← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun e he => ?_)
        have h1c : e.1 ∈ (S : Set (Site d)) := by
          have := boundaryEdges_fst_mem he; exact_mod_cast this
        rw [connWithinProb_eq p hp S e.1 hoS h1c]; ring









theorem geometric_subseq_antitone_decay' {f : ℕ → ℝ} {r C : ℝ} {L : ℕ}
    (hL : 1 ≤ L) (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 < C) (hanti : Antitone f)
    (hsub : ∀ k, f (k * L) ≤ C * r ^ k) :
    ∃ c > 0, ∃ C' > 0, ∀ n, f n ≤ C' * Real.exp (-c * n) := by
  have hlogr_neg : Real.log r < 0 := Real.log_neg hr0 hr1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  set c : ℝ := -(Real.log r) / L with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; exact div_pos (by linarith) hLpos
  refine ⟨c, hc_pos, C * r⁻¹, by positivity, fun n => ?_⟩
  set k := n / L with hk_def
  have hfn : f n ≤ C * r ^ k := le_trans (hanti (Nat.div_mul_le_self n L)) (hsub k)
  have hkpos_real : ((n : ℝ) / L - 1) < (k : ℝ) := by
    have hnlt := Nat.lt_div_mul_add (a := n) (b := L) hL
    have hkk : (n : ℝ) < (k : ℝ) * L + L := by rw [hk_def]; exact_mod_cast hnlt
    rw [div_sub_one hLpos.ne', div_lt_iff₀ hLpos]; linarith
  have hrk : (r : ℝ) ^ (k : ℝ) = Real.exp ((k : ℝ) * Real.log r) := by
    rw [Real.rpow_def_of_pos hr0]; ring_nf
  have step2 : (r : ℝ) ^ k ≤ Real.exp (((n : ℝ) / L - 1) * Real.log r) := by
    rw [show (r : ℝ) ^ k = r ^ (k : ℝ) from (Real.rpow_natCast r k).symm, hrk]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hkpos_real.le hlogr_neg.le)
  have step3 : Real.exp (((n : ℝ) / L - 1) * Real.log r) = r⁻¹ * Real.exp (-c * n) := by
    rw [sub_mul, one_mul, Real.exp_sub, hc_def,
        show -(-Real.log r / L) * (n : ℝ) = (n / L) * Real.log r from by ring,
        show Real.exp (Real.log r) = r from Real.exp_log hr0]
    ring
  calc f n ≤ C * r ^ k := hfn
    _ ≤ C * Real.exp (((n : ℝ) / L - 1) * Real.log r) :=
        mul_le_mul_of_nonneg_left step2 hC.le
    _ = C * (r⁻¹ * Real.exp (-c * n)) := by rw [step3]
    _ = C * r⁻¹ * Real.exp (-c * n) := by ring






theorem subcritical_geometric (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ k, crossProb d p hp (k * L) ≤ r⁻¹ * r ^ k := by
  classical
  set g : ℕ → ℝ := fun k => crossProb d p hp ((k + 1) * L) with hg_def
  have hgnn : ∀ k, 0 ≤ g k := fun k => crossProb_nonneg d p hp _
  have hg0 : g 0 ≤ 1 := by simpa [hg_def] using crossProb_le_one d p hp ((0 + 1) * L)
  have hgrec : ∀ k, g (k + 1) ≤ phi d p hp S * g k := by
    intro k
    have hstep := subcritical_oneStep p hp S hoS L hL hSbox (k + 1) (by omega)
    simp only [hg_def]
    convert hstep using 2
  obtain ⟨r, hr0, hr1, hgrec'⟩ := step_with_pos_ratio hgnn hphi hgrec
  have hsubg : ∀ k, g k ≤ r ^ k := recursion_le_pow hg0 hr0.le hgrec'
  refine ⟨r, hr0, hr1, fun k => ?_⟩
  cases k with
  | zero =>
    simp only [Nat.zero_mul, pow_zero, mul_one]
    have h1 : crossProb d p hp 0 ≤ 1 := crossProb_le_one d p hp 0
    have h2 : (1 : ℝ) ≤ r⁻¹ := by rw [one_le_inv_iff₀]; exact ⟨hr0, hr1.le⟩
    linarith
  | succ j =>
    have hgj : crossProb d p hp ((j + 1) * L) ≤ r ^ j := hsubg j
    rw [show r⁻¹ * r ^ (j + 1) = r ^ j from by field_simp; ring]
    exact hgj















theorem subcritical_decay_unconditional (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (hphi : phi d p hp S < 1)
    (L : ℕ) (hL : 1 ≤ L) (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
  obtain ⟨r, hr0, hr1, hsub⟩ := subcritical_geometric p hp S hoS hphi L hL hSbox
  exact geometric_subseq_antitone_decay' hL hr0 hr1 (by positivity)
    (crossProb_antitone d p hp) hsub

end Percolation

end StatMech
