/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.BkCriterionInfinite
import Code.Sharpness.BKFirstExit
import Code.Sharpness.TildeBc
import Code.Percolation.DctDifferentialFull
import Code.Percolation.SubcriticalDecayFull
import Code.Percolation.SharpnessUnconditional
import Code.Lattice.JordanContour

open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology

namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph
open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


noncomputable def shk_translateFinset (g : Multiplicative (Site d))
    (S : Finset (Site d)) : Finset (Site d) :=
  S.image (fun x => g • x)

@[simp] theorem shk_mem_translateFinset_smul
    (g : Multiplicative (Site d)) (S : Finset (Site d)) (x : Site d) :
    g • x ∈ shk_translateFinset g S ↔ x ∈ S := by
  classical
  constructor
  · intro hx
    rw [shk_translateFinset, Finset.mem_image] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have : y = x := by
      apply_fun (fun z => g⁻¹ • z) at hxy
      simpa only [inv_smul_smul] using hxy
    simpa [this] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem shk_translateFinset_card (g : Multiplicative (Site d))
    (S : Finset (Site d)) :
    (shk_translateFinset g S).card = S.card := by
  classical
  exact Finset.card_image_of_injective S
    (MulAction.toPerm (β := Site d) g).injective



noncomputable def shk_translateInduceIso (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d)) :
    openSubgraphInduce d omega (S : Set (Site d)) ≃g
      openSubgraphInduce d (ConfigSpace.shift g omega)
        (shk_translateFinset g S : Set (Site d)) where
  toEquiv :=
    { toFun := fun x => ⟨g • (x : Site d), by
          exact shk_mem_translateFinset_smul g S x |>.2 x.2⟩
      invFun := fun x => ⟨g⁻¹ • (x : Site d), by
          have hx : g • (g⁻¹ • (x : Site d)) ∈ shk_translateFinset g S := by
            simpa only [smul_inv_smul] using x.2
          exact (shk_mem_translateFinset_smul g S _).1 hx⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp only [inv_smul_smul]
      right_inv := fun x => by
        apply Subtype.ext
        simp only [smul_inv_smul] }
  map_rel_iff' := by
    intro x y
    simp only [openSubgraphInduce_adj]
    exact openSubgraph_adj_shift g omega x y


theorem shk_connectedWithin_shift_iff (g : Multiplicative (Site d))
    (omega : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d))
    (x y : S) :
    ConnectedWithin d (ConfigSpace.shift g omega)
        (shk_translateFinset g S : Set (Site d))
        ⟨g • (x : Site d), by exact (shk_mem_translateFinset_smul g S x).2 x.2⟩
        ⟨g • (y : Site d), by exact (shk_mem_translateFinset_smul g S y).2 y.2⟩ ↔
      ConnectedWithin d omega (S : Set (Site d)) x y := by
  simpa only [ConnectedWithin, shk_translateInduceIso] using
    ((shk_translateInduceIso g omega S).reachable_iff (u := x) (v := y))



theorem shk_shift_preimage_connWithinEvent (g : Multiplicative (Site d))
    (S : Finset (Site d)) (u x : Site d) (hu : u ∈ S) (hx : x ∈ S) :
    (ConfigSpace.shift g) ⁻¹'
        connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x) =
      connWithinEvent d (S : Set (Site d)) u x := by
  ext omega
  constructor
  · rintro ⟨_, _, hconn⟩
    exact ⟨hu, hx, (shk_connectedWithin_shift_iff g omega S
      ⟨u, hu⟩ ⟨x, hx⟩).1 hconn⟩
  · rintro ⟨_, _, hconn⟩
    exact ⟨(shk_mem_translateFinset_smul g S u).2 hu,
      (shk_mem_translateFinset_smul g S x).2 hx,
      (shk_connectedWithin_shift_iff g omega S ⟨u, hu⟩ ⟨x, hx⟩).2 hconn⟩



theorem shk_connWithinEvent_prob_translate (p : ℝ≥0) (hp : p ≤ 1)
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (u x : Site d) (hu : u ∈ S) (hx : x ∈ S) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x)) =
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (S : Set (Site d)) u x) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  have hmeas : MeasurableSet
      (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x)) := by
    apply measurableSet_of_dependsOn
    exact shp_connWithinEvent_dependsOn
  have hpres := (bernoulli_translationInvariant (E := Sym2 (Site d))
    (G := Multiplicative (Site d)) p hp) g
  have hpre := hpres.measureReal_preimage hmeas.nullMeasurableSet
  rw [shk_shift_preimage_connWithinEvent g S u x hu hx] at hpre
  exact hpre.symm


def shk_pairSmul (g : Multiplicative (Site d)) (q : Site d × Site d) :
    Site d × Site d := (g • q.1, g • q.2)

theorem shk_pairSmul_injective (g : Multiplicative (Site d)) :
    Function.Injective (shk_pairSmul (d := d) g) := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [shk_pairSmul, Prod.mk.injEq] at h ⊢
  exact ⟨(MulAction.toPerm (β := Site d) g).injective h.1,
    (MulAction.toPerm (β := Site d) g).injective h.2⟩



theorem shk_boundaryEdges_translate (g : Multiplicative (Site d))
    (S : Finset (Site d)) :
    boundaryEdges d (shk_translateFinset g S) =
      (boundaryEdges d S).image (shk_pairSmul g) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hqS, hqout, hqadj⟩ := shk_mem_boundaryEdges_iff.mp hq
    let a := g⁻¹ • q.1
    let b := g⁻¹ • q.2
    have hga : g • a = q.1 := by simp [a]
    have hgb : g • b = q.2 := by simp [b]
    have haS : a ∈ S := by
      apply (shk_mem_translateFinset_smul g S a).1
      simpa only [hga] using hqS
    have hbS : b ∉ S := by
      intro hb
      apply hqout
      have := (shk_mem_translateFinset_smul g S b).2 hb
      simpa only [hgb] using this
    have hab : (hypercubicLattice d).Adj a b := by
      apply (hyper_adj_smul g a b).1
      simpa only [hga, hgb] using hqadj
    rw [Finset.mem_image]
    refine ⟨(a, b), shk_mem_boundaryEdges_iff.mpr ⟨haS, hbS, hab⟩, ?_⟩
    simp only [shk_pairSmul, hga, hgb]
  · intro hq
    rw [Finset.mem_image] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨hqin, hqout, hqadj⟩ := shk_mem_boundaryEdges_iff.mp hq0
    apply shk_mem_boundaryEdges_iff.mpr
    exact ⟨(shk_mem_translateFinset_smul g S q0.1).2 hqin,
      fun h => hqout ((shk_mem_translateFinset_smul g S q0.2).1 h),
      (hyper_adj_smul g q0.1 q0.2).2 hqadj⟩



theorem shk_boundaryConnSum_translate (p : ℝ≥0) (hp : p ≤ 1)
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (h0 : origin d ∈ S) :
    ∑ q ∈ boundaryEdges d (shk_translateFinset g S),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connWithinEvent d (shk_translateFinset g S : Set (Site d))
            (g • origin d) q.1) =
      ∑ q ∈ boundaryEdges d S, connWithinProb d p hp S q.1 := by
  classical
  rw [shk_boundaryEdges_translate, Finset.sum_image]
  apply Finset.sum_congr rfl
  intro q hq
  have hqS : q.1 ∈ S := (shk_mem_boundaryEdges_iff.mp hq).1
  have htrans := shk_connWithinEvent_prob_translate p hp g S
    (origin d) q.1 h0 hqS
  have hbook := connWithinProb_eq p hp S q.1 (by simpa using h0) (by simpa using hqS)
  simpa only [shk_pairSmul] using htrans.trans hbook.symm
  exact (shk_pairSmul_injective g).injOn


theorem shk_phi_translate (p : ℝ≥0) (hp : p ≤ 1)
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (h0 : origin d ∈ S) :
    (p : ℝ) * ∑ q ∈ boundaryEdges d (shk_translateFinset g S),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connWithinEvent d (shk_translateFinset g S : Set (Site d))
            (g • origin d) q.1) = phi d p hp S := by
  rw [shk_boundaryConnSum_translate p hp g S h0]
  rfl


noncomputable def shk_restrictedSusceptibility (p : ℝ≥0) (hp : p ≤ 1)
    (Lam : Finset (Site d)) (u : Site d) : ℝ :=
  ∑ x ∈ Lam, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
    (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x})




theorem shk_restrictedSusceptibility_le (p : ℝ≥0) (hp : p ≤ 1)
    (S Lam : Finset (Site d)) (h0S : origin d ∈ S) (h0Lam : origin d ∈ Lam)
    (hphi : phi d p hp S < 1) :
    shk_restrictedSusceptibility p hp Lam (origin d) ≤
      (S.card : ℝ) / (1 - phi d p hp S) := by
  classical
  let chi : Site d → ℝ := fun u => shk_restrictedSusceptibility p hp Lam u
  obtain ⟨u, huLam, humax⟩ := Finset.exists_max_image Lam chi ⟨origin d, h0Lam⟩
  let g : Multiplicative (Site d) := Multiplicative.ofAdd u
  have hgu : g • origin d = u := by
    funext i
    simp [g, smul_site_apply, origin]
  let Su := shk_translateFinset g S
  have huSu : u ∈ Su := by
    rw [← hgu]
    exact (shk_mem_translateFinset_smul g S (origin d)).2 h0S
  let Sin := Lam ∩ Su
  let bnd := boundaryEdges d Su
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let q : Site d → ℝ := fun x =>
    mu.real (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x})
  let q' : Site d → Site d → ℝ := fun b x =>
    mu.real (connEvent (hypercubicLattice d) (Lam : Set (Site d)) b {x})
  let cw : Site d × Site d → ℝ := fun e =>
    mu.real (connEvent (hypercubicLattice d) (Su : Set (Site d)) u {e.1})
  have hcont : ∀ b : Site d, ∑ x ∈ Lam, q' b x ≤ chi u := by
    intro b
    by_cases hb : b ∈ Lam
    · exact humax b hb
    · have hz : ∀ x ∈ Lam, q' b x = 0 := by
        intro x _
        simp only [q', connEvent, ConnToSet]
        have hempty : {omega : ConfigSpace (Sym2 (Site d)) |
            ∃ (_ : b ∈ (Lam : Set (Site d))) (z : Site d)
              (_ : z ∈ (Lam : Set (Site d))), z ∈ ({x} : Set (Site d)) ∧
                ConnWithin (hypercubicLattice d) omega (Lam : Set (Site d))
                  ⟨b, by assumption⟩ ⟨z, by assumption⟩} = ∅ := by
          ext omega
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hb', _⟩
          exact hb (by simpa using hb')
        rw [hempty]
        exact measureReal_empty
      calc
        (∑ x ∈ Lam, q' b x) = 0 := Finset.sum_eq_zero fun x hx => hz x hx
        _ ≤ chi u := by
          simp only [chi, shk_restrictedSusceptibility]
          exact Finset.sum_nonneg fun x _ => measureReal_nonneg
  have hfe : ∀ x ∈ Lam, x ∉ Sin →
      q x ≤ ∑ e ∈ bnd, ((p : ℝ) * cw e) * q' e.2 x := by
    intro x hxLam hxSin
    have hxSu : x ∉ Su := by
      intro hx
      exact hxSin (Finset.mem_inter.mpr ⟨hxLam, hx⟩)
    have hb := bk_criterion_infinite_lattice_singleton p hp Lam Su u x huSu hxSu
    simpa only [q, q', cw, bnd, mul_assoc] using hb
  have hselfSin : chi u ≤ (Sin.card : ℝ) + phi d p hp S * chi u := by
    apply susceptibility_self_consistent Lam Sin Finset.inter_subset_left bnd
      (fun e => e.2) (p : ℝ) p.coe_nonneg cw q q'
      (fun _ _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
      (fun x _ => measureReal_le_one) hfe (chi u)
    · rfl
    · exact hcont
    · have hcoeff := shk_phi_translate p hp g S h0S
      rw [hgu] at hcoeff
      simpa only [Su, bnd, cw,
        shk_connEvent_singleton_eq_connWithinEvent] using hcoeff.symm
  have hcard : (Sin.card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast le_trans (Finset.card_le_card Finset.inter_subset_right)
      (le_of_eq (shk_translateFinset_card g S))
  have hself : chi u ≤ (S.card : ℝ) + phi d p hp S * chi u :=
    hselfSin.trans (add_le_add hcard le_rfl)
  have hchi0 : 0 ≤ chi u := Finset.sum_nonneg fun x _ => measureReal_nonneg
  have hub := (susceptibility_finite_of_self_consistent
    (chi u) (S.card : ℝ) (phi d p hp S) hchi0 hphi hself).2
  exact (humax (origin d) h0Lam).trans hub


theorem shk_connWithinProb_mono {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) (S : Finset (Site d)) (x : Site d) :
    connWithinProb d p hp S x ≤ connWithinProb d q hq S x := by
  classical
  by_cases h0 : origin d ∈ S
  · by_cases hx : x ∈ S
    · have hm := ibk_measure_mono_parameter hp hq hpq
        (internalEdgesFinset S)
        (shk_connEvent_singleton_dependsOn S (origin d) x)
        (isIncreasing_connEvent (hypercubicLattice d) (S : Set (Site d))
          (origin d) {x})
      rw [shk_connEvent_singleton_eq_connWithinEvent] at hm
      have hpbook := connWithinProb_eq p hp S x (by simpa using h0) (by simpa using hx)
      have hqbook := connWithinProb_eq q hq S x (by simpa using h0) (by simpa using hx)
      rw [hpbook, hqbook]
      simpa only [withinConnEvent, connWithinEvent] using hm
    · unfold connWithinProb
      rw [dif_pos h0, dif_neg hx, dif_pos h0, dif_neg hx]
  · unfold connWithinProb
    rw [dif_neg h0, dif_neg h0]


theorem shk_phi_mono {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1)
    (hpq : p ≤ q) (S : Finset (Site d)) :
    phi d p hp S ≤ phi d q hq S := by
  unfold phi
  have hsum : (∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1) ≤
      ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 := by
    exact Finset.sum_le_sum fun e _ => shk_connWithinProb_mono hp hq hpq S e.1
  have hsum0 : 0 ≤ ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 :=
    Finset.sum_nonneg fun e _ => connWithinProb_nonneg d q hq S e.1
  calc
    (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1 ≤
        (p : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 :=
      mul_le_mul_of_nonneg_left hsum p.coe_nonneg
    _ ≤ (q : ℝ) * ∑ e ∈ boundaryEdges d S, connWithinProb d q hq S e.1 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hpq) hsum0


theorem bondParam_mono : Monotone bondParam := by
  intro beta gamma hbg
  unfold bondParam
  apply Real.toNNReal_le_toNNReal
  have hexp : Real.exp (-gamma) ≤ Real.exp (-beta) :=
    Real.exp_le_exp.mpr (neg_le_neg hbg)
  linarith



theorem exists_phiBeta_witness_of_lt_tildeBetaCPerco {beta : ℝ}
    (hbeta : beta < tildeBetaCPerco d) :
    ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d beta S < 1 := by
  unfold tildeBetaCPerco at hbeta
  have hne : (tildeBetaCPercoSet d).Nonempty := by
    refine ⟨0, le_rfl, {origin d}, by simp, ?_⟩
    simp [phiBeta, bondParam, phi]
  obtain ⟨gamma, hgamma, hbg⟩ := exists_lt_of_lt_csSup hne hbeta
  obtain ⟨hgamma0, S, h0S, hphi⟩ := hgamma
  refine ⟨S, h0S, ?_⟩
  unfold phiBeta at hphi ⊢
  exact (shk_phi_mono (bondParam_le_one beta) (bondParam_le_one gamma)
    (bondParam_mono hbg.le) S).trans_lt hphi




noncomputable def shk_twoPointProb (p : ℝ≥0) (hp : p ≤ 1)
    (x : Site d) : ℝ :=
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
    {omega | Connected d omega (origin d) x}


theorem shk_withinBoxEvent_mono (x : Site d) :
    Monotone (fun n : ℕ =>
      connWithinEvent d (box d n) (origin d) x) := by
  intro m n hmn omega homega
  obtain ⟨h0m, hxm, hconn⟩ := homega
  have hsub : box d m ⊆ box d n := box_mono d hmn
  exact ⟨hsub h0m, hsub hxm,
    connectedWithin_mono_set' omega hsub hconn⟩


theorem shk_connected_iff_mem_iUnion_withinBox (omega : ConfigSpace (Sym2 (Site d)))
    (x : Site d) :
    Connected d omega (origin d) x ↔
      omega ∈ ⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x := by
  constructor
  · intro hconn
    obtain ⟨w⟩ := hconn
    obtain ⟨n, hn⟩ := finset_subset_box_su w.support.toFinset
    have hw : ∀ z ∈ w.support, z ∈ box d n := by
      intro z hz
      exact hn (by simpa using hz)
    have h0 : origin d ∈ box d n := hw _ w.start_mem_support
    have hx : x ∈ box d n := hw _ w.end_mem_support
    refine Set.mem_iUnion.mpr ⟨n, h0, hx, ?_⟩
    exact walk_induce_reachable (openSubgraph d omega) (box d n) w hw h0 hx
  · intro hmem
    obtain ⟨n, h0, hx, hconn⟩ := Set.mem_iUnion.mp hmem
    exact hconn.connected


theorem shk_connWithinBox_tendsto_twoPoint (p : ℝ≥0) (hp : p ≤ 1)
    (x : Site d) :
    Tendsto (fun n =>
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (box d n) (origin d) x))
      atTop (nhds (shk_twoPointProb p hp x)) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (shk_withinBoxEvent_mono (d := d) x)
  have hreal := (ENNReal.tendsto_toReal
    (measure_ne_top mu (⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x))).comp hmeasure
  have hunion : (⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x) =
      {omega | Connected d omega (origin d) x} := by
    ext omega
    exact (shk_connected_iff_mem_iUnion_withinBox omega x).symm
  rw [hunion] at hreal
  simpa only [Function.comp_apply, Measure.real, shk_twoPointProb, mu] using hreal



theorem shk_twoPoint_partialSum_le (p : ℝ≥0) (hp : p ≤ 1)
    (S : Finset (Site d)) (h0S : origin d ∈ S)
    (hphi : phi d p hp S < 1) (T : Finset (Site d)) :
    ∑ x ∈ T, shk_twoPointProb p hp x ≤
      (S.card : ℝ) / (1 - phi d p hp S) := by
  let mu := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  let f : ℕ → Site d → ℝ := fun n x =>
    mu.real (connWithinEvent d (box d n) (origin d) x)
  have hlim : Tendsto (fun n => ∑ x ∈ T, f n x) atTop
      (nhds (∑ x ∈ T, shk_twoPointProb p hp x)) := by
    exact tendsto_finsetSum T fun x _ =>
      shk_connWithinBox_tendsto_twoPoint p hp x
  obtain ⟨N, hTN⟩ := finset_subset_box_su T
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop N] with n hn
  have hTbox : T ⊆ boxFinset d n := by
    intro x hx
    apply mem_boxFinset.mpr
    exact box_mono d hn (hTN (by simpa using hx))
  have hboxcoe : (boxFinset d n : Set (Site d)) = box d n := by
    ext x
    simp only [Finset.mem_coe, mem_boxFinset]
  calc
    (∑ x ∈ T, f n x) ≤ ∑ x ∈ boxFinset d n, f n x :=
      Finset.sum_le_sum_of_subset_of_nonneg hTbox
        (fun x _ _ => measureReal_nonneg)
    _ = shk_restrictedSusceptibility p hp (boxFinset d n) (origin d) := by
      simp only [f, mu, shk_restrictedSusceptibility,
        shk_connEvent_singleton_eq_connWithinEvent, hboxcoe]
    _ ≤ (S.card : ℝ) / (1 - phi d p hp S) :=
      shk_restrictedSusceptibility_le p hp S (boxFinset d n) h0S
        (mem_boxFinset.mpr (origin_mem_box' n)) hphi


theorem shk_twoPoint_summable_of_phi_lt_one (p : ℝ≥0) (hp : p ≤ 1)
    (S : Finset (Site d)) (h0S : origin d ∈ S)
    (hphi : phi d p hp S < 1) :
    Summable (shk_twoPointProb (d := d) p hp) := by
  apply summable_of_sum_le (fun _ => measureReal_nonneg)
  exact shk_twoPoint_partialSum_le p hp S h0S hphi




theorem finite_susceptibility_of_lt_tildeBetaCPerco {beta : ℝ}
    (hbeta : beta < tildeBetaCPerco d) :
    ∃ S : Finset (Site d),
      origin d ∈ S ∧
      phiBeta d beta S < 1 ∧
      Summable (shk_twoPointProb (d := d) (bondParam beta)
        (bondParam_le_one beta)) ∧
      ∀ Lam : Finset (Site d), origin d ∈ Lam →
        shk_restrictedSusceptibility (bondParam beta)
            (bondParam_le_one beta) Lam (origin d) ≤
          (S.card : ℝ) / (1 - phiBeta d beta S) := by
  obtain ⟨S, h0S, hphi⟩ :=
    exists_phiBeta_witness_of_lt_tildeBetaCPerco hbeta
  refine ⟨S, h0S, hphi, ?_, ?_⟩
  · exact shk_twoPoint_summable_of_phi_lt_one (bondParam beta)
      (bondParam_le_one beta) S h0S hphi
  · intro Lam h0Lam
    exact shk_restrictedSusceptibility_le (bondParam beta)
      (bondParam_le_one beta) S Lam h0S h0Lam hphi

end Sharpness

end StatMech
