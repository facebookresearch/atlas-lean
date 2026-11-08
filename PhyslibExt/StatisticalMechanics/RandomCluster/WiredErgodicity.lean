/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FKDisjointBoxReduce
public import PhyslibExt.StatisticalMechanics.RandomCluster.DisjointBoxFactorization
public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination
public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain
public import PhyslibExt.StatisticalMechanics.RandomCluster.MultiEdgeDecay
public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# Ergodicity of the wired `q = 2` infinite-volume measure

The wired `q = 2` infinite-volume random-cluster measure on `ℤ^d`, `d ≥ 1`, is ergodic under
translations.

## i. Overview

Translate a box `Λ_N` by `(2N + 1) e_{i₀}` so that it is disjoint from `Λ_N`; both sit inside
`Λ_{N+r}`. Conditioned on the edges outside the translated box, the wired measure on the inner box
is dominated by the wired measure on `Λ_N` (domain Markov property with an induced wiring), and the
event on the translated box depends only on edges outside `F`. The product bound of
`FKDisjointBoxDomainMarkov` gives the disjoint-box factorization `fwm_WiredDisjointBoxFactorise`
for the wired box measures, which implies upper decay, mixing, and ergodicity.

## ii. Key results

- `cbk_condBcProb_innerRestrict_le` : conditional domination of the inner box by the wired box
  measure.
- `cbk_factorise_pair_ge1` : the factorization bound for one pair of multi-open events.
- `cbk_wiredDisjointBoxFactorise_ge1` : the factorization bound for all pairs.
- `cbk_wiredIV_isErgodic` : ergodicity of the wired `q = 2` infinite-volume measure.

## iii. Table of contents

- A. Inner boxes and induced wirings
- B. Shifted boxes
- C. Factorization and ergodicity

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Theorem 4.19.
-/

@[expose] public section

open MeasureTheory Filter Topology Set SimpleGraph
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open ConfigSpace

variable {d : ℕ}

/-! ## A. Inner boxes and induced wirings -/

lemma cbk_boxVertInclLE_val {N m : ℕ} (h : N ≤ m) (x : boxVerts d N) :
    (boxVertInclLE d h x : Site d) = (x : Site d) := rfl

lemma cbk_adjMatch {N m : ℕ} (h : N ≤ m) :
    ocd_AdjMatch (boxGraph d N) (boxGraph d m) (boxVertInclLE d h) :=
  ocd_latticeAdjMatch (boxVertInclLE d h) (cbk_boxVertInclLE_val h)

lemma cbk_margin {N m : ℕ} (hNm : N < m) (x : boxVerts d N) :
    ¬ boxBoundary d m (boxVertInclLE d (le_of_lt hNm) x) := by
  intro hbdry
  rw [boxBoundary, mem_vertexBoundary] at hbdry
  apply hbdry.2
  have hxN : (x : Site d) ∈ box d N := x.2
  exact box_mono d (by omega) hxN

lemma cbk_inducedWiring_le {N m : ℕ} (hN : 1 ≤ N) (hNm : N < m)
    (ψ : ConfigSpace (Sym2 (boxVerts d m))) :
    ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) (boxBoundary d m) ψ
      ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) :=
  ocd_latticeInducedWiring_le (boxVertInclLE d (le_of_lt hNm)) (cbk_boxVertInclLE_val _)
    (dfi_boxVertInclLE_injective d _) (boxBoundary d m) (boxBoundary d N)
    (cbk_margin hNm) (fun x z => flc_hbdryIn_box hN x z) ψ

lemma cbk_condBcProb_innerRestrict_le {N m : ℕ} (hN : 1 ≤ N) (hNm : N < m)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 (boxVerts d m)))
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A).indicator (fun _ => (1 : ℝ)) ρ
        * condBcProb (boxGraph d m)
            (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d m)) p q
            (ocd_innerEdgeFinset (boxVertInclLE d (le_of_lt hNm))) ψ ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d N) (boxBoundary d N) p q ω
          :=
  ocd_condBcProb_innerRestrict_le (dfi_boxVertInclLE_injective d (le_of_lt hNm))
    (cbk_adjMatch (le_of_lt hNm)) (boxBoundary d N) hp hp1 hq ψ
    (cbk_inducedWiring_le hN hNm ψ) hA

lemma cbk_nearMass_eq_sum (N : ℕ) (t : Finset (Sym2 (boxVerts d N))) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N)))
      = ∑ ω, (cdc_boxMultiOpenEvent N t).indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d N) (boxBoundary d N) p 2 ω := by
  rw [ftb_fmu_eq_cdc_multiOpen, cdc_multiOpenEvent_image_eq_boxRestrict N t]
  have hmeas : MeasurableSet (boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t)) :=
    (continuous_boxRestrict d N).measurable (MeasurableSet.of_discrete)
  rw [wiredFiniteMeasure_real_boxRestrictEvent N hp hp1 (cdc_boxMultiOpenEvent N t) hmeas]

lemma cbk_ocd_innerEdge_eq {N m : ℕ} (h : N ≤ m) :
    ocd_innerEdge (boxVertInclLE d h) = innerEdgeLE d h := rfl

lemma cbk_innerRestrict_preimage {N m : ℕ} (h : N ≤ m) (t : Finset (Sym2 (boxVerts d N))) :
    ocd_innerRestrict (boxVertInclLE d h) ⁻¹' (cdc_boxMultiOpenEvent N t)
      = cdc_boxMultiOpenEvent m (t.image (innerEdgeLE d h)) := by
  rw [show cdc_boxMultiOpenEvent N t = med_genericMultiOpenEvent t from rfl,
    ocd_innerRestrict_preimage_multiOpenEvent (dfi_boxVertInclLE_injective d h) t,
    cbk_ocd_innerEdge_eq h]
  rfl

/-! ## B. Shifted boxes -/

/-- The vector `(2N + 1) e_{i₀}`, which translates `Λ_N` to a disjoint box. -/
noncomputable def cbk_shiftVec {d : ℕ} (i₀ : Fin d) (N : ℕ) : Site d :=
  fun i => if i = i₀ then (2 * N + 1 : ℤ) else 0

lemma cbk_vrad_shiftVec {d : ℕ} (i₀ : Fin d) (N : ℕ) :
    flc_vrad (cbk_shiftVec i₀ N) = 2 * N + 1 := by
  have habs : ((2 * (N : ℤ) + 1)).natAbs = 2 * N + 1 := by
    rw [Int.natAbs_eq_iff]; left; push_cast; ring
  unfold flc_vrad cbk_shiftVec
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    by_cases hi : i = i₀ <;> simp only [hi, ite_true, ite_false]
    · rw [habs]
    · simp
  · refine le_trans ?_ (Finset.le_sup
      (f := fun i => ((if i = i₀ then (2 * (N : ℤ) + 1) else 0)).natAbs) (Finset.mem_univ i₀))
    simp only [ite_true]
    rw [habs]

lemma cbk_box_disjoint_transBox {d : ℕ} (i₀ : Fin d) (N : ℕ) {y : Site d}
    (hy : y ∈ box d N) (hyt : y ∈ fvs_transBox d N (cbk_shiftVec i₀ N)) : False := by
  have h0 : (y i₀).natAbs ≤ N := hy i₀
  have hyt' : (y - cbk_shiftVec i₀ N) ∈ box d N := hyt
  have h1 : ((y - cbk_shiftVec i₀ N) i₀).natAbs ≤ N := hyt' i₀
  have hv0 : cbk_shiftVec i₀ N i₀ = (2 * N + 1 : ℤ) := by simp [cbk_shiftVec]
  have hsub : (y - cbk_shiftVec i₀ N) i₀ = y i₀ - (2 * N + 1 : ℤ) := by
    simp [Pi.sub_apply, hv0]
  rw [hsub] at h1
  have ha : |y i₀| ≤ (N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h0
  have hb : |y i₀ - (2 * N + 1 : ℤ)| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  rw [abs_le] at ha hb
  omega

/-- The vertex of `Λ_{N+r}` obtained by translating a vertex of `Λ_N` by `v` with `‖v‖_∞ ≤ r`. -/
noncomputable def cbk_shiftBoxVert {N r : ℕ} (v : Site d) (hv : flc_vrad v ≤ r)
    (a : boxVerts d N) : boxVerts d (N + r) :=
  ⟨v + (a : Site d), by
    intro i
    have ha : ((a : Site d) i).natAbs ≤ N := a.2 i
    have hvi : (v i).natAbs ≤ flc_vrad v := flc_vrad_le v i
    have : ((v + (a : Site d)) i) = v i + (a : Site d) i := by simp [Pi.add_apply]
    rw [this]
    calc (v i + (a : Site d) i).natAbs ≤ (v i).natAbs + ((a : Site d) i).natAbs :=
          Int.natAbs_add_le _ _
      _ ≤ flc_vrad v + N := Nat.add_le_add hvi ha
      _ ≤ N + r := by omega⟩

/-- The edge of `Λ_{N+r}` obtained by translating an edge of `Λ_N` by `v` with `‖v‖_∞ ≤ r`. -/
noncomputable def cbk_shiftEdge {N r : ℕ} (v : Site d) (hv : flc_vrad v ≤ r) :
    Sym2 (boxVerts d N) → Sym2 (boxVerts d (N + r)) :=
  Sym2.map (cbk_shiftBoxVert v hv)

lemma cbk_edgeIncl_shiftEdge {N r : ℕ} (v : Site d) (hv : flc_vrad v ≤ r)
    (eb : Sym2 (boxVerts d N)) :
    edgeIncl d (N + r) (cbk_shiftEdge v hv eb) = (Multiplicative.ofAdd v) • (edgeIncl d N eb) := by
  have hvert : ∀ a : boxVerts d N,
      ((cbk_shiftBoxVert v hv a : boxVerts d (N + r)) : Site d)
        = (Multiplicative.ofAdd v) • (a : Site d) := by
    intro a
    change v + (a : Site d) = (Multiplicative.ofAdd v) • (a : Site d)
    funext i
    rw [StatMech.Percolation.smul_site_apply, Pi.add_apply]
    simp [toAdd_ofAdd]
  refine Sym2.inductionOn eb (fun a b => ?_)
  unfold cbk_shiftEdge edgeIncl
  rw [Sym2.map_mk, Sym2.map_mk, Sym2.map_mk]
  rw [StatMech.Percolation.smul_sym2_mk, hvert a, hvert b]

lemma cbk_shifted_realised {N r : ℕ} (v : Site d) (hv : flc_vrad v ≤ r)
    (t : Finset (Sym2 (boxVerts d N))) :
    (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)
      = (t.image (cbk_shiftEdge v hv)).image (edgeIncl d (N + r)) := by
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro eb _
  simp only [Function.comp_apply]
  rw [cbk_edgeIncl_shiftEdge v hv eb]

lemma cbk_innerEdgeLE_eq {N r : ℕ} (h : N ≤ N + r) :
    (Set.range (innerEdgeLE d h)) = Set.range (ocd_innerEdge (boxVertInclLE d h)) := rfl

lemma cbk_shiftBoxVert_not_inner {N r : ℕ} (i₀ : Fin d) {hv : flc_vrad (cbk_shiftVec i₀ N) ≤ r}
    (a : boxVerts d N) :
    ((cbk_shiftBoxVert (cbk_shiftVec i₀ N) hv a : boxVerts d (N + r)) : Site d) ∉ box d N := by
  intro hmem
  have hy : (cbk_shiftVec i₀ N + (a : Site d)) ∈ box d N := hmem
  have hyt : (cbk_shiftVec i₀ N + (a : Site d)) ∈ fvs_transBox d N (cbk_shiftVec i₀ N) := by
    change (cbk_shiftVec i₀ N + (a : Site d)) - cbk_shiftVec i₀ N ∈ box d N
    have : (cbk_shiftVec i₀ N + (a : Site d)) - cbk_shiftVec i₀ N = (a : Site d) := by ring
    rw [this]; exact a.2
  exact cbk_box_disjoint_transBox i₀ N hy hyt

lemma cbk_shiftEdge_not_range {N r : ℕ} (i₀ : Fin d) {hv : flc_vrad (cbk_shiftVec i₀ N) ≤ r}
    (eb : Sym2 (boxVerts d N)) :
    cbk_shiftEdge (cbk_shiftVec i₀ N) hv eb ∉ Set.range (innerEdgeLE d (Nat.le_add_right N r)) := by
  revert eb
  refine Sym2.ind (fun a b => ?_)
  rintro ⟨e', he'⟩
  revert he'
  refine Sym2.ind (fun c c' hcc' => ?_) e'
  unfold cbk_shiftEdge innerEdgeLE at hcc'
  rw [Sym2.map_mk, Sym2.map_mk, Sym2.eq_iff] at hcc'
  rcases hcc' with ⟨h1, _⟩ | ⟨h1, _⟩
  · refine cbk_shiftBoxVert_not_inner (hv := hv) i₀ a ?_
    have : ((cbk_shiftBoxVert (cbk_shiftVec i₀ N) hv a : boxVerts d (N + r)) : Site d)
        = ((boxVertInclLE d (Nat.le_add_right N r) c : boxVerts d (N + r)) : Site d) :=
      congrArg Subtype.val h1.symm
    rw [this]; exact c.2
  · refine cbk_shiftBoxVert_not_inner (hv := hv) i₀ b ?_
    have : ((cbk_shiftBoxVert (cbk_shiftVec i₀ N) hv b : boxVerts d (N + r)) : Site d)
        = ((boxVertInclLE d (Nat.le_add_right N r) c : boxVerts d (N + r)) : Site d) :=
      congrArg Subtype.val h1.symm
    rw [this]; exact c.2

/-! ## C. Factorization and ergodicity -/

lemma cbk_boxMultiOpen_union (m : ℕ) (s s' : Finset (Sym2 (boxVerts d m))) :
    cdc_boxMultiOpenEvent m (s ∪ s')
      = cdc_boxMultiOpenEvent m s ∩ cdc_boxMultiOpenEvent m s' := by
  ext σ
  simp only [cdc_boxMultiOpenEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · rintro ⟨h1, h2⟩ e (he | he)
    · exact h1 e he
    · exact h2 e he

lemma cbk_factorise_pair_ge1 {d : ℕ} (i₀ : Fin d) {N : ℕ} (hN : 1 ≤ N)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (t_T t_T' : Finset (Sym2 (boxVerts d N))) :
    (wiredFiniteMeasure d (N + (flc_vrad (cbk_shiftVec i₀ N) + 1)) hp hp1
        (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real
          (fmu_multiOpen (t_T.image (edgeIncl d N)) ∩
            (shift (Multiplicative.ofAdd (- cbk_shiftVec i₀ N))
              : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d)))
              ⁻¹' fmu_multiOpen (t_T'.image (edgeIncl d N)))
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t_T.image (edgeIncl d N)))
        * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real
              (fmu_multiOpen (t_T'.image (edgeIncl d N))) := by
  classical
  set v := cbk_shiftVec i₀ N with hvdef
  set c := flc_vrad v with hcdef
  set r := c + 1 with hrdef
  set g := Multiplicative.ofAdd (- v) with hgdef
  have hc : c = 2 * N + 1 := cbk_vrad_shiftVec i₀ N
  have hNr : N ≤ N + r := Nat.le_add_right N r
  have hvr : flc_vrad v ≤ r := by rw [hrdef]; omega
  set T := t_T.image (edgeIncl d N) with hT
  set T' := t_T'.image (edgeIncl d N) with hT'
  have hginv : (g⁻¹ : Multiplicative (Site d)) = Multiplicative.ofAdd v := by
    rw [hgdef, ← ofAdd_neg, neg_neg]
  set tT := t_T.image (innerEdgeLE d hNr) with htT
  have hTreal : T = tT.image (edgeIncl d (N + r)) := by
    rw [hT, htT, Finset.image_image]
    apply Finset.image_congr; intro e _
    simp only [Function.comp_apply, edgeIncl_innerEdgeLE]
  set tT' := t_T'.image (cbk_shiftEdge v hvr) with htT'
  have hT'real : T'.image (fun e => g⁻¹ • e) = tT'.image (edgeIncl d (N + r)) := by
    rw [hT', htT']
    have : (t_T'.image (edgeIncl d N)).image (fun e => g⁻¹ • e)
        = (t_T'.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) := by
      apply Finset.image_congr; intro e _; rw [hginv]
    rw [this, cbk_shifted_realised v hvr t_T']
  set F := ocd_innerEdgeFinset (boxVertInclLE d hNr) with hF
  have hdisj : ∀ e ∈ tT', e ∉ F := by
    intro e he
    rw [htT', Finset.mem_image] at he
    obtain ⟨eb, _, rfl⟩ := he
    rw [hF]
    intro hmem
    rw [ocd_mem_innerEdgeFinset, ← cbk_innerEdgeLE_eq hNr] at hmem
    exact cbk_shiftEdge_not_range (hv := hvr) i₀ eb hmem
  have hCC' : boundaryCliqueGraph (boxBoundary d (N + r))
      ≤ boundaryCliqueGraph (boxBoundary d (N + r)) := le_refl _
  have hαcap : ∀ ψ ∈ fibreReps F,
      (∑ ρ, (cdc_boxMultiOpenEvent (N + r) tT).indicator (fun _ => (1 : ℝ)) ρ
        * condBcProb (boxGraph d (N + r))
            (boundaryCliqueGraph (boxBoundary d (N + r))) p 2 F ψ ρ)
        ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
            : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T) := by
    intro ψ _
    have hcap := cbk_condBcProb_innerRestrict_le (N := N) (m := N + r) hN
      (by omega : N < N + r) hp hp1 (by norm_num : (1 : ℝ) ≤ 2) ψ
      (A := cdc_boxMultiOpenEvent N t_T) (cdc_boxMultiOpenEvent_isIncreasing N t_T)
    have hSAeq : cdc_boxMultiOpenEvent (N + r) tT
        = ocd_innerRestrict (boxVertInclLE d (le_of_lt (by omega : N < N + r)))
            ⁻¹' (cdc_boxMultiOpenEvent N t_T) := by
      rw [htT, cbk_innerRestrict_preimage (le_of_lt (by omega : N < N + r)) t_T]
    rw [hSAeq, hF]
    refine le_trans hcap (le_of_eq ?_)
    rw [hT, ← cbk_nearMass_eq_sum N t_T hp hp1]
  have hBcap : (wiredFiniteMeasure d (N + r) hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT'))
      ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen T') := by
    have hSBmass : boxRestrict d (N + r) ⁻¹' (cdc_boxMultiOpenEvent (N + r) tT')
        = cdc_multiOpenEvent ((t_T'.image (edgeIncl d N)).image
            (fun e => (Multiplicative.ofAdd v) • e)) := by
      rw [← cdc_multiOpenEvent_image_eq_boxRestrict (N + r) tT', htT',
        ← cbk_shifted_realised v hvr t_T']
    rw [hSBmass]
    have hsq := flc_squeeze_lower v N t_T' hp hp1 N (le_refl N) hN
    rw [lmc_transBoxMass_eq_centred v N t_T' hp hp1 N (le_refl N)] at hsq
    rw [show N + r = N + flc_vrad v + 1 by rw [hrdef, ← hcdef]; ring]
    rw [hT', ftb_fmu_eq_cdc_multiOpen]
    exact hsq
  have hfac := dgf_factorise_pair hp hp1 (inferInstance :
    DecidableRel (boundaryCliqueGraph (boxBoundary d (N + r))).Adj)
    hTreal hT'real hdisj hCC' hαcap hBcap
  exact hfac

lemma cbk_wiredDisjointBoxFactorise_ge1 {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    fwm_WiredDisjointBoxFactorise hp hp1
      (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d))))) := by
  classical
  intro P N hreal
  set i₀ : Fin d := ⟨0, hd⟩ with hi₀
  set K := max N 1 with hKdef
  have hNK : N ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := le_max_right _ _
  have hrealK : ∀ T ∈ P, ∃ t : Finset (Sym2 (boxVerts d K)), T = t.image (edgeIncl d K) := by
    intro T hT
    obtain ⟨t₀, ht₀⟩ := hreal T hT
    exact ⟨t₀.image (innerEdgeLE d hNK), fwm_realised_box_mono hNK ht₀⟩
  set v := cbk_shiftVec i₀ K with hvdef
  set rK := flc_vrad v + 1 with hrK
  set g := Multiplicative.ofAdd (- v) with hgdef
  refine ⟨g, (K + rK) - N, fun T hT T' hT' => ?_⟩
  have hNr : N + ((K + rK) - N) = K + rK := by omega
  obtain ⟨tT, hTreal⟩ := hrealK T hT
  obtain ⟨tT', hT'real⟩ := hrealK T' hT'
  obtain ⟨t₀T, ht₀T⟩ := hreal T hT
  obtain ⟨t₀T', ht₀T'⟩ := hreal T' hT'
  constructor
  · rw [hNr]
    have hginv : (g⁻¹ : Multiplicative (Site d)) = Multiplicative.ofAdd v := by
      rw [hgdef, ← ofAdd_neg, neg_neg]
    have hvr : flc_vrad v ≤ rK := by rw [hrK]; omega
    refine ⟨tT.image (innerEdgeLE d (Nat.le_add_right K rK))
        ∪ tT'.image (cbk_shiftEdge v hvr), ?_⟩
    rw [Finset.image_union, hTreal, hT'real]
    congr 1
    · rw [Finset.image_image]
      apply Finset.image_congr; intro e _
      simp only [Function.comp_apply, edgeIncl_innerEdgeLE]
    · rw [show (fun e => g⁻¹ • e) = (fun e : Sym2 (Site d) => (Multiplicative.ofAdd v) • e) by
            funext e; rw [hginv],
        cbk_shifted_realised v hvr tT']
  · rw [hNr]
    have hpair := cbk_factorise_pair_ge1 i₀ hK1 hp hp1 tT tT'
    rw [← hvdef, ← hrK, ← hgdef] at hpair
    rw [hTreal, hT'real]
    refine hpair.trans (mul_le_mul ?_ ?_ measureReal_nonneg measureReal_nonneg)
    · rw [show tT.image (edgeIncl d K) = T by rw [← hTreal]]
      exact fwm_wired_domain_monotone_of_realised (N := N) (m := K) hNK t₀T ht₀T hp hp1
    · rw [show tT'.image (edgeIncl d K) = T' by rw [← hT'real]]
      exact fwm_wired_domain_monotone_of_realised (N := N) (m := K) hNK t₀T' ht₀T' hp hp1

/--
**Ergodicity of the wired random-cluster measure.** For `d ≥ 1` and `p ∈ (0, 1)`, the wired `q = 2`
infinite-volume random-cluster measure on `ℤ^d` is ergodic under translations
(Grimmett, *The Random-Cluster Model*, 2006, Theorem 4.19).
-/
theorem cbk_wiredIV_isErgodic {d : ℕ} (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))) :=
  fwm_wiredIV_isErgodic_of_factorise hp hp1 (cbk_wiredDisjointBoxFactorise_ge1 hd hp hp1)

end FK

end StatMech
