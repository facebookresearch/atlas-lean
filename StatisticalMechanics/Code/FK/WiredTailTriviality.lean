/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.FreeTailTriviality
import Code.FK.CrossBoxGeneralKeystone











open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

namespace StatMech.FK

open StatMech.Lattice

variable {d : Nat}




theorem wiredFinite_inter_outside_le_mul_generalQ
    {N m : Nat} (hN : 1 <= N) (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A)
    {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
    (hB : DependsOnOutside
      (ocd_innerEdgeFinset (Vin := boxVerts d N)
        (boxVertInclLE d (le_of_lt hNm))) B) :
    (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d m ⁻¹'
          ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A) ∩ B)) <=
      (wiredFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) *
        (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d m ⁻¹' B) := by
  classical
  let F := ocd_innerEdgeFinset (Vin := boxVerts d N)
    (boxVertInclLE d (le_of_lt hNm))
  let Aout := ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A
  let C := boundaryCliqueGraph (boxBoundary d m)
  let c := ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
    wiredFkProb (boxGraph d N) (boxBoundary d N) p q omega
  have hAout : IsIncreasing Aout := by
    intro omega eta home hmem
    exact hA (fun e => home (ocd_innerEdge (boxVertInclLE d
      (le_of_lt hNm)) e)) hmem
  have hper (psi : ConfigSpace (Sym2 (boxVerts d m))) :
      (∑ rho, Aout.indicator (fun _ => (1 : Real)) rho *
          condBcProb (boxGraph d m) C p q F psi rho) <= c := by
    simpa only [F, Aout, C, c] using
      cbk_condBcProb_innerRestrict_le (d := d) hN hNm hp hp1 hq psi hA
  have hfinite :
      (∑ rho, (Aout ∩ B).indicator (fun _ => (1 : Real)) rho *
          bcProb (boxGraph d m) C p q rho) <=
        c * (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
          bcProb (boxGraph d m) C p q rho) := by
    rw [bcProb_fibre_decompose (boxGraph d m) C hp hp1
      (lt_of_lt_of_le one_pos hq) F B,
      bcProb_fibre_decompose (boxGraph d m) C hp hp1
        (lt_of_lt_of_le one_pos hq) F (Aout ∩ B)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro psi hpsi
    rw [fibreReps, Finset.mem_filter] at hpsi
    let mass := ∑ sigma ∈ condFibre F psi,
      bcProb (boxGraph d m) C p q sigma
    have hmass : 0 <= mass := Finset.sum_nonneg fun sigma _ =>
      bcProb_nonneg (boxGraph d m) C hp hp1
        (lt_of_lt_of_le one_pos hq) sigma
    have hBout :
        (∑ rho, B.indicator (fun _ => (1 : Real)) rho *
          condBcProb (boxGraph d m) C p q F psi rho) =
          B.indicator (fun _ => (1 : Real)) psi := by
      simpa only [F] using condBcProb_sum_outside (boxGraph d m) C hp hp1
        (lt_of_lt_of_le one_pos hq) hB hpsi.2
    have hcross :
        (∑ rho, (Aout ∩ B).indicator (fun _ => (1 : Real)) rho *
          condBcProb (boxGraph d m) C p q F psi rho) =
          B.indicator (fun _ => (1 : Real)) psi *
            (∑ rho, Aout.indicator (fun _ => (1 : Real)) rho *
              condBcProb (boxGraph d m) C p q F psi rho) := by
      simpa only [F] using
        (condBcProb_cross_outside (boxGraph d m) C (A := Aout) hB)
    rw [hBout, hcross]
    have hind : 0 <= B.indicator (fun _ => (1 : Real)) psi :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) psi
    calc
      mass * (B.indicator (fun _ => (1 : Real)) psi *
          ∑ rho, Aout.indicator (fun _ => (1 : Real)) rho *
            condBcProb (boxGraph d m) C p q F psi rho) <=
        mass * (B.indicator (fun _ => (1 : Real)) psi * c) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hper psi) hind) hmass
      _ = c * (mass * B.indicator (fun _ => (1 : Real)) psi) := by ring
  have hcross : boxRestrict d m ⁻¹' (Aout ∩ B) =
      (boxRestrict d N ⁻¹' A) ∩ (boxRestrict d m ⁻¹' B) := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_inter_iff, Aout]
    rw [show ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm))
      (boxRestrict d m omega) = boxRestrict d N omega from
        boxRestrictLE_boxRestrict d (le_of_lt hNm) omega]
  have hmeasA : MeasurableSet (boxRestrict d N ⁻¹' A) :=
    (continuous_boxRestrict d N).measurable MeasurableSet.of_discrete
  have hmeasB : MeasurableSet (boxRestrict d m ⁻¹' B) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) (Aout ∩ B) (by
        rw [hcross]
        exact hmeasA.inter hmeasB),
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
      (zero_lt_one.trans_le hq) B hmeasB,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent N hp hp1
      (zero_lt_one.trans_le hq) A hmeasA]
  simpa only [c, C, bcProb_clique_eq_wiredFkProb] using hfinite



private theorem dependsOnOutside_boxRestrictLE_preimage
    {N m r : Nat} (hNm : N < m) (hmr : m <= r)
    {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
    (hB : DependsOnOutside
      (ocd_innerEdgeFinset (Vin := boxVerts d N)
        (boxVertInclLE d (le_of_lt hNm))) B) :
    DependsOnOutside
      (ocd_innerEdgeFinset (Vin := boxVerts d N)
        (boxVertInclLE d (le_trans (le_of_lt hNm) hmr)))
      (boxRestrictLE d hmr ⁻¹' B) := by
  intro psi rho hagree
  apply hB
  intro e he
  change rho (innerEdgeLE d hmr e) = psi (innerEdgeLE d hmr e)
  apply hagree (innerEdgeLE d hmr e)
  intro hin
  rw [ocd_mem_innerEdgeFinset] at hin
  obtain ⟨en, hen⟩ := hin
  apply he
  rw [ocd_mem_innerEdgeFinset]
  refine ⟨en, ?_⟩
  change innerEdgeLE d (le_of_lt hNm) en = e
  apply edgeIncl_injective d m
  change innerEdgeLE d (le_trans (le_of_lt hNm) hmr) en =
    innerEdgeLE d hmr e at hen
  have hfull := congrArg (edgeIncl d r) hen
  rw [edgeIncl_innerEdgeLE, edgeIncl_innerEdgeLE] at hfull
  simpa [edgeIncl_innerEdgeLE] using hfull



theorem wiredInfiniteVolume_inter_boxOutside_le_finite_generalQ
    {N m : Nat} (hN : 1 <= N) (hNm : N < m)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A)
    {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
    (hB : DependsOnOutside
      (ocd_innerEdgeFinset (Vin := boxVerts d N)
        (boxVertInclLE d (le_of_lt hNm))) B) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        ((boxRestrict d N ⁻¹' A) ∩ (boxRestrict d m ⁻¹' B)) <=
      (wiredFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d m ⁻¹' B) := by
  classical
  let mu := wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  obtain ⟨phi, hphi, hconv⟩ :=
    wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hlarge : ∀ᶠ k in atTop, m <= phi k :=
    (eventually_ge_atTop m).mono fun k hk => hk.trans (hphi.id_le k)
  have hineq : ∀ᶠ k in atTop,
      (wiredFiniteMeasure d (phi k) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
          ((boxRestrict d N ⁻¹' A) ∩ (boxRestrict d m ⁻¹' B)) <=
        (wiredFiniteMeasure d N hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (boxRestrict d N ⁻¹' A) *
          (wiredFiniteMeasure d (phi k) hp hp1
            (zero_lt_one.trans_le hq) : Measure _).real
              (boxRestrict d m ⁻¹' B) := by
    filter_upwards [hlarge] with k hmk
    let Bk : Set (ConfigSpace (Sym2 (boxVerts d (phi k)))) :=
      boxRestrictLE d hmk ⁻¹' B
    have hNk : N < phi k := hNm.trans_le hmk
    have hBk : DependsOnOutside
        (ocd_innerEdgeFinset (Vin := boxVerts d N)
          (boxVertInclLE d (le_of_lt hNk))) Bk := by
      exact dependsOnOutside_boxRestrictLE_preimage hNm hmk hB
    have hfinite := wiredFinite_inter_outside_le_mul_generalQ
      hN hNk hp hp1 hq hA hBk
    have hBfull : boxRestrict d (phi k) ⁻¹' Bk =
        boxRestrict d m ⁻¹' B := by
      ext omega
      simp only [Bk, Set.mem_preimage, boxRestrictLE_boxRestrict]
    have hcross : boxRestrict d (phi k) ⁻¹'
        ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNk)) ⁻¹' A) ∩ Bk) =
        (boxRestrict d N ⁻¹' A) ∩ (boxRestrict d m ⁻¹' B) := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_inter_iff, Bk]
      rw [show ocd_innerRestrict (boxVertInclLE d (le_of_lt hNk))
          (boxRestrict d (phi k) omega) = boxRestrict d N omega from
        boxRestrictLE_boxRestrict d (le_of_lt hNk) omega]
      rw [boxRestrictLE_boxRestrict]
    rw [hcross, hBfull] at hfinite
    exact hfinite
  have hleft := hconv.tendsto_real_of_isClopen
    ((fkWiredLimit_isClopen_preimage N A).inter
      (fkWiredLimit_isClopen_preimage m B))
  have hright0 := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage m B)
  have hconst : Tendsto (fun _ : Nat =>
      (wiredFiniteMeasure d N hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A)) atTop
      (nhds ((wiredFiniteMeasure d N hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A))) := tendsto_const_nhds
  have hright := hconst.mul hright0
  exact le_of_tendsto_of_tendsto hleft hright hineq




theorem wiredInfiniteVolume_inter_exterior_le_finite_generalQ
    (N : Nat) (hN : 1 <= N)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A)
    {s : Set (ConfigSpace (Sym2 (Site d)))}
    (hs : @MeasurableSet _ (outsideSigma (fkTailEdgeWindow d N)) s) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        ((boxRestrict d N ⁻¹' A) ∩ s) <=
      (wiredFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s := by
  classical
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)
  let c := (wiredFiniteMeasure d N hp hp1
    (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A)
  let Afull := boxRestrict d N ⁻¹' A
  have hAfull : MeasurableSet Afull :=
    (continuous_boxRestrict d N).measurable MeasurableSet.of_discrete
  have hsfull : MeasurableSet s :=
    (outsideSigma_le (fkTailEdgeWindow d N)) s hs
  have hc0 : 0 <= c := measureReal_nonneg
  have hc1 : c <= 1 := measureReal_le_one
  by_contra hle
  have hgap : 0 < mu.real (Afull ∩ s) - c * mu.real s :=
    sub_pos.mpr (lt_of_not_ge hle)
  let delta := (mu.real (Afull ∩ s) - c * mu.real s) / 4
  have hdelta : 0 < delta := div_pos hgap (by norm_num)
  obtain ⟨F, S, hF, happrox⟩ :=
    ati_exterior_approx_cylinder (mu := mu) (fkTailEdgeWindow d N) hs
      (ε := ENNReal.ofReal delta) (by simpa using hdelta)
  let Bfull : Set (ConfigSpace (Sym2 (Site d))) :=
    MeasureTheory.cylinder (α := fun _ : Sym2 (Site d) => Bool) F S
  have hBfull : MeasurableSet Bfull :=
    (isClopen_cylinderEvent F S).isOpen.measurableSet
  have happReal : mu.real (s ∆ Bfull) < delta := by
    have htop : mu (s ∆ Bfull) ≠ ⊤ := measure_ne_top mu _
    have h := (ENNReal.toReal_lt_toReal htop (by simp)).2 happrox
    rwa [ENNReal.toReal_ofReal hdelta.le] at h
  obtain ⟨m, hNm, B, hBreal, hBout⟩ :=
    exteriorCylinder_realise_in_box N F S hF
  have hineq0 := wiredInfiniteVolume_inter_boxOutside_le_finite_generalQ
    hN hNm hp hp1 hq hA hBout
  have hineq : mu.real (Afull ∩ Bfull) <= c * mu.real Bfull := by
    have hBfull_eq : Bfull = boxRestrict d m ⁻¹' B := hBreal
    rw [hBfull_eq]
    simpa only [mu, c, Afull, Bfull] using hineq0
  have hBdiff : |mu.real Bfull - mu.real s| < delta := by
    have hle' := abs_measureReal_sub_le_measureReal_symmDiff (μ := mu)
      hBfull.nullMeasurableSet hsfull.nullMeasurableSet
    rw [symmDiff_comm] at hle'
    exact hle'.trans_lt happReal
  have hinterSubset : (Afull ∩ Bfull) ∆ (Afull ∩ s) ⊆ s ∆ Bfull := by
    intro omega homega
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at homega ⊢
    tauto
  have hIdiff : |mu.real (Afull ∩ Bfull) - mu.real (Afull ∩ s)| < delta := by
    have habs := abs_measureReal_sub_le_measureReal_symmDiff (μ := mu)
      (hAfull.inter hBfull).nullMeasurableSet
      (hAfull.inter hsfull).nullMeasurableSet
    have hmono : mu.real ((Afull ∩ Bfull) ∆ (Afull ∩ s)) <=
        mu.real (s ∆ Bfull) := measureReal_mono hinterSubset (by finiteness)
    exact habs.trans_lt (hmono.trans_lt happReal)
  obtain ⟨hBlow, hBup⟩ := abs_lt.mp hBdiff
  obtain ⟨hIlow, hIup⟩ := abs_lt.mp hIdiff
  dsimp [delta] at hBlow hBup hIlow hIup
  nlinarith



theorem wiredInfiniteVolume_tail_box_inter_le_mul_generalQ
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (s : Set (ConfigSpace (Sym2 (Site d)))) (hs : FKIsTailEvent d s)
    (R : Nat) {A : Set (ConfigSpace (Sym2 (boxVerts d R)))}
    (hA : IsIncreasing A) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        ((boxRestrict d R ⁻¹' A) ∩ s) <=
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d R ⁻¹' A) *
        (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s := by
  let mu := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hbound : ∀ N, max 1 R <= N ->
      mu.real ((boxRestrict d R ⁻¹' A) ∩ s) <=
        (wiredFiniteMeasure d N hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (boxRestrict d R ⁻¹' A) * mu.real s := by
    intro N hRN
    have hRle : R <= N := (le_max_right 1 R).trans hRN
    let AN : Set (ConfigSpace (Sym2 (boxVerts d N))) :=
      boxRestrictLE d hRle ⁻¹' A
    have hAN : IsIncreasing AN := by
      intro omega eta home hmem
      exact hA (boxRestrictLE_monotone d hRle home) hmem
    have hevent : boxRestrict d N ⁻¹' AN = boxRestrict d R ⁻¹' A := by
      ext omega
      simp only [AN, Set.mem_preimage, boxRestrictLE_boxRestrict]
    have hupper := wiredInfiniteVolume_inter_exterior_le_finite_generalQ
      N ((le_max_left 1 R).trans hRN) hp hp1 hq hAN (hs N)
    rw [hevent] at hupper
    exact hupper
  have hconv := fkgq_wired_infinite_measure R hp hp1 hq hA
  have hprod : Tendsto (fun N =>
      (wiredFiniteMeasure d N hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d R ⁻¹' A) * mu.real s) atTop
      (nhds (mu.real (boxRestrict d R ⁻¹' A) * mu.real s)) :=
    hconv.mul_const (mu.real s)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hprod
    (Filter.eventually_atTop.mpr ⟨max 1 R, hbound⟩)



theorem cond_tail_le_wiredInfiniteVolume_clopen_generalQ
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {s : Set (ConfigSpace (Sym2 (Site d)))} (hs : FKIsTailEvent d s)
    (hs0 : (wiredInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _) s ≠ 0) :
    Ising.StochasticallyDominatedClopen
      (((wiredInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _))[|s])
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  intro A hAclopen hAinc
  obtain ⟨N, T, hAT, hT⟩ := isClopen_eq_boxRestrict_preimage A hAclopen
  have hprod := wiredInfiniteVolume_tail_box_inter_le_mul_generalQ
    hp hp1 hq s hs N (hT hAinc)
  rw [← hAT] at hprod
  have hs_top : mu s ≠ ⊤ := measure_ne_top mu s
  have hs_pos : 0 < mu.real s := by
    unfold Measure.real
    exact ENNReal.toReal_pos hs0 hs_top
  have hcondReal : (mu[|s]).real A =
      (mu s).toReal⁻¹ * mu.real (A ∩ s) := by
    rw [ProbabilityTheory.cond]
    unfold Measure.real
    rw [Measure.smul_apply, Measure.restrict_apply hAclopen.isOpen.measurableSet,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change (mu[|s]).real A <= mu.real A
  rw [hcondReal, inv_mul_eq_div]
  change mu.real (A ∩ s) <= mu.real A * mu.real s at hprod
  exact (div_le_iff₀ hs_pos).mpr hprod


theorem wiredInfiniteVolume_tail_trivial_generalQ
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (s : Set (ConfigSpace (Sym2 (Site d)))) (hs : FKIsTailEvent d s) :
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 0 ∨
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 1 := by
  let mu := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  by_cases hs0 : mu s = 0
  · exact Or.inl (by simpa only [mu] using hs0)
  by_cases hsc0 : mu sᶜ = 0
  · right
    have hadd := measure_add_measure_compl (μ := mu) hs.measurableSet
    rw [hsc0, add_zero] at hadd
    rw [measure_univ] at hadd
    simpa only [mu] using hadd
  haveI hp1s : IsProbabilityMeasure (mu[|s]) := cond_isProbabilityMeasure hs0
  haveI hp2s : IsProbabilityMeasure (mu[|sᶜ]) := cond_isProbabilityMeasure hsc0
  have hdom1 := cond_tail_le_wiredInfiniteVolume_clopen_generalQ
    hp hp1 hq hs hs0
  have hdom2 := cond_tail_le_wiredInfiniteVolume_clopen_generalQ
    hp hp1 hq hs.compl hsc0
  have hsum : mu s + mu sᶜ = 1 := by
    rw [← measure_univ (μ := mu)]
    exact measure_add_measure_compl hs.measurableSet
  have hdecomp : mu = mu s • (mu[|s]) + mu sᶜ • (mu[|sᶜ]) :=
    fec_invariant_decomp hs.measurableSet hs0 hsc0
  have htop : mu s ≠ ⊤ := measure_ne_top mu s
  have hsctop : mu sᶜ ≠ ⊤ := measure_ne_top mu sᶜ
  have heq := Ising.gec_max_extreme (E := Sym2 (Site d))
    (μ := mu) (ν₁ := mu[|s]) (ν₂ := mu[|sᶜ])
    (pos_iff_ne_zero.mpr hs0) (pos_iff_ne_zero.mpr hsc0)
    hsum htop hsctop hdecomp (by simpa only [mu] using hdom1)
      (by simpa only [mu] using hdom2)
  right
  have hself : (mu[|s]) s = 1 := cond_apply_self hs0 htop
  rw [heq.1] at hself
  simpa only [mu] using hself



theorem wiredInfiniteVolume_isErgodic_generalQ
    (hd : 1 <= d) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d))
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  let mu := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : StatMech.ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    fkgqt_wiredIV_isTranslationInvariant hp hp1 hq
  refine ⟨hti, ?_⟩
  intro s hs hinv
  obtain ⟨t, ht, hae⟩ := fk_invariant_event_ae_tail hd hti s hs hinv
  have heq : mu s = mu t := measure_congr hae
  rcases wiredInfiniteVolume_tail_trivial_generalQ hp hp1 hq t ht with ht0 | ht1
  · exact Or.inl (heq.trans ht0)
  · right
    rw [measure_univ]
    exact heq.trans ht1



theorem wiredInfinite_canonical_uniqueness_all_parameters
    (hd : 1 <= d) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega = 0} = 1 ∨
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega = 1} = 1) ∧
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          (Percolation.atLeastTwoInfinite d) = 0 ∧
      (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega <= 1} = 1 := by
  exact Percolation.cbk_canonical_uniqueness
    (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
    hd (wiredInfiniteVolume_isErgodic_generalQ hd hp hp1 hq)
    (wiredInfiniteVolume_hasFiniteEnergyMerge hp hp1 hq)
    (wiredInfinite_canonical_trifurcation_pos_of_top_pos hp hp1 hq)

end StatMech.FK
