/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.FreeDLRExtreme
import Code.FK.FreeTailErgodicityPrereq
import Code.FK.FKDisjointBoxDomainMarkov
import Code.FK.MultiEdgeDecay
import Code.FK.FKGeneralQConsumer
import Code.Foundations.AeTailInvariant

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff

namespace StatMech

namespace FK

open StatMech.Lattice

variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin]
  [Fintype Vout] [DecidableEq Vout]



theorem freeInner_mul_outside_le_bcProb
    (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (ιV : Vin → Vout) (hι : Function.Injective ιV)
    (hadj : ocd_AdjMatch Gin Gout ιV)
    (C : SimpleGraph Vout) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A)
    {B : Set (ConfigSpace (Sym2 Vout))}
    (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := Vin) ιV) B) :
    (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * fkProb Gin p q omega) *
        (∑ rho, B.indicator (fun _ => (1 : ℝ)) rho * bcProb Gout C p q rho) ≤
      ∑ rho, ((ocd_innerRestrict ιV ⁻¹' A) ∩ B).indicator
        (fun _ => (1 : ℝ)) rho * bcProb Gout C p q rho := by
  classical
  let F := ocd_innerEdgeFinset (Vin := Vin) ιV
  let Aout := ocd_innerRestrict ιV ⁻¹' A
  let c := ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * fkProb Gin p q omega
  have hAout : IsIncreasing Aout := by
    intro omega eta home hmem
    exact hA (fun e => home (ocd_innerEdge ιV e)) hmem
  have hper : ∀ psi : ConfigSpace (Sym2 Vout),
      c ≤ ∑ rho, Aout.indicator (fun _ => (1 : ℝ)) rho *
        condBcProb Gout C p q F psi rho := by
    intro psi
    have hfree := bdp_condBcProb_innerRestrict_ge hι hadj
      hp hp1 hq psi hA
    have hbot : StatMech.Lattice.boundaryCliqueGraph
        (bdp_noBdry (Vout := Vout)) ≤ C := by
      intro x y hxy
      rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hxy
      exact False.elim hxy.2.1
    have hmono := condBcProb_mono_bc Gout
      (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) C
      hbot hp hp1 hq F psi hAout
    exact hfree.trans hmono
  rw [bcProb_fibre_decompose Gout C hp hp1 (lt_of_lt_of_le one_pos hq) F B,
    bcProb_fibre_decompose Gout C hp hp1 (lt_of_lt_of_le one_pos hq) F (Aout ∩ B),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  rw [fibreReps, Finset.mem_filter] at hpsi
  let mass := ∑ sigma ∈ condFibre F psi, bcProb Gout C p q sigma
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun sigma _ =>
    bcProb_nonneg Gout C hp hp1 (lt_of_lt_of_le one_pos hq) sigma
  have hBout :
      (∑ rho, B.indicator (fun _ => (1 : ℝ)) rho *
        condBcProb Gout C p q F psi rho) =
        B.indicator (fun _ => (1 : ℝ)) psi := by
    simpa only [F] using condBcProb_sum_outside Gout C hp hp1
      (lt_of_lt_of_le one_pos hq) hB hpsi.2
  have hcross :
      (∑ rho, (Aout ∩ B).indicator (fun _ => (1 : ℝ)) rho *
        condBcProb Gout C p q F psi rho) =
        B.indicator (fun _ => (1 : ℝ)) psi *
          (∑ rho, Aout.indicator (fun _ => (1 : ℝ)) rho *
            condBcProb Gout C p q F psi rho) := by
    simpa only [F] using
      (condBcProb_cross_outside Gout C (A := Aout) hB)
  rw [hBout, hcross]
  have hind : 0 ≤ B.indicator (fun _ => (1 : ℝ)) psi :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) psi
  calc
    c * (mass * B.indicator (fun _ => (1 : ℝ)) psi) =
        mass * (B.indicator (fun _ => (1 : ℝ)) psi * c) := by ring
    _ ≤ mass * (B.indicator (fun _ => (1 : ℝ)) psi *
        ∑ rho, Aout.indicator (fun _ => (1 : ℝ)) rho *
          condBcProb Gout C p q F psi rho) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hper psi) hind) hmass

variable {d : ℕ}



theorem isFKDLR_freeMass_mul_outside_le_generalQ
    {N m : ℕ} (hNm : N < m) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 1 ≤ q)
    (phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hphi : IsFKDLR d p q phi)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A)
    {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
    (hB : DependsOnOutside
      (ocd_innerEdgeFinset (Vin := boxVerts d N)
        (boxVertInclLE d (le_of_lt hNm))) B) :
    dlrBcEventMass (boxGraph d N) (⊥ : SimpleGraph (boxVerts d N)) p q A *
        (phi : Measure _).real (boxRestrict d m ⁻¹' B) ≤
      (phi : Measure _).real (boxRestrict d m ⁻¹'
        ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A) ∩ B)) := by
  classical
  obtain ⟨weight, hweight, hsum, hsupp, hmix⟩ := hphi m
  let innerMass := dlrBcEventMass (boxGraph d N)
    (⊥ : SimpleGraph (boxVerts d N)) p q A
  have hcomponent (C : SimpleGraph (boxVerts d m)) :
      innerMass * dlrBcEventMass (boxGraph d m) C p q B ≤
        dlrBcEventMass (boxGraph d m) C p q
          ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A) ∩ B) := by
    unfold innerMass dlrBcEventMass
    rw [show (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        bcProb (boxGraph d N) (⊥ : SimpleGraph (boxVerts d N)) p q omega) =
        ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
          fkProb (boxGraph d N) p q omega by
      apply Finset.sum_congr rfl
      intro omega _
      rw [bcProb_bot_eq_fkProb]]
    exact freeInner_mul_outside_le_bcProb
      (boxGraph d N) (boxGraph d m)
      (boxVertInclLE d (le_of_lt hNm)) (cbk_boxVertInclLE_injective _)
      (cbk_adjMatch _) C hp hp1 hq hA hB
  rw [hmix B, hmix]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _
  have hw := hweight C
  have hc := hcomponent C
  nlinarith [mul_le_mul_of_nonneg_left hc hw]

theorem edgeIncl_mem_fkTailEdgeWindow (N : ℕ)
    (eb : Sym2 (boxVerts d N)) :
    edgeIncl d N eb ∈ fkTailEdgeWindow d N := by
  intro x hx
  induction eb using Sym2.ind with
  | _ u v =>
      rw [edgeIncl, Sym2.map_mk] at hx
      rcases (Sym2.mem_iff.mp hx) with rfl | rfl
      · exact u.2
      · exact v.2




theorem exteriorCylinder_realise_in_box
    (N : ℕ) (F : Finset (Sym2 (Site d)))
    (S : Set (ConfigSpace F))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆ (fkTailEdgeWindow d N)ᶜ) :
    ∃ (m : ℕ) (hNm : N < m)
      (B : Set (ConfigSpace (Sym2 (boxVerts d m)))),
      MeasureTheory.cylinder F S = boxRestrict d m ⁻¹' B ∧
      DependsOnOutside
        (ocd_innerEdgeFinset (Vin := boxVerts d N)
          (boxVertInclLE d (le_of_lt hNm))) B := by
  classical
  obtain ⟨m0, t, ht⟩ := cdc_finset_in_box F
  let m := m0 + N + 1
  have hm0 : m0 ≤ m := Nat.le_add_right m0 (N + 1)
  have hNm : N < m := by omega
  have hrange : ∀ e ∈ F, e ∈ Set.range (edgeIncl d m) := by
    intro e he
    rw [ht] at he
    obtain ⟨eb, _, heb⟩ := Finset.mem_image.mp he
    refine ⟨innerEdgeLE d hm0 eb, ?_⟩
    rw [edgeIncl_innerEdgeLE]
    exact heb
  let B : Set (ConfigSpace (Sym2 (boxVerts d m))) :=
    extendEdge d m ⁻¹' MeasureTheory.cylinder F S
  refine ⟨m, hNm, B,
    cylinder_eq_boxRestrict_preimage_extend m F S hrange, ?_⟩
  intro psi rho hagree
  change extendEdge d m psi ∈ MeasureTheory.cylinder F S ↔
    extendEdge d m rho ∈ MeasureTheory.cylinder F S
  have hrestr : F.restrict (extendEdge d m psi) =
      F.restrict (extendEdge d m rho) := by
    funext e
    obtain ⟨eb, heb⟩ := hrange e.1 e.2
    have hebOut : eb ∉ ocd_innerEdgeFinset
        (Vin := boxVerts d N) (boxVertInclLE d (le_of_lt hNm)) := by
      intro hin
      rw [ocd_mem_innerEdgeFinset] at hin
      obtain ⟨en, hen⟩ := hin
      have heWin : e.1 ∈ fkTailEdgeWindow d N := by
        rw [← heb, ← hen]
        rw [show ocd_innerEdge (boxVertInclLE d (le_of_lt hNm)) en =
          innerEdgeLE d (le_of_lt hNm) en from rfl,
          edgeIncl_innerEdgeLE]
        exact edgeIncl_mem_fkTailEdgeWindow N en
      exact (hF e.2) heWin
    change extendEdge d m psi e.1 = extendEdge d m rho e.1
    rw [← heb, extendEdge_eq_of_range, extendEdge_eq_of_range]
    exact (hagree eb hebOut).symm
  simp only [MeasureTheory.mem_cylinder]
  rw [hrestr]



theorem isFKDLR_freeMass_mul_exterior_le_generalQ
    (N : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (hphi : IsFKDLR d p q phi)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A)
    {s : Set (ConfigSpace (Sym2 (Site d)))}
    (hs : @MeasurableSet _ (outsideSigma (fkTailEdgeWindow d N)) s) :
    dlrBcEventMass (boxGraph d N) (⊥ : SimpleGraph (boxVerts d N)) p q A *
        (phi : Measure _).real s ≤
      (phi : Measure _).real ((boxRestrict d N ⁻¹' A) ∩ s) := by
  classical
  let mu : Measure (ConfigSpace (Sym2 (Site d))) := phi
  let c := dlrBcEventMass (boxGraph d N)
    (⊥ : SimpleGraph (boxVerts d N)) p q A
  let Afull := boxRestrict d N ⁻¹' A
  have hAfull : MeasurableSet Afull :=
    (continuous_boxRestrict d N).measurable MeasurableSet.of_discrete
  have hsfull : MeasurableSet s :=
    (outsideSigma_le (fkTailEdgeWindow d N)) s hs
  have hc_eq : c =
      (freeFiniteMeasure d N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real Afull := by
    rw [freeFiniteMeasure_real_boxRestrictEvent N hp hp1
      (zero_lt_one.trans_le hq) A hAfull]
    unfold c dlrBcEventMass
    apply Finset.sum_congr rfl
    intro omega _
    rw [bcProb_bot_eq_fkProb]
  have hc0 : 0 ≤ c := by rw [hc_eq]; exact measureReal_nonneg
  have hc1 : c ≤ 1 := by rw [hc_eq]; exact measureReal_le_one
  by_contra hle
  have hgap : 0 < c * mu.real s - mu.real (Afull ∩ s) := sub_pos.mpr (lt_of_not_ge hle)
  let delta := (c * mu.real s - mu.real (Afull ∩ s)) / 4
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
  have hfinite := isFKDLR_freeMass_mul_outside_le_generalQ
    hNm hp hp1 hq phi hphi hA hBout
  have hcross : boxRestrict d m ⁻¹'
      ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A) ∩ B) =
      Afull ∩ Bfull := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_inter_iff, Afull, Bfull]
    have hinner : ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm))
        (boxRestrict d m omega) = boxRestrict d N omega := by
      change boxRestrictLE d (le_of_lt hNm) (boxRestrict d m omega) = _
      exact boxRestrictLE_boxRestrict d (le_of_lt hNm) omega
    rw [hinner]
    have hBmem := Set.ext_iff.mp hBreal omega
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨ha, hBmem.mpr hb⟩
    · rintro ⟨ha, hb⟩
      exact ⟨ha, hBmem.mp hb⟩
  have hineq : c * mu.real Bfull ≤ mu.real (Afull ∩ Bfull) := by
    rw [← hBreal, hcross] at hfinite
    simpa only [c, mu, Bfull, Afull] using hfinite
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
    have hmono : mu.real ((Afull ∩ Bfull) ∆ (Afull ∩ s)) ≤
        mu.real (s ∆ Bfull) := measureReal_mono hinterSubset (by finiteness)
    exact habs.trans_lt (hmono.trans_lt happReal)
  obtain ⟨hBlow, hBup⟩ := abs_lt.mp hBdiff
  obtain ⟨hIlow, hIup⟩ := abs_lt.mp hIdiff
  dsimp [delta] at hBlow hBup hIlow hIup
  nlinarith



theorem freeInfiniteVolume_tail_box_product_le_generalQ
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Set (ConfigSpace (Sym2 (Site d))))
    (hs : FKIsTailEvent d s)
    (N : ℕ) {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
    (hA : IsIncreasing A) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' A) *
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s ≤
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      ((boxRestrict d N ⁻¹' A) ∩ s) := by
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  let rhs := mu.real ((boxRestrict d N ⁻¹' A) ∩ s)
  have hdlr := freeInfiniteVolume_isFKDLR (d := d) hp hp1 hq
  have hbound : ∀ m, N ≤ m →
      (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) * mu.real s ≤ rhs := by
    intro m hNm
    let Am : Set (ConfigSpace (Sym2 (boxVerts d m))) :=
      boxRestrictLE d hNm ⁻¹' A
    have hAm : IsIncreasing Am := by
      intro omega eta home hmem
      exact hA (boxRestrictLE_monotone d hNm home) hmem
    have hevent : boxRestrict d m ⁻¹' Am = boxRestrict d N ⁻¹' A := by
      ext omega
      simp only [Am, Set.mem_preimage, boxRestrictLE_boxRestrict]
    have hlower := isFKDLR_freeMass_mul_exterior_le_generalQ m hp hp1 hq
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq))
      hdlr hAm (hs m)
    have hcoeff : dlrBcEventMass (boxGraph d m)
        (⊥ : SimpleGraph (boxVerts d m)) p q Am =
        (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) := by
      rw [← hevent, freeFiniteMeasure_real_boxRestrictEvent m hp hp1
        (zero_lt_one.trans_le hq) Am
        ((continuous_boxRestrict d m).measurable MeasurableSet.of_discrete)]
      unfold dlrBcEventMass
      apply Finset.sum_congr rfl
      intro omega _
      rw [bcProb_bot_eq_fkProb]
    rw [hcoeff, hevent] at hlower
    exact hlower
  have hconv := fkgq_free_infinite_measure (d := d) N hp hp1 hq hA
  have hprod : Tendsto
      (fun m => (freeFiniteMeasure d m hp hp1
        (zero_lt_one.trans_le hq) : Measure _).real
          (boxRestrict d N ⁻¹' A) * mu.real s) atTop
      (𝓝 (mu.real (boxRestrict d N ⁻¹' A) * mu.real s)) :=
    hconv.mul_const (mu.real s)
  exact le_of_tendsto hprod (Filter.eventually_atTop.mpr ⟨N, hbound⟩)



theorem freeInfiniteVolume_le_cond_tail_clopen_generalQ
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {s : Set (ConfigSpace (Sym2 (Site d)))}
    (hs : FKIsTailEvent d s)
    (hs0 : (freeInfiniteVolume d hp hp1
      (zero_lt_one.trans_le hq) : Measure _) s ≠ 0) :
    Ising.StochasticallyDominatedClopen
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
      (((freeInfiniteVolume d hp hp1
        (zero_lt_one.trans_le hq) : Measure _))[|s]) := by
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  intro A hAclopen hAinc
  obtain ⟨N, T, hAT, hT⟩ := isClopen_eq_boxRestrict_preimage A hAclopen
  have hprod := freeInfiniteVolume_tail_box_product_le_generalQ
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
  change mu.real A ≤ (mu[|s]).real A
  rw [hcondReal]
  change mu.real A * mu.real s ≤ mu.real (A ∩ s) at hprod
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hs_pos).mpr hprod


theorem freeInfiniteVolume_tail_trivial_generalQ
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (s : Set (ConfigSpace (Sym2 (Site d))))
    (hs : FKIsTailEvent d s) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 0 ∨
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 1 := by
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
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
  have hdom1 := freeInfiniteVolume_le_cond_tail_clopen_generalQ
    hp hp1 hq hs hs0
  have hdom2 := freeInfiniteVolume_le_cond_tail_clopen_generalQ
    hp hp1 hq hs.compl hsc0
  have hsum : mu s + mu sᶜ = 1 := by
    rw [← measure_univ (μ := mu)]
    exact measure_add_measure_compl hs.measurableSet
  have hdecomp : mu = mu s • (mu[|s]) + mu sᶜ • (mu[|sᶜ]) :=
    fec_invariant_decomp hs.measurableSet hs0 hsc0
  have htop : mu s ≠ ⊤ := measure_ne_top mu s
  have hsctop : mu sᶜ ≠ ⊤ := measure_ne_top mu sᶜ
  have heq := Ising.gec_min_extreme (E := Sym2 (Site d))
    (μ := mu) (ν₁ := mu[|s]) (ν₂ := mu[|sᶜ])
    (pos_iff_ne_zero.mpr hs0) (pos_iff_ne_zero.mpr hsc0)
    hsum htop hsctop hdecomp (by simpa only [mu] using hdom1)
      (by simpa only [mu] using hdom2)
  right
  have hself : (mu[|s]) s = 1 := cond_apply_self hs0 htop
  rw [heq.1] at hself
  simpa only [mu] using hself



theorem freeInfiniteVolume_isErgodic_generalQ
    (hd : 1 ≤ d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))) := by
  let mu := (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  have hti : StatMech.ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    fkgqt_freeIV_isTranslationInvariant hp hp1 hq
  refine ⟨hti, ?_⟩
  intro s hs hinv
  obtain ⟨t, ht, hae⟩ := fk_invariant_event_ae_tail hd hti s hs hinv
  have heq : mu s = mu t := measure_congr hae
  rcases freeInfiniteVolume_tail_trivial_generalQ hp hp1 hq t ht with ht0 | ht1
  · exact Or.inl (heq.trans ht0)
  · right
    rw [measure_univ]
    exact heq.trans ht1



theorem freeInfinite_canonical_uniqueness_all_parameters
    (hd : 1 ≤ d) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega = 0} = 1 ∨
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega = 1} = 1) ∧
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          (Percolation.atLeastTwoInfinite d) = 0 ∧
      (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega ≤ 1} = 1 := by
  exact freeInfinite_canonical_uniqueness_of_isErgodic hd hp hp1 hq
    (freeInfiniteVolume_isErgodic_generalQ hd hp hp1 hq)



theorem freeInfiniteVolume_tail_trivial
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (s : Set (ConfigSpace (Sym2 (Site d)))) (hs : FKIsTailEvent d s) :
    (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) s = 0 ∨
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) s = 1 :=
  freeInfiniteVolume_tail_trivial_generalQ hp hp1
    (by norm_num : (1 : ℝ) ≤ 2) s hs



theorem freeInfiniteVolume_isErgodic_all_parameters
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d))
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))) :=
  freeInfiniteVolume_isErgodic_generalQ hd hp hp1
    (by norm_num : (1 : ℝ) ≤ 2)


theorem freeInfinite_q2_canonical_uniqueness_all_parameters
    (hd : 1 ≤ d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega = 0} = 1 ∨
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega = 1} = 1) ∧
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          (Percolation.atLeastTwoInfinite d) = 0 ∧
      (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _)
          {omega | Percolation.numInfiniteClusters d omega ≤ 1} = 1 :=
  freeInfinite_canonical_uniqueness_all_parameters hd hp hp1
    (by norm_num : (1 : ℝ) ≤ 2)

end FK

end StatMech
