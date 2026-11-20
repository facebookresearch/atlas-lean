/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














import Code.Percolation.PcUpperViaFK
import Code.FK.ComparisonHolley
import Code.FK.Limits
import Code.FK.FKGeneralQConsumer
import Code.Ising.TransitionAssembly

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace StatMech
namespace FK

open StatMech.Lattice



theorem bernoulliReduced_boxBdryConnEvent_le_wiredFinite
    {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site d))
        ⟨reducedDensity p 2, (reducedDensity_mem_Ioo hp hp1 (by norm_num)).1.le⟩
        (reducedDensity_mem_Ioo hp hp1 (by norm_num)).2.le).real
        (boxBdryConnEvent d n) ≤
      (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  let r : ℝ := reducedDensity p 2
  have hr0 : 0 < r := (reducedDensity_mem_Ioo hp hp1 (by norm_num)).1
  have hr1 : r < 1 := (reducedDensity_mem_Ioo hp hp1 (by norm_num)).2
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  have hAinc : IsIncreasing A := isIncreasing_connToBdryEvent n
  have hAdep : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d n).edgeFinset : Set (Sym2 (boxVerts d n))) :=
    connToBdryEvent_dependsOn (boxGraph d n) (boxBoundary d n)
      (IsingFK.boxOrigin d n)
  have hlow := bernoulli_reduced_le_fk (boxGraph d n) hp hp1
    (by norm_num : (1 : ℝ) ≤ 2)
  have hlowA := hlow A MeasurableSet.of_discrete hAinc
  have hfreeWired := fkProb_le_wiredFkProb_increasing
    (boxGraph d n) (boxBoundary d n) hp hp1
      (by norm_num : (1 : ℝ) ≤ 2) hAinc
  have hbern :
      (bernoulliProductMeasure (E := Sym2 (boxVerts d n))
          ⟨r, hr0.le⟩ hr1.le).real A =
        (measOfMass (fkProb (boxGraph d n) r 1)).real A := by
    rw [measOfMass_real_eq_indicator_sum _
      (fun omega => fkProb_nonneg (boxGraph d n) hr0 hr1 one_pos omega)]
    symm
    exact fkProbOne_event_eq_bernoulli (boxGraph d n) hr0 hr1 A hAdep
  rw [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl,
    bernoulliProduct_boxRestrict_preimage]
  change (bernoulliProductMeasure (E := Sym2 (boxVerts d n))
      ⟨r, hr0.le⟩ hr1.le).real A ≤ _
  rw [hbern, wiredFiniteMeasure_real_boxRestrictEvent n hp hp1 A
    ((continuous_boxRestrict d n).measurable MeasurableSet.of_discrete)]
  rw [measOfMass_real_eq_indicator_sum _
    (fun omega => fkProb_nonneg (boxGraph d n) hp hp1 (by norm_num) omega)] at hlowA
  exact hlowA.trans hfreeWired



theorem bernoulliTheta_reduced_le_fkTheta
    {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Percolation.theta d
        ⟨reducedDensity p 2, (reducedDensity_mem_Ioo hp hp1 (by norm_num)).1.le⟩
        (reducedDensity_mem_Ioo hp hp1 (by norm_num)).2.le ≤
      fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  let r : ℝ≥0 :=
    ⟨reducedDensity p 2, (reducedDensity_mem_Ioo hp hp1 (by norm_num)).1.le⟩
  have hr1 : r ≤ 1 := (reducedDensity_mem_Ioo hp hp1 (by norm_num)).2.le
  have hbern := boxBdryConnEvent_real_tendsto_percolation (d := d)
    (bernoulliProductMeasure (E := Sym2 (Site d)) r hr1)
  have hfk := boxBdryConnEvent_diag_tendsto (d := d) hp hp1
  apply le_of_tendsto_of_tendsto
    (by simpa only [Percolation.theta, r] using hbern) hfk
  exact Filter.Eventually.of_forall
    (bernoulliReduced_boxBdryConnEvent_le_wiredFinite hp hp1)




theorem bernoulliReduced_boxBdryConnEvent_le_wiredFinite_general
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (n : ℕ) :
    (bernoulliProductMeasure (E := Sym2 (Site d))
        ⟨reducedDensity p q, (reducedDensity_mem_Ioo hp hp1 hq).1.le⟩
        (reducedDensity_mem_Ioo hp hp1 hq).2.le).real
        (boxBdryConnEvent d n) ≤
      (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  let r : ℝ := reducedDensity p q
  have hr0 : 0 < r := (reducedDensity_mem_Ioo hp hp1 hq).1
  have hr1 : r < 1 := (reducedDensity_mem_Ioo hp hp1 hq).2
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  have hAinc : IsIncreasing A := isIncreasing_connToBdryEvent n
  have hAdep : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ)))
      ((boxGraph d n).edgeFinset : Set (Sym2 (boxVerts d n))) :=
    connToBdryEvent_dependsOn (boxGraph d n) (boxBoundary d n)
      (IsingFK.boxOrigin d n)
  have hlow := bernoulli_reduced_le_fk (boxGraph d n) hp hp1 hq
  have hlowA := hlow A MeasurableSet.of_discrete hAinc
  have hfreeWired := fkProb_le_wiredFkProb_increasing
    (boxGraph d n) (boxBoundary d n) hp hp1 hq hAinc
  have hbern :
      (bernoulliProductMeasure (E := Sym2 (boxVerts d n))
          ⟨r, hr0.le⟩ hr1.le).real A =
        (measOfMass (fkProb (boxGraph d n) r 1)).real A := by
    rw [measOfMass_real_eq_indicator_sum _
      (fun omega => fkProb_nonneg (boxGraph d n) hr0 hr1 one_pos omega)]
    symm
    exact fkProbOne_event_eq_bernoulli (boxGraph d n) hr0 hr1 A hAdep
  rw [show boxBdryConnEvent d n = boxRestrict d n ⁻¹' A from rfl,
    bernoulliProduct_boxRestrict_preimage]
  change (bernoulliProductMeasure (E := Sym2 (boxVerts d n))
      ⟨r, hr0.le⟩ hr1.le).real A ≤ _
  rw [hbern, fkgq_wiredFiniteMeasure_real_boxRestrictEvent n hp hp1
    (zero_lt_one.trans_le hq) A
    ((continuous_boxRestrict d n).measurable MeasurableSet.of_discrete)]
  rw [measOfMass_real_eq_indicator_sum _
    (fun omega => fkProb_nonneg (boxGraph d n) hp hp1
      (zero_lt_one.trans_le hq) omega)] at hlowA
  exact hlowA.trans hfreeWired



theorem fkgq_boxBdryConnEvent_diag_antitone
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Antitone (fun n => (wiredFiniteMeasure d (n + 1) hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real
      (boxBdryConnEvent d (n + 1))) := by
  apply antitone_nat_of_succ_le
  intro n
  let A : Set (ConfigSpace (Sym2 (boxVerts d (n + 1)))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d (n + 1)) (boxBoundary d (n + 1)) omega
      (IsingFK.boxOrigin d (n + 1))}
  have hcross := fkgq_wiredFiniteMeasure_succ_le_smallerBox
    (d := d) (n + 1) hp hp1 hq (S := A) (isIncreasing_connToBdryEvent (n + 1))
      ((continuous_boxRestrict d (n + 1)).measurable MeasurableSet.of_discrete)
  have hshell : boxBdryConnEvent d (n + 2) ⊆ boxBdryConnEvent d (n + 1) :=
    boxBdryConnEvent_succ_subset (n + 1) (by omega)
  calc
    (wiredFiniteMeasure d (n + 2) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxBdryConnEvent d (n + 2))
      ≤ (wiredFiniteMeasure d (n + 2) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxBdryConnEvent d (n + 1)) := measureReal_mono hshell
    _ ≤ ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
          wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1)) p q omega := by
        simpa [A, Nat.add_assoc] using hcross
    _ = (wiredFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxBdryConnEvent d (n + 1)) := by
        rw [show boxBdryConnEvent d (n + 1) = boxRestrict d (n + 1) ⁻¹' A from rfl,
          fkgq_wiredFiniteMeasure_real_boxRestrictEvent (n + 1) hp hp1
            (zero_lt_one.trans_le hq) A
            ((continuous_boxRestrict d (n + 1)).measurable MeasurableSet.of_discrete)]



theorem fkgq_boxBdryConnEvent_diag_tendsto
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q))) := by
  let mu := fun n => (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  let nu := (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
    Measure (ConfigSpace (Sym2 (Site d))))
  let a := fun n => (mu n).real (boxBdryConnEvent d n)
  let a1 := fun n => a (n + 1)
  let b := fun n => nu.real (boxBdryConnEvent d n)
  have ha1anti : Antitone a1 := by
    simpa [a1, a, mu] using fkgq_boxBdryConnEvent_diag_antitone hp hp1 hq
  have ha1b : BddBelow (Set.range a1) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact measureReal_nonneg⟩
  let L := ⨅ n, a1 n
  have ha1lim : Tendsto a1 atTop (nhds L) := by
    dsimp [L]
    exact tendsto_atTop_ciInf ha1anti ha1b
  have halim : Tendsto a atTop (nhds L) := by
    exact (Filter.tendsto_add_atTop_iff_nat 1).mp (by simpa [a1, Nat.add_comm] using ha1lim)
  have hblim : Tendsto b atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q))) := by
    simpa [b, nu] using wiredIv_boxBdryConnEvent_tendsto (d := d) hp hp1
      (zero_lt_one.trans_le hq)
  have hLle : L ≤ fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
    have hLbk : ∀ k, 1 ≤ k → L ≤ b k := by
      intro k hk
      let A : Set (ConfigSpace (Sym2 (boxVerts d k))) :=
        {omega | IsingFK.ConnToBdry (boxGraph d k) (boxBoundary d k) omega
          (IsingFK.boxOrigin d k)}
      have hfixed := fkgq_wired_infinite_measure (d := d) k hp hp1 hq
        (S := A) (isIncreasing_connToBdryEvent k)
      have hshift := hfixed.comp (tendsto_add_atTop_nat k)
      have hdiagShift := halim.comp (tendsto_add_atTop_nat k)
      apply le_of_tendsto_of_tendsto' hdiagShift (by simpa [b, nu, A] using hshift)
      intro n
      exact measureReal_mono (by
        simpa [Nat.add_comm] using
          (boxBdryConnEvent_subset_le (d := d) k (k + n) hk
            (Nat.le_add_right k n))) (measure_ne_top _ _)
    refine ge_of_tendsto hblim ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hLbk k hk
  have hfkLe : fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) ≤ L := by
    have hbk : ∀ k, b k ≤ a k := by
      intro k
      let A : Set (ConfigSpace (Sym2 (boxVerts d k))) :=
        {omega | IsingFK.ConnToBdry (boxGraph d k) (boxBoundary d k) omega
          (IsingFK.boxOrigin d k)}
      have hfixed := fkgq_wired_infinite_measure (d := d) k hp hp1 hq
        (S := A) (isIncreasing_connToBdryEvent k)
      have hfixed' : Tendsto (fun m => (mu m).real (boxBdryConnEvent d k)) atTop
          (nhds (b k)) := by
        simpa [mu, b, nu, A] using hfixed
      apply le_of_tendsto hfixed'
      filter_upwards [eventually_ge_atTop k] with m hm
      have hchain : (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
          (boxBdryConnEvent d k) ≤ a k := by
        have hanti : Antitone (fun j =>
            (wiredFiniteMeasure d (k + j) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
              (boxBdryConnEvent d k)) := by
          apply antitone_nat_of_succ_le
          intro j
          simpa [A, Nat.add_assoc] using
            (fkgq_wired_succ (d := d) k (k + j) (Nat.le_add_right k j)
              hp hp1 hq (S := A) (isIncreasing_connToBdryEvent k))
        have := hanti (Nat.zero_le (m - k))
        simpa [a, mu, A, Nat.add_sub_of_le hm] using this
      exact hchain
    exact le_of_tendsto_of_tendsto' hblim halim hbk
  rw [le_antisymm hLle hfkLe] at halim
  exact halim



theorem bernoulliTheta_reduced_le_fkTheta_general
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Percolation.theta d
        ⟨reducedDensity p q, (reducedDensity_mem_Ioo hp hp1 hq).1.le⟩
        (reducedDensity_mem_Ioo hp hp1 hq).2.le ≤
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
  let r : ℝ≥0 := ⟨reducedDensity p q, (reducedDensity_mem_Ioo hp hp1 hq).1.le⟩
  have hr1 : r ≤ 1 := (reducedDensity_mem_Ioo hp hp1 hq).2.le
  have hbern := boxBdryConnEvent_real_tendsto_percolation (d := d)
    (bernoulliProductMeasure (E := Sym2 (Site d)) r hr1)
  have hfk := fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp hp1 hq
  apply le_of_tendsto_of_tendsto
    (by simpa only [Percolation.theta, r] using hbern) hfk
  exact Filter.Eventually.of_forall
    (bernoulliReduced_boxBdryConnEvent_le_wiredFinite_general hp hp1 hq)



theorem fkgq_wiredFiniteMeasure_monotone_in_p
    {d m : ℕ} {p1 p2 q : ℝ}
    (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2) (hp2' : p2 < 1)
    (hle : p1 ≤ p2) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d m)))} (hA : IsIncreasing A) :
    (wiredFiniteMeasure d m hp1 hp1' (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d m ⁻¹' A) ≤
      (wiredFiniteMeasure d m hp2 hp2' (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d m ⁻¹' A) := by
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' A) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp1 hp1'
      (zero_lt_one.trans_le hq) A hmeas,
    fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp2 hp2'
      (zero_lt_one.trans_le hq) A hmeas]
  have hbc1 : ∀ omega,
      wiredFkProb (boxGraph d m) (boxBoundary d m) p1 q omega =
        bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p1 q omega :=
    fun omega => (bcProb_clique_eq_wiredFkProb
      (boxGraph d m) (boxBoundary d m) p1 q omega).symm
  have hbc2 : ∀ omega,
      wiredFkProb (boxGraph d m) (boxBoundary d m) p2 q omega =
        bcProb (boxGraph d m) (boundaryCliqueGraph (boxBoundary d m)) p2 q omega :=
    fun omega => (bcProb_clique_eq_wiredFkProb
      (boxGraph d m) (boxBoundary d m) p2 q omega).symm
  simp only [hbc1, hbc2]
  exact bcProb_monotone_in_p (boxGraph d m)
    (boundaryCliqueGraph (boxBoundary d m)) hp1 hp1' hp2 hp2' hle hq hA



theorem fkgq_fkTheta_monotone_in_p
    {d : ℕ} {p1 p2 q : ℝ}
    (hp1 : 0 < p1) (hp1' : p1 < 1) (hp2 : 0 < p2) (hp2' : p2 < 1)
    (hle : p1 ≤ p2) (hq : 1 ≤ q) :
    fkTheta d hp1 hp1' (zero_lt_one.trans_le hq) (q := q) ≤
      fkTheta d hp2 hp2' (zero_lt_one.trans_le hq) (q := q) := by
  have hlim1 := fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp1 hp1' hq
  have hlim2 := fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp2 hp2' hq
  apply le_of_tendsto_of_tendsto hlim1 hlim2
  apply Filter.Eventually.of_forall
  intro n
  let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (IsingFK.boxOrigin d n)}
  simpa [A] using fkgq_wiredFiniteMeasure_monotone_in_p
    (d := d) (m := n) hp1 hp1' hp2 hp2' hle hq
      (A := A) (isIncreasing_connToBdryEvent n)


theorem reducedDensity_inverse_general
    {r q : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hq0 : 0 < q) :
    reducedDensity (q * r / (1 - r + q * r)) q = r := by
  have hden : 0 < 1 - r + q * r := by positivity
  unfold reducedDensity
  field_simp
  ring


theorem inverseReducedDensity_general_mem_Ioo
    {r q : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hq0 : 0 < q) :
    0 < q * r / (1 - r + q * r) ∧ q * r / (1 - r + q * r) < 1 := by
  have hden : 0 < 1 - r + q * r := by positivity
  constructor
  · positivity
  · rw [div_lt_one hden]
    linarith



theorem fkTheta_pos_of_bernoulliTheta_pos_general
    {d : ℕ} {r : ℝ≥0} {q : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hq : 1 ≤ q)
    (htheta : 0 < Percolation.theta d r hr1.le) :
    ∃ p : ℝ, ∃ hp : 0 < p, ∃ hp1 : p < 1,
      0 < fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
  let p : ℝ := q * (r : ℝ) / (1 - r + q * r)
  have hr0r : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hr1r : (r : ℝ) < 1 := by exact_mod_cast hr1
  have hpIoo := inverseReducedDensity_general_mem_Ioo hr0r hr1r
    (zero_lt_one.trans_le hq)
  have hred : reducedDensity p q = r := reducedDensity_inverse_general hr0r hr1r
    (zero_lt_one.trans_le hq)
  refine ⟨p, hpIoo.1, hpIoo.2, ?_⟩
  have hdom := bernoulliTheta_reduced_le_fkTheta_general
    (d := d) hpIoo.1 hpIoo.2 hq
  have hthetaEq :
      Percolation.theta d
          ⟨reducedDensity p q, (reducedDensity_mem_Ioo hpIoo.1 hpIoo.2 hq).1.le⟩
          (reducedDensity_mem_Ioo hpIoo.1 hpIoo.2 hq).2.le =
        Percolation.theta d r hr1.le := by
    congr
  exact lt_of_lt_of_le (hthetaEq.symm ▸ htheta) hdom


theorem fkPc_le_of_fkTheta_pos_general
    {d : ℕ} {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (htheta : 0 < fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q)) :
    fkPc d q ≤ p := by
  rcases (fkSubcriticalSet d q).eq_empty_or_nonempty with hempty | hne
  · rw [fkPc, hempty, Real.sSup_empty]
    exact hp.le
  · apply csSup_le hne
    intro r hr
    obtain ⟨hr0, hr1, _hq, hrzero⟩ := hr
    by_contra hnot
    have hpr : p < r := lt_of_not_ge hnot
    have hmono := fkgq_fkTheta_monotone_in_p (d := d) (q := q)
      hp hp1 hr0 hr1 hpr.le hq
    rw [hrzero] at hmono
    linarith



theorem fkPc_lt_one_of_two_le {d : ℕ} {q : ℝ} (hd : 2 ≤ d) (hq : 1 ≤ q) :
    fkPc d q < 1 := by
  obtain ⟨beta, hbeta, hmag⟩ := IsingFK.pup_exists_positive_magnetization
  have hr0r : 0 < IsingFK.pOfBeta beta := Ising.pOfBeta_pos hbeta
  have hr1r : IsingFK.pOfBeta beta < 1 := Ising.pOfBeta_lt_one beta
  let r : ℝ≥0 := ⟨IsingFK.pOfBeta beta, hr0r.le⟩
  have hr0 : 0 < r := by exact_mod_cast hr0r
  have hr1 : r < 1 := by exact_mod_cast hr1r
  have hid : Ising.magnetization 2 beta =
      fkTheta 2 hr0r hr1r (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    Ising.mfc_magPercoId 2 (by norm_num) (IsingFK.hbx_hisingBox 2)
      beta hbeta hr0r hr1r
  have hfk2 : 0 < fkTheta 2 hr0r hr1r (by norm_num : (0 : ℝ) < 2) (q := 2) := by
    rwa [← hid]
  have htheta2 : 0 < Percolation.theta 2 r hr1.le :=
    lt_of_lt_of_le hfk2 (fkTheta_two_le_bernoulliTheta r hr0 hr1)
  have hthetad : 0 < Percolation.theta d r hr1.le := by
    have h := lt_of_lt_of_le htheta2
      (Percolation.theta_two_le_theta_add (d - 2) r hr1.le)
    simpa [Nat.add_sub_of_le hd] using h
  obtain ⟨p, hp, hp1, hfk⟩ :=
    fkTheta_pos_of_bernoulliTheta_pos_general hr0 hr1 hq hthetad
  exact lt_of_le_of_lt (fkPc_le_of_fkTheta_pos_general hp hp1 hq hfk) hp1


theorem reducedDensity_two_inverse {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    reducedDensity (2 * r / (1 + r)) 2 = r := by
  unfold reducedDensity
  have hden : 0 < 1 + r := by linarith
  field_simp
  ring


theorem inverseReducedDensity_two_mem_Ioo {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < 2 * r / (1 + r) ∧ 2 * r / (1 + r) < 1 := by
  have hden : 0 < 1 + r := by linarith
  constructor
  · positivity
  · rw [div_lt_one hden]
    linarith



theorem fkTheta_two_pos_of_bernoulliTheta_pos
    {d : ℕ} {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (hθ : 0 < Percolation.theta d r hr1.le) :
    ∃ p : ℝ, ∃ hp : 0 < p, ∃ hp1 : p < 1,
      0 < fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  let p : ℝ := 2 * (r : ℝ) / (1 + r)
  have hr0r : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hr1r : (r : ℝ) < 1 := by exact_mod_cast hr1
  have hpIoo := inverseReducedDensity_two_mem_Ioo hr0r hr1r
  have hred : reducedDensity p 2 = r := reducedDensity_two_inverse hr0r hr1r
  refine ⟨p, hpIoo.1, hpIoo.2, ?_⟩
  have hdom := bernoulliTheta_reduced_le_fkTheta (d := d) hpIoo.1 hpIoo.2
  have hrnn :
      (⟨reducedDensity p 2,
          (reducedDensity_mem_Ioo hpIoo.1 hpIoo.2 (by norm_num)).1.le⟩ : ℝ≥0) = r := by
    exact NNReal.eq hred
  have hthetaEq :
      Percolation.theta d
          ⟨reducedDensity p 2,
            (reducedDensity_mem_Ioo hpIoo.1 hpIoo.2 (by norm_num)).1.le⟩
          (reducedDensity_mem_Ioo hpIoo.1 hpIoo.2 (by norm_num)).2.le =
        Percolation.theta d r hr1.le := by
    congr
  exact lt_of_lt_of_le (hthetaEq.symm ▸ hθ) hdom



theorem fkPc_le_of_fkTheta_pos {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hθ : 0 < fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)) :
    fkPc d 2 ≤ p := by
  rcases (fkSubcriticalSet d 2).eq_empty_or_nonempty with hempty | hne
  · rw [fkPc, hempty, Real.sSup_empty]
    exact hp.le
  · apply csSup_le hne
    intro r hr
    obtain ⟨hr0, hr1, _hq, hrzero⟩ := hr
    by_contra hnot
    have hpr : p < r := lt_of_not_ge hnot
    have hmono : fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) ≤
        fkTheta d hr0 hr1 (by norm_num : (0 : ℝ) < 2) (q := 2) :=
      tzp_fkTheta_monotone_in_p hp hp1 hr0 hr1 hpr.le
    rw [hrzero] at hmono
    linarith



theorem fkPc_two_lt_one_of_two_le {d : ℕ} (hd : 2 ≤ d) : fkPc d 2 < 1 := by
  obtain ⟨beta, hbeta, hmag⟩ := IsingFK.pup_exists_positive_magnetization
  have hr0r : 0 < IsingFK.pOfBeta beta := Ising.pOfBeta_pos hbeta
  have hr1r : IsingFK.pOfBeta beta < 1 := Ising.pOfBeta_lt_one beta
  let r : ℝ≥0 := ⟨IsingFK.pOfBeta beta, hr0r.le⟩
  have hr0 : 0 < r := by exact_mod_cast hr0r
  have hr1 : r < 1 := by exact_mod_cast hr1r
  have hid : Ising.magnetization 2 beta =
      fkTheta 2 hr0r hr1r (by norm_num : (0 : ℝ) < 2) (q := 2) :=
    Ising.mfc_magPercoId 2 (by norm_num) (IsingFK.hbx_hisingBox 2)
      beta hbeta hr0r hr1r
  have hfk2 : 0 < fkTheta 2 hr0r hr1r (by norm_num : (0 : ℝ) < 2) (q := 2) := by
    rwa [← hid]
  have hθ2 : 0 < Percolation.theta 2 r hr1.le :=
    lt_of_lt_of_le hfk2 (fkTheta_two_le_bernoulliTheta r hr0 hr1)
  have hθd : 0 < Percolation.theta d r hr1.le := by
    have h := lt_of_lt_of_le hθ2
      (Percolation.theta_two_le_theta_add (d - 2) r hr1.le)
    simpa [Nat.add_sub_of_le hd] using h
  obtain ⟨p, hp, hp1, hfk⟩ :=
    fkTheta_two_pos_of_bernoulliTheta_pos hr0 hr1 hθd
  exact lt_of_le_of_lt (fkPc_le_of_fkTheta_pos hp hp1 hfk) hp1

end FK

namespace IsingFK

open StatMech.Ising StatMech.FK



theorem ising_transition_at_fkPc_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    0 < pToBeta 2 (fkPc d 2) ∧
      (∀ beta, 0 < beta → beta < pToBeta 2 (fkPc d 2) →
        magnetization d beta = 0) ∧
      (∀ beta, pToBeta 2 (fkPc d 2) < beta →
        0 < magnetization d beta) := by
  let pc := fkPc d 2
  let betaC := pToBeta 2 pc
  change 0 < betaC ∧
    (∀ beta, 0 < beta → beta < betaC → magnetization d beta = 0) ∧
    (∀ beta, betaC < beta → 0 < magnetization d beta)
  have hpc0 : 0 < pc := fkPc_pos_of_two_le hd (by norm_num)
  have hpc1 : fkPc d 2 < 1 := fkPc_two_lt_one_of_two_le hd
  have hbetaC : 0 < betaC := pToBeta_two_pos hpc0 hpc1
  refine ⟨hbetaC, ?_, ?_⟩
  · intro beta hbeta hbetalt
    have hp : 0 < pOfBeta beta := pOfBeta_pos hbeta
    have hp1 : pOfBeta beta < 1 := pOfBeta_lt_one beta
    have hparam : pOfBeta beta < pc := by
      apply ((strictMonoOn_pToBeta 2 (by norm_num)).lt_iff_lt
        (Set.mem_Iio.mpr hp1) (Set.mem_Iio.mpr hpc1)).mp
      rw [fkRoute_pToBeta_pOfBeta]
      exact hbetalt
    have hzero : fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 :=
      tzp_fkTheta_eq_zero_of_lt_pc hp hp1 hparam
    have hid := mfc_magPercoId d (le_trans (by norm_num) hd)
      (hbx_hisingBox d) beta hbeta hp hp1
    exact hid.trans hzero
  · intro beta hbetagt
    have hbeta : 0 < beta := lt_trans hbetaC hbetagt
    have hp : 0 < pOfBeta beta := pOfBeta_pos hbeta
    have hp1 : pOfBeta beta < 1 := pOfBeta_lt_one beta
    have hparam : pc < pOfBeta beta :=
      (fkPc_lt_pOfBeta_iff d hbeta hpc1).mpr hbetagt
    have htheta := fkTheta_pos_of_fkPc_lt d hp hp1 hparam
    have hid := mfc_magPercoId d (le_trans (by norm_num) hd)
      (hbx_hisingBox d) beta hbeta hp hp1
    rwa [hid]



theorem ising_transition_unconditional_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    ∃ betaC : ℝ, 0 < betaC ∧
      (∀ beta, 0 < beta → beta < betaC → magnetization d beta = 0) ∧
      (∀ beta, betaC < beta → 0 < magnetization d beta) :=
  ⟨pToBeta 2 (fkPc d 2), ising_transition_at_fkPc_of_two_le hd⟩



theorem isingBetaC_eq_fkPc_of_two_le {d : ℕ} (hd : 2 ≤ d) :
    betaC (magnetization d) = -(1 / 2) * Real.log (1 - fkPc d 2) := by
  let betaC0 := pToBeta 2 (fkPc d 2)
  obtain ⟨hbetaC0, hbelow, habove⟩ := ising_transition_at_fkPc_of_two_le hd
  let S : Set ℝ := {beta : ℝ | 0 < beta ∧ magnetization d beta = 0}
  have hub : ∀ beta ∈ S, beta ≤ betaC0 := by
    intro beta hbetaS
    by_contra hnot
    have hgt : betaC0 < beta := lt_of_not_ge hnot
    exact (ne_of_gt (habove beta hgt)) hbetaS.2
  have hbdd : BddAbove S := ⟨betaC0, hub⟩
  have hwit : betaC0 / 2 ∈ S :=
    ⟨by linarith, hbelow _ (by linarith) (by linarith)⟩
  have hsupLe : sSup S ≤ betaC0 := csSup_le ⟨betaC0 / 2, hwit⟩ hub
  have hleSup : betaC0 ≤ sSup S := by
    apply le_of_forall_lt_imp_le_of_dense
    intro a ha
    by_cases ha0 : a ≤ 0
    · exact ha0.trans (le_trans (by linarith : (0 : ℝ) ≤ betaC0 / 2)
        (le_csSup hbdd hwit))
    · have haPos : 0 < a := lt_of_not_ge ha0
      exact le_csSup hbdd ⟨haPos, hbelow a haPos ha⟩
  have hs : sSup S = betaC0 := le_antisymm hsupLe hleSup
  unfold betaC
  change sSup S = _
  rw [hs, show betaC0 = pToBeta 2 (fkPc d 2) from rfl, pToBeta_two]

end IsingFK
end StatMech
