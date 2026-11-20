/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FK.InfiniteVolume
import Code.IsingFK.EsWired
import Code.IsingFK.EsLatticeBridge
import Code.IsingFK.FvES
import Code.IsingFK.MagPercoIdBox
import Code.Foundations.Prokhorov

open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

namespace StatMech
namespace FK

open Lattice





theorem probabilityMeasure_seq_compact
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [SecondCountableTopology X] [T2Space X]
    (mu : ℕ → ProbabilityMeasure X) :
    ∃ (nu : ProbabilityMeasure X) (phi : ℕ → ℕ), StrictMono phi ∧
      Tendsto (mu ∘ phi) atTop (nhds nu) := by
  obtain ⟨nu, phi, hphi, hlim⟩ := CompactSpace.tendsto_subseq mu
  exact ⟨nu, phi, hphi, hlim⟩



variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ivp_freeJointProb (q : ℕ) (p : ℝ)
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) : ℝ :=
  esWeight G p z.1 z.2 / esZ G q p

theorem ivp_freeJointProb_nonneg {q : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) : 0 ≤ ivp_freeJointProb G q p z := by
  apply div_nonneg (esWeight_nonneg G hp hp1 z.1 z.2)
  exact Finset.sum_nonneg fun w _ =>
    Finset.sum_nonneg fun s _ => esWeight_nonneg G hp hp1 s w




theorem ivp_freeJointProb_eq_fkProb_div_pow {q : Nat} {p : Real}
    (hq : 0 < (q : Real))
    (sigma : V -> Fin q) (omega : ConfigSpace (Sym2 V)) :
    ivp_freeJointProb G q p (sigma, omega) =
      if ConstOnOpen G omega sigma then
        fkProb G p (q : Real) omega / (q : Real) ^ numClusters G omega
      else 0 := by
  unfold ivp_freeJointProb
  rw [esWeight_factor, monoProd_eq_indicator, esZ_eq_fkZ]
  by_cases hconst : ConstOnOpen G omega sigma
  · rw [if_pos hconst, if_pos hconst]
    unfold fkProb fkWeight
    have hpow : (q : Real) ^ numClusters G omega ≠ 0 :=
      pow_ne_zero _ hq.ne'
    field_simp
  · rw [if_neg hconst, if_neg hconst]
    simp

theorem ivp_freeJointProb_sum_eq_one {q : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    ∑ z : (V → Fin q) × ConfigSpace (Sym2 V), ivp_freeJointProb G q p z = 1 := by
  unfold ivp_freeJointProb
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_div]
  rw [show (∑ s : V → Fin q, ∑ w : ConfigSpace (Sym2 V), esWeight G p s w) =
      esZ G q p by rw [esZ, Finset.sum_comm]]
  exact div_self (esZ_pos G hp hp1 hq).ne'


noncomputable def ivp_freeJointPMF (q : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    PMF ((V → Fin q) × ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (ivp_freeJointProb G q p z)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => ivp_freeJointProb_nonneg G hp.le hp1.le z),
      ivp_freeJointProb_sum_eq_one G hp hp1 hq, ENNReal.ofReal_one]


theorem ivp_freeJointPMF_map_fst (q : ℕ) [NeZero q] (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (ivp_freeJointPMF G q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.fst =
      Potts.pottsPMF G q beta J := by
  ext s
  rw [PMF.map_apply, Potts.pottsPMF_apply, tsum_fintype]
  simp only [ivp_freeJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  rw [Finset.sum_eq_single s]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← esFirstMarginal_eq_pottsProb G q beta J]
      unfold esFirstMarginal ivp_freeJointProb
      rw [Finset.sum_div]
    · intro w _
      exact ivp_freeJointProb_nonneg G hp.le hp1.le (s, w)
  · intro t _ hts
    simp [Ne.symm hts]
  · simp


theorem ivp_freeJointPMF_map_snd (q : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    (ivp_freeJointPMF G q hp hp1 hq).map Prod.snd = fkPMF G hp hp1 hq := by
  ext w
  rw [PMF.map_apply, fkPMF_apply, tsum_fintype]
  simp only [ivp_freeJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  change (∑ s : V → Fin q, ∑ z : ConfigSpace (Sym2 V),
      if w = z then ENNReal.ofReal (ivp_freeJointProb G q p (s, z)) else 0) = _
  rw [Finset.sum_comm, Finset.sum_eq_single w]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← esSecondMarginal_eq_fkProb G q p]
      unfold esSecondMarginal ivp_freeJointProb
      rw [Finset.sum_div]
    · intro s _
      exact ivp_freeJointProb_nonneg G hp.le hp1.le (s, w)
  · intro z _ hzw
    simp [Ne.symm hzw]
  · simp



namespace Wired

open IsingFK

variable (bdry : V → Prop) [DecidablePred bdry]


noncomputable def ivp_wiredJointProb {q : ℕ} (b : Fin q) (beta J : ℝ)
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) : ℝ :=
  esWeightWired G bdry b (1 - Real.exp (-(beta * J))) z.1 z.2 /
    esZWired G bdry q b (1 - Real.exp (-(beta * J)))

theorem ivp_esZWired_pos {q : ℕ} [NeZero q] (b : Fin q) (beta J : ℝ) :
    0 < esZWired G bdry q b (1 - Real.exp (-(beta * J))) := by
  rw [esZWired_eq_pottsZWired G bdry b beta J]
  exact mul_pos (esFirstConst_pos G beta J) (pottsZWired_pos G bdry q b beta J)

theorem ivp_wiredJointProb_nonneg {q : ℕ} [NeZero q] (b : Fin q) (beta J : ℝ)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J)))
    (z : (V → Fin q) × ConfigSpace (Sym2 V)) :
    0 ≤ ivp_wiredJointProb G bdry b beta J z := by
  exact div_nonneg
    (esWeightWired_nonneg G bdry hp
      (by linarith [Real.exp_pos (-(beta * J))]) z.1 z.2)
    (ivp_esZWired_pos G bdry b beta J).le

theorem ivp_wiredJointProb_sum_eq_one {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ) :
    ∑ z : (V → Fin q) × ConfigSpace (Sym2 V),
      ivp_wiredJointProb G bdry b beta J z = 1 := by
  unfold ivp_wiredJointProb
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_div]
  rw [show (∑ s : V → Fin q, ∑ w : ConfigSpace (Sym2 V),
      esWeightWired G bdry b (1 - Real.exp (-(beta * J))) s w) =
      esZWired G bdry q b (1 - Real.exp (-(beta * J))) by
        rw [esZWired, Finset.sum_comm]]
  exact div_self (ivp_esZWired_pos G bdry b beta J).ne'


noncomputable def ivp_wiredJointPMF {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ) (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    PMF ((V → Fin q) × ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (ivp_wiredJointProb G bdry b beta J z)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg
        (fun z _ => ivp_wiredJointProb_nonneg G bdry b beta J hp z),
      ivp_wiredJointProb_sum_eq_one G bdry b beta J, ENNReal.ofReal_one]


theorem ivp_wiredJointPMF_map_fst {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ) (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    (ivp_wiredJointPMF G bdry b beta J hp).map Prod.fst =
      PMF.ofFintype
        (fun s => ENNReal.ofReal (pottsProbWired G bdry q b beta J s)) (by
          rw [← ENNReal.ofReal_sum_of_nonneg
              (fun s _ => pottsProbWired_nonneg G bdry q b beta J s),
            pottsProbWired_sum_eq_one G bdry q b beta J, ENNReal.ofReal_one]) := by
  ext s
  rw [PMF.map_apply, PMF.ofFintype_apply, tsum_fintype]
  simp only [ivp_wiredJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  rw [Finset.sum_eq_single s]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [← esWiredFirstMarginal_eq_pottsProbWired G bdry b beta J]
      unfold esWiredFirstMarginal ivp_wiredJointProb
      rw [Finset.sum_div]
    · intro w _
      exact ivp_wiredJointProb_nonneg G bdry b beta J hp (s, w)
  · intro t _ hts
    simp [Ne.symm hts]
  · simp


theorem ivp_wiredJointPMF_map_snd {q : ℕ} [NeZero q]
    (b : Fin q) (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1)
    (v0 : V) (hv0 : bdry v0) :
    (ivp_wiredJointPMF G bdry b beta J hp.le).map Prod.snd =
      wiredFkPMF G bdry hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
  ext w
  rw [PMF.map_apply, wiredFkPMF, PMF.ofFintype_apply, tsum_fintype]
  simp only [ivp_wiredJointPMF, PMF.ofFintype_apply]
  rw [Fintype.sum_prod_type]
  classical
  change (∑ s : V → Fin q, ∑ z : ConfigSpace (Sym2 V),
      if w = z then ENNReal.ofReal (ivp_wiredJointProb G bdry b beta J (s, z)) else 0) = _
  rw [Finset.sum_comm, Finset.sum_eq_single w]
  · simp only [if_pos]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [wiredFkProb_eq_bcProb G bdry]
      rw [← esWiredSecondMarginal_eq_bcProb G bdry b
        (1 - Real.exp (-(beta * J))) w v0 hv0 (Nat.pos_of_neZero q)
        (fun z => one_le_numClustersBC G bdry v0 z)]
      unfold esWiredSecondMarginal ivp_wiredJointProb
      rw [Finset.sum_div]
    · intro s _
      exact ivp_wiredJointProb_nonneg G bdry b beta J hp.le (s, w)
  · intro z _ hzw
    simp [Ne.symm hzw]
  · simp

end Wired




abbrev PottsConfig (d q : ℕ) := Site d → Fin q


abbrev PottsJointConfig (d q : ℕ) :=
  PottsConfig d q × ConfigSpace (Sym2 (Site d))


noncomputable def ivp_extendSpin (d n q : ℕ) [NeZero q]
    (sigma : boxVerts d n → Fin q) : PottsConfig d q :=
  fun x => if hx : x ∈ box d n then sigma ⟨x, hx⟩ else default

theorem ivp_measurable_extendSpin (d n q : ℕ) [NeZero q] :
    Measurable (ivp_extendSpin d n q) :=
  Measurable.of_discrete


noncomputable def ivp_extendJoint (d n q : ℕ) [NeZero q]
    (z : (boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) :
    PottsJointConfig d q :=
  (ivp_extendSpin d n q z.1, extendEdge d n z.2)

theorem ivp_measurable_extendJoint (d n q : ℕ) [NeZero q] :
    Measurable (ivp_extendJoint d n q) :=
  Measurable.of_discrete


noncomputable def freePottsFiniteMeasure (d n q : ℕ) [NeZero q]
    (beta J : ℝ) : ProbabilityMeasure (PottsConfig d q) :=
  ⟨(Potts.pottsPMF (boxGraph d n) q beta J).toMeasure.map (ivp_extendSpin d n q),
    Measure.isProbabilityMeasure_map (ivp_measurable_extendSpin d n q).aemeasurable⟩


noncomputable def freePottsJointFiniteMeasure (d n q : ℕ) [NeZero q]
    (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendJoint d n q),
    Measure.isProbabilityMeasure_map (ivp_measurable_extendJoint d n q).aemeasurable⟩


noncomputable def wiredPottsPMF (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V → Prop) [DecidablePred bdry] (q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ) : PMF (V → Fin q) :=
  PMF.ofFintype
    (fun s => ENNReal.ofReal (IsingFK.pottsProbWired G bdry q b beta J s)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun s _ => IsingFK.pottsProbWired_nonneg G bdry q b beta J s),
        IsingFK.pottsProbWired_sum_eq_one G bdry q b beta J, ENNReal.ofReal_one])


noncomputable def wiredPottsFiniteMeasure (d n q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ) : ProbabilityMeasure (PottsConfig d q) :=
  ⟨(wiredPottsPMF (boxGraph d n) (boxBoundary d n) q b beta J).toMeasure.map
      (ivp_extendSpin d n q),
    Measure.isProbabilityMeasure_map (ivp_measurable_extendSpin d n q).aemeasurable⟩


noncomputable def wiredPottsJointFiniteMeasure (d n q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n) b beta J hp).toMeasure.map
      (ivp_extendJoint d n q),
    Measure.isProbabilityMeasure_map (ivp_measurable_extendJoint d n q).aemeasurable⟩




theorem freePottsJointFiniteMeasure_map_fst (d n q : ℕ) [NeZero q]
    (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (freePottsJointFiniteMeasure d n q beta J hp hp1).map
        continuous_fst.measurable.aemeasurable =
      freePottsFiniteMeasure d n q beta J := by
  ext s hs
  change (((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendJoint d n q)).map Prod.fst) s = _
  rw [Measure.map_map continuous_fst.measurable (ivp_measurable_extendJoint d n q)]
  change ((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendSpin d n q ∘ Prod.fst)) s = _
  have hfst : Measurable (Prod.fst :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (ivp_measurable_extendSpin d n q) hfst]
  rw [show Measure.map Prod.fst
      (ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure =
      ((ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.fst).toMeasure from
        PMF.toMeasure_map Prod.fst _ hfst,
    ivp_freeJointPMF_map_fst]
  rfl


theorem freePottsJointFiniteMeasure_map_snd (d n q : ℕ) [NeZero q]
    (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (freePottsJointFiniteMeasure d n q beta J hp hp1).map
        continuous_snd.measurable.aemeasurable =
      freeFiniteMeasure d n hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
  ext s hs
  change (((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendJoint d n q)).map Prod.snd) s = _
  rw [Measure.map_map continuous_snd.measurable (ivp_measurable_extendJoint d n q)]
  change ((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (extendEdge d n ∘ Prod.snd)) s = _
  have hsnd : Measurable (Prod.snd :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (measurable_extendEdge d n) hsnd]
  rw [show Measure.map Prod.snd
      (ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure =
      ((ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.snd).toMeasure from
        PMF.toMeasure_map Prod.snd _ hsnd,
    ivp_freeJointPMF_map_snd]
  rfl


theorem wiredPottsJointFiniteMeasure_map_fst (d n q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    (wiredPottsJointFiniteMeasure d n q b beta J hp).map
        continuous_fst.measurable.aemeasurable =
      wiredPottsFiniteMeasure d n q b beta J := by
  ext s hs
  change (((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp).toMeasure.map (ivp_extendJoint d n q)).map Prod.fst) s = _
  rw [Measure.map_map continuous_fst.measurable (ivp_measurable_extendJoint d n q)]
  change ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp).toMeasure.map (ivp_extendSpin d n q ∘ Prod.fst)) s = _
  have hfst : Measurable (Prod.fst :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (ivp_measurable_extendSpin d n q) hfst]
  rw [show Measure.map Prod.fst
      (Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp).toMeasure =
      ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp).map Prod.fst).toMeasure from PMF.toMeasure_map Prod.fst _ hfst,
    Wired.ivp_wiredJointPMF_map_fst]
  rfl


theorem wiredPottsJointFiniteMeasure_map_snd (d n q : ℕ) [NeZero q]
    (hd : 1 ≤ d) (hn : 1 ≤ n) (b : Fin q) (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (wiredPottsJointFiniteMeasure d n q b beta J hp.le).map
        continuous_snd.measurable.aemeasurable =
      wiredFiniteMeasure d n hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
  obtain ⟨v0, hv0⟩ := IsingFK.boxBoundary_nonempty d n hd hn
  ext s hs
  change (((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp.le).toMeasure.map (ivp_extendJoint d n q)).map Prod.snd) s = _
  rw [Measure.map_map continuous_snd.measurable (ivp_measurable_extendJoint d n q)]
  change ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp.le).toMeasure.map (extendEdge d n ∘ Prod.snd)) s = _
  have hsnd : Measurable (Prod.snd :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (measurable_extendEdge d n) hsnd]
  rw [show Measure.map Prod.snd
      (Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp.le).toMeasure =
      ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp.le).map Prod.snd).toMeasure from PMF.toMeasure_map Prod.snd _ hsnd,
    Wired.ivp_wiredJointPMF_map_snd (boxGraph d n) (boxBoundary d n)
      b beta J hp hp1 v0 hv0]
  rfl







theorem freePottsInfiniteVolume_exists (d q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (beta J : ℝ) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q))
      (mu : ProbabilityMeasure (PottsConfig d q)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      Tendsto (fun n => freePottsJointFiniteMeasure d (phi n) q beta J
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by
            have he := Real.exp_pos (-(beta * J))
            linarith))
        atTop (nhds Xi) ∧
      Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
        atTop (nhds mu) ∧
      Xi.map continuous_fst.measurable.aemeasurable = mu ∧
      Xi.map continuous_snd.measurable.aemeasurable =
        freeInfiniteVolume d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by
            have he := Real.exp_pos (-(beta * J))
            linarith)
          (by exact_mod_cast (show 0 < q by omega) : (0 : ℝ) < q) := by
  let p : ℝ := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    unfold p
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨psi, hpsi, hfk⟩ := freeInfiniteVolume_isLimit d hp hp1 hqR
  obtain ⟨Xi, eta, heta, hjoint0⟩ := probabilityMeasure_seq_compact
    (fun n => freePottsJointFiniteMeasure d (psi n) q beta J hp hp1)
  let phi : ℕ → ℕ := psi ∘ eta
  let mu : ProbabilityMeasure (PottsConfig d q) :=
    Xi.map continuous_fst.measurable.aemeasurable
  have hphi : StrictMono phi := hpsi.comp heta
  have hjoint : Tendsto
      (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
      atTop (nhds Xi) := by
    simpa [phi, Function.comp_def] using hjoint0
  have hspin0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi hjoint continuous_fst
  have hspin : Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
      atTop (nhds mu) := by
    simpa only [freePottsJointFiniteMeasure_map_fst] using hspin0
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi hjoint continuous_snd
  have hedge : Tendsto (fun n => freeFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (Xi.map continuous_snd.measurable.aemeasurable)) := by
    simpa only [freePottsJointFiniteMeasure_map_snd] using hedge0
  have hfk' : Tendsto (fun n => freeFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (freeInfiniteVolume d hp hp1 hqR)) := by
    simpa [phi, Function.comp_def] using hfk.comp heta.tendsto_atTop
  have hedgeEq : Xi.map continuous_snd.measurable.aemeasurable =
      freeInfiniteVolume d hp hp1 hqR :=
    tendsto_nhds_unique hedge hfk'
  refine ⟨Xi, mu, phi, hphi, ?_, hspin, rfl, hedgeEq⟩
  simpa [p] using hjoint




theorem wiredPottsInfiniteVolume_exists (d q : ℕ) [NeZero q]
    (hd : 1 ≤ d) (hq : 2 ≤ q)
    (b : Fin q) (beta J : ℝ) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q))
      (mu : ProbabilityMeasure (PottsConfig d q)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      Tendsto (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J
          (by
            apply sub_nonneg.mpr
            rw [Real.exp_le_one_iff]
            exact neg_nonpos.mpr (mul_pos hbeta hJ).le))
        atTop (nhds Xi) ∧
      Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
        atTop (nhds mu) ∧
      Xi.map continuous_fst.measurable.aemeasurable = mu ∧
      Xi.map continuous_snd.measurable.aemeasurable =
        wiredInfiniteVolume d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by
            have he := Real.exp_pos (-(beta * J))
            linarith)
          (by exact_mod_cast (show 0 < q by omega) : (0 : ℝ) < q) := by
  let p : ℝ := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    unfold p
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨psi, hpsi, hfk⟩ := wiredInfiniteVolume_isLimit d hp hp1 hqR
  let rho : ℕ → ℕ := fun n => psi (n + 1)
  have hrho : StrictMono rho :=
    hpsi.comp (strictMono_nat_of_lt_succ fun n => by omega)
  have hrho_pos : ∀ n, 1 ≤ rho n := by
    intro n
    have hle : n + 1 ≤ psi (n + 1) := hpsi.id_le (n + 1)
    change 1 ≤ psi (n + 1)
    omega
  have hfkRho : Tendsto (fun n => wiredFiniteMeasure d (rho n) hp hp1 hqR)
      atTop (nhds (wiredInfiniteVolume d hp hp1 hqR)) := by
    simpa [rho, Function.comp_def] using hfk.comp (tendsto_add_atTop_nat 1)
  obtain ⟨Xi, eta, heta, hjoint0⟩ := probabilityMeasure_seq_compact
    (fun n => wiredPottsJointFiniteMeasure d (rho n) q b beta J hp.le)
  let phi : ℕ → ℕ := rho ∘ eta
  let mu : ProbabilityMeasure (PottsConfig d q) :=
    Xi.map continuous_fst.measurable.aemeasurable
  have hphi : StrictMono phi := hrho.comp heta
  have hjoint : Tendsto
      (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le)
      atTop (nhds Xi) := by
    simpa [phi, Function.comp_def] using hjoint0
  have hspin0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le)
    Xi hjoint continuous_fst
  have hspin : Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
      atTop (nhds mu) := by
    simpa only [wiredPottsJointFiniteMeasure_map_fst] using hspin0
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le)
    Xi hjoint continuous_snd
  have hmapEdge : ∀ n,
      (wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le).map
          continuous_snd.measurable.aemeasurable =
        wiredFiniteMeasure d (phi n) hp hp1 hqR := by
    intro n
    exact wiredPottsJointFiniteMeasure_map_snd d (phi n) q hd
      (by simpa [phi] using hrho_pos (eta n)) b beta J hp hp1
  have hedge : Tendsto (fun n => wiredFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (Xi.map continuous_snd.measurable.aemeasurable)) := by
    simpa only [hmapEdge] using hedge0
  have hfk' : Tendsto (fun n => wiredFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (wiredInfiniteVolume d hp hp1 hqR)) := by
    simpa [phi, Function.comp_def] using hfkRho.comp heta.tendsto_atTop
  have hedgeEq : Xi.map continuous_snd.measurable.aemeasurable =
      wiredInfiniteVolume d hp hp1 hqR :=
    tendsto_nhds_unique hedge hfk'
  refine ⟨Xi, mu, phi, hphi, ?_, hspin, rfl, hedgeEq⟩
  simpa [p] using hjoint

end FK
end StatMech
