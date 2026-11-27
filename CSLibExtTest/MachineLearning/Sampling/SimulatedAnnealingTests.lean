/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.Sampling.SimulatedAnnealing
import Mathlib.Tactic.FinCases

@[expose] public section

namespace Cslib.MachineLearning.Sampling.SimulatedAnnealing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {S : Type*} [Fintype S] [DecidableEq S] (R : S → PMF S) (V : S → ℝ)

/-- Two-well landscape on `Fin 3`: energies `![0, 2, 1]`. -/
def twoWellV : Fin 3 → ℝ := ![0, 2, 1]

/-- Two-well proposal: each state proposes itself or its lower neighbour
with probability `1/2` each (symmetric). -/
noncomputable def twoWellR : Fin 3 → PMF (Fin 3)
  | 0 => PMF.ofFintype (fun j => if j = 0 ∨ j = 1 then 1 / 2 else 0) (by simp [Fin.sum_univ_three, ENNReal.inv_two_add_inv_two])
  | 1 => PMF.ofFintype (fun j => if j = 0 ∨ j = 2 then 1 / 2 else 0) (by simp [Fin.sum_univ_three, ENNReal.inv_two_add_inv_two])
  | 2 => PMF.ofFintype (fun j => if j = 1 ∨ j = 2 then 1 / 2 else 0) (by simp [Fin.sum_univ_three, ENNReal.inv_two_add_inv_two])

/-- The two-well landscape is strongly irreducible and weakly reversible. -/
theorem twoWell_si_wr : StronglyIrreducible twoWellR twoWellV ∧
    WeaklyReversible twoWellR twoWellV := by
  have asymm : ∀ a b : Fin 3, Arc twoWellR a b → Arc twoWellR b a := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Arc, twoWellR, PMF.ofFintype_apply]
  have a01 : Arc twoWellR 0 1 := by simp [Arc, twoWellR, PMF.ofFintype_apply]
  have a10 : Arc twoWellR 1 0 := by simp [Arc, twoWellR, PMF.ofFintype_apply]
  have a12 : Arc twoWellR 1 2 := by simp [Arc, twoWellR, PMF.ofFintype_apply]
  have a21 : Arc twoWellR 2 1 := by simp [Arc, twoWellR, PMF.ofFintype_apply]
  have e01 : Relation.ReflTransGen (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ 2) 0 1 :=
    Relation.ReflTransGen.single ⟨a01, by norm_num [twoWellV]⟩
  have e10 : Relation.ReflTransGen (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ 2) 1 0 :=
    Relation.ReflTransGen.single ⟨a10, by norm_num [twoWellV]⟩
  have e12 : Relation.ReflTransGen (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ 2) 1 2 :=
    Relation.ReflTransGen.single ⟨a12, by norm_num [twoWellV]⟩
  have e21 : Relation.ReflTransGen (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ 2) 2 1 :=
    Relation.ReflTransGen.single ⟨a21, by norm_num [twoWellV]⟩
  have hSI : StronglyIrreducible twoWellR twoWellV := by
    intro i j
    refine ⟨2, ?_, ?_⟩
    · fin_cases j <;> simp only [twoWellV] <;> norm_num
    · fin_cases j <;> fin_cases i
      · exact Relation.ReflTransGen.refl
      · exact e01
      · exact e01.trans e12
      · exact e10
      · exact Relation.ReflTransGen.refl
      · exact e12
      · exact e21.trans e10
      · exact e21
      · exact Relation.ReflTransGen.refl
  have dir : ∀ (E : ℝ) (p q : Fin 3),
      ReachableAt twoWellR twoWellV E p q → ReachableAt twoWellR twoWellV E q p := by
    intro E p q h
    obtain ⟨hpE, hrtc⟩ := h
    have rev := Relation.ReflTransGen.head_induction_on (motive := fun a _ => twoWellV a ≤ E →
        Relation.ReflTransGen (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ E) q a ∧
        twoWellV q ≤ E) hrtc
      (fun hqE => ⟨Relation.ReflTransGen.refl, hqE⟩)
      (fun h' h ih haE => by
        obtain ⟨harc, hcE⟩ := h'
        obtain ⟨hrtc', hqE⟩ := ih hcE
        exact ⟨hrtc'.tail ⟨asymm _ _ harc, haE⟩, hqE⟩)
      hpE
    exact ⟨rev.2, rev.1⟩
  have hWR : WeaklyReversible twoWellR twoWellV := by
    intro E i j
    exact ⟨dir E j i, dir E i j⟩
  exact ⟨hSI, hWR⟩

/-- In the two-well landscape, `2` is a non-global local minimum of depth
`1`, and `d* = 1`. -/
theorem twoWell_depths : IsHajekLocalMin twoWellR twoWellV 2 ∧
    depth twoWellR twoWellV 2 = 1 ∧ dStar twoWellR twoWellV = 1 := by
  have a10 : Arc twoWellR 1 0 := by simp [Arc, twoWellR, PMF.ofFintype_apply]
  have a21 : Arc twoWellR 2 1 := by simp [Arc, twoWellR, PMF.ofFintype_apply]
  have v1 : twoWellV 1 = 2 := by simp [twoWellV]
  have v2 : twoWellV 2 = 1 := by simp [twoWellV]
  have hc3 : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by
    intro c
    match c with
    | 0 => exact Or.inl rfl
    | 1 => exact Or.inr (Or.inl rfl)
    | 2 => exact Or.inr (Or.inr rfl)
  have trap1 : ∀ b : Fin 3, Relation.ReflTransGen
      (fun a c => Arc twoWellR a c ∧ twoWellV c ≤ twoWellV 2) 2 b → b = 2 := by
    intro b h
    have key := Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => a = 2 → b = 2) h
      (fun h => h)
      (fun {a c} h' _ ih ha => by
        subst ha
        obtain ⟨harc, hcE⟩ := h'
        obtain rfl | rfl | rfl := hc3 c
        · simp [Arc, twoWellR, PMF.ofFintype_apply] at harc
        · rw [v1, v2] at hcE
          norm_num at hcE
        · exact ih rfl)
    exact key rfl
  have trap2 : ∀ (H : ℝ) (b : Fin 3), Relation.ReflTransGen
      (fun a c => Arc twoWellR a c ∧ twoWellV c ≤ H) 2 b →
      b = 2 ∨ twoWellV 1 ≤ H := by
    intro H b h
    have key := Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => a = 2 → b = 2 ∨ twoWellV 1 ≤ H) h
      (fun h => Or.inl h)
      (fun {a c} h' _ ih ha => by
        subst ha
        obtain ⟨harc, hcE⟩ := h'
        obtain rfl | rfl | rfl := hc3 c
        · simp [Arc, twoWellR, PMF.ofFintype_apply] at harc
        · exact Or.inr hcE
        · exact ih rfl)
    exact key rfl
  have hlocal : IsHajekLocalMin twoWellR twoWellV 2 := by
    intro t hlt hreach
    obtain ⟨-, hrtc⟩ := hreach
    have ht2 : t = 2 := trap1 t hrtc
    subst ht2
    exact absurd hlt (lt_irrefl _)
  have hdepth : depth twoWellR twoWellV 2 = 1 := by
    have h1 : (0:ℝ) < 1 ∧ ∃ t, twoWellV t < twoWellV 2 ∧
        ReachableAt twoWellR twoWellV (twoWellV 2 + 1) 2 t := by
      refine ⟨zero_lt_one, 0, by norm_num [twoWellV], ?_, ?_⟩
      · exact le_add_of_nonneg_right zero_le_one
      · have s21 : (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ twoWellV 2 + 1) 2 1 :=
          ⟨a21, by norm_num [twoWellV]⟩
        have s10 : (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ twoWellV 2 + 1) 1 0 :=
          ⟨a10, by norm_num [twoWellV]⟩
        have e1 : Relation.ReflTransGen
            (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ twoWellV 2 + 1) 2 1 :=
          Relation.ReflTransGen.single s21
        have e2 : Relation.ReflTransGen
            (fun a b => Arc twoWellR a b ∧ twoWellV b ≤ twoWellV 2 + 1) 1 0 :=
          Relation.ReflTransGen.single s10
        exact e1.trans e2
    have hle : depth twoWellR twoWellV 2 ≤ 1 := by
      calc depth twoWellR twoWellV 2
          = ⨅ (E : ℝ) (_ : 0 < E ∧ ∃ t, twoWellV t < twoWellV 2 ∧
              ReachableAt twoWellR twoWellV (twoWellV 2 + E) 2 t),
            ENNReal.ofReal E := rfl
        _ ≤ (⨅ _ : 0 < (1:ℝ) ∧ ∃ t, twoWellV t < twoWellV 2 ∧
              ReachableAt twoWellR twoWellV (twoWellV 2 + 1) 2 t,
            ENNReal.ofReal 1) := iInf_le _ 1
        _ ≤ ENNReal.ofReal 1 := iInf_le _ h1
        _ = 1 := ENNReal.ofReal_one
    have hge : 1 ≤ depth twoWellR twoWellV 2 := by
      rw [depth]
      apply le_iInf
      intro E
      apply le_iInf
      intro hP
      obtain ⟨-, t, hlt, hreach⟩ := hP
      obtain ⟨-, hrtc⟩ := hreach
      have htrap := trap2 (twoWellV 2 + E) t hrtc
      have hE : (1:ℝ) ≤ E := by
        rcases htrap with rfl | hle2
        · exact absurd hlt (lt_irrefl _)
        · rw [v1, v2] at hle2
          linarith
      calc (1:ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal E := ENNReal.ofReal_le_ofReal hE
    exact le_antisymm hle hge
  have h0min : (0 : Fin 3) ∈ globalMinSet twoWellV := by
    simp only [globalMinSet, Set.mem_setOf_eq]
    intro t
    fin_cases t <;> norm_num [twoWellV]
  have h1nlocal : ¬ IsHajekLocalMin twoWellR twoWellV 1 := by
    intro h
    have h0 := h 0 (by norm_num [twoWellV])
    apply h0
    refine ⟨le_rfl, Relation.ReflTransGen.single ?_⟩
    exact ⟨a10, by norm_num [twoWellV]⟩
  have h2nglob : (2 : Fin 3) ∉ globalMinSet twoWellV := by
    intro h
    simp only [globalMinSet, Set.mem_setOf_eq] at h
    have hle := h 0
    simp only [twoWellV] at hle
    norm_num at hle
  have hdStar : dStar twoWellR twoWellV = 1 := by
    have f0 : (⨆ _ : IsHajekLocalMin twoWellR twoWellV 0 ∧
        0 ∉ globalMinSet twoWellV, depth twoWellR twoWellV 0) = ⊥ :=
      iSup_neg (fun h => h.2 h0min)
    have f1 : (⨆ _ : IsHajekLocalMin twoWellR twoWellV 1 ∧
        1 ∉ globalMinSet twoWellV, depth twoWellR twoWellV 1) = ⊥ :=
      iSup_neg (fun h => h1nlocal h.1)
    have f2 : (⨆ _ : IsHajekLocalMin twoWellR twoWellV 2 ∧
        2 ∉ globalMinSet twoWellV, depth twoWellR twoWellV 2)
        = depth twoWellR twoWellV 2 :=
      iSup_pos ⟨hlocal, h2nglob⟩
    have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    have hEq : dStar twoWellR twoWellV = (⨆ s : Fin 3,
        ⨆ _ : IsHajekLocalMin twoWellR twoWellV s ∧ s ∉ globalMinSet twoWellV,
        depth twoWellR twoWellV s) := rfl
    rw [hEq, ← Finset.sup_univ_eq_iSup, huniv]
    simp only [Finset.sup_insert, Finset.sup_singleton, f0, f1, f2, bot_sup_eq]
    exact hdepth
  exact ⟨hlocal, hdepth, hdStar⟩

/-- Energies of the Figure 1 landscape in Bruce Hajek, "Optimization by
simulated annealing: a necessary and sufficient condition for convergence",
in *Adaptive Statistical Procedures and Related Topics*, IMS Lecture
Notes--Monograph Series, vol. 8 (1986), pp. 417--427, Figure 1 on p. 420,
DOI `10.1214/lnms/1215540316` (26 states; a transcription of the printed
figure). This is the IMS chapter, not Hajek's later journal paper
"Cooling schedules for optimal annealing", Mathematics of Operations
Research 13(2) (1988), pp. 311--329. The states are indexed as
follows: `0`–`6` are the labelled states s1–s7; `7`–`8` are the two
unlabelled states at height 4; `9`–`12` at height 5; `13`–`18` at height 8;
`19`–`23` at height 10; `24`–`25` are the two peaks at height 12. -/
def fig1V : Fin 26 → ℝ := ![1, 1, 1, 5, 5, 4, 8, 4, 4, 5, 5, 5, 5, 8, 8, 8, 8, 8, 8, 10, 10, 10, 10, 10, 12, 12]

/-- Out-neighbours in Hajek's Figure 1: `t ∈ fig1Out s` iff the figure has
an arc from `s` to `t` (51 arcs, 21 of them one-way). -/
def fig1Out : Fin 26 → Finset (Fin 26) :=
  ![{1, 10},
    {0, 7},
    {8, 12},
    {20, 14},
    {11, 15, 16},
    {11},
    {20},
    {0},
    {2},
    {10},
    {7, 9, 13},
    {4, 5},
    {8, 18},
    {19, 9, 10},
    {3},
    {4, 21},
    {23, 11},
    {12},
    {23, 12, 17},
    {24, 7},
    {6, 21, 24},
    {22, 14},
    {25, 15},
    {25, 16, 18},
    {19, 21},
    {22, 23}]

/-- Proposal for Figure 1: uniform on out-neighbours (every state has at
least one). -/
noncomputable def fig1R (s : Fin 26) : PMF (Fin 26) :=
  PMF.ofFinset (fun t => if t ∈ fig1Out s then ((fig1Out s).card : ℝ≥0∞)⁻¹ else 0)
    (fig1Out s)
    (by
      have hne : (fig1Out s).Nonempty := by fin_cases s <;> decide
      rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const]
      rw [nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast hne.card_pos.ne') (by simp))
    (by intro t ht; simp [ht])

theorem arc_iff (s t : Fin 26) : Arc fig1R s t ↔ t ∈ fig1Out s := by
  simp only [Arc, fig1R, PMF.ofFinset_apply]
  by_cases ht : t ∈ fig1Out s
  · rw [if_pos ht]
    exact ⟨fun _ => ht, fun _ => ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)⟩
  · simp [ht]

/-- Every Figure 1 state has height at most 12. -/
theorem fig1V_le12 : ∀ v : Fin 26, fig1V v ≤ 12 := by
  intro v
  fin_cases v <;> norm_num [fig1V]

/-- A chain of out-neighbour steps with all heights `≤ 12` gives a height-12
`ReflTransGen` path (induction on the tail). -/
theorem fig1_chain_rtc12_aux : ∀ (l : List (Fin 26)) (a b : Fin 26),
    List.IsChain (fun s t => t ∈ fig1Out s) (a :: l) →
    (∀ v ∈ a :: l, fig1V v ≤ 12) →
    (a :: l).getLast? = some b →
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ 12) a b := by
  intro l
  induction l with
  | nil =>
      intro a b _ _ hlast
      simp at hlast
      subst hlast
      exact Relation.ReflTransGen.refl
  | cons c l' ih =>
      intro a b hchain h12 hlast
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hmem, h2⟩ := hchain
      have hstep : Relation.ReflTransGen
          (fun s t => Arc fig1R s t ∧ fig1V t ≤ 12) a c :=
        Relation.ReflTransGen.single ⟨(arc_iff a c).mpr hmem, h12 c (by simp)⟩
      have htail : Relation.ReflTransGen
          (fun s t => Arc fig1R s t ∧ fig1V t ≤ 12) c b :=
        ih c b h2 (fun v hv => h12 v (List.mem_cons_of_mem a hv))
          (by rwa [List.getLast?_cons_cons] at hlast)
      exact hstep.trans htail

/-- A concrete vertex list from `a` to `b` with consecutive out-neighbour
steps gives a height-12 `ReflTransGen` path. -/
theorem fig1_chain_rtc12 (p : List (Fin 26)) (a b : Fin 26)
    (hhead : p.head? = some a)
    (hchain : List.IsChain (fun s t => t ∈ fig1Out s) p)
    (h12 : ∀ v ∈ p, fig1V v ≤ 12)
    (hlast : p.getLast? = some b) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ 12) a b := by
  cases p with
  | nil => simp at hhead
  | cons a' l =>
      simp at hhead
      subst hhead
      exact fig1_chain_rtc12_aux l _ _ hchain h12 hlast

/-- Every Figure 1 state is reachable from state `0` at height 12. -/
theorem fig1_rtc12_from0 : ∀ i : Fin 26,
    Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 0 i := by
  intro i
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact fig1_chain_rtc12 [0, 1] 0 1 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23, 18, 12, 8, 2] 0 2 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 14, 3] 0 3 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 15, 4] 0 4 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 15, 4, 11, 5] 0 5 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 14, 3, 20, 6] 0 6 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 1, 7] 0 7 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23, 18, 12, 8] 0 8 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 9] 0 9 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10] 0 10 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 15, 4, 11] 0 11 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23, 18, 12] 0 12 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13] 0 13 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 14] 0 14 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 15] 0 15 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23, 16] 0 16 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23, 18, 17] 0 17 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23, 18] 0 18 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19] 0 19 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 14, 3, 20] 0 20 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21] 0 21 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22] 0 22 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25, 23] 0 23 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24] 0 24 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [0, 10, 13, 19, 24, 21, 22, 25] 0 25 rfl (by decide) (fun v _ => fig1V_le12 v) rfl

/-- State `0` is reachable from every Figure 1 state at height 12. -/
theorem fig1_rtc12_to0 : ∀ j : Fin 26,
    Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) j 0 := by
  intro j
  fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact fig1_chain_rtc12 [1, 0] 1 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [2, 12, 18, 23, 25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 2 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [3, 20, 24, 19, 7, 0] 3 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [4, 15, 21, 14, 3, 20, 24, 19, 7, 0] 4 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [5, 11, 4, 15, 21, 14, 3, 20, 24, 19, 7, 0] 5 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [6, 20, 24, 19, 7, 0] 6 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [7, 0] 7 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [8, 2, 12, 18, 23, 25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 8 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [9, 10, 7, 0] 9 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [10, 7, 0] 10 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [11, 4, 15, 21, 14, 3, 20, 24, 19, 7, 0] 11 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [12, 18, 23, 25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 12 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [13, 10, 7, 0] 13 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [14, 3, 20, 24, 19, 7, 0] 14 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [15, 21, 14, 3, 20, 24, 19, 7, 0] 15 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [16, 11, 4, 15, 21, 14, 3, 20, 24, 19, 7, 0] 16 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [17, 12, 18, 23, 25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 17 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [18, 23, 25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 18 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [19, 7, 0] 19 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [20, 24, 19, 7, 0] 20 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [21, 14, 3, 20, 24, 19, 7, 0] 21 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 22 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [23, 25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 23 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [24, 19, 7, 0] 24 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl
  · exact fig1_chain_rtc12 [25, 22, 15, 21, 14, 3, 20, 24, 19, 7, 0] 25 0 rfl (by decide) (fun v _ => fig1V_le12 v) rfl

/-- Figure 1 is strongly irreducible: every pair connects at height 12 via
state `0`. -/
theorem fig1_stronglyIrreducible : StronglyIrreducible fig1R fig1V := by
  intro i j
  refine ⟨12, fig1V_le12 j, (fig1_rtc12_to0 j).trans (fig1_rtc12_from0 i)⟩

/-- Every Figure 1 height is one of `1, 4, 5, 8, 10, 12`. -/
theorem fig1V_mem : ∀ v : Fin 26,
    fig1V v = 1 ∨ fig1V v = 4 ∨ fig1V v = 5 ∨ fig1V v = 8 ∨ fig1V v = 10 ∨
      fig1V v = 12 := by
  intro v
  fin_cases v <;> norm_num [fig1V]

/-- Every Figure 1 height is at least `1`. -/
theorem fig1V_ge1 : ∀ v : Fin 26, 1 ≤ fig1V v := by
  intro v
  rcases fig1V_mem v with h | h | h | h | h | h <;> linarith

/-- A chain of out-neighbour steps with all heights `≤ E` gives a height-`E`
`ReflTransGen` path (induction on the tail). -/
theorem fig1_chain_rtcE_aux (E : ℝ) : ∀ (l : List (Fin 26)) (a b : Fin 26),
    List.IsChain (fun s t => t ∈ fig1Out s) (a :: l) →
    (∀ v ∈ a :: l, fig1V v ≤ E) →
    (a :: l).getLast? = some b →
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ E) a b := by
  intro l
  induction l with
  | nil =>
      intro a b _ _ hlast
      simp at hlast
      subst hlast
      exact Relation.ReflTransGen.refl
  | cons c l' ih =>
      intro a b hchain hE hlast
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hmem, h2⟩ := hchain
      have hstep : Relation.ReflTransGen
          (fun s t => Arc fig1R s t ∧ fig1V t ≤ E) a c :=
        Relation.ReflTransGen.single ⟨(arc_iff a c).mpr hmem, hE c (by simp)⟩
      have htail : Relation.ReflTransGen
          (fun s t => Arc fig1R s t ∧ fig1V t ≤ E) c b :=
        ih c b h2 (fun v hv => hE v (List.mem_cons_of_mem a hv))
          (by rwa [List.getLast?_cons_cons] at hlast)
      exact hstep.trans htail

/-- A concrete vertex list from `a` to `b` with consecutive out-neighbour
steps gives a height-`E` `ReflTransGen` path. -/
theorem fig1_chain_rtcE (E : ℝ) (p : List (Fin 26)) (a b : Fin 26)
    (hhead : p.head? = some a)
    (hchain : List.IsChain (fun s t => t ∈ fig1Out s) p)
    (hE : ∀ v ∈ p, fig1V v ≤ E)
    (hlast : p.getLast? = some b) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ E) a b := by
  cases p with
  | nil => simp at hhead
  | cons a' l =>
      simp at hhead
      subst hhead
      exact fig1_chain_rtcE_aux E l _ _ hchain hE hlast

/-- A height-`E` path is also a height-`E'` path when every height `≤ E`
is also `≤ E'`. -/
theorem fig1_rtc_mono {E E' : ℝ} {a b : Fin 26}
    (h : ∀ v, fig1V v ≤ E → fig1V v ≤ E')
    (hrtc : Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ E) a b) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ E') a b := by
  induction hrtc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, h _ hbc.2⟩

/-- At height 12, reachability is symmetric: every pair connects via `0`. -/
theorem fig1symm12 (i j : Fin 26) (_ : ReachableAt fig1R fig1V 12 j i) :
    ReachableAt fig1R fig1V 12 i j :=
  ⟨fig1V_le12 i, (fig1_rtc12_to0 i).trans (fig1_rtc12_from0 j)⟩

/-- Above height 12, reachability is the same as at height 12. -/
theorem fig1_iff12 {E : ℝ} (h : 12 ≤ E) (a b : Fin 26) :
    ReachableAt fig1R fig1V E a b ↔ ReachableAt fig1R fig1V 12 a b := by
  constructor
  · intro hr
    obtain ⟨_, hrtc⟩ := hr
    exact ⟨fig1V_le12 a, fig1_rtc_mono (fun v _ => fig1V_le12 v) hrtc⟩
  · intro hr
    obtain ⟨_, hrtc⟩ := hr
    exact ⟨le_trans (fig1V_le12 a) h, fig1_rtc_mono (fun v hv => le_trans hv h) hrtc⟩

/-- Level-1 block representative: `1` maps to `0`, everything else is fixed. -/
def blockOf1 : Fin 26 → Fin 26 := fun v => if v = 1 then 0 else v

/-- States of height at most `1` are exactly `0, 1, 2`. -/
theorem fig1V_le1_mem (v : Fin 26) (hv : fig1V v ≤ 1) :
    v = 0 ∨ v = 1 ∨ v = 2 := by
  revert hv
  fin_cases v <;> norm_num [fig1V]

/-- A height-1 arc stays within a level-1 block. -/
theorem fig1_blockOf1_step {a b : Fin 26} (hab : Arc fig1R a b)
    (ha : fig1V a ≤ 1) (hb : fig1V b ≤ 1) : blockOf1 a = blockOf1 b := by
  have ha3 := fig1V_le1_mem a ha
  have hb3 := fig1V_le1_mem b hb
  rw [arc_iff] at hab
  rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl <;>
    revert hab <;> decide

/-- A height-1 path stays within a level-1 block, and its endpoint has
height at most `1`. -/
theorem fig1_blockOf1_rtc (j i : Fin 26) (hj : fig1V j ≤ 1)
    (hrtc : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 1) j i) :
    blockOf1 j = blockOf1 i ∧ fig1V i ≤ 1 := by
  induction hrtc with
  | refl => exact ⟨rfl, hj⟩
  | tail _ hstep ih =>
      obtain ⟨hblk, hle⟩ := ih
      exact ⟨hblk.trans (fig1_blockOf1_step hstep.1 hle hstep.2), hstep.2⟩

/-- Within a level-1 block, every state reaches every other at height 1. -/
theorem fig1_reach1_of_block (j i : Fin 26) (hj : fig1V j ≤ 1)
    (hblk : blockOf1 j = blockOf1 i) (hi : fig1V i ≤ 1) :
    ReachableAt fig1R fig1V 1 j i := by
  have hj3 := fig1V_le1_mem j hj
  have hi3 := fig1V_le1_mem i hi
  rcases hj3 with rfl | rfl | rfl <;> rcases hi3 with rfl | rfl | rfl
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · refine ⟨hj, fig1_chain_rtcE 1 [0, 1] 0 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 1 [1, 0] 1 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩

/-- At height 1, reachability is symmetric. -/
theorem fig1symm1 (i j : Fin 26) (h : ReachableAt fig1R fig1V 1 j i) :
    ReachableAt fig1R fig1V 1 i j := by
  obtain ⟨hj, hrtc⟩ := h
  obtain ⟨hblk, hi⟩ := fig1_blockOf1_rtc j i hj hrtc
  exact fig1_reach1_of_block i j hi hblk.symm hj

/-- Below height 4, a height bound of `E` is as good as a bound of `1`. -/
theorem fig1V_le_of_le_E {E : ℝ} (h4 : E < 4) {v : Fin 26} (hv : fig1V v ≤ E) :
    fig1V v ≤ 1 := by
  rcases fig1V_mem v with h | h | h | h | h | h <;> linarith

/-- Between heights 1 and 4, reachability is the same as at height 1. -/
theorem fig1_iff1 {E : ℝ} (h1 : 1 ≤ E) (h4 : E < 4) (a b : Fin 26) :
    ReachableAt fig1R fig1V E a b ↔ ReachableAt fig1R fig1V 1 a b := by
  constructor
  · intro hr
    obtain ⟨hea, hrtc⟩ := hr
    exact ⟨fig1V_le_of_le_E h4 hea,
      fig1_rtc_mono (fun v hv => fig1V_le_of_le_E h4 hv) hrtc⟩
  · intro hr
    obtain ⟨h1a, hrtc⟩ := hr
    exact ⟨le_trans h1a h1, fig1_rtc_mono (fun v hv => le_trans hv h1) hrtc⟩

/-- Level-4 block representative: `1, 7` map to `0`, `8` maps to `2`. -/
def blockOf4 : Fin 26 → Fin 26 :=
  fun v => if v = 1 then 0 else if v = 7 then 0 else if v = 8 then 2 else v

/-- States of height at most `4` are exactly `0, 1, 2, 5, 7, 8`. -/
theorem fig1V_le4_mem (v : Fin 26) (hv : fig1V v ≤ 4) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 5 ∨ v = 7 ∨ v = 8 := by
  revert hv
  fin_cases v <;> norm_num [fig1V]

/-- A height-4 arc stays within a level-4 block. -/
theorem fig1_blockOf4_step {a b : Fin 26} (hab : Arc fig1R a b)
    (ha : fig1V a ≤ 4) (hb : fig1V b ≤ 4) : blockOf4 a = blockOf4 b := by
  have ha6 := fig1V_le4_mem a ha
  have hb6 := fig1V_le4_mem b hb
  rw [arc_iff] at hab
  rcases ha6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hab <;> decide

/-- A height-4 path stays within a level-4 block, and its endpoint has
height at most `4`. -/
theorem fig1_blockOf4_rtc (j i : Fin 26) (hj : fig1V j ≤ 4)
    (hrtc : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 4) j i) :
    blockOf4 j = blockOf4 i ∧ fig1V i ≤ 4 := by
  induction hrtc with
  | refl => exact ⟨rfl, hj⟩
  | tail _ hstep ih =>
      obtain ⟨hblk, hle⟩ := ih
      exact ⟨hblk.trans (fig1_blockOf4_step hstep.1 hle hstep.2), hstep.2⟩

/-- Within a level-4 block, every state reaches every other at height 4. -/
theorem fig1_reach4_of_block (j i : Fin 26) (hj : fig1V j ≤ 4)
    (hblk : blockOf4 j = blockOf4 i) (hi : fig1V i ≤ 4) :
    ReachableAt fig1R fig1V 4 j i := by
  have hj6 := fig1V_le4_mem j hj
  have hi6 := fig1V_le4_mem i hi
  rcases hj6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · refine ⟨hj, fig1_chain_rtcE 4 [0, 1] 0 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 4 [0, 1, 7] 0 7 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 4 [1, 0] 1 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 4 [1, 7] 1 7 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 4 [2, 8] 2 8 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 4 [7, 0] 7 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 4 [7, 0, 1] 7 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 4 [8, 2] 8 2 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩

/-- At height 4, reachability is symmetric. -/
theorem fig1symm4 (i j : Fin 26) (h : ReachableAt fig1R fig1V 4 j i) :
    ReachableAt fig1R fig1V 4 i j := by
  obtain ⟨hj, hrtc⟩ := h
  obtain ⟨hblk, hi⟩ := fig1_blockOf4_rtc j i hj hrtc
  exact fig1_reach4_of_block i j hi hblk.symm hj

/-- Below height 5, a height bound of `E` is as good as a bound of `4`. -/
theorem fig1V_le4_of_le_E {E : ℝ} (h5 : E < 5) {v : Fin 26} (hv : fig1V v ≤ E) :
    fig1V v ≤ 4 := by
  rcases fig1V_mem v with h | h | h | h | h | h <;> linarith

/-- Between heights 4 and 5, reachability is the same as at height 4. -/
theorem fig1_iff4 {E : ℝ} (h4 : 4 ≤ E) (h5 : E < 5) (a b : Fin 26) :
    ReachableAt fig1R fig1V E a b ↔ ReachableAt fig1R fig1V 4 a b := by
  constructor
  · intro hr
    obtain ⟨hea, hrtc⟩ := hr
    exact ⟨fig1V_le4_of_le_E h5 hea,
      fig1_rtc_mono (fun v hv => fig1V_le4_of_le_E h5 hv) hrtc⟩
  · intro hr
    obtain ⟨h4a, hrtc⟩ := hr
    exact ⟨le_trans h4a h4, fig1_rtc_mono (fun v hv => le_trans hv h4) hrtc⟩

/-- Level-5 block representative: `1, 7, 9, 10` map to `0`, `8, 12` map
to `2`, `5, 11` map to `4`. -/
def blockOf5 : Fin 26 → Fin 26 :=
  fun v => if v = 1 then 0 else if v = 7 then 0 else if v = 9 then 0 else
    if v = 10 then 0 else if v = 8 then 2 else if v = 12 then 2 else
    if v = 5 then 4 else if v = 11 then 4 else v

/-- States of height at most `5` are exactly
`0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12`. -/
theorem fig1V_le5_mem (v : Fin 26) (hv : fig1V v ≤ 5) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨
      v = 10 ∨ v = 11 ∨ v = 12 := by
  revert hv
  fin_cases v <;> norm_num [fig1V]

/-- A height-5 arc stays within a level-5 block. -/
theorem fig1_blockOf5_step {a b : Fin 26} (hab : Arc fig1R a b)
    (ha : fig1V a ≤ 5) (hb : fig1V b ≤ 5) : blockOf5 a = blockOf5 b := by
  have ha12 := fig1V_le5_mem a ha
  have hb12 := fig1V_le5_mem b hb
  rw [arc_iff] at hab
  rcases ha12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hab <;> decide

/-- A height-5 path stays within a level-5 block, and its endpoint has
height at most `5`. -/
theorem fig1_blockOf5_rtc (j i : Fin 26) (hj : fig1V j ≤ 5)
    (hrtc : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 5) j i) :
    blockOf5 j = blockOf5 i ∧ fig1V i ≤ 5 := by
  induction hrtc with
  | refl => exact ⟨rfl, hj⟩
  | tail _ hstep ih =>
      obtain ⟨hblk, hle⟩ := ih
      exact ⟨hblk.trans (fig1_blockOf5_step hstep.1 hle hstep.2), hstep.2⟩

/-- Within a level-5 block, every state reaches every other at height 5. -/
theorem fig1_reach5_of_block (j i : Fin 26) (hj : fig1V j ≤ 5)
    (hblk : blockOf5 j = blockOf5 i) (hi : fig1V i ≤ 5) :
    ReachableAt fig1R fig1V 5 j i := by
  have hj12 := fig1V_le5_mem j hj
  have hi12 := fig1V_le5_mem i hi
  rcases hj12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hi12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- j = 0
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · refine ⟨hj, fig1_chain_rtcE 5 [0, 1] 0 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [0, 1, 7] 0 7 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [0, 10, 9] 0 9 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [0, 10] 0 10 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  -- j = 1
  · refine ⟨hj, fig1_chain_rtcE 5 [1, 0] 1 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [1, 7] 1 7 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [1, 0, 10, 9] 1 9 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [1, 0, 10] 1 10 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  -- j = 2
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [2, 8] 2 8 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [2, 12] 2 12 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  -- j = 3
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  -- j = 4
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · refine ⟨hj, fig1_chain_rtcE 5 [4, 11, 5] 4 5 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [4, 11] 4 11 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  -- j = 5
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [5, 11, 4] 5 4 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [5, 11] 5 11 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  -- j = 7
  · refine ⟨hj, fig1_chain_rtcE 5 [7, 0] 7 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [7, 0, 1] 7 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [7, 0, 10, 9] 7 9 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [7, 0, 10] 7 10 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  -- j = 8
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [8, 2] 8 2 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [8, 2, 12] 8 12 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  -- j = 9
  · refine ⟨hj, fig1_chain_rtcE 5 [9, 10, 7, 0] 9 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [9, 10, 7, 0, 1] 9 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [9, 10, 7] 9 7 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · refine ⟨hj, fig1_chain_rtcE 5 [9, 10] 9 10 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  -- j = 10
  · refine ⟨hj, fig1_chain_rtcE 5 [10, 7, 0] 10 0 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [10, 7, 0, 1] 10 1 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [10, 7] 10 7 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [10, 9] 10 9 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  -- j = 11
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [11, 4] 11 4 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · refine ⟨hj, fig1_chain_rtcE 5 [11, 5] 11 5 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩
  · exact absurd hblk (by decide)
  -- j = 12
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [12, 8, 2] 12 2 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · refine ⟨hj, fig1_chain_rtcE 5 [12, 8] 12 8 rfl (by decide) ?_ rfl⟩
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> norm_num [fig1V]
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact absurd hblk (by decide)
  · exact ⟨hj, Relation.ReflTransGen.refl⟩

/-- At height 5, reachability is symmetric. -/
theorem fig1symm5 (i j : Fin 26) (h : ReachableAt fig1R fig1V 5 j i) :
    ReachableAt fig1R fig1V 5 i j := by
  obtain ⟨hj, hrtc⟩ := h
  obtain ⟨hblk, hi⟩ := fig1_blockOf5_rtc j i hj hrtc
  exact fig1_reach5_of_block i j hi hblk.symm hj

/-- Below height 8, a height bound of `E` is as good as a bound of `5`. -/
theorem fig1V_le5_of_le_E {E : ℝ} (h8 : E < 8) {v : Fin 26} (hv : fig1V v ≤ E) :
    fig1V v ≤ 5 := by
  rcases fig1V_mem v with h | h | h | h | h | h <;> linarith

/-- Between heights 5 and 8, reachability is the same as at height 5. -/
theorem fig1_iff5 {E : ℝ} (h5 : 5 ≤ E) (h8 : E < 8) (a b : Fin 26) :
    ReachableAt fig1R fig1V E a b ↔ ReachableAt fig1R fig1V 5 a b := by
  constructor
  · intro hr
    obtain ⟨hea, hrtc⟩ := hr
    exact ⟨fig1V_le5_of_le_E h8 hea,
      fig1_rtc_mono (fun v hv => fig1V_le5_of_le_E h8 hv) hrtc⟩
  · intro hr
    obtain ⟨h5a, hrtc⟩ := hr
    exact ⟨le_trans h5a h5, fig1_rtc_mono (fun v hv => le_trans hv h5) hrtc⟩

/-- Level-8 block representative. -/
def blockOf8 : Fin 26 → Fin 26 :=
  fun v => if v = 1 then 0 else if v = 7 then 0 else if v = 9 then 0 else
    if v = 10 then 0 else if v = 13 then 0 else if v = 8 then 2 else if v = 12 then 2 else
    if v = 17 then 2 else if v = 18 then 2 else if v = 14 then 3 else if v = 5 then 4 else
    if v = 11 then 4 else if v = 15 then 4 else if v = 16 then 4 else v

/-- States of height at most `8` are exactly `0, ..., 18`. -/
theorem fig1V_le8_mem (v : Fin 26) (hv : fig1V v ≤ 8) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨
      v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 17 ∨ v = 18 := by
  revert hv
  fin_cases v <;> norm_num [fig1V]

/-- A height-8 arc stays within a level-8 block. -/
theorem fig1_blockOf8_step {a b : Fin 26} (hab : Arc fig1R a b)
    (ha : fig1V a ≤ 8) (hb : fig1V b ≤ 8) : blockOf8 a = blockOf8 b := by
  have ha19 := fig1V_le8_mem a ha
  have hb19 := fig1V_le8_mem b hb
  rw [arc_iff] at hab
  rcases ha19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hab <;> decide

/-- A height-8 path stays within a block; endpoint height ≤ `8`. -/
theorem fig1_blockOf8_rtc (j i : Fin 26) (hj : fig1V j ≤ 8)
    (hrtc : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 8) j i) :
    blockOf8 j = blockOf8 i ∧ fig1V i ≤ 8 := by
  induction hrtc with
  | refl => exact ⟨rfl, hj⟩
  | tail _ hstep ih =>
      obtain ⟨hblk, hle⟩ := ih
      exact ⟨hblk.trans (fig1_blockOf8_step hstep.1 hle hstep.2), hstep.2⟩

/-- Every level-8 state reaches its block hub at height 8. -/
theorem fig1_toHub8 (v : Fin 26) (hv : fig1V v ≤ 8) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ 8) v (blockOf8 v) := by
  have h19 := fig1V_le8_mem v hv
  rcases h19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 8 [1, 0] 1 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 8 [5, 11, 4] 5 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 8 [7, 0] 7 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [8, 2] 8 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [9, 10, 7, 0] 9 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [10, 7, 0] 10 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [11, 4] 11 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [12, 8, 2] 12 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [13, 10, 7, 0] 13 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [14, 3] 14 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [15, 4] 15 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [16, 11, 4] 16 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [17, 12, 8, 2] 17 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [18, 12, 8, 2] 18 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]

/-- Every level-8 block hub reaches its states at height 8. -/
theorem fig1_fromHub8 (v : Fin 26) (hv : fig1V v ≤ 8) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ 8) (blockOf8 v) v := by
  have h19 := fig1V_le8_mem v hv
  rcases h19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 8 [0, 1] _ 1 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 8 [4, 11, 5] _ 5 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 8 [0, 1, 7] _ 7 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [2, 8] _ 8 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [0, 10, 9] _ 9 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [0, 10] _ 10 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [4, 11] _ 11 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [2, 12] _ 12 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [0, 10, 13] _ 13 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [3, 14] _ 14 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [4, 15] _ 15 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [4, 16] _ 16 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [2, 12, 18, 17] _ 17 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 8 [2, 12, 18] _ 18 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]

/-- Within a level-8 block, every state reaches every other at height 8. -/
theorem fig1_reach8_of_block (j i : Fin 26) (hj : fig1V j ≤ 8)
    (hblk : blockOf8 j = blockOf8 i) (hi : fig1V i ≤ 8) :
    ReachableAt fig1R fig1V 8 j i := by
  have h1 := fig1_toHub8 j hj
  have h2 := fig1_fromHub8 i hi
  rw [hblk] at h1
  exact ⟨hj, h1.trans h2⟩

/-- At height 8, reachability is symmetric. -/
theorem fig1symm8 (i j : Fin 26) (h : ReachableAt fig1R fig1V 8 j i) :
    ReachableAt fig1R fig1V 8 i j := by
  obtain ⟨hj, hrtc⟩ := h
  obtain ⟨hblk, hi⟩ := fig1_blockOf8_rtc j i hj hrtc
  exact fig1_reach8_of_block i j hi hblk.symm hj

/-- Below height 10, a height bound of `E` is as good as a bound of `8`. -/
theorem fig1V_le8_of_le_E {E : ℝ} (h10 : E < 10) {v : Fin 26} (hv : fig1V v ≤ E) :
    fig1V v ≤ 8 := by
  rcases fig1V_mem v with h | h | h | h | h | h <;> linarith

/-- Between heights 8 and 10, reachability is the same as at height 8. -/
theorem fig1_iff8 {E : ℝ} (h8 : 8 ≤ E) (h10 : E < 10) (a b : Fin 26) :
    ReachableAt fig1R fig1V E a b ↔ ReachableAt fig1R fig1V 8 a b := by
  constructor
  · intro hr
    obtain ⟨hea, hrtc⟩ := hr
    exact ⟨fig1V_le8_of_le_E h10 hea,
      fig1_rtc_mono (fun v hv => fig1V_le8_of_le_E h10 hv) hrtc⟩
  · intro hr
    obtain ⟨h8a, hrtc⟩ := hr
    exact ⟨le_trans h8a h8, fig1_rtc_mono (fun v hv => le_trans hv h8) hrtc⟩

/-- Level-10 block representative. -/
def blockOf10 : Fin 26 → Fin 26 :=
  fun v => if v = 1 then 0 else if v = 7 then 0 else if v = 9 then 0 else
    if v = 10 then 0 else if v = 13 then 0 else if v = 19 then 0 else if v = 3 then 2 else
    if v = 4 then 2 else if v = 5 then 2 else if v = 6 then 2 else if v = 8 then 2 else
    if v = 11 then 2 else if v = 12 then 2 else if v = 14 then 2 else if v = 15 then 2 else
    if v = 16 then 2 else if v = 17 then 2 else if v = 18 then 2 else if v = 20 then 2 else
    if v = 21 then 2 else if v = 22 then 2 else if v = 23 then 2 else v

/-- States of height at most `10` are exactly `0, ..., 23`. -/
theorem fig1V_le10_mem (v : Fin 26) (hv : fig1V v ≤ 10) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨
      v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 ∨ v = 16 ∨ v = 17 ∨ v = 18 ∨ v = 19 ∨ v = 20 ∨ v = 21 ∨
      v = 22 ∨ v = 23 := by
  revert hv
  fin_cases v <;> norm_num [fig1V]

/-- A height-10 arc stays within a level-10 block. -/
theorem fig1_blockOf10_step {a b : Fin 26} (hab : Arc fig1R a b)
    (ha : fig1V a ≤ 10) (hb : fig1V b ≤ 10) : blockOf10 a = blockOf10 b := by
  have ha24 := fig1V_le10_mem a ha
  have hb24 := fig1V_le10_mem b hb
  rw [arc_iff] at hab
  rcases ha24 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb24 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hab <;> decide

/-- A height-10 path stays within a block; endpoint height ≤ `10`. -/
theorem fig1_blockOf10_rtc (j i : Fin 26) (hj : fig1V j ≤ 10)
    (hrtc : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 10) j i) :
    blockOf10 j = blockOf10 i ∧ fig1V i ≤ 10 := by
  induction hrtc with
  | refl => exact ⟨rfl, hj⟩
  | tail _ hstep ih =>
      obtain ⟨hblk, hle⟩ := ih
      exact ⟨hblk.trans (fig1_blockOf10_step hstep.1 hle hstep.2), hstep.2⟩

/-- Every level-10 state reaches its block hub at height 10. -/
theorem fig1_toHub10 (v : Fin 26) (hv : fig1V v ≤ 10) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ 10) v (blockOf10 v) := by
  have h24 := fig1V_le10_mem v hv
  rcases h24 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 10 [1, 0] 1 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 10 [3, 20, 21, 22, 15, 4, 16, 23, 18, 12, 8, 2] 3 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [4, 16, 23, 18, 12, 8, 2] 4 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [5, 11, 4, 16, 23, 18, 12, 8, 2] 5 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [6, 20, 21, 22, 15, 4, 16, 23, 18, 12, 8, 2] 6 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [7, 0] 7 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [8, 2] 8 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [9, 10, 7, 0] 9 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [10, 7, 0] 10 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [11, 4, 16, 23, 18, 12, 8, 2] 11 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [12, 8, 2] 12 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [13, 10, 7, 0] 13 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [14, 3, 20, 21, 22, 15, 4, 16, 23, 18, 12, 8, 2] 14 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [15, 4, 16, 23, 18, 12, 8, 2] 15 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [16, 23, 18, 12, 8, 2] 16 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [17, 12, 8, 2] 17 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [18, 12, 8, 2] 18 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [19, 7, 0] 19 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [20, 21, 22, 15, 4, 16, 23, 18, 12, 8, 2] 20 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [21, 22, 15, 4, 16, 23, 18, 12, 8, 2] 21 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [22, 15, 4, 16, 23, 18, 12, 8, 2] 22 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [23, 18, 12, 8, 2] 23 _ rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]

/-- Every level-10 block hub reaches its states at height 10. -/
theorem fig1_fromHub10 (v : Fin 26) (hv : fig1V v ≤ 10) :
    Relation.ReflTransGen (fun s t => Arc fig1R s t ∧ fig1V t ≤ 10) (blockOf10 v) v := by
  have h24 := fig1V_le10_mem v hv
  rcases h24 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 10 [0, 1] _ 1 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · exact Relation.ReflTransGen.refl
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15, 21, 14, 3] _ 3 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4] _ 4 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 5] _ 5 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15, 21, 14, 3, 20, 6] _ 6 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [0, 1, 7] _ 7 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 8] _ 8 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [0, 10, 9] _ 9 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [0, 10] _ 10 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11] _ 11 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12] _ 12 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [0, 10, 13] _ 13 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15, 21, 14] _ 14 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15] _ 15 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16] _ 16 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 17] _ 17 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18] _ 18 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [0, 10, 13, 19] _ 19 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15, 21, 14, 3, 20] _ 20 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15, 21] _ 21 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23, 16, 11, 4, 15, 21, 22] _ 22 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [fig1V]
  · refine fig1_chain_rtcE 10 [2, 12, 18, 23] _ 23 rfl (by decide) ?_ rfl
    intro w hw; simp at hw; rcases hw with rfl | rfl | rfl | rfl <;> norm_num [fig1V]

/-- Within a level-10 block, every state reaches every other at height 10. -/
theorem fig1_reach10_of_block (j i : Fin 26) (hj : fig1V j ≤ 10)
    (hblk : blockOf10 j = blockOf10 i) (hi : fig1V i ≤ 10) :
    ReachableAt fig1R fig1V 10 j i := by
  have h1 := fig1_toHub10 j hj
  have h2 := fig1_fromHub10 i hi
  rw [hblk] at h1
  exact ⟨hj, h1.trans h2⟩

/-- At height 10, reachability is symmetric. -/
theorem fig1symm10 (i j : Fin 26) (h : ReachableAt fig1R fig1V 10 j i) :
    ReachableAt fig1R fig1V 10 i j := by
  obtain ⟨hj, hrtc⟩ := h
  obtain ⟨hblk, hi⟩ := fig1_blockOf10_rtc j i hj hrtc
  exact fig1_reach10_of_block i j hi hblk.symm hj

/-- Below height 12, a height bound of `E` is as good as a bound of `10`. -/
theorem fig1V_le10_of_le_E {E : ℝ} (h12 : E < 12) {v : Fin 26} (hv : fig1V v ≤ E) :
    fig1V v ≤ 10 := by
  rcases fig1V_mem v with h | h | h | h | h | h <;> linarith

/-- Between heights 10 and 12, reachability is the same as at height 10. -/
theorem fig1_iff10 {E : ℝ} (h10 : 10 ≤ E) (h12 : E < 12) (a b : Fin 26) :
    ReachableAt fig1R fig1V E a b ↔ ReachableAt fig1R fig1V 10 a b := by
  constructor
  · intro hr
    obtain ⟨hea, hrtc⟩ := hr
    exact ⟨fig1V_le10_of_le_E h12 hea,
      fig1_rtc_mono (fun v hv => fig1V_le10_of_le_E h12 hv) hrtc⟩
  · intro hr
    obtain ⟨h10a, hrtc⟩ := hr
    exact ⟨le_trans h10a h10, fig1_rtc_mono (fun v hv => le_trans hv h10) hrtc⟩

/-- Figure 1 is weakly reversible. -/
theorem fig1_weaklyReversible : WeaklyReversible fig1R fig1V := by
  intro E i j
  rcases lt_or_ge E 1 with hE1 | hE1
  · constructor
    · intro hr
      obtain ⟨hj, _⟩ := hr
      have h1j := fig1V_ge1 j
      linarith
    · intro hr
      obtain ⟨hi, _⟩ := hr
      have h1i := fig1V_ge1 i
      linarith
  rcases lt_or_ge E 4 with hE4 | hE4
  · rw [fig1_iff1 hE1 hE4 j i, fig1_iff1 hE1 hE4 i j]
    exact ⟨fig1symm1 i j, fig1symm1 j i⟩
  rcases lt_or_ge E 5 with hE5 | hE5
  · rw [fig1_iff4 hE4 hE5 j i, fig1_iff4 hE4 hE5 i j]
    exact ⟨fig1symm4 i j, fig1symm4 j i⟩
  rcases lt_or_ge E 8 with hE8 | hE8
  · rw [fig1_iff5 hE5 hE8 j i, fig1_iff5 hE5 hE8 i j]
    exact ⟨fig1symm5 i j, fig1symm5 j i⟩
  rcases lt_or_ge E 10 with hE10 | hE10
  · rw [fig1_iff8 hE8 hE10 j i, fig1_iff8 hE8 hE10 i j]
    exact ⟨fig1symm8 i j, fig1symm8 j i⟩
  rcases lt_or_ge E 12 with hE12 | hE12
  · rw [fig1_iff10 hE10 hE12 j i, fig1_iff10 hE10 hE12 i j]
    exact ⟨fig1symm10 i j, fig1symm10 j i⟩
  rw [fig1_iff12 hE12 j i, fig1_iff12 hE12 i j]
  exact ⟨fig1symm12 i j, fig1symm12 j i⟩

/-- Figure 1 satisfies Hajek's standing assumptions SI and WR. -/
theorem fig1_si_wr : StronglyIrreducible fig1R fig1V ∧
    WeaklyReversible fig1R fig1V := by
  exact ⟨fig1_stronglyIrreducible, fig1_weaklyReversible⟩

/-- The global minima of Figure 1 are exactly s1, s2 and s3. -/
theorem fig1_globalMinSet : globalMinSet fig1V = {0, 1, 2} := by
  have hge : ∀ t, (1 : ℝ) ≤ fig1V t := by
    intro t
    fin_cases t <;> norm_num [fig1V]
  have heq : ∀ s, fig1V s = 1 ↔ s = 0 ∨ s = 1 ∨ s = 2 := by
    intro s
    fin_cases s <;> norm_num [fig1V]
  have hv0 : fig1V 0 = 1 := by norm_num [fig1V]
  have hv1 : fig1V 1 = 1 := by norm_num [fig1V]
  have hv2 : fig1V 2 = 1 := by norm_num [fig1V]
  ext s
  simp only [globalMinSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hle : fig1V s ≤ 1 := by rw [← hv0]; exact h 0
    exact (heq s).mp (le_antisymm hle (hge s))
  · intro h
    rcases h with rfl | rfl | rfl
    · intro t
      rw [hv0]
      exact hge t
    · intro t
      rw [hv1]
      exact hge t
    · intro t
      rw [hv2]
      exact hge t

/-- A one-arc downhill witness shows `s` is not a local minimum. -/
theorem fig1_nlocalMin_of_witness (s t : Fin 26) (hlt : fig1V t < fig1V s)
    (harc : Arc fig1R s t) (hle : fig1V t ≤ fig1V s) :
    ¬ IsHajekLocalMin fig1R fig1V s := by
  intro h
  have h0 := h t hlt
  apply h0
  exact ⟨le_rfl, Relation.ReflTransGen.single ⟨harc, hle⟩⟩

/-- A two-arc witness through `m` shows `s` is not a local minimum. -/
theorem fig1_nlocalMin_of_chain2 (s m t : Fin 26) (hlt : fig1V t < fig1V s)
    (hm1 : m ∈ fig1Out s) (hm2 : t ∈ fig1Out m)
    (hmE : fig1V m ≤ fig1V s) (htE : fig1V t ≤ fig1V s) :
    ¬ IsHajekLocalMin fig1R fig1V s := by
  intro h
  have h0 := h t hlt
  apply h0
  refine ⟨le_rfl, ?_⟩
  have e1 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ fig1V s) s m :=
    Relation.ReflTransGen.single ⟨(arc_iff s m).mpr hm1, hmE⟩
  have e2 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ fig1V s) m t :=
    Relation.ReflTransGen.single ⟨(arc_iff m t).mpr hm2, htE⟩
  exact e1.trans e2

theorem fig1_nlocalMin4 : ¬ IsHajekLocalMin fig1R fig1V 4 :=
  fig1_nlocalMin_of_chain2 4 11 5 (by norm_num [fig1V]) (by decide) (by decide)
    (by norm_num [fig1V]) (by norm_num [fig1V])

theorem fig1_nlocalMin7 : ¬ IsHajekLocalMin fig1R fig1V 7 :=
  fig1_nlocalMin_of_witness 7 0 (by norm_num [fig1V])
    ((arc_iff 7 0).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin8 : ¬ IsHajekLocalMin fig1R fig1V 8 :=
  fig1_nlocalMin_of_witness 8 2 (by norm_num [fig1V])
    ((arc_iff 8 2).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin9 : ¬ IsHajekLocalMin fig1R fig1V 9 :=
  fig1_nlocalMin_of_chain2 9 10 7 (by norm_num [fig1V]) (by decide) (by decide)
    (by norm_num [fig1V]) (by norm_num [fig1V])

theorem fig1_nlocalMin10 : ¬ IsHajekLocalMin fig1R fig1V 10 :=
  fig1_nlocalMin_of_witness 10 7 (by norm_num [fig1V])
    ((arc_iff 10 7).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin11 : ¬ IsHajekLocalMin fig1R fig1V 11 :=
  fig1_nlocalMin_of_witness 11 5 (by norm_num [fig1V])
    ((arc_iff 11 5).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin12 : ¬ IsHajekLocalMin fig1R fig1V 12 :=
  fig1_nlocalMin_of_witness 12 8 (by norm_num [fig1V])
    ((arc_iff 12 8).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin13 : ¬ IsHajekLocalMin fig1R fig1V 13 :=
  fig1_nlocalMin_of_witness 13 9 (by norm_num [fig1V])
    ((arc_iff 13 9).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin14 : ¬ IsHajekLocalMin fig1R fig1V 14 :=
  fig1_nlocalMin_of_witness 14 3 (by norm_num [fig1V])
    ((arc_iff 14 3).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin15 : ¬ IsHajekLocalMin fig1R fig1V 15 :=
  fig1_nlocalMin_of_witness 15 4 (by norm_num [fig1V])
    ((arc_iff 15 4).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin16 : ¬ IsHajekLocalMin fig1R fig1V 16 :=
  fig1_nlocalMin_of_witness 16 11 (by norm_num [fig1V])
    ((arc_iff 16 11).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin17 : ¬ IsHajekLocalMin fig1R fig1V 17 :=
  fig1_nlocalMin_of_witness 17 12 (by norm_num [fig1V])
    ((arc_iff 17 12).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin18 : ¬ IsHajekLocalMin fig1R fig1V 18 :=
  fig1_nlocalMin_of_witness 18 12 (by norm_num [fig1V])
    ((arc_iff 18 12).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin19 : ¬ IsHajekLocalMin fig1R fig1V 19 :=
  fig1_nlocalMin_of_witness 19 7 (by norm_num [fig1V])
    ((arc_iff 19 7).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin20 : ¬ IsHajekLocalMin fig1R fig1V 20 :=
  fig1_nlocalMin_of_witness 20 6 (by norm_num [fig1V])
    ((arc_iff 20 6).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin21 : ¬ IsHajekLocalMin fig1R fig1V 21 :=
  fig1_nlocalMin_of_witness 21 14 (by norm_num [fig1V])
    ((arc_iff 21 14).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin22 : ¬ IsHajekLocalMin fig1R fig1V 22 :=
  fig1_nlocalMin_of_witness 22 15 (by norm_num [fig1V])
    ((arc_iff 22 15).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin23 : ¬ IsHajekLocalMin fig1R fig1V 23 :=
  fig1_nlocalMin_of_witness 23 16 (by norm_num [fig1V])
    ((arc_iff 23 16).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin24 : ¬ IsHajekLocalMin fig1R fig1V 24 :=
  fig1_nlocalMin_of_witness 24 19 (by norm_num [fig1V])
    ((arc_iff 24 19).mpr (by decide)) (by norm_num [fig1V])

theorem fig1_nlocalMin25 : ¬ IsHajekLocalMin fig1R fig1V 25 :=
  fig1_nlocalMin_of_witness 25 22 (by norm_num [fig1V])
    ((arc_iff 25 22).mpr (by decide)) (by norm_num [fig1V])

/-- A height-1 state is a local minimum (nothing is lower). -/
theorem fig1_localMin_of_ge1 (s : Fin 26) (hs : fig1V s = 1) :
    IsHajekLocalMin fig1R fig1V s := by
  intro t hlt _
  rw [hs] at hlt
  have h1 := fig1V_ge1 t
  linarith

/-- `3` is a local minimum (its level-5 block is the singleton `{3}`). -/
theorem fig1_localMin_mem3 : IsHajekLocalMin fig1R fig1V 3 := by
  intro t hlt hreach
  have hV : fig1V (3 : Fin 26) = 5 := by norm_num [fig1V]
  rw [hV] at hreach
  obtain ⟨-, hrtc⟩ := hreach
  obtain ⟨hblk, ht⟩ := fig1_blockOf5_rtc 3 t (by norm_num [fig1V]) hrtc
  have ht12 := fig1V_le5_mem t ht
  rcases ht12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hblk (by decide)
      | exact lt_irrefl _ hlt

/-- `5` is a local minimum (its level-4 block is the singleton `{5}`). -/
theorem fig1_localMin_mem5 : IsHajekLocalMin fig1R fig1V 5 := by
  intro t hlt hreach
  have hV : fig1V (5 : Fin 26) = 4 := by norm_num [fig1V]
  rw [hV] at hreach
  obtain ⟨-, hrtc⟩ := hreach
  obtain ⟨hblk, ht⟩ := fig1_blockOf4_rtc 5 t (by norm_num [fig1V]) hrtc
  have ht6 := fig1V_le4_mem t ht
  rcases ht6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hblk (by decide)
      | exact lt_irrefl _ hlt

/-- `6` is a local minimum (its level-8 block is the singleton `{6}`). -/
theorem fig1_localMin_mem6 : IsHajekLocalMin fig1R fig1V 6 := by
  intro t hlt hreach
  have hV : fig1V (6 : Fin 26) = 8 := by norm_num [fig1V]
  rw [hV] at hreach
  obtain ⟨-, hrtc⟩ := hreach
  obtain ⟨hblk, ht⟩ := fig1_blockOf8_rtc 6 t (by norm_num [fig1V]) hrtc
  have ht19 := fig1V_le8_mem t ht
  rcases ht19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact absurd hblk (by decide)
      | exact lt_irrefl _ hlt

/-- The local minima of Figure 1 are exactly the three global minima together
with s4, s6 and s7; in particular s5 is not a local minimum. -/
theorem fig1_localMin : (∀ s : Fin 26, IsHajekLocalMin fig1R fig1V s ↔
    s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 5 ∨ s = 6) ∧
    ¬ IsHajekLocalMin fig1R fig1V 4 := by
  constructor
  · intro s
    constructor
    · intro hs
      fin_cases s
      · exact by decide
      · exact by decide
      · exact by decide
      · exact by decide
      · exact absurd hs fig1_nlocalMin4
      · exact by decide
      · exact by decide
      · exact absurd hs fig1_nlocalMin7
      · exact absurd hs fig1_nlocalMin8
      · exact absurd hs fig1_nlocalMin9
      · exact absurd hs fig1_nlocalMin10
      · exact absurd hs fig1_nlocalMin11
      · exact absurd hs fig1_nlocalMin12
      · exact absurd hs fig1_nlocalMin13
      · exact absurd hs fig1_nlocalMin14
      · exact absurd hs fig1_nlocalMin15
      · exact absurd hs fig1_nlocalMin16
      · exact absurd hs fig1_nlocalMin17
      · exact absurd hs fig1_nlocalMin18
      · exact absurd hs fig1_nlocalMin19
      · exact absurd hs fig1_nlocalMin20
      · exact absurd hs fig1_nlocalMin21
      · exact absurd hs fig1_nlocalMin22
      · exact absurd hs fig1_nlocalMin23
      · exact absurd hs fig1_nlocalMin24
      · exact absurd hs fig1_nlocalMin25
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact fig1_localMin_of_ge1 0 (by norm_num [fig1V])
      · exact fig1_localMin_of_ge1 1 (by norm_num [fig1V])
      · exact fig1_localMin_of_ge1 2 (by norm_num [fig1V])
      · exact fig1_localMin_mem3
      · exact fig1_localMin_mem5
      · exact fig1_localMin_mem6
  · exact fig1_nlocalMin4

/-- s7 has depth 2: it escapes exactly at height 10. -/
theorem fig1_depth6 : depth fig1R fig1V 6 = 2 := by
  have hV6 : fig1V (6 : Fin 26) = 8 := by norm_num [fig1V]
  have hreach : ReachableAt fig1R fig1V (fig1V 6 + 2) 6 2 := by
    have hEq10 : fig1V 6 + 2 = 10 := by norm_num [fig1V]
    rw [hEq10]
    exact fig1_reach10_of_block 6 2 (by norm_num [fig1V]) (by decide)
      (by norm_num [fig1V])
  have h2 : (0:ℝ) < 2 ∧ ∃ t, fig1V t < fig1V 6 ∧
      ReachableAt fig1R fig1V (fig1V 6 + 2) 6 t :=
    ⟨by norm_num, 2, by norm_num [fig1V], hreach⟩
  have hle : depth fig1R fig1V 6 ≤ 2 := by
    calc depth fig1R fig1V 6
        = ⨅ (E : ℝ) (_ : 0 < E ∧ ∃ t, fig1V t < fig1V 6 ∧
            ReachableAt fig1R fig1V (fig1V 6 + E) 6 t), ENNReal.ofReal E := rfl
      _ ≤ (⨅ _ : 0 < (2:ℝ) ∧ ∃ t, fig1V t < fig1V 6 ∧
            ReachableAt fig1R fig1V (fig1V 6 + 2) 6 t, ENNReal.ofReal 2) :=
          iInf_le _ 2
      _ ≤ ENNReal.ofReal 2 := iInf_le _ h2
      _ = 2 := by norm_num
  have hge : 2 ≤ depth fig1R fig1V 6 := by
    rw [depth]
    apply le_iInf
    intro E
    apply le_iInf
    intro hP
    obtain ⟨hEpos, t, hlt, hreachE⟩ := hP
    have h10 : (10:ℝ) ≤ fig1V 6 + E := by
      by_contra hcon
      have hcon : fig1V 6 + E < 10 := lt_of_not_ge hcon
      have h8le : (8:ℝ) ≤ fig1V 6 + E := by linarith
      have hreach8 := (fig1_iff8 h8le hcon 6 t).mp hreachE
      obtain ⟨-, hrtc⟩ := hreach8
      obtain ⟨hblk, ht⟩ := fig1_blockOf8_rtc 6 t (by norm_num [fig1V]) hrtc
      have ht19 := fig1V_le8_mem t ht
      rcases ht19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd hblk (by decide)
          | (norm_num [fig1V] at hlt)
    have hE : (2:ℝ) ≤ E := by linarith
    calc (2:ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      _ ≤ ENNReal.ofReal E := ENNReal.ofReal_le_ofReal hE
  exact le_antisymm hle hge

/-- s4 has depth 5: it escapes exactly at height 10. -/
theorem fig1_depth3 : depth fig1R fig1V 3 = 5 := by
  have hV3 : fig1V (3 : Fin 26) = 5 := by norm_num [fig1V]
  have hreach : ReachableAt fig1R fig1V (fig1V 3 + 5) 3 2 := by
    have hEq10 : fig1V 3 + 5 = 10 := by norm_num [fig1V]
    rw [hEq10]
    exact fig1_reach10_of_block 3 2 (by norm_num [fig1V]) (by decide)
      (by norm_num [fig1V])
  have h5 : (0:ℝ) < 5 ∧ ∃ t, fig1V t < fig1V 3 ∧
      ReachableAt fig1R fig1V (fig1V 3 + 5) 3 t :=
    ⟨by norm_num, 2, by norm_num [fig1V], hreach⟩
  have hle : depth fig1R fig1V 3 ≤ 5 := by
    calc depth fig1R fig1V 3
        = ⨅ (E : ℝ) (_ : 0 < E ∧ ∃ t, fig1V t < fig1V 3 ∧
            ReachableAt fig1R fig1V (fig1V 3 + E) 3 t), ENNReal.ofReal E := rfl
      _ ≤ (⨅ _ : 0 < (5:ℝ) ∧ ∃ t, fig1V t < fig1V 3 ∧
            ReachableAt fig1R fig1V (fig1V 3 + 5) 3 t, ENNReal.ofReal 5) :=
          iInf_le _ 5
      _ ≤ ENNReal.ofReal 5 := iInf_le _ h5
      _ = 5 := by norm_num
  have hge : 5 ≤ depth fig1R fig1V 3 := by
    rw [depth]
    apply le_iInf
    intro E
    apply le_iInf
    intro hP
    obtain ⟨hEpos, t, hlt, hreachE⟩ := hP
    have h10 : (10:ℝ) ≤ fig1V 3 + E := by
      by_contra hcon
      have hcon : fig1V 3 + E < 10 := lt_of_not_ge hcon
      rcases lt_or_ge (fig1V 3 + E) 8 with h8 | h8
      · have h5le : (5:ℝ) ≤ fig1V 3 + E := by linarith
        have hreach5 := (fig1_iff5 h5le h8 3 t).mp hreachE
        obtain ⟨-, hrtc⟩ := hreach5
        obtain ⟨hblk, ht⟩ := fig1_blockOf5_rtc 3 t (by norm_num [fig1V]) hrtc
        have ht12 := fig1V_le5_mem t ht
        rcases ht12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact absurd hblk (by decide)
            | (norm_num [fig1V] at hlt)
      · have hreach8 := (fig1_iff8 h8 hcon 3 t).mp hreachE
        obtain ⟨-, hrtc⟩ := hreach8
        obtain ⟨hblk, ht⟩ := fig1_blockOf8_rtc 3 t (by norm_num [fig1V]) hrtc
        have ht19 := fig1V_le8_mem t ht
        rcases ht19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact absurd hblk (by decide)
            | (norm_num [fig1V] at hlt)
    have hE : (5:ℝ) ≤ E := by linarith
    calc (5:ℝ≥0∞) = ENNReal.ofReal 5 := by norm_num
      _ ≤ ENNReal.ofReal E := ENNReal.ofReal_le_ofReal hE
  exact le_antisymm hle hge

/-- s6 has depth 6: it escapes exactly at height 10. -/
theorem fig1_depth5 : depth fig1R fig1V 5 = 6 := by
  have hV5 : fig1V (5 : Fin 26) = 4 := by norm_num [fig1V]
  have hreach : ReachableAt fig1R fig1V (fig1V 5 + 6) 5 2 := by
    have hEq10 : fig1V 5 + 6 = 10 := by norm_num [fig1V]
    rw [hEq10]
    exact fig1_reach10_of_block 5 2 (by norm_num [fig1V]) (by decide)
      (by norm_num [fig1V])
  have h6 : (0:ℝ) < 6 ∧ ∃ t, fig1V t < fig1V 5 ∧
      ReachableAt fig1R fig1V (fig1V 5 + 6) 5 t :=
    ⟨by norm_num, 2, by norm_num [fig1V], hreach⟩
  have hle : depth fig1R fig1V 5 ≤ 6 := by
    calc depth fig1R fig1V 5
        = ⨅ (E : ℝ) (_ : 0 < E ∧ ∃ t, fig1V t < fig1V 5 ∧
            ReachableAt fig1R fig1V (fig1V 5 + E) 5 t), ENNReal.ofReal E := rfl
      _ ≤ (⨅ _ : 0 < (6:ℝ) ∧ ∃ t, fig1V t < fig1V 5 ∧
            ReachableAt fig1R fig1V (fig1V 5 + 6) 5 t, ENNReal.ofReal 6) :=
          iInf_le _ 6
      _ ≤ ENNReal.ofReal 6 := iInf_le _ h6
      _ = 6 := by norm_num
  have hge : 6 ≤ depth fig1R fig1V 5 := by
    rw [depth]
    apply le_iInf
    intro E
    apply le_iInf
    intro hP
    obtain ⟨hEpos, t, hlt, hreachE⟩ := hP
    have h10 : (10:ℝ) ≤ fig1V 5 + E := by
      by_contra hcon
      have hcon : fig1V 5 + E < 10 := lt_of_not_ge hcon
      rcases lt_or_ge (fig1V 5 + E) 5 with h5lt | h5ge
      · have h4le : (4:ℝ) ≤ fig1V 5 + E := by linarith
        have hreach4 := (fig1_iff4 h4le h5lt 5 t).mp hreachE
        obtain ⟨-, hrtc⟩ := hreach4
        obtain ⟨hblk, ht⟩ := fig1_blockOf4_rtc 5 t (by norm_num [fig1V]) hrtc
        have ht6 := fig1V_le4_mem t ht
        rcases ht6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
            | exact absurd hblk (by decide)
            | (norm_num [fig1V] at hlt)
      · rcases lt_or_ge (fig1V 5 + E) 8 with h8 | h8
        · have hreach5 := (fig1_iff5 h5ge h8 5 t).mp hreachE
          obtain ⟨-, hrtc⟩ := hreach5
          obtain ⟨hblk, ht⟩ := fig1_blockOf5_rtc 5 t (by norm_num [fig1V]) hrtc
          have ht12 := fig1V_le5_mem t ht
          rcases ht12 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
              | exact absurd hblk (by decide)
              | (norm_num [fig1V] at hlt)
        · have hreach8 := (fig1_iff8 h8 hcon 5 t).mp hreachE
          obtain ⟨-, hrtc⟩ := hreach8
          obtain ⟨hblk, ht⟩ := fig1_blockOf8_rtc 5 t (by norm_num [fig1V]) hrtc
          have ht19 := fig1V_le8_mem t ht
          rcases ht19 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
              | exact absurd hblk (by decide)
              | (norm_num [fig1V] at hlt)
    have hE : (6:ℝ) ≤ E := by linarith
    calc (6:ℝ≥0∞) = ENNReal.ofReal 6 := by norm_num
      _ ≤ ENNReal.ofReal E := ENNReal.ofReal_le_ofReal hE
  exact le_antisymm hle hge

/-- Depths in Figure 1: s4 has depth 5, s6 has depth 6, s7 has depth 2, and
`dStar = 6`. -/
theorem fig1_depths : depth fig1R fig1V 3 = 5 ∧ depth fig1R fig1V 5 = 6 ∧
    depth fig1R fig1V 6 = 2 ∧ dStar fig1R fig1V = 6 := by
  have hEq : dStar fig1R fig1V = (⨆ (s : Fin 26),
      ⨆ _ : IsHajekLocalMin fig1R fig1V s ∧ s ∉ globalMinSet fig1V,
      depth fig1R fig1V s) := rfl
  have hle : dStar fig1R fig1V ≤ 6 := by
    rw [hEq]
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    have hloc := (fig1_localMin.1 s).mp hs.1
    rcases hloc with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      apply hs.2
      rw [fig1_globalMinSet]
      decide
    · exfalso
      apply hs.2
      rw [fig1_globalMinSet]
      decide
    · exfalso
      apply hs.2
      rw [fig1_globalMinSet]
      decide
    · rw [fig1_depth3]
      norm_num
    · rw [fig1_depth5]
    · rw [fig1_depth6]
      norm_num
  have hge : 6 ≤ dStar fig1R fig1V := by
    rw [hEq]
    have h5mem : IsHajekLocalMin fig1R fig1V 5 ∧ 5 ∉ globalMinSet fig1V := by
      refine ⟨fig1_localMin_mem5, ?_⟩
      rw [fig1_globalMinSet]
      decide
    calc (6:ℝ≥0∞) = depth fig1R fig1V 5 := fig1_depth5.symm
      _ ≤ (⨆ _ : IsHajekLocalMin fig1R fig1V 5 ∧ 5 ∉ globalMinSet fig1V,
            depth fig1R fig1V 5) :=
          le_iSup (fun _ : IsHajekLocalMin fig1R fig1V 5 ∧ 5 ∉ globalMinSet fig1V =>
            depth fig1R fig1V 5) h5mem
      _ ≤ (⨆ (s : Fin 26), ⨆ _ : IsHajekLocalMin fig1R fig1V s ∧
            s ∉ globalMinSet fig1V, depth fig1R fig1V s) :=
          le_iSup (fun s : Fin 26 => ⨆ _ : IsHajekLocalMin fig1R fig1V s ∧
            s ∉ globalMinSet fig1V, depth fig1R fig1V s) 5
  exact ⟨fig1_depth3, fig1_depth5, fig1_depth6, le_antisymm hle hge⟩

/-- In Figure 1, s2 is reachable from s1 at height 1, while s3 is reachable
from s1 at height 12 and at no lower height. -/
theorem fig1_reach : ReachableAt fig1R fig1V 1 0 1 ∧
    ReachableAt fig1R fig1V 12 0 2 ∧
    ∀ E : ℝ, E < 12 → ¬ ReachableAt fig1R fig1V E 0 2 := by
  have h01 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 1) 0 1 :=
    Relation.ReflTransGen.single ⟨(arc_iff 0 1).mpr (by decide), by norm_num [fig1V]⟩
  have hp1 : ReachableAt fig1R fig1V 1 0 1 :=
    ⟨by norm_num [fig1V], h01⟩
  have e1 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 0 10 :=
    Relation.ReflTransGen.single ⟨(arc_iff 0 10).mpr (by decide), by norm_num [fig1V]⟩
  have e2 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 10 13 :=
    Relation.ReflTransGen.single ⟨(arc_iff 10 13).mpr (by decide), by norm_num [fig1V]⟩
  have e3 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 13 19 :=
    Relation.ReflTransGen.single ⟨(arc_iff 13 19).mpr (by decide), by norm_num [fig1V]⟩
  have e4 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 19 24 :=
    Relation.ReflTransGen.single ⟨(arc_iff 19 24).mpr (by decide), by norm_num [fig1V]⟩
  have e5 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 24 21 :=
    Relation.ReflTransGen.single ⟨(arc_iff 24 21).mpr (by decide), by norm_num [fig1V]⟩
  have e6 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 21 22 :=
    Relation.ReflTransGen.single ⟨(arc_iff 21 22).mpr (by decide), by norm_num [fig1V]⟩
  have e7 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 22 25 :=
    Relation.ReflTransGen.single ⟨(arc_iff 22 25).mpr (by decide), by norm_num [fig1V]⟩
  have e8 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 25 23 :=
    Relation.ReflTransGen.single ⟨(arc_iff 25 23).mpr (by decide), by norm_num [fig1V]⟩
  have e9 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 23 18 :=
    Relation.ReflTransGen.single ⟨(arc_iff 23 18).mpr (by decide), by norm_num [fig1V]⟩
  have e10 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 18 12 :=
    Relation.ReflTransGen.single ⟨(arc_iff 18 12).mpr (by decide), by norm_num [fig1V]⟩
  have e11 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 12 8 :=
    Relation.ReflTransGen.single ⟨(arc_iff 12 8).mpr (by decide), by norm_num [fig1V]⟩
  have e12 : Relation.ReflTransGen (fun a b => Arc fig1R a b ∧ fig1V b ≤ 12) 8 2 :=
    Relation.ReflTransGen.single ⟨(arc_iff 8 2).mpr (by decide), by norm_num [fig1V]⟩
  have hp2 : ReachableAt fig1R fig1V 12 0 2 :=
    ⟨by norm_num [fig1V],
      e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans (e7.trans
        (e8.trans (e9.trans (e10.trans (e11.trans e12))))))))))⟩
  have hneg : ∀ E : ℝ, E < 12 → ¬ ReachableAt fig1R fig1V E 0 2 := by
    intro E hE hreach
    obtain ⟨h0E, hrtc⟩ := hreach
    have hle10 : ∀ c : Fin 26, fig1V c ≤ E → fig1V c ≤ 10 := by
      intro c hc
      have hlt : fig1V c < 12 := lt_of_le_of_lt hc hE
      fin_cases c <;> revert hlt <;> norm_num [fig1V]
    have hclose : ∀ a c : Fin 26,
        (a = 0 ∨ a = 1 ∨ a = 7 ∨ a = 9 ∨ a = 10 ∨ a = 13 ∨ a = 19) →
        Arc fig1R a c → fig1V c ≤ E →
        (c = 0 ∨ c = 1 ∨ c = 7 ∨ c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 19) := by
      intro a c ha harc hcE
      have hc10 : fig1V c ≤ 10 := hle10 c hcE
      rw [arc_iff] at harc
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [fig1Out] at harc
        rcases harc with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · simp [fig1Out] at harc
        rcases harc with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
      · simp [fig1Out] at harc
        subst harc
        exact Or.inl rfl
      · simp [fig1Out] at harc
        subst harc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · simp [fig1Out] at harc
        rcases harc with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · simp [fig1Out] at harc
        rcases harc with rfl | rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · simp [fig1Out] at harc
        rcases harc with rfl | rfl
        · norm_num [fig1V] at hc10
        · exact Or.inr (Or.inr (Or.inl rfl))
    have key := Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => (a = 0 ∨ a = 1 ∨ a = 7 ∨ a = 9 ∨ a = 10 ∨ a = 13 ∨ a = 19) →
        ((2 : Fin 26) = 0 ∨ (2 : Fin 26) = 1 ∨ (2 : Fin 26) = 7 ∨ (2 : Fin 26) = 9 ∨
          (2 : Fin 26) = 10 ∨ (2 : Fin 26) = 13 ∨ (2 : Fin 26) = 19))
      hrtc
      (fun h => h)
      (fun h' _ ih ha => ih (hclose _ _ ha h'.1 h'.2))
    have h2T := key (Or.inl rfl)
    exact absurd h2T (by decide)
  exact ⟨hp1, hp2, hneg⟩


end Cslib.MachineLearning.Sampling.SimulatedAnnealing
