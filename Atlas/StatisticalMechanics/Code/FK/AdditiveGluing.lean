/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































import Mathlib
import Code.FK.FKInterfaceSubadd
import Code.FK.SuperMultiplicative
import Code.FK.BoxFeketePerVolume
import Code.FK.BoxTiling
import Code.FK.GenuineEdgeCollapse
import Code.Lattice.BoxSurfaceVolume

open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace StatMech

namespace FK








section Partition

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]
  (P : U → Prop) [DecidablePred P]


abbrev agl_left : SimpleGraph {x // P x} := K₀.comap (Subtype.val)


abbrev agl_right : SimpleGraph {x // ¬ P x} := K₀.comap (Subtype.val)

noncomputable instance : DecidableRel (agl_left K₀ P).Adj := Classical.decRel _
noncomputable instance : DecidableRel (agl_right K₀ P).Adj := Classical.decRel _


noncomputable def agl_sumEquiv : ({x // P x} ⊕ {x // ¬ P x}) ≃ U := Equiv.sumCompl P



noncomputable def agl_glueGraph : SimpleGraph ({x // P x} ⊕ {x // ¬ P x}) :=
  K₀.comap (agl_sumEquiv P)

noncomputable instance : DecidableRel (agl_glueGraph K₀ P).Adj := Classical.decRel _

@[simp] theorem agl_sumEquiv_inl (a : {x // P x}) :
    agl_sumEquiv P (Sum.inl a) = (a : U) := rfl

@[simp] theorem agl_sumEquiv_inr (b : {x // ¬ P x}) :
    agl_sumEquiv P (Sum.inr b) = (b : U) := rfl

@[simp] theorem agl_glueGraph_adj (u v : {x // P x} ⊕ {x // ¬ P x}) :
    (agl_glueGraph K₀ P).Adj u v ↔ K₀.Adj (agl_sumEquiv P u) (agl_sumEquiv P v) := by
  unfold agl_glueGraph
  rw [comap_adj]





theorem agl_partitionCrossInterface :
    fis_CrossInterface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P) := by
  refine ⟨?_, ?_, ?_⟩
  · 
    intro u v huv
    rw [agl_glueGraph_adj]
    match u, v, huv with
    | Sum.inl a, Sum.inl b, huv =>
      rw [SimpleGraph.sum_adj] at huv
      
      simpa [agl_left, comap_adj] using huv
    | Sum.inr c, Sum.inr e, huv =>
      rw [SimpleGraph.sum_adj] at huv
      simpa [agl_right, comap_adj] using huv
    | Sum.inl a, Sum.inr e, huv => simp only [SimpleGraph.sum_adj] at huv
    | Sum.inr c, Sum.inl b, huv => simp only [SimpleGraph.sum_adj] at huv
  · 
    intro a b hab
    rw [agl_glueGraph_adj] at hab
    simpa [agl_left, comap_adj] using hab
  · 
    intro c e hce
    rw [agl_glueGraph_adj] at hce
    simpa [agl_right, comap_adj] using hce


noncomputable def agl_iso : K₀ ≃g agl_glueGraph K₀ P where
  toEquiv := (agl_sumEquiv P).symm
  map_rel_iff' := by
    intro a b
    rw [agl_glueGraph_adj]
    simp only [Equiv.apply_symm_apply]


noncomputable def agl_interfaceCard : ℕ :=
  (fis_interface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P)).card



theorem agl_fkZ_eq (p q : ℝ) :
    fkZ K₀ p q = fkZ (agl_glueGraph K₀ P) p q :=
  fsm_fkZ_iso K₀ (agl_glueGraph K₀ P) (agl_iso K₀ P) p q









theorem agl_neglog_partition_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    -Real.log (fkZ K₀ p q)
      ≤ -Real.log (fkZ (agl_left K₀ P) p q) + -Real.log (fkZ (agl_right K₀ P) p q)
        - (agl_interfaceCard K₀ P : ℝ) * Real.log (1 - p) := by
  rw [agl_fkZ_eq K₀ P p q]
  exact fis_neglog_interface_le (agl_partitionCrossInterface K₀ P) hp hp1 hq

end Partition









open StatMech.Lattice



theorem agl_nn_translate (d : ℕ) (v x y : Site d) :
    (hypercubicLattice d).Adj (x + v) (y + v) ↔ (hypercubicLattice d).Adj x y := by
  simp only [hypercubicLattice_adj]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [← h] <;>
    refine Finset.sum_congr rfl (fun i _ => ?_) <;> simp [Pi.add_apply]

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]




noncomputable def agl_transBlockIso (d : ℕ) (v : Site d) (f : V → Site d) (g : W → Site d)
    (φ : V ≃ W) (hfg : ∀ x, g (φ x) = f x + v) :
    (hypercubicLattice d).comap f ≃g (hypercubicLattice d).comap g where
  toEquiv := φ
  map_rel_iff' := by
    intro x y
    simp only [comap_adj, Equiv.coe_fn_mk, hfg]
    exact agl_nn_translate d v (f x) (f y)



theorem agl_fkZ_translate (d : ℕ) (v : Site d) (f : V → Site d) (g : W → Site d)
    (φ : V ≃ W) (hfg : ∀ x, g (φ x) = f x + v) (p q : ℝ)
    [DecidableRel ((hypercubicLattice d).comap f).Adj]
    [DecidableRel ((hypercubicLattice d).comap g).Adj] :
    fkZ ((hypercubicLattice d).comap f) p q = fkZ ((hypercubicLattice d).comap g) p q :=
  fsm_fkZ_iso _ _ (agl_transBlockIso d v f g φ hfg) p q













noncomputable def agl_leftBlockIso (N m : ℕ) (P : boxVerts d N → Prop) [DecidablePred P]
    (v : Site d) (φ : boxVerts d m ≃ {x // P x})
    (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) :
    boxGraph d m ≃g agl_left (boxGraph d N) P where
  toEquiv := φ
  map_rel_iff' := by
    intro y z
    
    show (agl_left (boxGraph d N) P).Adj (φ y) (φ z) ↔ (boxGraph d m).Adj y z
    unfold agl_left boxGraph
    simp only [comap_adj]
    rw [hφ y, hφ z]
    exact agl_nn_translate d v (y : Site d) (z : Site d)


theorem agl_left_block_fkZ_eq (N m : ℕ) (P : boxVerts d N → Prop) [DecidablePred P]
    (v : Site d) (φ : boxVerts d m ≃ {x // P x})
    (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) (p q : ℝ) :
    fkZ (agl_left (boxGraph d N) P) p q = fkZ (boxGraph d m) p q :=
  (fsm_fkZ_iso (boxGraph d m) (agl_left (boxGraph d N) P)
    (agl_leftBlockIso N m P v φ hφ) p q).symm


noncomputable def agl_rightBlockIso (N m : ℕ) (P : boxVerts d N → Prop) [DecidablePred P]
    (v : Site d) (φ : boxVerts d m ≃ {x // ¬ P x})
    (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) :
    boxGraph d m ≃g agl_right (boxGraph d N) P where
  toEquiv := φ
  map_rel_iff' := by
    intro y z
    show (agl_right (boxGraph d N) P).Adj (φ y) (φ z) ↔ (boxGraph d m).Adj y z
    unfold agl_right boxGraph
    simp only [comap_adj]
    rw [hφ y, hφ z]
    exact agl_nn_translate d v (y : Site d) (z : Site d)


theorem agl_right_block_fkZ_eq (N m : ℕ) (P : boxVerts d N → Prop) [DecidablePred P]
    (v : Site d) (φ : boxVerts d m ≃ {x // ¬ P x})
    (hφ : ∀ y : boxVerts d m, ((φ y : boxVerts d N) : Site d) = (y : Site d) + v) (p q : ℝ) :
    fkZ (agl_right (boxGraph d N) P) p q = fkZ (boxGraph d m) p q :=
  (fsm_fkZ_iso (boxGraph d m) (agl_right (boxGraph d N) P)
    (agl_rightBlockIso N m P v φ hφ) p q).symm





















theorem agl_subseq_almost_mono_converges (g : ℕ → ℝ) (K : ℕ → ℕ) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hmono : ∀ j, g (K j) - δ j ≤ g (K (j + 1)))
    (hbdd : BddAbove (Set.range fun j => g (K j))) :
    ∃ L, Tendsto (fun j => g (K j)) atTop (𝓝 L) :=
  bpv_almost_mono_converges (fun j => g (K j)) δ hδ hsum hmono hbdd






theorem agl_full_from_subseq (g : ℕ → ℝ) (K : ℕ → ℕ) (L : ℝ)
    (hsub : Tendsto (fun j => g (K j)) atTop (𝓝 L))
    (bj : ℕ → ℕ) (hbj : Tendsto bj atTop atTop)
    (osc : ℕ → ℝ) (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, |g n - g (K (bj n))| ≤ osc (bj n)) :
    Tendsto g atTop (𝓝 L) := by
  have hcomp : Tendsto (fun n => g (K (bj n))) atTop (𝓝 L) := hsub.comp hbj
  have hosc' : Tendsto (fun n => osc (bj n)) atTop (𝓝 0) := hosc.comp hbj
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hcomp) (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hosc') (ε / 2) (by linarith)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hnN1 : N1 ≤ n := le_trans (le_max_left _ _) hn
  have hnN2 : N2 ≤ n := le_trans (le_max_right _ _) hn
  have hd1 : dist (g (K (bj n))) L < ε / 2 := hN1 n hnN1
  have hd2 : dist (osc (bj n)) 0 < ε / 2 := hN2 n hnN2
  have hsd : |g n - g (K (bj n))| ≤ osc (bj n) := hsand n
  have hoscnn : 0 ≤ osc (bj n) := le_trans (abs_nonneg _) hsd
  rw [Real.dist_eq] at hd1 hd2 ⊢
  rw [sub_zero, abs_of_nonneg hoscnn] at hd2
  calc |g n - L| = |(g n - g (K (bj n))) + (g (K (bj n)) - L)| := by ring_nf
    _ ≤ |g n - g (K (bj n))| + |g (K (bj n)) - L| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add_of_le_of_lt
        · exact le_trans hsd (le_of_lt hd2)
        · exact hd1
    _ = ε := by ring






theorem agl_perVolume_converges (g : ℕ → ℝ) (K : ℕ → ℕ) (δ osc : ℕ → ℝ) (bj : ℕ → ℕ)
    (hδ : ∀ j, 0 ≤ δ j) (hsum : Summable δ)
    (hmono : ∀ j, g (K j) - δ j ≤ g (K (j + 1)))
    (hbdd : BddAbove (Set.range fun j => g (K j)))
    (hbj : Tendsto bj atTop atTop)
    (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, |g n - g (K (bj n))| ≤ osc (bj n)) :
    ∃ L, Tendsto g atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := agl_subseq_almost_mono_converges g K δ hδ hsum hmono hbdd
  exact ⟨L, agl_full_from_subseq g K L hL bj hbj osc hosc hsand⟩





def agl_K (j : ℕ) : ℕ := 2 ^ (j + 1) - 1

@[simp] theorem agl_K_zero : agl_K 0 = 1 := rfl

theorem agl_K_succ (j : ℕ) : agl_K (j + 1) = 2 * agl_K j + 1 := by
  unfold agl_K
  have h1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_two_pow
  omega

theorem agl_K_pos (j : ℕ) : 1 ≤ agl_K j := by
  unfold agl_K
  have : 2 ≤ 2 ^ (j + 1) := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem agl_K_tendsto_atTop : Tendsto agl_K atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  refine ⟨b, fun j hj => ?_⟩
  unfold agl_K
  have h1 : b + 1 ≤ 2 ^ (j + 1) := by
    calc b + 1 ≤ j + 1 := by omega
      _ ≤ 2 ^ (j + 1) := Nat.lt_two_pow_self.le
  omega









variable (d : ℕ)


noncomputable def agl_u (t : ℝ) (n : ℕ) : ℝ :=
  -Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2)


noncomputable def agl_E (n : ℕ) : ℝ := ((boxGraph d n).edgeFinset.card : ℝ)


theorem agl_g_eq (t : ℝ) (n : ℕ) :
    ivp2_tiltFreeEnergy (boxGraph d n) 2 t
      = -(agl_u d t n / agl_E d n) + Real.log (1 + Real.exp t) := by
  unfold ivp2_tiltFreeEnergy agl_u agl_E
  ring














def agl_AdditiveDoublingBound (t : ℝ) : Prop :=
  ∃ (I : ℕ → ℝ),
    (∀ j, 0 ≤ I j)
    ∧ Summable (fun j => I j / agl_E d (agl_K (j + 1)))
    ∧ (∀ j, agl_u d t (agl_K (j + 1))
        ≤ (2 : ℝ) ^ d * agl_u d t (agl_K j) + I j * (-Real.log (1 - fsc_logistic t)))
    ∧ (∀ j, |(2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))| ≤ I j)



















theorem agl_boxTiltFreeEnergy_tendsto (t : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card)
    (hdoubling : agl_AdditiveDoublingBound d t)
    (hbdd : ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    (bj : ℕ → ℕ) (hbj : Tendsto bj atTop atTop)
    (osc : ℕ → ℝ) (hosc : Tendsto osc atTop (𝓝 0))
    (hsand : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n)) :
    ∃ L : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := hdoubling
  obtain ⟨M, hM⟩ := hbdd
  set c : ℝ := -Real.log (1 - fsc_logistic t) with hc
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hMc0 : 0 ≤ M + c := by linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  
  apply agl_perVolume_converges
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) agl_K δ osc bj
  · intro j; exact mul_nonneg hMc0 (hIE0 j)
  · exact hIsum.mul_left (M + c)
  · 
    intro j
    rw [agl_g_eq d t (agl_K j), agl_g_eq d t (agl_K (j + 1))]
    have hKeq : agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ j
    have hstep := bxt_perVolume_doubling_step (a := agl_u d t (agl_K j))
      (A := agl_u d t (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hdefle : (|agl_u d t (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      have habs : |agl_u d t (agl_K j)| / agl_E d (agl_K j)
          = |agl_u d t (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [habs]; have := hM j; linarith
    have hgoal : -(agl_u d t (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(agl_u d t (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  · 
    refine ⟨M + Real.log (1 + Real.exp t), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    rw [agl_g_eq d t (agl_K j)]
    have hlb : -M ≤ agl_u d t (agl_K j) / agl_E d (agl_K j) := (abs_le.mp (hM j)).1
    linarith
  · exact hbj
  · exact hosc
  · exact hsand






























theorem agl_doublingStep_of_partition (t : ℝ) (K : ℕ) (P : boxVerts d (2 * K + 1) → Prop)
    [DecidablePred P] (v : Site d) (φ : boxVerts d K ≃ {x // P x})
    (hφ : ∀ y : boxVerts d K, ((φ y : boxVerts d (2 * K + 1)) : Site d) = (y : Site d) + v)
    (IR : ℝ) (hIR : 0 ≤ IR)
    (hRight : -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2)
        ≤ ((2:ℝ) ^ d - 1) * agl_u d t K + IR * (-Real.log (1 - fsc_logistic t))) :
    agl_u d t (2 * K + 1)
      ≤ (2 : ℝ) ^ d * agl_u d t K
        + ((agl_interfaceCard (boxGraph d (2 * K + 1)) P : ℝ) + IR)
            * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0:ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  
  have hpart := agl_neglog_partition_le (boxGraph d (2 * K + 1)) P hp0 hp1 (by norm_num : (0:ℝ) < 2)
  
  have hleft : fkZ (agl_left (boxGraph d (2 * K + 1)) P) p 2 = fkZ (boxGraph d K) p 2 :=
    agl_left_block_fkZ_eq (2 * K + 1) K P v φ hφ p 2
  have hleftu : -Real.log (fkZ (agl_left (boxGraph d (2 * K + 1)) P) p 2) = agl_u d t K := by
    rw [hleft]; rfl
  
  rw [hleftu] at hpart
  
  unfold agl_u at *
  nlinarith [hpart, hRight]





theorem agl_rightBlock_recursion_satisfiable (t : ℝ) (K : ℕ) (P : boxVerts d (2 * K + 1) → Prop)
    [DecidablePred P] :
    ∃ IR : ℝ, 0 ≤ IR ∧
      -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2)
        ≤ ((2:ℝ) ^ d - 1) * agl_u d t K + IR * (-Real.log (1 - fsc_logistic t)) := by
  have hp0 : (0:ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hclog : 0 < -Real.log (1 - fsc_logistic t) := by
    rw [neg_pos]; exact Real.log_neg (by linarith) (by linarith)
  
  set L := -Real.log (fkZ (agl_right (boxGraph d (2 * K + 1)) P) (fsc_logistic t) 2)
  set R0 := ((2:ℝ) ^ d - 1) * agl_u d t K
  refine ⟨max 0 ((L - R0) / (-Real.log (1 - fsc_logistic t))), le_max_left _ _, ?_⟩
  have hge : (L - R0) / (-Real.log (1 - fsc_logistic t))
      ≤ max 0 ((L - R0) / (-Real.log (1 - fsc_logistic t))) := le_max_right _ _
  have hmul : (L - R0) ≤ max 0 ((L - R0) / (-Real.log (1 - fsc_logistic t)))
      * (-Real.log (1 - fsc_logistic t)) := by
    rw [← div_le_iff₀ hclog]; exact hge
  linarith













def agl_AdditiveBoxFeketeData (t : ℝ) : Prop :=
  agl_AdditiveDoublingBound d t
    ∧ (∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    ∧ (∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
        ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n)))







theorem agl_exists_convex_ivPressure (hd : 1 ≤ d)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, agl_AdditiveBoxFeketeData d t) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ univ g := by
  classical
  have hconv : ∀ t, ∃ L : ℝ,
      Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 L) := by
    intro t
    obtain ⟨hdbl, hbdd, bj, osc, hbj, hosc, hsand⟩ := hdata t
    exact agl_boxTiltFreeEnergy_tendsto d t (fun j => hE (agl_K j)) hdbl hbdd bj hbj osc hosc hsand
  refine ⟨fun t => (hconv t).choose, fun t => (hconv t).choose_spec, ?_⟩
  exact ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2)
    (fun t => (hconv t).choose)
    (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hE n))
    (fun t => (hconv t).choose_spec)



















theorem agl_fk_uniqueness_of_additiveData (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, agl_AdditiveBoxFeketeData d t) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨g, hboxfree, hg⟩ := agl_exists_convex_ivPressure d hd hEbox hdata
  exact fpe2_fk_uniqueness_of_boxFekete hd N eb heb hEbox hg hboxfree
    (gec_GenuineFreeCollapse hd N hEbox)
    (gec_GenuineWiredCollapse hd N hEbox)



















theorem agl_additiveDoublingBound_satisfiable (d : ℕ) (hd : 1 ≤ d) (c : ℝ) (hc : 0 ≤ c) :
    ∃ (u E : ℕ → ℝ),
      (∃ (I : ℕ → ℝ),
        (∀ j, 0 ≤ I j)
        ∧ Summable (fun j => I j / E (agl_K (j + 1)))
        ∧ (∀ j, u (agl_K (j + 1)) ≤ (2 : ℝ) ^ d * u (agl_K j) + I j * c)
        ∧ (∀ j, |(2 : ℝ) ^ d * E (agl_K j) - E (agl_K (j + 1))| ≤ I j)) := by
  refine ⟨fun _ => 0, fun n => (n:ℝ) ^ d,
    fun j => |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d|, ?_, ?_, ?_, ?_⟩
  · intro j; exact abs_nonneg _
  · 
    have hgsum : Summable (fun j => (d : ℝ) * (1/2)^j) :=
      (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).mul_left _
    refine Summable.of_nonneg_of_le
      (g := fun j => |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d|
        / ((agl_K (j + 1) : ℝ)) ^ d)
      (fun j => by positivity)
      (f := fun j => (d : ℝ) * (1/2)^j) ?_ hgsum
    · intro j
      have hKpos : (0:ℝ) < (agl_K j : ℝ) := by exact_mod_cast (agl_K_pos j)
      have hKsucc : agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ j
      
      have h2d : (2:ℝ)^d * (agl_K j : ℝ)^d = (2 * (agl_K j : ℝ))^d := by rw [mul_pow]
      have hKsuccR : ((agl_K (j + 1) : ℝ)) = 2 * (agl_K j : ℝ) + 1 := by
        rw [hKsucc]; push_cast; ring
      have hle : ((agl_K (j + 1) : ℝ))^d - (2 * (agl_K j : ℝ))^d
          ≤ d * ((agl_K (j + 1) : ℝ))^(d-1) := by
        have hpow := boxSV_pow_sub_pow_le (2 * (agl_K j : ℝ) + 1) (2 * (agl_K j : ℝ))
          (by positivity) (by linarith) d
        rw [show (2 * (agl_K j : ℝ) + 1) - 2 * (agl_K j : ℝ) = 1 by ring, one_mul] at hpow
        rw [hKsuccR]; linarith [hpow]
      have hEsuccpos : (0:ℝ) < ((agl_K (j + 1) : ℝ))^d := by
        have : (0:ℝ) < (agl_K (j + 1) : ℝ) := by exact_mod_cast (agl_K_pos (j+1))
        positivity
      rw [div_le_iff₀ hEsuccpos]
      
      have habs : |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d|
          = ((agl_K (j + 1) : ℝ))^d - (2 * (agl_K j : ℝ))^d := by
        rw [h2d, abs_sub_comm, abs_of_nonneg]
        have : (2 * (agl_K j : ℝ))^d ≤ ((agl_K (j + 1) : ℝ))^d := by
          apply pow_le_pow_left₀ (by positivity)
          rw [hKsuccR]; linarith
        linarith
      rw [habs]
      
      have hKge : (2:ℝ)^j ≤ (agl_K (j + 1) : ℝ) := by
        have hnat : (2:ℕ)^j ≤ agl_K (j+1) := by
          unfold agl_K
          have hstep : 2^j + 1 ≤ 2^(j+1+1) := by
            calc 2^j + 1 ≤ 2^j + 2^j := by have := Nat.one_le_two_pow (n := j); omega
              _ = 2^(j+1) := by ring
              _ ≤ 2^(j+1+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        exact_mod_cast hnat
      have hdfac : (d:ℝ) * ((agl_K (j + 1) : ℝ))^(d-1)
          ≤ (d:ℝ) * (1/2)^j * ((agl_K (j + 1) : ℝ))^d := by
        rw [show ((agl_K (j + 1) : ℝ))^d = ((agl_K (j + 1) : ℝ))^(d-1) * (agl_K (j + 1) : ℝ) by
          rw [← pow_succ]; congr 1; omega]
        have hpow1 : (0:ℝ) ≤ ((agl_K (j + 1) : ℝ))^(d-1) := by positivity
        have hhalf : (1:ℝ) ≤ (1/2)^j * (agl_K (j + 1) : ℝ) := by
          have h2jpos : (0:ℝ) < (2:ℝ)^j := by positivity
          have hhalfpow : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by rw [one_div, inv_pow]
          rw [hhalfpow]
          calc (1:ℝ) = (2:ℝ)^j * ((2:ℝ)^j)⁻¹ := (mul_inv_cancel₀ h2jpos.ne').symm
            _ ≤ (agl_K (j + 1) : ℝ) * ((2:ℝ)^j)⁻¹ := by
                apply mul_le_mul_of_nonneg_right hKge (by positivity)
            _ = ((2:ℝ)^j)⁻¹ * (agl_K (j + 1) : ℝ) := by ring
        have hdK : (0:ℝ) ≤ (d:ℝ) * ((agl_K (j + 1) : ℝ))^(d-1) :=
          mul_nonneg (Nat.cast_nonneg _) hpow1
        nlinarith [hdK, hhalf, mul_nonneg hdK (by linarith [hhalf] : (0:ℝ) ≤ (1/2)^j * (agl_K (j + 1) : ℝ) - 1)]
      calc ((agl_K (j + 1) : ℝ))^d - (2 * (agl_K j : ℝ))^d
          ≤ d * ((agl_K (j + 1) : ℝ))^(d-1) := hle
        _ ≤ (d:ℝ) * (1/2)^j * ((agl_K (j + 1) : ℝ))^d := hdfac
  · intro j
    have : (0:ℝ) ≤ |(2 : ℝ) ^ d * ((agl_K j : ℝ)) ^ d - ((agl_K (j + 1) : ℝ)) ^ d| * c :=
      mul_nonneg (abs_nonneg _) hc
    simpa using this
  · intro j; exact le_refl _














































theorem agl_residue_remark : True := trivial

end FK

end StatMech
