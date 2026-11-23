/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ShapleyValue
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MathlibExt.GameTheory.BondarevaShapleyWanted

/-! # Bondareva-Shapley theorem -/

open Finset
open MathlibExt.GameTheory.ShapleyValue

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- **Core allocation.** A payoff vector $x \colon N \to \mathbb{R}$ is a core allocation of a
cooperative game $v$ on a finite set $N$ of players if it is efficient,
$\sum_{i \in N} x_i = v(N)$, and coalitionally rational, $v(S) \le \sum_{i \in S} x_i$ for every
coalition $S \subseteq N$. -/
def IsCoreAllocation (v : CoopGame Player) (x : Player → ℝ) : Prop :=
  (∑ i : Player, x i = v.charFun Set.univ) ∧
    ∀ S : Finset Player, v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i

/-- **Balanced cooperative game.** A cooperative game $v$ on a finite set $N$ of players is
balanced if for every family of real weights $(\lambda_S)_{S \subseteq N}$ with $\lambda_S \ge 0$
for every coalition $S \subseteq N$ and $\sum_{S \subseteq N,\, i \in S} \lambda_S = 1$ for every
player $i \in N$, one has $\sum_{S \subseteq N} \lambda_S \, v(S) \le v(N)$. -/
def IsBalanced (v : CoopGame Player) : Prop :=
  ∀ lam : Finset Player → ℝ,
    (∀ S, 0 ≤ lam S) →
    (∀ i : Player, ∑ S ∈ (Finset.univ.filter fun S => i ∈ S), lam S = 1) →
    ∑ S : Finset Player, lam S * v.charFun (S : Set Player) ≤ v.charFun Set.univ

/-- ε-approximate core from balancedness, via Hahn–Banach separation. -/
private theorem approx_core_exists
    {Player : Type*} [Fintype Player] [DecidableEq Player]
    (v : CoopGame Player) (hbal : IsBalanced v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Player → ℝ, (∀ S : Finset Player, v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i)
      ∧ ∑ i : Player, x i < v.charFun Set.univ + ε := by
  classical
  have hv0' : v.charFun (((∅ : Finset Player)) : Set Player) = 0 := by
    rw [Finset.coe_empty]
    exact v.empty
  set E := (Player → ℝ) × ℝ with hE
  set g : Option (Finset Player) → E := fun o => match o with
    | some S => ((fun j => if j ∈ S then (1 : ℝ) else 0),
        v.charFun (S : Set Player) - (if S = ∅ then 1 else 0))
    | none => ((fun _ => (-1 : ℝ)), -(v.charFun Set.univ + ε)) with hg
  set K : Set E := convexHull ℝ (Set.range g) with hK
  have hKconv : Convex ℝ K := convex_convexHull ℝ _
  have hKclosed : IsClosed K := by
    apply Set.Finite.isClosed_convexHull
    exact Set.finite_range g
  have h0notin : (0 : E) ∉ K := by
    intro h0mem
    rw [hK, convexHull_range_eq_exists_affineCombination] at h0mem
    obtain ⟨s, w, hnn, hsum1, haff⟩ := h0mem
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum1] at haff
    set W : Option (Finset Player) → ℝ := fun o => if o ∈ s then w o else 0 with hW
    have hWnn : ∀ o, 0 ≤ W o := by
      intro o
      simp only [hW]
      by_cases h : o ∈ s
      · simp [h, hnn o h]
      · simp [h]
    have hWsum : ∑ o : Option (Finset Player), W o = 1 := by
      have h0 : ∀ o ∈ (Finset.univ : Finset (Option (Finset Player))), o ∉ s → W o = 0 := by
        intro o _ hos
        simp [hW, hos]
      have hsub := Finset.sum_subset (Finset.subset_univ s) (f := W) h0
      have hcongr : (∑ o ∈ s, W o) = ∑ o ∈ s, w o := by
        apply Finset.sum_congr rfl
        intro o h
        simp [hW, h]
      have : (∑ o : Option (Finset Player), W o) = ∑ o ∈ s, w o := by
        rw [← hcongr]
        exact hsub.symm
      rw [this]
      exact hsum1
    have hWcomb : ∑ o : Option (Finset Player), W o • g o = 0 := by
      have h0 : ∀ o ∈ (Finset.univ : Finset (Option (Finset Player))),
          o ∉ s → W o • g o = 0 := by
        intro o _ hos
        simp [hW, hos]
      have hsub := Finset.sum_subset (Finset.subset_univ s) (f := fun o => W o • g o) h0
      have hcongr : (∑ o ∈ s, W o • g o) = ∑ o ∈ s, w o • g o := by
        apply Finset.sum_congr rfl
        intro o h
        simp [hW, h]
      have : (∑ o : Option (Finset Player), W o • g o) = ∑ o ∈ s, w o • g o := by
        rw [← hcongr]
        exact hsub.symm
      rw [this]
      exact haff
    have hg_some1 : ∀ (S : Finset Player) (j : Player),
        (g (some S)).1 j = (if j ∈ S then (1 : ℝ) else 0) := by
      intro S j
      simp [hg]
    have hg_some2 : ∀ S : Finset Player,
        (g (some S)).2 = v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0) := by
      intro S
      simp [hg]
    have hg_none1 : ∀ j : Player, (g none).1 j = (-1 : ℝ) := by
      intro j
      simp [hg]
    have hg_none2 : (g none).2 = -(v.charFun Set.univ + ε) := by
      simp [hg]
    have hcoord1 : ∀ j : Player,
        ∑ S ∈ Finset.univ.filter (fun S => j ∈ S), W (some S) = W none := by
      intro j
      have h0 : ((∑ o : Option (Finset Player), W o • g o).1) j = 0 := by
        rw [hWcomb]
        rfl
      have hLHS : ((∑ o : Option (Finset Player), W o • g o).1) j
          = ∑ o : Option (Finset Player), W o * (g o).1 j := by
        rw [Prod.fst_sum]
        rw [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro o _
        rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      rw [hLHS] at h0
      have hsplit := Fintype.sum_option (fun o => W o * (g o).1 j)
      rw [hsplit] at h0
      rw [hg_none1 j] at h0
      have hsome : (∑ S : Finset Player, W (some S) * (g (some S)).1 j)
          = ∑ S ∈ Finset.univ.filter (fun S => j ∈ S), W (some S) := by
        have e : ∀ S : Finset Player, W (some S) * (g (some S)).1 j
            = (if j ∈ S then W (some S) else 0) := by
          intro S
          rw [hg_some1 S j]
          by_cases h : j ∈ S
          · simp [h]
          · simp [h]
        rw [Finset.sum_congr rfl (fun S _ => e S)]
        rw [← Finset.sum_filter]
      rw [hsome] at h0
      have : W none * (-1 : ℝ) + ∑ S ∈ Finset.univ.filter (fun S => j ∈ S), W (some S) = 0 := h0
      linarith
    have hcoord2 : (∑ S : Finset Player, W (some S)
          * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)))
        + W none * (-(v.charFun Set.univ + ε)) = 0 := by
      have h0 : (∑ o : Option (Finset Player), W o • g o).2 = 0 := by
        rw [hWcomb]
        rfl
      have hLHS : (∑ o : Option (Finset Player), W o • g o).2
          = ∑ o : Option (Finset Player), W o * (g o).2 := by
        rw [Prod.snd_sum]
        apply Finset.sum_congr rfl
        intro o _
        rw [Prod.smul_snd, smul_eq_mul]
      rw [hLHS] at h0
      have hsplit := Fintype.sum_option (fun o => W o * (g o).2)
      rw [hsplit, hg_none2] at h0
      have hsome : (∑ S : Finset Player, W (some S) * (g (some S)).2)
          = ∑ S : Finset Player, W (some S)
            * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [hg_some2 S]
      rw [hsome] at h0
      linarith
    have hWnone_nn : 0 ≤ W none := hWnn none
    by_cases hWnone0 : W none = 0
    · have hWsome0 : ∀ S : Finset Player, S ≠ ∅ → W (some S) = 0 := by
        intro S hne
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hsum0 : ∑ T ∈ Finset.univ.filter (fun T => j ∈ T), W (some T) = 0 := by
          rw [hcoord1 j, hWnone0]
        have hnn_f : ∀ T ∈ Finset.univ.filter (fun T => j ∈ T), 0 ≤ W (some T) := by
          intro T _
          exact hWnn (some T)
        have hall0 := (Finset.sum_eq_zero_iff_of_nonneg hnn_f).mp hsum0
        have hmem : S ∈ Finset.univ.filter (fun T => j ∈ T) := by
          simp [hj]
        exact hall0 S hmem
      have hsum_opt := Fintype.sum_option (fun o => W o)
      rw [hWsum] at hsum_opt
      have hSsum : (∑ S : Finset Player, W (some S)) = W (some ∅) := by
        apply Finset.sum_eq_single ∅
        · intro S _ hne
          exact hWsome0 S hne
        · simp
      have hWempty : W (some ∅) = 1 := by
        rw [hSsum] at hsum_opt
        linarith
      have hSsum2 : (∑ S : Finset Player, W (some S)
            * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)))
          = W (some ∅) * (v.charFun (((∅ : Finset Player)) : Set Player) - 1) := by
        apply Finset.sum_eq_single ∅
        · intro S _ hne
          rw [hWsome0 S hne]
          simp
        · simp
      rw [hSsum2, hv0'] at hcoord2
      rw [hWempty, hWnone0] at hcoord2
      norm_num at hcoord2
    · have hpos : 0 < W none := lt_of_le_of_ne' hWnone_nn hWnone0
      set lam : Finset Player → ℝ := fun S => W (some S) / W none with hlam
      have hlam_nn : ∀ S, 0 ≤ lam S := by
        intro S
        simp only [hlam]
        exact div_nonneg (hWnn (some S)) (le_of_lt hpos)
      have hlam_bal : ∀ i : Player,
          ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), lam S = 1 := by
        intro i
        have h := hcoord1 i
        have hdiv : (∑ S ∈ Finset.univ.filter (fun S => i ∈ S), W (some S)) / W none
            = ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), lam S := by
          simp only [hlam]
          rw [Finset.sum_div]
        rw [h, div_self hWnone0] at hdiv
        exact hdiv.symm
      have hle := hbal lam hlam_nn hlam_bal
      have hdiv2 : (∑ S : Finset Player, lam S
            * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)))
          + (-(v.charFun Set.univ + ε)) = 0 := by
        have h1 : ((∑ S : Finset Player, W (some S)
              * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)))
            + W none * (-(v.charFun Set.univ + ε))) / W none = 0 / W none := by
          rw [hcoord2]
        rw [add_div, mul_div_cancel_left₀ _ hWnone0] at h1
        simp only [zero_div] at h1
        have h2 : (∑ S : Finset Player, W (some S)
              * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0))) / W none
            = ∑ S : Finset Player, lam S
              * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro S _
          simp only [hlam]
          rw [div_mul_eq_mul_div]
        rw [h2] at h1
        exact h1
      have hsplit : (∑ S : Finset Player, lam S
            * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)))
          = (∑ S : Finset Player, lam S * v.charFun (S : Set Player)) - lam ∅ := by
        have e : ∀ S : Finset Player, lam S
              * (v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0))
            = lam S * v.charFun (S : Set Player) - (if S = ∅ then lam S else 0) := by
          intro S
          by_cases h : S = ∅
          · simp [h]; ring
          · simp [h]
        rw [Finset.sum_congr rfl (fun S _ => e S)]
        rw [Finset.sum_sub_distrib]
        have hsingle : (∑ S : Finset Player, (if S = ∅ then lam S else 0)) = lam ∅ := by
          have : (∑ S : Finset Player, (if S = ∅ then lam S else 0))
              = ∑ S ∈ (Finset.univ : Finset (Finset Player)), (if S = ∅ then lam S else 0) := rfl
          rw [this]
          simp
        rw [hsingle]
      rw [hsplit] at hdiv2
      have hlam_empty_nn : 0 ≤ lam ∅ := hlam_nn ∅
      linarith
  obtain ⟨f, u, hfu, hfK⟩ :=
    geometric_hahn_banach_point_closed hKconv hKclosed h0notin
  have hf0 : f (0 : E) = 0 := map_zero f
  have hu_pos : 0 < u := by
    rw [← hf0]
    exact hfu
  have hfg : ∀ o : Option (Finset Player), u < f (g o) := by
    intro o
    apply hfK
    rw [hK]
    apply subset_convexHull
    exact Set.mem_range_self o
  have hfg_pos : ∀ o : Option (Finset Player), 0 < f (g o) := by
    intro o
    linarith [hu_pos, hfg o]
  set a : Player → ℝ := fun j =>
    f (((fun j' => if j = j' then (1 : ℝ) else 0), (0 : ℝ))) with ha
  set c : ℝ := f ((0 : Player → ℝ), 1) with hc
  have hf_decomp : ∀ (y : Player → ℝ) (t : ℝ),
      f (y, t) = (∑ j : Player, y j * a j) + t * c := by
    intro y t
    have hpair : (y, t) = LinearMap.inl ℝ (Player → ℝ) ℝ y
        + LinearMap.inr ℝ (Player → ℝ) ℝ t := by
      simp [LinearMap.inl_apply, LinearMap.inr_apply]
    rw [hpair, map_add]
    congr 1
    · have hy : y = ∑ j : Player, y j • (fun j' => if j = j' then (1 : ℝ) else 0) :=
        pi_eq_sum_univ y
      have hinl : LinearMap.inl ℝ (Player → ℝ) ℝ y
          = ∑ j : Player, y j • LinearMap.inl ℝ (Player → ℝ) ℝ
            ((fun j' => if j = j' then (1 : ℝ) else 0)) := by
        conv_lhs => rw [hy, map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
      rw [hinl, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
      simp [LinearMap.inl_apply, ha]
    · have hinr_eq : LinearMap.inr ℝ (Player → ℝ) ℝ t
          = t • ((0 : Player → ℝ), (1 : ℝ)) := by
        rw [LinearMap.inr_apply, Prod.smul_mk]
        simp
      rw [hinr_eq, map_smul, smul_eq_mul, ← hc]
  have hfg_empty := hfg_pos (some ∅)
  have hg_empty_eq : g (some ∅) = ((fun j => if j ∈ (∅ : Finset Player) then (1 : ℝ) else 0),
      v.charFun (((∅ : Finset Player)) : Set Player)
        - (if (∅ : Finset Player) = ∅ then (1 : ℝ) else 0)) := rfl
  have hc_neg : c < 0 := by
    rw [hg_empty_eq, hf_decomp] at hfg_empty
    simp [v.empty] at hfg_empty
    linarith
  have hnegc_pos : 0 < -c := by linarith
  set x : Player → ℝ := fun j => a j / (-c) with hx
  refine ⟨x, ?_, ?_⟩
  · intro S
    by_cases hS : S = ∅
    · subst hS
      simp [v.empty, hx]
    · have hpos := hfg_pos (some S)
      have hgS_eq : g (some S) = ((fun j => if j ∈ S then (1 : ℝ) else 0),
          v.charFun (S : Set Player) - (if S = ∅ then (1 : ℝ) else 0)) := rfl
      rw [hgS_eq, hf_decomp] at hpos
      rw [ite_eq_right hS] at hpos
      have hsum : (∑ j : Player, (if j ∈ S then (1 : ℝ) else 0) * a j)
          = ∑ j ∈ S, a j := by
        have hSS : Finset.univ.filter (fun j => j ∈ S) = S := by
          ext j
          simp
        have hthis : (∑ j : Player, (if j ∈ S then (1 : ℝ) else 0) * a j)
            = ∑ j ∈ Finset.univ.filter (fun j => j ∈ S), (1 : ℝ) * a j := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : j ∈ S <;> simp [h]
        rw [hthis, hSS]
        apply Finset.sum_congr rfl
        intro j _
        rw [one_mul]
      rw [hsum, sub_zero] at hpos
      have hA : (∑ j ∈ S, x j) = (∑ j ∈ S, a j) / (-c) := by
        simp only [hx]
        rw [Finset.sum_div]
      have hcne : c ≠ 0 := ne_of_lt hc_neg
      have hcdiv : c / (-c) = -1 := by
        rw [div_neg, div_self hcne]
      have hposdiv : 0 < ((∑ j ∈ S, a j) + v.charFun (S : Set Player) * c) / (-c) :=
        div_pos hpos hnegc_pos
      rw [add_div, mul_div_assoc, hcdiv, mul_neg, mul_one] at hposdiv
      rw [hA]
      linarith
  · have hpos := hfg_pos none
    have hgN_eq : g none = ((fun _ => (-1 : ℝ)), (-(v.charFun Set.univ + ε))) := rfl
    rw [hgN_eq, hf_decomp] at hpos
    have hsumN : (∑ j : Player, (-1 : ℝ) * a j) = -(∑ j : Player, a j) := by
      rw [← Finset.mul_sum, neg_one_mul]
    rw [hsumN] at hpos
    have hX : (∑ j : Player, x j) = (∑ j : Player, a j) / (-c) := by
      simp only [hx]
      rw [Finset.sum_div]
    have hcne : c ≠ 0 := ne_of_lt hc_neg
    have hcdiv : c / (-c) = -1 := by
      rw [div_neg, div_self hcne]
    have hnegdiv : (-(∑ j : Player, a j)) / (-c)
        = -((∑ j : Player, a j) / (-c)) := by
      rw [neg_div]
    have hneg1 : (-(v.charFun Set.univ + ε)) * (-1) = v.charFun Set.univ + ε := by
      ring
    have hposdiv : 0 < ((-(∑ j : Player, a j)) + (-(v.charFun Set.univ + ε)) * c) / (-c) :=
      div_pos hpos hnegc_pos
    rw [add_div, mul_div_assoc, hcdiv, hneg1, hnegdiv, ← hX] at hposdiv
    linarith

/-- Exact core from ε-approximate cores, via compactness. -/
private theorem exact_core_of_approx
    {Player : Type*} [Fintype Player]
    (v : CoopGame Player)
    (approx : ∀ ε : ℝ, 0 < ε →
      ∃ x : Player → ℝ, (∀ S : Finset Player, v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i)
        ∧ ∑ i : Player, x i < v.charFun Set.univ + ε) :
    ∃ x : Player → ℝ, IsCoreAllocation v x := by
  classical
  obtain ⟨x1, hx1_le, hx1_sum⟩ := approx 1 one_pos
  set F : Set (Player → ℝ) := {x | (∀ S : Finset Player, v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i)
    ∧ ∑ i : Player, x i ≤ ∑ i : Player, x1 i} with hF
  have hx1_mem : x1 ∈ F := ⟨hx1_le, le_rfl⟩
  have hFclosed : IsClosed F := by
    have h1 : IsClosed {x : Player → ℝ | ∀ S : Finset Player,
        v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i} := by
      have : {x : Player → ℝ | ∀ S : Finset Player, v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i}
          = ⋂ S : Finset Player, {x : Player → ℝ | v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i} := by
        ext x
        simp
      rw [this]
      apply isClosed_iInter
      intro S
      apply isClosed_le continuous_const
      apply continuous_finsetSum
      intro i _
      exact continuous_apply i
    have h2 : IsClosed {x : Player → ℝ | ∑ i : Player, x i ≤ ∑ i : Player, x1 i} := by
      apply isClosed_le _ continuous_const
      apply continuous_finsetSum
      intro i _
      exact continuous_apply i
    have hF_eq : F = {x : Player → ℝ | ∀ S : Finset Player,
          v.charFun (S : Set Player) ≤ ∑ i ∈ S, x i}
        ∩ {x : Player → ℝ | ∑ i : Player, x i ≤ ∑ i : Player, x1 i} := by
      ext x
      simp [hF]
    rw [hF_eq]
    exact h1.inter h2
  set lo : Player → ℝ := fun i => v.charFun ({i} : Set Player) with hlo
  set hi : Player → ℝ := fun i =>
    ∑ i : Player, x1 i - ∑ j ∈ Finset.univ.erase i, v.charFun ({j} : Set Player) with hhi
  have hFsub : F ⊆ Set.Icc lo hi := by
    intro x hx
    obtain ⟨hx_le, hx_sum⟩ := hx
    constructor
    · intro i
      simp only [hlo]
      have h := hx_le {i}
      rw [Finset.sum_singleton] at h
      have hcoe : ((({i} : Finset Player)) : Set Player) = ({i} : Set Player) := by
        simp
      rw [hcoe] at h
      exact h
    · intro i
      simp only [hhi]
      have hsplit : ∑ j : Player, x j = x i + ∑ j ∈ Finset.univ.erase i, x j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hge : ∀ j ∈ Finset.univ.erase i,
          v.charFun ({j} : Set Player) ≤ x j := by
        intro j _
        have h := hx_le {j}
        rw [Finset.sum_singleton] at h
        have hcoe : ((({j} : Finset Player)) : Set Player) = ({j} : Set Player) := by
          simp
        rw [hcoe] at h
        exact h
      have hsum_ge : ∑ j ∈ Finset.univ.erase i, v.charFun ({j} : Set Player)
          ≤ ∑ j ∈ Finset.univ.erase i, x j :=
        Finset.sum_le_sum hge
      linarith
  have hFcomp : IsCompact F :=
    IsCompact.of_isClosed_subset isCompact_Icc hFclosed hFsub
  have hcont : ContinuousOn (fun x : Player → ℝ => ∑ i : Player, x i) F := by
    apply Continuous.continuousOn
    apply continuous_finsetSum
    intro i _
    exact continuous_apply i
  obtain ⟨xstar, hxstar_mem, hxstar_min⟩ :=
    hFcomp.exists_isMinOn ⟨x1, hx1_mem⟩ hcont
  obtain ⟨hxstar_le, hxstar_sum_le⟩ := hxstar_mem
  have hge_univ : v.charFun Set.univ ≤ ∑ i : Player, xstar i := by
    have h := hxstar_le Finset.univ
    rw [Finset.coe_univ] at h
    exact h
  have heq : ∑ i : Player, xstar i = v.charFun Set.univ := by
    by_contra hne
    have hlt : v.charFun Set.univ < ∑ i : Player, xstar i :=
      lt_of_le_of_ne hge_univ (Ne.symm hne)
    set ε0 : ℝ := (∑ i : Player, xstar i) - v.charFun Set.univ with hε0
    have hε0_pos : 0 < ε0 := by simp [hε0]; linarith
    obtain ⟨x', hx'_le, hx'_sum⟩ := approx ε0 hε0_pos
    have hx'_mem : x' ∈ F := by
      constructor
      · exact hx'_le
      · simp only [hε0] at hx'_sum
        linarith [hxstar_sum_le]
    have hle_min : (∑ i : Player, xstar i) ≤ (∑ i : Player, x' i) := hxstar_min hx'_mem
    simp only [hε0] at hx'_sum
    linarith
  exact ⟨xstar, heq, hxstar_le⟩

/--
**Bondareva–Shapley theorem.** Let $v$ be a cooperative game with transferable utility on a
finite set $N$ of players. Then $v$ has a core allocation $x \colon N \to \mathbb{R}$, that is,
the core of $v$ is nonempty, if and only if $v$ is balanced.

Source: O. N. Bondareva, Probl. Kibernet. 10 (1963), 119-139; L. S. Shapley, Naval Res. Log. Quart.
14 (1967), 453-460, DOI 10.1002/nav.3800140404.

Proves `Wanted` entry `bondareva_shapley`.
-/
theorem bondareva_shapley
    {Player : Type*} [Fintype Player] [DecidableEq Player]
    (v : CoopGame Player) :
    (∃ x : Player → ℝ, IsCoreAllocation v x) ↔ IsBalanced v := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hsum, hle⟩ := hx
    intro lam hnn hbal
    have hterm : ∀ S ∈ (Finset.univ : Finset (Finset Player)),
        lam S * v.charFun (S : Set Player) ≤ lam S * (∑ i ∈ S, x i) := by
      intro S _
      exact mul_le_mul_of_nonneg_left (hle S) (hnn S)
    have hle_sum : ∑ S : Finset Player, lam S * v.charFun (S : Set Player)
        ≤ ∑ S : Finset Player, lam S * (∑ i ∈ S, x i) := by
      apply Finset.sum_le_sum
      intro S hS
      exact hterm S hS
    have hident : (∑ S : Finset Player, lam S * (∑ i ∈ S, x i))
        = ∑ i : Player, x i * (∑ S ∈ (Finset.univ.filter fun S => i ∈ S), lam S) := by
      have step1 : ∀ S ∈ (Finset.univ : Finset (Finset Player)), lam S * (∑ i ∈ S, x i)
          = ∑ i ∈ (Finset.univ : Finset Player), (if i ∈ S then lam S * x i else 0) := by
        intro S _
        rw [Finset.mul_sum]
        have hSS : Finset.univ.filter (fun i => i ∈ S) = S := by
          ext i
          simp
        have hcongr : (∑ i ∈ S, lam S * x i)
            = (∑ i ∈ Finset.univ.filter (fun i => i ∈ S), lam S * x i) := by
          rw [hSS]
        rw [hcongr]
        rw [Finset.sum_filter]
      have e1 : (∑ S : Finset Player, lam S * (∑ i ∈ S, x i))
          = ∑ S ∈ (Finset.univ : Finset (Finset Player)),
            ∑ i ∈ (Finset.univ : Finset Player), (if i ∈ S then lam S * x i else 0) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact step1 S hS
      rw [e1]
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      apply Finset.sum_congr rfl
      intro i _
      have h1 : (∑ S ∈ (Finset.univ : Finset (Finset Player)),
            (if i ∈ S then lam S * x i else 0))
          = ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), lam S * x i := by
        rw [Finset.sum_filter]
      have h2 : x i * (∑ S ∈ Finset.univ.filter (fun S => i ∈ S), lam S)
          = ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), x i * lam S := by
        rw [Finset.mul_sum]
      rw [h1, h2]
      apply Finset.sum_congr rfl
      intro S _
      ring
    rw [hident] at hle_sum
    have hbal_rw : (∑ i : Player, x i * (∑ S ∈ (Finset.univ.filter fun S => i ∈ S), lam S))
        = ∑ i : Player, x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hbal i, mul_one]
    rw [hbal_rw, hsum] at hle_sum
    exact hle_sum
  · intro hbal
    apply exact_core_of_approx v
    intro ε hε
    exact approx_core_exists v hbal ε hε

end MathlibExt.GameTheory.BondarevaShapleyWanted
end
