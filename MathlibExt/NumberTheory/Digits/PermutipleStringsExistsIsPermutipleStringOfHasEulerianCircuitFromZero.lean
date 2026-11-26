/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.PermutipleStrings
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Eulerian circuits through zero yield permutiple strings (Holt)

This module proves that an Eulerian circuit through the zero state of the multi-image
union of mother-graph cycles yields a permutiple string.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).
-/

namespace MetaMathlibExt

@[expose] public section

/-- A list over the mapped multiset lifts to a list over the original multiset. -/
private theorem exists_list_of_map_eq {M : Multiset (ℕ × ℕ)} {w : List (ℕ × ℕ)}
    {f : (ℕ × ℕ) → (ℕ × ℕ)} (h : M.map f = (w : Multiset (ℕ × ℕ))) :
    ∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = M ∧ s.map f = w := by
  induction w generalizing M with
  | nil =>
    have hM : M = 0 := by
      have h0 : M.map f = 0 := by simpa using h
      exact Multiset.map_eq_zero.mp h0
    exact ⟨[], by simp [hM], rfl⟩
  | cons y w ih =>
    have hcons : M.map f = y ::ₘ (w : Multiset (ℕ × ℕ)) := by
      simpa [Multiset.cons_coe] using h
    obtain ⟨a, ha, hfa, hrest⟩ := (Multiset.map_eq_cons f M _ y).mpr hcons
    obtain ⟨s', hs', hmap'⟩ := ih hrest
    refine ⟨a :: s', ?_, by simp [hfa, hmap']⟩
    rw [(Multiset.cons_coe a s').symm, hs', Multiset.cons_erase ha]

/-- A chained list of transitions yields a run of the Hoey-Sloane machine. -/
private theorem run_of_chain {n b : ℕ} {s : List (ℕ × ℕ)} {w : List (ℕ × ℕ)}
    {c c' : ℕ} (hmap : s.map (hoeySloaneTransition n b) = w)
    (hchain : w.IsChain (fun x y => x.2 = y.1))
    (hmem :
      ∀ e ∈ s, IsHoeySloaneStep n b ((hoeySloaneTransition n b e).1)
        ((hoeySloaneTransition n b e).2) e)
    (hhead : w.head?.map Prod.fst = some c)
    (hlast : w.getLast?.map Prod.snd = some c') :
    IsHoeySloaneRun n b c s c' := by
  induction s generalizing w c c' with
  | nil =>
    have hw : w = [] := by simpa using hmap.symm
    subst hw
    cases hhead
  | cons e rest ih =>
    have hmap' : w = (hoeySloaneTransition n b e) :: rest.map (hoeySloaneTransition n b) := by
      simpa using hmap.symm
    subst hmap'
    cases rest with
    | nil =>
      have hc : c = ((hoeySloaneTransition n b e).1) := by simpa using hhead.symm
      have hc' : c' = ((hoeySloaneTransition n b e).2) := by simpa using hlast.symm
      subst hc
      subst hc'
      exact ⟨_, hmem e (by simp), rfl⟩
    | cons e2 rest' =>
      simp only [List.map_cons, List.isChain_cons_cons] at hchain
      obtain ⟨hlink, hchain'⟩ := hchain
      have hhead' : ((e2 :: rest').map (hoeySloaneTransition n b)).head?.map Prod.fst =
          some ((hoeySloaneTransition n b e).2) := by
        simp [hlink.symm]
      have hlast' :
          ((e2 :: rest').map (hoeySloaneTransition n b)).getLast?.map Prod.snd =
            some c' := by
        simpa using hlast
      have hmem' : ∀ e_1 ∈ (e2 :: rest'),
          IsHoeySloaneStep n b ((hoeySloaneTransition n b e_1).1)
            ((hoeySloaneTransition n b e_1).2) e_1 := by
        intro e_1 he_1
        exact hmem e_1 (by simp [he_1])
      have ihrun := ih rfl hchain' hmem' hhead' hlast'
      have hc : c = ((hoeySloaneTransition n b e).1) := by simpa using hhead.symm
      subst hc
      exact ⟨_, hmem e (by simp), ihrun⟩

/-- First projections of cycle edges give the vertex list as a multiset. -/
private theorem fst_map_cycleEdges (vs : List ℕ) :
    ((cycleEdges vs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map Prod.fst = (vs : Multiset ℕ) := by
  have hlen : vs.length ≤ (vs.rotate 1).length := by simp
  have hlist : (cycleEdges vs).map Prod.fst = vs := List.map_fst_zip hlen
  have hcoe : (((cycleEdges vs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map Prod.fst : Multiset ℕ) =
      (((cycleEdges vs).map Prod.fst : List ℕ) : Multiset ℕ) := rfl
  rw [hcoe, hlist]

/-- Second projections of cycle edges give the vertex list as a multiset. -/
private theorem snd_map_cycleEdges (vs : List ℕ) :
    ((cycleEdges vs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map Prod.snd = (vs : Multiset ℕ) := by
  have hlen : (vs.rotate 1).length ≤ vs.length := by simp
  have hlist : (cycleEdges vs).map Prod.snd = vs.rotate 1 := List.map_snd_zip hlen
  have hcoe : (((cycleEdges vs : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map Prod.snd : Multiset ℕ) =
      (((cycleEdges vs).map Prod.snd : List ℕ) : Multiset ℕ) := rfl
  rw [hcoe, hlist]
  exact Multiset.coe_eq_coe.mpr (List.rotate_perm vs 1)

/-- First and second projections of a cycle union agree as multisets. -/
private theorem fst_eq_snd_cycleUnion (cs : Multiset (List ℕ)) :
    (cycleUnion cs).map Prod.fst = (cycleUnion cs).map Prod.snd := by
  rw [cycleUnion, Multiset.map_bind, Multiset.map_bind]
  apply Multiset.bind_congr
  intro vs _
  rw [fst_map_cycleEdges, snd_map_cycleEdges]

/-- Every edge of a cycle union is a mother-graph edge. -/
private theorem mother_of_mem_cycleUnion {n b : ℕ} {cs : Multiset (List ℕ)}
    (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs) {e : ℕ × ℕ} (he : e ∈ cycleUnion cs) :
    IsMotherGraphEdge n b e.1 e.2 := by
  rw [cycleUnion, Multiset.mem_bind] at he
  obtain ⟨vs, hvs, hevs⟩ := he
  have hcycle := hcs vs hvs
  rw [Multiset.mem_coe] at hevs
  exact hcycle.2.2 e hevs

/-- Permutation-equivalent enumerations differ by a permutation of indices. -/
private theorem exists_perm_of_ofFn_perm {n : ℕ} (f g : Fin n → ℕ)
    (h : List.Perm (List.ofFn f) (List.ofFn g)) :
    ∃ σ : Equiv.Perm (Fin n), g = f ∘ σ := by
  induction n with
  | zero =>
    refine ⟨1, ?_⟩
    funext i
    exact i.elim0
  | succ n ih =>
    have hmem : g 0 ∈ List.ofFn f := h.mem_iff.mpr (List.mem_ofFn.mpr ⟨0, rfl⟩)
    obtain ⟨i0, hi0⟩ := List.mem_ofFn.mp hmem
    let σ₁ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 i0
    let f₁ : Fin (n + 1) → ℕ := f ∘ σ₁
    have hf₁0 : f₁ 0 = g 0 := by
      simp [f₁, σ₁, hi0]
    have hperm1 : List.Perm (List.ofFn f₁) (List.ofFn f) := Equiv.Perm.ofFn_comp_perm σ₁ f
    have hperm2 : List.Perm (List.ofFn f₁) (List.ofFn g) := hperm1.trans h
    rw [List.ofFn_succ (f := f₁), List.ofFn_succ (f := g)] at hperm2
    rw [hf₁0] at hperm2
    have htail : List.Perm (List.ofFn (fun i : Fin n => f₁ i.succ))
        (List.ofFn (fun i : Fin n => g i.succ)) :=
      List.Perm.cons_inv hperm2
    obtain ⟨τ, hτ⟩ := ih _ _ htail
    let σ₂ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, τ)
    have hσ₂0 : σ₂ 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
    have hσ₂succ (x : Fin n) : σ₂ x.succ = (τ x).succ := by
      simp [σ₂]
    refine ⟨σ₁ * σ₂, ?_⟩
    funext j
    cases j using Fin.cases with
    | zero =>
      change g 0 = f ((σ₁ * σ₂) 0)
      rw [Equiv.Perm.mul_apply, hσ₂0]
      exact hf₁0.symm
    | succ x =>
      change g x.succ = f ((σ₁ * σ₂) x.succ)
      rw [Equiv.Perm.mul_apply, hσ₂succ]
      have hτx : g x.succ = f₁ (τ x).succ := congrFun hτ x
      exact hτx

/-- Weighted digit differences of a run, least significant first. -/
private def weightSum (n b : ℕ) : List (ℕ × ℕ) → ℤ
  | [] => 0
  | e :: rest => ((n : ℤ) * e.2 - e.1) + (b : ℤ) * weightSum n b rest

/-- A run from `c` to `c'` accounts for the weighted digit differences. -/
private theorem run_weightSum {n b : ℕ} {s : List (ℕ × ℕ)} {c c' : ℕ}
    (h : IsHoeySloaneRun n b c s c') :
    (c' : ℤ) * (b : ℤ) ^ s.length - (c : ℤ) = weightSum n b s := by
  induction s generalizing c c' with
  | nil =>
    simp only [IsHoeySloaneRun] at h
    subst h
    simp [weightSum]
  | cons e rest ih =>
    simp only [IsHoeySloaneRun] at h
    obtain ⟨c₂, hstep, hrun⟩ := h
    have ihrest := ih hrun
    have heq := hstep.2.2.2
    simp only [weightSum, List.length_cons]
    have hpow : (b : ℤ) ^ (rest.length + 1) = (b : ℤ) * (b : ℤ) ^ rest.length := pow_succ' _ _
    rw [hpow]
    linear_combination (b : ℤ) * ihrest + heq

open scoped BigOperators in
/-- The weighted sum of an enumerated string is the weighted Fin sum. -/
private theorem weightSum_ofFn {k : ℕ} (n b : ℕ) (d dh : Fin (k + 1) → ℕ) :
    weightSum n b (List.ofFn fun j => (d j, dh j)) =
      ∑ j, (((n : ℤ) * dh j - (d j : ℤ)) * (b : ℤ) ^ (j : ℕ)) := by
  induction k with
  | zero =>
    rw [List.ofFn_succ]
    simp [weightSum]
  | succ k ih =>
    rw [List.ofFn_succ]
    simp only [weightSum]
    rw [ih (fun i => d i.succ) (fun i => dh i.succ)]
    rw [Fin.sum_univ_succ (fun j => (((n : ℤ) * dh j - (d j : ℤ)) * (b : ℤ) ^ (j : ℕ)))]
    simp only [Fin.val_zero, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hval : ((i.succ : Fin (k + 2)) : ℕ) = (i : ℕ) + 1 := Fin.val_succ i
    rw [hval, pow_succ']
    ring

open scoped BigOperators in
/-- A zero weighted sum gives the permutiple value equation. -/
private theorem sum_eq_of_weight_zero {k n b : ℕ} (d dh : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) (hσ : dh = d ∘ σ)
    (h0 : ∑ j, (((n : ℤ) * dh j - (d j : ℤ)) * (b : ℤ) ^ (j : ℕ)) = 0) :
    ∑ j, d j * b ^ (j : ℕ) = n * ∑ j, d (σ j) * b ^ (j : ℕ) := by
  have h1 : ∑ j, ((d j : ℤ) * (b : ℤ) ^ (j : ℕ)) =
      (n : ℤ) * ∑ j, ((dh j : ℤ) * (b : ℤ) ^ (j : ℕ)) := by
    have hsub : ∑ j, (((n : ℤ) * dh j - (d j : ℤ)) * (b : ℤ) ^ (j : ℕ)) =
        ∑ j, ((n : ℤ) * ((dh j : ℤ) * (b : ℤ) ^ (j : ℕ))) -
          ∑ j, ((d j : ℤ) * (b : ℤ) ^ (j : ℕ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h0] at hsub
    have hmul : ∑ j, ((n : ℤ) * ((dh j : ℤ) * (b : ℤ) ^ (j : ℕ))) =
        (n : ℤ) * ∑ j, ((dh j : ℤ) * (b : ℤ) ^ (j : ℕ)) :=
      (Finset.mul_sum _ _ _).symm
    rw [hmul] at hsub
    linear_combination hsub
  have hcast : ((∑ j, d j * b ^ (j : ℕ) : ℕ) : ℤ) =
      ∑ j, ((d j : ℤ) * (b : ℤ) ^ (j : ℕ)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul, Nat.cast_pow]
  have hcast2 : ((∑ j, d (σ j) * b ^ (j : ℕ) : ℕ) : ℤ) =
      ∑ j, (((d ∘ σ) j : ℤ) * (b : ℤ) ^ (j : ℕ)) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul, Nat.cast_pow]
    rfl
  have hσ' : (fun j => ((dh j : ℤ) * (b : ℤ) ^ (j : ℕ))) =
      fun j => (((d ∘ σ) j : ℤ) * (b : ℤ) ^ (j : ℕ)) := by
    rw [hσ]
  rw [hσ'] at h1
  have h1' : ((∑ j, d j * b ^ (j : ℕ) : ℕ) : ℤ) =
      ((n * ∑ j, d (σ j) * b ^ (j : ℕ) : ℕ) : ℤ) := by
    rw [hcast, Nat.cast_mul, hcast2]
    exact h1
  exact Nat.cast_injective h1'

/-- **Eulerian circuits through zero yield permutiple strings.** Let $1 < n < b$ and let $I$
be a multiset of cycles of the $(n, b)$-mother graph, with multiset union of cycle edges
$C_I$ and multi-image union $\Delta_I$. If $\Delta_I$ has an Eulerian circuit beginning
and ending at the zero state, then there is an $(n, b)$-permutiple string $s$ whose
multiset of entries is $C_I$.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 7 (`integers-2025-A111-thm-7`). -/
public theorem exists_isPermutipleString_of_hasEulerianCircuitFromZero (n b : ℕ) (hn : 1 < n)
    (hnb : n < b) (cs : Multiset (List ℕ)) (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs)
    (h : HasEulerianCircuitFromZero (multiImageUnion n b cs)) :
    ∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = cycleUnion cs ∧ IsPermutipleString n b s := by
  obtain ⟨w, hw_ne, hw_eq, hw_chain, hw_head, hw_last⟩ := h
  have hmap_eq : (cycleUnion cs).map (hoeySloaneTransition n b) = ↑w := by
    simpa [multiImageUnion] using hw_eq.symm
  obtain ⟨s, hs_eq, hs_map⟩ := exists_list_of_map_eq hmap_eq
  have hs_ne : s ≠ [] := by
    intro hs0
    subst hs0
    have hnil : w = [] := by simpa using hs_map.symm
    exact hw_ne hnil
  have hmother : ∀ e ∈ s, IsMotherGraphEdge n b e.1 e.2 := by
    intro e he
    have heM : e ∈ (s : Multiset (ℕ × ℕ)) := Multiset.mem_coe.mpr he
    rw [hs_eq] at heM
    exact mother_of_mem_cycleUnion hcs heM
  have hsteps :
      ∀ e ∈ s, IsHoeySloaneStep n b ((hoeySloaneTransition n b e).1)
        ((hoeySloaneTransition n b e).2) e := by
    intro e he
    exact isHoeySloaneStep_hoeySloaneTransition n b hn hnb e (hmother e he)
  have hrun : IsHoeySloaneRun n b 0 s 0 :=
    run_of_chain hs_map hw_chain hsteps hw_head hw_last
  have hfst_snd : (s : Multiset (ℕ × ℕ)).map Prod.fst = (s : Multiset (ℕ × ℕ)).map Prod.snd := by
    rw [hs_eq]
    exact fst_eq_snd_cycleUnion cs
  obtain ⟨e0, rest, rfl⟩ := List.exists_cons_of_ne_nil hs_ne
  let d : Fin (rest.length + 1) → ℕ := fun j => ((e0 :: rest).get j).1
  let dh : Fin (rest.length + 1) → ℕ := fun j => ((e0 :: rest).get j).2
  have hs_ofFn : (e0 :: rest) = List.ofFn fun j : Fin (rest.length + 1) => (d j, dh j) := by
    simp [d, dh]
  have h_ofFn_fst : List.ofFn d = (e0 :: rest).map Prod.fst := by
    simp [d]
  have h_ofFn_snd : List.ofFn dh = (e0 :: rest).map Prod.snd := by
    simp [dh]
  have hperm : List.Perm (List.ofFn d) (List.ofFn dh) := by
    rw [h_ofFn_fst, h_ofFn_snd]
    have hcoe : (((e0 :: rest).map Prod.fst : List ℕ) : Multiset ℕ) =
        (((e0 :: rest).map Prod.snd : List ℕ) : Multiset ℕ) := by
      have h1 : (((e0 :: rest : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map Prod.fst : Multiset ℕ) =
          ((((e0 :: rest).map Prod.fst : List ℕ)) : Multiset ℕ) := rfl
      have h2 : (((e0 :: rest : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)).map Prod.snd : Multiset ℕ) =
          ((((e0 :: rest).map Prod.snd : List ℕ)) : Multiset ℕ) := rfl
      rw [← h1, ← h2]
      exact hfst_snd
    exact Multiset.coe_eq_coe.mp hcoe
  obtain ⟨σ, hσ⟩ := exists_perm_of_ofFn_perm d dh hperm
  have hbound : ∀ j, d j < b := by
    intro j
    have hmem : (e0 :: rest).get j ∈ (e0 :: rest) := List.get_mem _ _
    have hm := hmother _ hmem
    simpa [d] using hm.1
  have hweight0 : weightSum n b (e0 :: rest) = 0 := by
    have h := run_weightSum hrun
    simpa using h.symm
  have hsum0 : ∑ j, (((n : ℤ) * dh j - (d j : ℤ)) * (b : ℤ) ^ (j : ℕ)) = 0 := by
    have h := weightSum_ofFn n b d dh
    rw [← hs_ofFn] at h
    rw [hweight0] at h
    exact h.symm
  have hperm_eq : ∑ j, d j * b ^ (j : ℕ) = n * ∑ j, d (σ j) * b ^ (j : ℕ) :=
    sum_eq_of_weight_zero d dh σ hσ hsum0
  have hperm : IsPermutiple n b d σ := ⟨hbound, hperm_eq⟩
  have hs_eq_ofFn : (e0 :: rest) = List.ofFn fun j : Fin (rest.length + 1) => (d j, d (σ j)) := by
    rw [hs_ofFn, hσ]
    rfl
  exact ⟨e0 :: rest, hs_eq, hrun, rest.length, d, σ, hperm, hs_eq_ofFn⟩

end

end MetaMathlibExt
