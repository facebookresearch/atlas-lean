/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.Sharpness.ABFieldDeriv
import Code.Sharpness.FieldGhostDict

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace
open RandomCurrent

variable {E : Type*} [Fintype E] [DecidableEq E]


def abgiClosedPivotal (e : E) (A : Set (ConfigSpace E)) : Set (ConfigSpace E) :=
  {omega | IsPivotal e A omega ∧ omega e = false}



theorem abgi_probV_closedPivotal (p : E → ℝ) (A : Set (ConfigSpace E)) (e : E) :
    probV p (abgiClosedPivotal e A) = (1 - p e) * pivotalProbV p A e := by
  unfold probV pivotalProbV
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
      (fun omega => (abgiClosedPivotal e A).indicator (fun _ => (1 : ℝ)) omega
        * configWeightV p omega)]
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
      (fun omega => {omega | IsPivotal e A omega}.indicator (fun _ => (1 : ℝ)) omega
        * configWeightV p omega)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  let omegaT := (Equiv.funSplitAt e Bool).symm (true, eta)
  let omegaF := (Equiv.funSplitAt e Bool).symm (false, eta)
  have ht : omegaT e = true := by
    simp [omegaT, Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : omegaF e = false := by
    simp [omegaF, Equiv.funSplitAt, Equiv.piSplitAt]
  have hsame : ∀ j, j ≠ e → omegaT j = omegaF j := by
    intro j hj
    simp [omegaT, omegaF, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hpiv : IsPivotal e A omegaT ↔ IsPivotal e A omegaF := by
    apply isPivotal_congr
    exact hsame
  have hoff : weightOffV p e omegaT = weightOffV p e omegaF :=
    weightOffV_congr p e hsame
  have hwT : configWeightV p omegaT = p e * weightOffV p e omegaT := by
    calc
      configWeightV p omegaT = edgeWeightV p omegaT e * weightOffV p e omegaT :=
        configWeightV_eq p e omegaT
      _ = p e * weightOffV p e omegaT := by simp [edgeWeightV, ht]
  have hwF : configWeightV p omegaF = (1 - p e) * weightOffV p e omegaF := by
    calc
      configWeightV p omegaF = edgeWeightV p omegaF e * weightOffV p e omegaF :=
        configWeightV_eq p e omegaF
      _ = (1 - p e) * weightOffV p e omegaF := by simp [edgeWeightV, hf]
  have hTnot : omegaT ∉ abgiClosedPivotal e A := by
    intro h
    exact Bool.noConfusion (ht.symm.trans h.2)
  change
    (abgiClosedPivotal e A).indicator (fun _ => (1 : ℝ)) omegaT * configWeightV p omegaT +
        (abgiClosedPivotal e A).indicator (fun _ => (1 : ℝ)) omegaF * configWeightV p omegaF =
      (1 - p e) *
        ({omega | IsPivotal e A omega}.indicator (fun _ => (1 : ℝ)) omegaT *
            configWeightV p omegaT +
          {omega | IsPivotal e A omega}.indicator (fun _ => (1 : ℝ)) omegaF *
            configWeightV p omegaF)
  by_cases hpt : IsPivotal e A omegaT
  · have hpf : IsPivotal e A omegaF := hpiv.mp hpt
    have hFmem : omegaF ∈ abgiClosedPivotal e A := ⟨hpf, hf⟩
    simp only [Set.indicator_of_notMem hTnot, Set.indicator_of_mem hFmem,
      Set.indicator_of_mem (show omegaT ∈ {omega | IsPivotal e A omega} from hpt),
      Set.indicator_of_mem (show omegaF ∈ {omega | IsPivotal e A omega} from hpf),
      zero_mul, zero_add, one_mul]
    rw [hwT, hwF, hoff]
    ring
  · have hpf : ¬ IsPivotal e A omegaF := hpiv.not.mp hpt
    have hFnot : omegaF ∉ abgiClosedPivotal e A := fun h => hpf h.1
    simp only [Set.indicator_of_notMem hTnot, Set.indicator_of_notMem hFnot,
      Set.indicator_of_notMem (show omegaT ∉ {omega | IsPivotal e A omega} from hpt),
      Set.indicator_of_notMem (show omegaF ∉ {omega | IsPivotal e A omega} from hpf),
      zero_mul, zero_add, mul_zero]



theorem abgi_probV_mono (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    {A B : Set (ConfigSpace E)} (hAB : A ⊆ B) : probV p A ≤ probV p B := by
  unfold probV
  apply Finset.sum_le_sum
  intro omega _
  apply mul_le_mul_of_nonneg_right _ (configWeightV_nonneg p hp omega)
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (hAB hA)]
  · rw [Set.indicator_of_notMem hA]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) omega


theorem abgi_probV_nonneg (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (A : Set (ConfigSpace E)) : 0 ≤ probV p A := by
  unfold probV
  apply Finset.sum_nonneg
  intro omega _
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
    (configWeightV_nonneg p hp omega)


theorem abgi_probV_union_le (p : E → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (A B : Set (ConfigSpace E)) : probV p (A ∪ B) ≤ probV p A + probV p B := by
  unfold probV
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro omega _
  have hw := configWeightV_nonneg p hp omega
  by_cases hA : omega ∈ A <;> by_cases hB : omega ∈ B <;>
    simp [Set.indicator, hA, hB, hw]

variable {W : Type*} [Fintype W] [DecidableEq W]





theorem abgi_closedPivotal_conn_subset_oriented
    (H : SimpleGraph W) (D : Set W) (u : W) (B : Set W)
    (x y : W) (hu : u ∈ D) (hx : x ∈ D) (hy : y ∈ D) :
    abgiClosedPivotal s(x, y) (connEvent H D u B) ⊆
      ((connEvent H D u {x} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D y B) ∪
      ((connEvent H D u {y} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D x B) := by
  intro omega homega
  let e : Sym2 W := s(x, y)
  let A : Set (ConfigSpace (Sym2 W)) := connEvent H D u B
  have hpiv : IsPivotal e A omega := homega.1
  have hclosed : omega e = false := homega.2
  have hclosedCfg : setClosed e omega = omega := by
    funext j
    by_cases hje : j = e
    · subst j
      simpa [hclosed] using setClosed_self e omega
    · exact setClosed_of_ne hje omega
  have hnotA : omega ∉ A := by
    have hpair := (isPivotal_iff_of_isIncreasing
      (isIncreasing_connEvent H D u B) omega).mp hpiv
    have hnot := hpair.1
    rwa [hclosedCfg] at hnot
  have horient := sab_pivotal_subset_firstExit H D u B x y hu hx hy hpiv
  rcases horient with hxy | hyx
  · have hinter := disjointOccurrence_subset_inter _ _ hxy
    exact Or.inl ⟨⟨hinter.1, hnotA⟩, hinter.2⟩
  · have hinter := disjointOccurrence_subset_inter _ _ hyx
    exact Or.inr ⟨⟨hinter.1, hnotA⟩, hinter.2⟩




theorem abgi_probV_closedPivotal_conn_le_oriented
    (p : Sym2 W → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (H : SimpleGraph W) (D : Set W) (u : W) (B : Set W)
    (x y : W) (hu : u ∈ D) (hx : x ∈ D) (hy : y ∈ D) :
    probV p (abgiClosedPivotal s(x, y) (connEvent H D u B)) ≤
      probV p ((connEvent H D u {x} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D y B) +
      probV p ((connEvent H D u {y} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D x B) := by
  calc
    probV p (abgiClosedPivotal s(x, y) (connEvent H D u B)) ≤
        probV p
          (((connEvent H D u {x} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D y B) ∪
            ((connEvent H D u {y} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D x B)) :=
      abgi_probV_mono p hp
        (abgi_closedPivotal_conn_subset_oriented H D u B x y hu hx hy)
    _ ≤ _ := abgi_probV_union_le p hp _ _

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma abgi_conn_ghost_of_conn_x_open (o x : V)
    (omega : ConfigSpace (Sym2 (Option V)))
    (hox : omega ∈ connEvent (withGhost G) Set.univ (some o) {some x})
    (hxg : omega s(some x, none) = true) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) {none} := by
  obtain ⟨ho, z, hzU, hz, hconn⟩ := hox
  simp only [Set.mem_singleton_iff] at hz
  subst z
  have hadj : ((openSub (withGhost G) omega).induce Set.univ).Adj
      ⟨some x, Set.mem_univ _⟩ ⟨none, Set.mem_univ _⟩ :=
    ⟨withGhost_adj_some_ghost G x, hxg⟩
  exact ⟨ho, none, Set.mem_univ _, Set.mem_singleton _, hconn.trans hadj.reachable⟩



theorem abgi_closedPivotal_ghost_eq (o x : V) :
    abgiClosedPivotal s(some x, none)
        (connEvent (withGhost G) Set.univ (some o) {none}) =
      connEvent (withGhost G) Set.univ (some o) {some x} ∩
        (connEvent (withGhost G) Set.univ (some o) {none})ᶜ := by
  ext omega
  let e : Sym2 (Option V) := s(some x, none)
  let A : Set (ConfigSpace (Sym2 (Option V))) :=
    connEvent (withGhost G) Set.univ (some o) {none}
  constructor
  · intro h
    have hpiv : IsPivotal e A omega := h.1
    have hclosed : omega e = false := h.2
    have hclosedCfg : setClosed e omega = omega := by
      funext j
      by_cases hje : j = e
      · subst j
        simpa [hclosed] using setClosed_self e omega
      · exact setClosed_of_ne hje omega
    have hnotA : omega ∉ A := by
      have hpair := (isPivotal_iff_of_isIncreasing
        (isIncreasing_connEvent (withGhost G) Set.univ (some o) {none}) omega).mp hpiv
      have hnot := hpair.1
      rw [hclosedCfg] at hnot
      exact hnot
    have hfirst := sab_pivotal_subset_firstExit (withGhost G) Set.univ
      (some o) {none} (some x) none (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
      hpiv
    rcases hfirst with hxy | hyx
    · have hinter := disjointOccurrence_subset_inter _ _ hxy
      exact ⟨hinter.1, hnotA⟩
    · have hinter := disjointOccurrence_subset_inter _ _ hyx
      exact False.elim (hnotA hinter.1)
  · rintro ⟨hox, hnotA⟩
    have hclosed : omega e = false := by
      cases heq : omega e with
      | false => rfl
      | true =>
          exact False.elim (hnotA (abgi_conn_ghost_of_conn_x_open G o x omega hox heq))
    have hclosedCfg : setClosed e omega = omega := by
      funext j
      by_cases hje : j = e
      · subst j
        simpa [hclosed] using setClosed_self e omega
      · exact setClosed_of_ne hje omega
    have hmono : omega ≤ setOpen e omega := fun j => by
      by_cases hje : j = e
      · subst j
        rw [setOpen_self]
        exact Bool.le_true _
      · rw [setOpen_of_ne hje]
    have hoxOpen : setOpen e omega ∈
        connEvent (withGhost G) Set.univ (some o) {some x} :=
      isIncreasing_connEvent (withGhost G) Set.univ (some o) {some x} hmono hox
    have hopen : setOpen e omega e = true := setOpen_self e omega
    have hopenA : setOpen e omega ∈ A :=
      abgi_conn_ghost_of_conn_x_open G o x (setOpen e omega) hoxOpen hopen
    refine ⟨?_, hclosed⟩
    exact (isPivotal_iff_of_isIncreasing
      (isIncreasing_connEvent (withGhost G) Set.univ (some o) {none}) omega).mpr
        ⟨by rwa [hclosedCfg], hopenA⟩



private lemma abgi_conn_target_of_conn_x_open (o x : V)
    (T : Set (Option V)) (hghost : none ∈ T)
    (omega : ConfigSpace (Sym2 (Option V)))
    (hox : omega ∈ connEvent (withGhost G) Set.univ (some o) {some x})
    (hxg : omega s(some x, none) = true) :
    omega ∈ connEvent (withGhost G) Set.univ (some o) T := by
  obtain ⟨ho, z, hzU, hz, hconn⟩ := hox
  simp only [Set.mem_singleton_iff] at hz
  subst z
  have hadj : ((openSub (withGhost G) omega).induce Set.univ).Adj
      ⟨some x, Set.mem_univ _⟩ ⟨none, Set.mem_univ _⟩ :=
    ⟨withGhost_adj_some_ghost G x, hxg⟩
  exact ⟨ho, none, Set.mem_univ _, hghost, hconn.trans hadj.reachable⟩



theorem abgi_closedPivotal_ghost_eq_target (o x : V)
    (T : Set (Option V)) (hghost : none ∈ T) :
    abgiClosedPivotal s(some x, none)
        (connEvent (withGhost G) Set.univ (some o) T) =
      connEvent (withGhost G) Set.univ (some o) {some x} ∩
        (connEvent (withGhost G) Set.univ (some o) T)ᶜ := by
  ext omega
  let e : Sym2 (Option V) := s(some x, none)
  let A : Set (ConfigSpace (Sym2 (Option V))) :=
    connEvent (withGhost G) Set.univ (some o) T
  constructor
  · intro h
    have hpiv : IsPivotal e A omega := h.1
    have hclosed : omega e = false := h.2
    have hclosedCfg : setClosed e omega = omega := by
      funext j
      by_cases hje : j = e
      · subst j
        simpa [hclosed] using setClosed_self e omega
      · exact setClosed_of_ne hje omega
    have hnotA : omega ∉ A := by
      have hpair := (isPivotal_iff_of_isIncreasing
        (isIncreasing_connEvent (withGhost G) Set.univ (some o) T) omega).mp hpiv
      have hnot := hpair.1
      rwa [hclosedCfg] at hnot
    have horient := abgi_closedPivotal_conn_subset_oriented
      (withGhost G) Set.univ (some o) T (some x) none
      (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _) h
    rcases horient with horient | horient
    · exact ⟨horient.1.1, hnotA⟩
    · obtain ⟨hu, z, hzU, hznone, hconn⟩ := horient.1.1
      simp only [Set.mem_singleton_iff] at hznone
      subst z
      exact False.elim (hnotA ⟨hu, none, hzU, hghost, hconn⟩)
  · rintro ⟨hox, hnotA⟩
    have hclosed : omega e = false := by
      cases heq : omega e with
      | false => rfl
      | true =>
          exact False.elim (hnotA
            (abgi_conn_target_of_conn_x_open G o x T hghost omega hox heq))
    have hclosedCfg : setClosed e omega = omega := by
      funext j
      by_cases hje : j = e
      · subst j
        simpa [hclosed] using setClosed_self e omega
      · exact setClosed_of_ne hje omega
    have hmono : omega ≤ setOpen e omega := fun j => by
      by_cases hje : j = e
      · subst j
        rw [setOpen_self]
        exact Bool.le_true _
      · rw [setOpen_of_ne hje]
    have hoxOpen : setOpen e omega ∈
        connEvent (withGhost G) Set.univ (some o) {some x} :=
      isIncreasing_connEvent (withGhost G) Set.univ (some o) {some x} hmono hox
    have hopenA : setOpen e omega ∈ A :=
      abgi_conn_target_of_conn_x_open G o x T hghost (setOpen e omega)
        hoxOpen (setOpen_self e omega)
    refine ⟨?_, hclosed⟩
    exact (isPivotal_iff_of_isIncreasing
      (isIncreasing_connEvent (withGhost G) Set.univ (some o) T) omega).mpr
        ⟨by rwa [hclosedCfg], hopenA⟩




theorem abgi_ghostInfluence_eq_restricted (p : Sym2 (Option V) → ℝ) (q : ℝ)
    (o x : V) :
    (1 - q) * pivotalProbV
        (paramOn (FieldGhostDict.ghostEdges V) q p)
        (connEvent (withGhost G) Set.univ (some o) {none}) s(some x, none) =
      probV (paramOn (FieldGhostDict.ghostEdges V) q p)
        (connEvent (withGhost G) Set.univ (some o) {some x} ∩
          (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) := by
  have hmem : s(some x, none) ∈ FieldGhostDict.ghostEdges V := by
    simp [FieldGhostDict.ghostEdges]
  calc
    (1 - q) * pivotalProbV
        (paramOn (FieldGhostDict.ghostEdges V) q p)
        (connEvent (withGhost G) Set.univ (some o) {none}) s(some x, none) =
      (1 - paramOn (FieldGhostDict.ghostEdges V) q p s(some x, none)) *
        pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) q p)
          (connEvent (withGhost G) Set.univ (some o) {none}) s(some x, none) := by
            simp [paramOn, hmem]
    _ = probV (paramOn (FieldGhostDict.ghostEdges V) q p)
        (abgiClosedPivotal s(some x, none)
          (connEvent (withGhost G) Set.univ (some o) {none})) :=
      (abgi_probV_closedPivotal _ _ _).symm
    _ = _ := by rw [abgi_closedPivotal_ghost_eq G]



theorem abgi_ghostInfluence_exp_eq_restricted (p : Sym2 (Option V) → ℝ)
    (h : ℝ) (o x : V) :
    pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) {none}) s(some x, none) *
        Real.exp (-h) =
      probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) {some x} ∩
          (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) := by
  rw [mul_comm, ← show (1 - qField h) = Real.exp (-h) by simp [qField]]
  exact abgi_ghostInfluence_eq_restricted G p (qField h) o x

private theorem abgi_ghostEdge_injective :
    Function.Injective (fun x : V => s(some x, none)) := by
  intro x y hxy
  rw [Sym2.eq_iff] at hxy
  rcases hxy with hxy | hxy
  · exact Option.some.inj hxy.1
  · simp at hxy







theorem abgi_deriv_field_eq_sum_restricted (p : Sym2 (Option V) → ℝ)
    (h : ℝ) (o : V) :
    deriv (fun t => probV
        (paramOn (FieldGhostDict.ghostEdges V) (qField t) p)
        (connEvent (withGhost G) Set.univ (some o) {none})) h =
      ∑ x : V, probV
        (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) {some x} ∩
          (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) := by
  rw [deriv_field_profile _ _ _
    (isIncreasing_connEvent (withGhost G) Set.univ (some o) {none}) h]
  unfold FieldGhostDict.ghostEdges
  rw [Finset.sum_image (fun _ _ _ _ hxy => abgi_ghostEdge_injective hxy)]
  apply Finset.sum_congr rfl
  intro x _
  exact abgi_ghostInfluence_exp_eq_restricted G p h o x


theorem abgi_ghostInfluence_exp_eq_restricted_target
    (p : Sym2 (Option V) → ℝ) (h : ℝ) (o x : V)
    (T : Set (Option V)) (hghost : none ∈ T) :
    pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) T) s(some x, none) *
        Real.exp (-h) =
      probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) {some x} ∩
          (connEvent (withGhost G) Set.univ (some o) T)ᶜ) := by
  have hmem : s(some x, none) ∈ FieldGhostDict.ghostEdges V := by
    simp [FieldGhostDict.ghostEdges]
  rw [mul_comm, ← show (1 - qField h) = Real.exp (-h) by simp [qField]]
  calc
    (1 - qField h) * pivotalProbV
        (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) T) s(some x, none) =
      (1 - paramOn (FieldGhostDict.ghostEdges V) (qField h) p
          s(some x, none)) *
        pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
          (connEvent (withGhost G) Set.univ (some o) T) s(some x, none) := by
            simp [paramOn, hmem]
    _ = probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (abgiClosedPivotal s(some x, none)
          (connEvent (withGhost G) Set.univ (some o) T)) :=
      (abgi_probV_closedPivotal _ _ _).symm
    _ = _ := by rw [abgi_closedPivotal_ghost_eq_target G o x T hghost]



theorem abgi_deriv_field_eq_sum_restricted_target
    (p : Sym2 (Option V) → ℝ) (h : ℝ) (o : V)
    (T : Set (Option V)) (hghost : none ∈ T) :
    deriv (fun t => probV
        (paramOn (FieldGhostDict.ghostEdges V) (qField t) p)
        (connEvent (withGhost G) Set.univ (some o) T)) h =
      ∑ x : V, probV
        (paramOn (FieldGhostDict.ghostEdges V) (qField h) p)
        (connEvent (withGhost G) Set.univ (some o) {some x} ∩
          (connEvent (withGhost G) Set.univ (some o) T)ᶜ) := by
  rw [deriv_field_profile _ _ _
    (isIncreasing_connEvent (withGhost G) Set.univ (some o) T) h]
  unfold FieldGhostDict.ghostEdges
  rw [Finset.sum_image (fun _ _ _ _ hxy => abgi_ghostEdge_injective hxy)]
  apply Finset.sum_congr rfl
  intro x _
  exact abgi_ghostInfluence_exp_eq_restricted_target G p h o x T hghost

end Sharpness
end StatMech
