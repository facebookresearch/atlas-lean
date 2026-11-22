/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Metrizable.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Separation.Profinite

@[expose] public section

section
/-!
# Brouwer's characterization of Cantor space
-/

noncomputable section

namespace MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted

private lemma list_iUnion_singleton {X : Type*} (a : Set X) : (⋃ s ∈ [a], s) = a := by
  ext x
  simp

private lemma list_iUnion_cons {X : Type*} (c : Set X) (l : List (Set X)) :
    (⋃ s ∈ c :: l, s) = c ∪ ⋃ s ∈ l, s := by
  ext x
  simp [Set.mem_iUnion]

private lemma splitClopen {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {U : Set X}
    (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ A B : Set X, IsClopen A ∧ IsClopen B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A ∪ B = U := by
  obtain ⟨x, hx⟩ := hne
  have hacc : AccPt x (Filter.principal (Set.univ : Set X)) :=
    PerfectSpace.univ_preperfect x (Set.mem_univ x)
  have hinter : AccPt x (Filter.principal (U ∩ Set.univ)) :=
    hacc.nhds_inter (hU.isOpen.mem_nhds hx)
  rw [accPt_iff_nhds] at hinter
  obtain ⟨y, hyU, hyx⟩ := hinter Set.univ Filter.univ_mem
  have hyU' : y ∈ U := hyU.2.1
  obtain ⟨Nx, Ny, hNxo, hNyo, hxNx, hyNy, hdisj⟩ := t2_separation (Ne.symm hyx)
  obtain ⟨V, hVcl, hxV, hVsub⟩ :=
    compact_exists_isClopen_in_isOpen (hNxo.inter hU.isOpen) ⟨hxNx, hx⟩
  have hVsubU : V ⊆ U := fun a ha => (hVsub ha).2
  have hyV : y ∉ V := by
    intro hyV
    have hx1 : y ∈ Nx := (hVsub hyV).1
    exact (Set.disjoint_left.mp hdisj hx1) hyNy
  refine ⟨V, U \ V, hVcl, hU.diff hVcl, ⟨x, hxV⟩, ⟨y, hyU', hyV⟩, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun a ha1 ha2 => ha2.2 ha1)
  · exact Set.union_sdiff_cancel hVsubU

private def brouwerStep {X : Type*} (kids : ℕ → Set X → List (Set X)) :
    List (Set X) × ℕ → Bool → List (Set X) × ℕ
  | ([], n), _ => ([], n)
  | ([C], n), false =>
    match kids n C with
    | [] => ([C], n + 1)
    | [a] => ([a], n + 1)
    | a :: _rest => ([a], n + 1)
  | ([C], n), true =>
    match kids n C with
    | [] => ([C], n + 1)
    | [a] => ([a], n + 1)
    | _a :: rest => (rest, n + 1)
  | (C :: _D :: _rest, n), false => ([C], n)
  | (_C :: D :: rest, n), true => ((D :: rest), n)

private def brouwerState {X : Type*} (kids : ℕ → Set X → List (Set X)) (t : List Bool) :
    List (Set X) × ℕ :=
  t.foldl (brouwerStep kids) ([Set.univ], 0)

private def brouwerPiece {X : Type*} (kids : ℕ → Set X → List (Set X)) (t : List Bool) :
    Set X :=
  ⋃ s ∈ (brouwerState kids t).1, s

private def brouwerPref (σ : ℕ → Bool) (n : ℕ) : List Bool :=
  (List.range n).map σ

/--
Every nonempty compact metrizable perfect totally disconnected space is homeomorphic to the Cantor
space.
Source: L. E. J. Brouwer, Proc. Kon. Ned. Akad. Wet. 12 (1910), 785-794.

Proves `Wanted` entry `brouwer_cantor_space_characterization`.
-/
theorem brouwer_cantor_space_characterization
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [PerfectSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] :
    Nonempty (X ≃ₜ (ℕ → Bool)) := by
  classical
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hUcomp : IsCompact (Set.univ : Set X) := isCompact_univ
  have hBdd : Bornology.IsBounded (Set.univ : Set X) := hUcomp.isBounded
  obtain ⟨C0, hC0⟩ := Metric.isBounded_iff.mp hBdd
  set B : ℝ := max C0 1 with hBdef
  have hBpos : (0 : ℝ) < B := lt_max_iff.mpr (Or.inr one_pos)
  have hBbound : ∀ x y : X, dist x y ≤ B := fun x y =>
    le_trans (hC0 (Set.mem_univ x) (Set.mem_univ y)) (le_max_left _ _)
  have key' : ∀ (n : ℕ) (P : Set X), IsClopen P → P.Nonempty →
      ∃ L : List (Set X),
        2 ≤ L.length ∧ (∀ Cc ∈ L, IsClopen Cc) ∧ (∀ Cc ∈ L, Cc.Nonempty) ∧
        (∀ Cc ∈ L, Cc ⊆ P) ∧
        (∀ Cc ∈ L, ∀ x ∈ Cc, ∀ y ∈ Cc, dist x y ≤ B * (2⁻¹ : ℝ) ^ (n + 1)) ∧
        L.Pairwise Disjoint ∧ (⋃ Cc ∈ L, Cc) = P := by
    intro n P hP hPne
    have hr : (0 : ℝ) < B * (2⁻¹ : ℝ) ^ (n + 1) / 2 :=
      half_pos (mul_pos hBpos (pow_pos (by norm_num) _))
    have hball : ∀ (V : Set X) (c : X), V ⊆ Metric.ball c (B * (2⁻¹ : ℝ) ^ (n + 1) / 2) →
        ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ B * (2⁻¹ : ℝ) ^ (n + 1) := by
      intro V c hVc x hx y hy
      have e1 : dist x c < B * (2⁻¹ : ℝ) ^ (n + 1) / 2 := Metric.mem_ball.mp (hVc hx)
      have e2 : dist y c < B * (2⁻¹ : ℝ) ^ (n + 1) / 2 := Metric.mem_ball.mp (hVc hy)
      have hrr : B * (2⁻¹ : ℝ) ^ (n + 1) / 2 + B * (2⁻¹ : ℝ) ^ (n + 1) / 2 =
          B * (2⁻¹ : ℝ) ^ (n + 1) := by ring
      calc dist x y ≤ dist x c + dist c y := dist_triangle _ _ _
        _ = dist x c + dist y c := by rw [dist_comm c y]
        _ ≤ B * (2⁻¹ : ℝ) ^ (n + 1) := by linarith
    have hcov : P ⊆ ⋃ V : {V : Set X //
        IsClopen V ∧ V ⊆ P ∧ ∃ c, c ∈ P ∧ V ⊆ Metric.ball c (B * (2⁻¹ : ℝ) ^ (n + 1) / 2)},
        (V : Set X) := by
      intro x hx
      have hmem : x ∈ P ∩ Metric.ball x (B * (2⁻¹ : ℝ) ^ (n + 1) / 2) :=
        ⟨hx, Metric.mem_ball_self hr⟩
      obtain ⟨V, hVcl, hxV, hVsub⟩ :=
        compact_exists_isClopen_in_isOpen (hP.isOpen.inter Metric.isOpen_ball) hmem
      exact Set.mem_iUnion.mpr ⟨⟨V, hVcl, (fun a ha => (hVsub ha).1),
        ⟨x, hx, (fun a ha => (hVsub ha).2)⟩⟩, hxV⟩
    obtain ⟨t, ht⟩ := hP.isClosed.isCompact.elim_finite_subcover
      (fun V : {V : Set X //
        IsClopen V ∧ V ⊆ P ∧ ∃ c, c ∈ P ∧ V ⊆ Metric.ball c (B * (2⁻¹ : ℝ) ^ (n + 1) / 2)} =>
        (V : Set X))
      (fun V => V.2.1.isOpen) hcov
    set Vf : Fin t.card → Set X := fun i =>
      ((t.equivFin.symm i : {V : Set X //
        IsClopen V ∧ V ⊆ P ∧ ∃ c, c ∈ P ∧ V ⊆ Metric.ball c (B * (2⁻¹ : ℝ) ^ (n + 1) / 2)}) :
        Set X) with hVf
    have hVprop : ∀ i : Fin t.card, IsClopen (Vf i) ∧ Vf i ⊆ P ∧
        ∃ c, c ∈ P ∧ Vf i ⊆ Metric.ball c (B * (2⁻¹ : ℝ) ^ (n + 1) / 2) :=
      fun i => ((t.equivFin.symm i).1).2
    set Df : Fin t.card → Set X := fun i =>
      Vf i \ ⋃ j ∈ Finset.univ.filter (fun j => j.val < i.val), Vf j with hDf
    have hDcl : ∀ i, IsClopen (Df i) := by
      intro i
      apply IsClopen.diff (hVprop i).1
      apply Set.Finite.isClopen_biUnion (Finset.finite_toSet _)
      intro j _
      exact (hVprop j).1
    have hDsub : ∀ i, Df i ⊆ P :=
      fun i => Set.sdiff_subset.trans (hVprop i).2.1
    have hDmesh : ∀ (i : Fin t.card) (x : X), x ∈ Df i → ∀ (y : X), y ∈ Df i →
        dist x y ≤ B * (2⁻¹ : ℝ) ^ (n + 1) := by
      intro i x hx y hy
      obtain ⟨c, -, hcb⟩ := (hVprop i).2.2
      exact hball (Vf i) c hcb x hx.1 y hy.1
    have hDdisj : ∀ (i j : Fin t.card), i.val < j.val → Disjoint (Df i) (Df j) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro a hai haj
      have h2 := haj.2
      have hmem : a ∈ ⋃ jj ∈ Finset.univ.filter (fun jj => jj.val < j.val), Vf jj :=
        Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hij⟩))
          hai.1
      exact h2 hmem
    have hDcover : (⋃ i, Df i) = P := by
      apply Set.Subset.antisymm (Set.iUnion_subset (fun i => hDsub i))
      intro x hx
      obtain ⟨V, hV⟩ := Set.mem_iUnion.mp (ht hx)
      obtain ⟨hVt, hxV⟩ := Set.mem_iUnion.mp hV
      set i₀ : Fin t.card := t.equivFin ⟨V, hVt⟩ with hi₀
      have e₀ : t.equivFin.symm i₀ = ⟨V, hVt⟩ :=
        Equiv.symm_apply_apply t.equivFin ⟨V, hVt⟩
      have hVi₀ : Vf i₀ = (V : Set X) :=
        congrArg (fun v : ↥t => (((v.1 : {V : Set X //
          IsClopen V ∧ V ⊆ P ∧ ∃ c, c ∈ P ∧ V ⊆ Metric.ball c (B * (2⁻¹ : ℝ) ^ (n + 1) / 2)}) :
          Set X))) e₀
      have hxVf : x ∈ Vf i₀ := by rw [hVi₀]; exact hxV
      have hSne : (Finset.univ.filter (fun j => x ∈ Vf j)).Nonempty :=
        ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxVf⟩⟩
      set j₀ := (Finset.univ.filter (fun j => x ∈ Vf j)).min' hSne with hj₀
      have hj₀mem : j₀ ∈ Finset.univ.filter (fun j => x ∈ Vf j) :=
        Finset.min'_mem _ _
      have hj₀le : ∀ j ∈ Finset.univ.filter (fun j => x ∈ Vf j), j₀ ≤ j :=
        fun j hj => Finset.min'_le _ _ hj
      have hxD : x ∈ Df j₀ := by
        have h1 : x ∈ Vf j₀ := (Finset.mem_filter.mp hj₀mem).2
        have h2 : x ∉ ⋃ jj ∈ Finset.univ.filter (fun jj => jj.val < j₀.val), Vf jj := by
          intro hcon
          obtain ⟨jj, hcon2⟩ := Set.mem_iUnion.mp hcon
          obtain ⟨hjf, hxjj⟩ := Set.mem_iUnion.mp hcon2
          have hjf' := Finset.mem_filter.mp (Finset.mem_coe.mp hjf)
          have hSmem : jj ∈ Finset.univ.filter (fun j => x ∈ Vf j) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxjj⟩
          have hle : j₀.val ≤ jj.val := hj₀le jj hSmem
          exact absurd hjf'.2 (not_lt_of_ge hle)
        exact ⟨h1, h2⟩
      exact Set.mem_iUnion.mpr ⟨j₀, hxD⟩
    set L0 : List (Set X) :=
      ((Finset.univ.filter (fun i => (Df i).Nonempty)).toList).map Df with hL0
    have hL0mem : ∀ Cc : Set X, Cc ∈ L0 ↔ ∃ i, (Df i).Nonempty ∧ Df i = Cc := by
      intro Cc
      constructor
      · intro hmem
        rw [hL0, List.mem_map] at hmem
        obtain ⟨i, hi, rfl⟩ := hmem
        rw [Finset.mem_toList, Finset.mem_filter] at hi
        exact ⟨i, hi.2, rfl⟩
      · rintro ⟨i, hne, rfl⟩
        rw [hL0, List.mem_map]
        refine ⟨i, ?_, rfl⟩
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hne⟩
    have hL0cl : ∀ Cc ∈ L0, IsClopen Cc := by
      intro Cc hCc
      obtain ⟨i, -, rfl⟩ := (hL0mem Cc).mp hCc
      exact hDcl i
    have hL0ne' : ∀ Cc ∈ L0, Cc.Nonempty := by
      intro Cc hCc
      obtain ⟨i, hne, rfl⟩ := (hL0mem Cc).mp hCc
      exact hne
    have hL0sub : ∀ Cc ∈ L0, Cc ⊆ P := by
      intro Cc hCc
      obtain ⟨i, -, rfl⟩ := (hL0mem Cc).mp hCc
      exact hDsub i
    have hL0mesh : ∀ Cc ∈ L0, ∀ x ∈ Cc, ∀ y ∈ Cc, dist x y ≤ B * (2⁻¹ : ℝ) ^ (n + 1) := by
      intro Cc hCc x hx y hy
      obtain ⟨i, -, rfl⟩ := (hL0mem Cc).mp hCc
      exact hDmesh i x hx y hy
    have hL0disj : ∀ a ∈ L0, ∀ b ∈ L0, a ≠ b → Disjoint a b := by
      intro a ha b hb hab
      obtain ⟨i, -, rfl⟩ := (hL0mem a).mp ha
      obtain ⟨j, -, rfl⟩ := (hL0mem b).mp hb
      have hij : i ≠ j := by
        intro hcon
        apply hab
        rw [hcon]
      rcases lt_trichotomy i.val j.val with h | h | h
      · exact hDdisj i j h
      · exact absurd (Fin.ext h) hij
      · exact Disjoint.symm (hDdisj j i h)
    have hL0nodup : L0.Nodup := by
      apply List.Nodup.map_on _ (Finset.nodup_toList _)
      intro i hi j hj heq
      have hi' : (Df i).Nonempty :=
        (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
      have hj' : (Df j).Nonempty := by rw [← heq]; exact hi'
      by_contra hne
      rcases lt_trichotomy i.val j.val with h | h | h
      · have hdis := hDdisj i j h
        rw [heq] at hdis
        obtain ⟨x, hx⟩ := hj'
        exact (Set.disjoint_left.mp hdis hx) hx
      · exact hne (Fin.ext h)
      · have hdis := hDdisj j i h
        rw [← heq] at hdis
        obtain ⟨x, hx⟩ := hi'
        exact (Set.disjoint_left.mp hdis hx) hx
    have hL0union : (⋃ Cc ∈ L0, Cc) = P := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨Cc, hCc⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hmem, hxCc⟩ := Set.mem_iUnion.mp hCc
        obtain ⟨i, -, rfl⟩ := (hL0mem _).mp hmem
        exact hDsub i hxCc
      · intro x hx
        rw [← hDcover] at hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        have hmem : Df i ∈ L0 := (hL0mem _).mpr ⟨i, ⟨x, hxi⟩, rfl⟩
        exact Set.mem_iUnion.mpr ⟨Df i, Set.mem_iUnion.mpr ⟨hmem, hxi⟩⟩
    by_cases hlen : 2 ≤ L0.length
    · exact ⟨L0, hlen, hL0cl, hL0ne', hL0sub, hL0mesh,
        hL0nodup.pairwise_of_forall_ne hL0disj, hL0union⟩
    · push Not at hlen
      have hL0ne : L0 ≠ [] := by
        intro hcon
        have hPe : P = ∅ := by
          rw [← hL0union, hcon]
          ext x
          simp
        exact hPne.ne_empty hPe
      have hlen1 : L0.length = 1 := by
        have hpos : 0 < L0.length :=
          Nat.pos_of_ne_zero (fun h => hL0ne (List.eq_nil_of_length_eq_zero h))
        omega
      obtain ⟨A, rest, hr⟩ := List.exists_cons_of_ne_nil hL0ne
      have h2 : rest.length + 1 = 1 := by rw [hr] at hlen1; simpa using hlen1
      have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hrest
      have hAmem : A ∈ L0 := by rw [hr]; exact List.mem_singleton.mpr rfl
      obtain ⟨i₀, -, hi₀eq⟩ := (hL0mem A).mp hAmem
      have hAP : A = P := by rw [← hL0union, hr, list_iUnion_singleton]
      have hAne : A.Nonempty := hL0ne' A hAmem
      have hAcl : IsClopen A := hL0cl A hAmem
      obtain ⟨A1, A2, hA1cl, hA2cl, hA1ne, hA2ne, hdisj12, hunion12⟩ :=
        splitClopen hAcl hAne
      have hA1A : A1 ⊆ A := by rw [← hunion12]; exact Set.subset_union_left
      have hA2A : A2 ⊆ A := by rw [← hunion12]; exact Set.subset_union_right
      have hAVf : A ⊆ Vf i₀ := by rw [← hi₀eq]; exact Set.sdiff_subset
      have hsub1 : A1 ⊆ Vf i₀ := hA1A.trans hAVf
      have hsub2 : A2 ⊆ Vf i₀ := hA2A.trans hAVf
      obtain ⟨c, -, hcb⟩ := (hVprop i₀).2.2
      have hmesh12 : ∀ Cc ∈ [A1, A2], ∀ x ∈ Cc, ∀ y ∈ Cc,
          dist x y ≤ B * (2⁻¹ : ℝ) ^ (n + 1) := by
        intro Cc hCc x hx y hy
        have hCc' : Cc = A1 ∨ Cc = A2 := by simpa using hCc
        rcases hCc' with rfl | rfl
        · exact hball (Vf i₀) c hcb x (hsub1 hx) y (hsub1 hy)
        · exact hball (Vf i₀) c hcb x (hsub2 hx) y (hsub2 hy)
      refine ⟨[A1, A2], by simp, ?_, ?_, ?_, hmesh12, ?_, ?_⟩
      · intro Cc hCc
        have hCc' : Cc = A1 ∨ Cc = A2 := by simpa using hCc
        rcases hCc' with rfl | rfl <;> assumption
      · intro Cc hCc
        have hCc' : Cc = A1 ∨ Cc = A2 := by simpa using hCc
        rcases hCc' with rfl | rfl <;> assumption
      · intro Cc hCc
        have hCc' : Cc = A1 ∨ Cc = A2 := by simpa using hCc
        rcases hCc' with rfl | rfl
        · exact hA1A.trans (hAP ▸ le_rfl)
        · exact hA2A.trans (hAP ▸ le_rfl)
      · exact List.pairwise_cons.mpr ⟨fun b hb => by
          rw [List.mem_singleton.mp hb]; exact hdisj12, List.pairwise_singleton _ _⟩
      · rw [show (⋃ Cc ∈ [A1, A2], Cc) = A1 ∪ A2 from by
          rw [list_iUnion_cons, list_iUnion_singleton], hunion12, hAP]
  have key : ∀ (n : ℕ) (P : Set X), ∃ L : List (Set X), IsClopen P → P.Nonempty →
        2 ≤ L.length ∧ (∀ Cc ∈ L, IsClopen Cc) ∧ (∀ Cc ∈ L, Cc.Nonempty) ∧
        (∀ Cc ∈ L, Cc ⊆ P) ∧
        (∀ Cc ∈ L, ∀ x ∈ Cc, ∀ y ∈ Cc, dist x y ≤ B * (2⁻¹ : ℝ) ^ (n + 1)) ∧
        L.Pairwise Disjoint ∧ (⋃ Cc ∈ L, Cc) = P := by
    intro n P
    by_cases h : IsClopen P ∧ P.Nonempty
    · obtain ⟨L, hL⟩ := key' n P h.1 h.2
      exact ⟨L, fun _ _ => hL⟩
    · exact ⟨[], fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose kids hkids using key
  have hRapp : ∀ (l : List Bool) (b : Bool),
      brouwerState kids (l ++ [b]) = brouwerStep kids (brouwerState kids l) b := by
    intro l b
    change List.foldl (brouwerStep kids) ([Set.univ], 0) (l ++ [b]) =
      brouwerStep kids (List.foldl (brouwerStep kids) ([Set.univ], 0) l) b
    rw [List.foldl_append]
    rfl
  have hE_single : ∀ (s : List Bool) (Cc : Set X) (m : ℕ),
      brouwerState kids s = ([Cc], m) → brouwerPiece kids s = Cc := by
    intro s Cc m h
    have h1 : (brouwerState kids s).1 = [Cc] := by rw [h]
    have h2 : brouwerPiece kids s = ⋃ s_1 ∈ [Cc], s_1 := by
      simp only [brouwerPiece, h1]
    rw [h2, list_iUnion_singleton]
  have hStep : ∀ S : List (Set X) × ℕ, S.1 ≠ [] ∧ S.1.Pairwise Disjoint ∧
      (∀ Cc ∈ S.1, IsClopen Cc) ∧ (∀ Cc ∈ S.1, Cc.Nonempty) ∧
      (∀ Cc ∈ S.1, ∀ x ∈ Cc, ∀ y ∈ Cc, dist x y ≤ B * (2⁻¹ : ℝ) ^ (S.2)) →
      ∀ b : Bool, (brouwerStep kids S b).1 ≠ [] ∧
        (brouwerStep kids S b).1.Pairwise Disjoint ∧
        (∀ Cc ∈ (brouwerStep kids S b).1, IsClopen Cc) ∧
        (∀ Cc ∈ (brouwerStep kids S b).1, Cc.Nonempty) ∧
        (∀ Cc ∈ (brouwerStep kids S b).1, ∀ x ∈ Cc, ∀ y ∈ Cc,
          dist x y ≤ B * (2⁻¹ : ℝ) ^ ((brouwerStep kids S b).2)) := by
    intro S hS b
    obtain ⟨hne, hpair, hcl, hne', hmesh⟩ := hS
    cases hL : S.1 with
    | nil => exact absurd hL hne
    | cons C rest =>
      cases rest with
      | nil =>
        have hSeq : S = ([C], S.2) := by rw [← hL, Prod.mk.eta]
        have hCcl : IsClopen C := hcl C (by rw [hL]; simp)
        have hCne : C.Nonempty := hne' C (by rw [hL]; simp)
        obtain ⟨Klen, Kcl, Kne, Ksub, Kmesh, Kpair, Kunion⟩ := hkids S.2 C hCcl hCne
        obtain ⟨a, r1, hr1⟩ := List.exists_cons_of_ne_nil (l := kids S.2 C)
          (by intro hcon; rw [hcon] at Klen; simp at Klen)
        have hr1ne : r1 ≠ [] := by
          intro hcon; rw [hr1, hcon] at Klen; simp at Klen
        obtain ⟨b0, rest'', hr2⟩ := List.exists_cons_of_ne_nil hr1ne
        have hK : kids S.2 C = a :: b0 :: rest'' := by rw [hr1, hr2]
        rw [hSeq]
        cases b with
        | false =>
          have ef1 : (brouwerStep kids ([C], S.2) false).1 = [a] := by
            simp only [brouwerStep, hK]
          have ef2 : (brouwerStep kids ([C], S.2) false).2 = S.2 + 1 := by
            simp only [brouwerStep, hK]
          rw [ef1, ef2]
          refine ⟨by simp, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
          · intro Cc hCc
            rw [List.mem_singleton.mp hCc]
            exact Kcl a (by rw [hK]; simp)
          · intro Cc hCc
            rw [List.mem_singleton.mp hCc]
            exact Kne a (by rw [hK]; simp)
          · intro Cc hCc x hx y hy
            rw [List.mem_singleton.mp hCc] at hx hy
            exact Kmesh a (by rw [hK]; simp) x hx y hy
        | true =>
          have et1 : (brouwerStep kids ([C], S.2) true).1 = b0 :: rest'' := by
            simp only [brouwerStep, hK]
          have et2 : (brouwerStep kids ([C], S.2) true).2 = S.2 + 1 := by
            simp only [brouwerStep, hK]
          rw [et1, et2]
          have Kpair' : (a :: b0 :: rest'').Pairwise Disjoint := by
            rw [← hK]; exact Kpair
          refine ⟨by simp, (List.pairwise_cons.mp Kpair').2, ?_, ?_, ?_⟩
          · intro Cc hCc
            exact Kcl Cc (by rw [hK]; exact List.mem_cons_of_mem a hCc)
          · intro Cc hCc
            exact Kne Cc (by rw [hK]; exact List.mem_cons_of_mem a hCc)
          · intro Cc hCc x hx y hy
            exact Kmesh Cc (by rw [hK]; exact List.mem_cons_of_mem a hCc) x hx y hy
      | cons D rest' =>
        have hSeq : S = ((C :: D :: rest'), S.2) := by rw [← hL, Prod.mk.eta]
        have hCm : C ∈ S.1 := by rw [hL]; simp
        rw [hSeq]
        cases b with
        | false =>
          have ef1 : (brouwerStep kids ((C :: D :: rest'), S.2) false).1 = [C] := by
            simp only [brouwerStep]
          have ef2 : (brouwerStep kids ((C :: D :: rest'), S.2) false).2 = S.2 := by
            simp only [brouwerStep]
          rw [ef1, ef2]
          refine ⟨by simp, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
          · intro Cc hCc
            rw [List.mem_singleton.mp hCc]
            exact hcl C hCm
          · intro Cc hCc
            rw [List.mem_singleton.mp hCc]
            exact hne' C hCm
          · intro Cc hCc x hx y hy
            rw [List.mem_singleton.mp hCc] at hx hy
            exact hmesh C hCm x hx y hy
        | true =>
          have et1 : (brouwerStep kids ((C :: D :: rest'), S.2) true).1 = D :: rest' := by
            simp only [brouwerStep]
          have et2 : (brouwerStep kids ((C :: D :: rest'), S.2) true).2 = S.2 := by
            simp only [brouwerStep]
          rw [et1, et2]
          have hpair' : (C :: D :: rest').Pairwise Disjoint := by
            rw [← hL]; exact hpair
          refine ⟨by simp, (List.pairwise_cons.mp hpair').2, ?_, ?_, ?_⟩
          · intro Cc hCc
            exact hcl Cc (by rw [hL]; exact List.mem_cons_of_mem C hCc)
          · intro Cc hCc
            exact hne' Cc (by rw [hL]; exact List.mem_cons_of_mem C hCc)
          · intro Cc hCc x hx y hy
            exact hmesh Cc (by rw [hL]; exact List.mem_cons_of_mem C hCc) x hx y hy
  have hfold : ∀ (l : List Bool) (S : List (Set X) × ℕ),
      (S.1 ≠ [] ∧ S.1.Pairwise Disjoint ∧ (∀ Cc ∈ S.1, IsClopen Cc) ∧
      (∀ Cc ∈ S.1, Cc.Nonempty) ∧
      (∀ Cc ∈ S.1, ∀ x ∈ Cc, ∀ y ∈ Cc, dist x y ≤ B * (2⁻¹ : ℝ) ^ (S.2))) →
      ((l.foldl (brouwerStep kids) S).1 ≠ [] ∧
      ((l.foldl (brouwerStep kids) S)).1.Pairwise Disjoint ∧
      (∀ Cc ∈ (l.foldl (brouwerStep kids) S).1, IsClopen Cc) ∧
      (∀ Cc ∈ (l.foldl (brouwerStep kids) S).1, Cc.Nonempty) ∧
      (∀ Cc ∈ (l.foldl (brouwerStep kids) S).1, ∀ x ∈ Cc, ∀ y ∈ Cc,
        dist x y ≤ B * (2⁻¹ : ℝ) ^ ((l.foldl (brouwerStep kids) S).2))) := by
    intro l
    induction l with
    | nil => intro S h; simpa using h
    | cons b l ih => intro S h; exact ih _ (hStep S h b)
  have hInitAux : ∀ S : List (Set X) × ℕ, S = ([Set.univ], (0 : ℕ)) →
      (S.1 ≠ [] ∧ S.1.Pairwise Disjoint ∧
      (∀ (Cc : Set X), Cc ∈ S.1 → IsClopen Cc) ∧
      (∀ (Cc : Set X), Cc ∈ S.1 → Cc.Nonempty) ∧
      (∀ (Cc : Set X), Cc ∈ S.1 → ∀ (x : X), x ∈ Cc → ∀ (y : X), y ∈ Cc →
        dist x y ≤ B * (2⁻¹ : ℝ) ^ (S.2))) := by
    intro S hS
    subst hS
    obtain ⟨x0⟩ := ‹Nonempty X›
    refine ⟨by simp, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
    · intro Cc hCc
      have hCce : Cc = Set.univ := List.mem_singleton.mp hCc
      subst hCce
      exact isClopen_univ
    · intro Cc hCc
      have hCce : Cc = Set.univ := List.mem_singleton.mp hCc
      subst hCce
      exact ⟨x0, Set.mem_univ x0⟩
    · intro Cc hCc x hx y hy
      have hCce : Cc = Set.univ := List.mem_singleton.mp hCc
      subst hCce
      simpa using hBbound x y
  have hInv : ∀ t : List Bool, (brouwerState kids t).1 ≠ [] ∧
      (brouwerState kids t).1.Pairwise Disjoint ∧
      (∀ Cc ∈ (brouwerState kids t).1, IsClopen Cc) ∧
      (∀ Cc ∈ (brouwerState kids t).1, Cc.Nonempty) ∧
      (∀ Cc ∈ (brouwerState kids t).1, ∀ x ∈ Cc, ∀ y ∈ Cc,
        dist x y ≤ B * (2⁻¹ : ℝ) ^ ((brouwerState kids t).2)) := by
    intro t
    have hfoldt := hfold t ([Set.univ], (0 : ℕ)) (hInitAux _ rfl)
    simpa [brouwerState] using hfoldt
  have hChild : ∀ t : List Bool,
      brouwerPiece kids (t ++ [false]) ∪ brouwerPiece kids (t ++ [true]) =
        brouwerPiece kids t ∧
      Disjoint (brouwerPiece kids (t ++ [false])) (brouwerPiece kids (t ++ [true])) := by
    intro t
    have hRappf : brouwerState kids (t ++ [false]) =
        brouwerStep kids (brouwerState kids t) false := hRapp t false
    have hRappt : brouwerState kids (t ++ [true]) =
        brouwerStep kids (brouwerState kids t) true := hRapp t true
    obtain ⟨hne, hpair, hcl, hne', hmesh⟩ := hInv t
    cases hL : (brouwerState kids t).1 with
    | nil => exact absurd hL hne
    | cons C rest =>
      cases rest with
      | nil =>
        have hS : brouwerState kids t = ([C], (brouwerState kids t).2) := by
          rw [← hL, Prod.mk.eta]
        have hCcl : IsClopen C := hcl C (by rw [hL]; simp)
        have hCne : C.Nonempty := hne' C (by rw [hL]; simp)
        obtain ⟨Klen, Kcl, Kne, Ksub, Kmesh, Kpair, Kunion⟩ := hkids _ C hCcl hCne
        obtain ⟨a, r1, hr1⟩ := List.exists_cons_of_ne_nil (l := kids _ C)
          (by intro hcon; rw [hcon] at Klen; simp at Klen)
        have hr1ne : r1 ≠ [] := by
          intro hcon; rw [hr1, hcon] at Klen; simp at Klen
        obtain ⟨b0, rest'', hr2⟩ := List.exists_cons_of_ne_nil hr1ne
        have hK : kids (brouwerState kids t).2 C = a :: b0 :: rest'' := by rw [hr1, hr2]
        have hEf : brouwerPiece kids (t ++ [false]) = a := by
          have hst : brouwerState kids (t ++ [false]) =
              ([a], (brouwerState kids t).2 + 1) := by
            have e : brouwerStep kids ([C], (brouwerState kids t).2) false =
                ([a], (brouwerState kids t).2 + 1) := by simp only [brouwerStep, hK]
            rw [hRappf, hS]; exact e
          exact hE_single _ _ _ hst
        have hEt : brouwerPiece kids (t ++ [true]) = ⋃ s ∈ b0 :: rest'', s := by
          have hst : brouwerState kids (t ++ [true]) =
              ((b0 :: rest''), (brouwerState kids t).2 + 1) := by
            have e : brouwerStep kids ([C], (brouwerState kids t).2) true =
                ((b0 :: rest''), (brouwerState kids t).2 + 1) := by simp only [brouwerStep, hK]
            rw [hRappt, hS]; exact e
          simp only [brouwerPiece, hst]
        have hEt2 : brouwerPiece kids t = C := hE_single _ _ _ hS
        constructor
        · rw [hEf, hEt, hEt2]
          have hKK : (⋃ s ∈ a :: b0 :: rest'', s) = C := by
            rw [← hK]; exact Kunion
          rw [← list_iUnion_cons]
          exact hKK
        · rw [hEf, hEt]
          apply Set.disjoint_left.mpr
          intro x hxa hxU
          obtain ⟨s, hsU⟩ := Set.mem_iUnion.mp hxU
          obtain ⟨hsmem, hxs⟩ := Set.mem_iUnion.mp hsU
          have hpair' : (a :: b0 :: rest'').Pairwise Disjoint := by
            rw [← hK]; exact Kpair
          have hds := (List.pairwise_cons.mp hpair').1 s hsmem
          exact (Set.disjoint_left.mp hds hxa) hxs
      | cons D rest' =>
        have hS : brouwerState kids t = ((C :: D :: rest'), (brouwerState kids t).2) := by
          rw [← hL, Prod.mk.eta]
        have hEf : brouwerPiece kids (t ++ [false]) = C := by
          have hst : brouwerState kids (t ++ [false]) = ([C], (brouwerState kids t).2) := by
            have e : brouwerStep kids ((C :: D :: rest'), (brouwerState kids t).2) false =
                ([C], (brouwerState kids t).2) := by simp only [brouwerStep]
            rw [hRappf, hS]; exact e
          exact hE_single _ _ _ hst
        have hEt : brouwerPiece kids (t ++ [true]) = ⋃ s ∈ D :: rest', s := by
          have hst : brouwerState kids (t ++ [true]) =
              ((D :: rest'), (brouwerState kids t).2) := by
            have e : brouwerStep kids ((C :: D :: rest'), (brouwerState kids t).2) true =
                ((D :: rest'), (brouwerState kids t).2) := by simp only [brouwerStep]
            rw [hRappt, hS]; exact e
          simp only [brouwerPiece, hst]
        have hL2 : (brouwerState kids t).1 = C :: D :: rest' := by rw [hS]
        have hEt2 : brouwerPiece kids t = ⋃ s ∈ C :: D :: rest', s := by
          simp only [brouwerPiece, hL2]
        constructor
        · rw [hEf, hEt, hEt2]
          conv_rhs => rw [list_iUnion_cons]
        · rw [hEf, hEt]
          apply Set.disjoint_left.mpr
          intro x hxc hxU
          obtain ⟨s, hsU⟩ := Set.mem_iUnion.mp hxU
          obtain ⟨hsmem, hxs⟩ := Set.mem_iUnion.mp hsU
          have hpair' : (C :: D :: rest').Pairwise Disjoint := by
            rw [← hL]; exact hpair
          have hds := (List.pairwise_cons.mp hpair').1 s hsmem
          exact (Set.disjoint_left.mp hds hxc) hxs
  have hstep_sub : ∀ (t : List Bool) (b : Bool),
      brouwerPiece kids (t ++ [b]) ⊆ brouwerPiece kids t := by
    intro t b
    cases b with
    | false =>
      have hU := (hChild t).1
      rw [← hU]
      exact Set.subset_union_left
    | true =>
      have hU := (hChild t).1
      rw [← hU]
      exact Set.subset_union_right
  have hMono : ∀ (t₁ : List Bool) (l : List Bool),
      brouwerPiece kids (t₁ ++ l) ⊆ brouwerPiece kids t₁ := by
    intro t₁ l
    induction l generalizing t₁ with
    | nil => simp
    | cons b l ih =>
      have happ : t₁ ++ (b :: l) = (t₁ ++ [b]) ++ l := by
        rw [List.append_assoc, List.cons_append, List.nil_append]
      rw [happ]
      exact Set.Subset.trans (ih (t₁ ++ [b])) (hstep_sub t₁ b)
  have hEclopen : ∀ t : List Bool, IsClopen (brouwerPiece kids t) := by
    intro t
    have h1 : ∀ l : List (Set X), (∀ s ∈ l, IsClopen s) → IsClopen (⋃ s ∈ l, s) := by
      intro l
      induction l with
      | nil =>
        intro _
        have h0 : (⋃ s ∈ ([] : List (Set X)), s) = ∅ := by ext x; simp
        rw [h0]
        exact isClopen_empty
      | cons c l ih =>
        intro h
        rw [list_iUnion_cons]
        exact (h c (by simp)).union (ih (fun s hs => h s (by simp [hs])))
    exact h1 _ (fun Cc hCc => (hInv t).2.2.1 Cc hCc)
  have hEne : ∀ t : List Bool, (brouwerPiece kids t).Nonempty := by
    intro t
    obtain ⟨hne, -, -, hne', -⟩ := hInv t
    obtain ⟨a, r, hr⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨x, hx⟩ := hne' a (by rw [hr]; simp)
    exact ⟨x, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨(by rw [hr]; simp), hx⟩⟩⟩
  have hpref_succ : ∀ (σ : ℕ → Bool) (n : ℕ),
      brouwerPref σ (n + 1) = brouwerPref σ n ++ [σ n] := by
    intro σ n
    have e : n + 1 = n.succ := by omega
    rw [e]
    simp only [brouwerPref, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  have hPrefMono : ∀ (σ : ℕ → Bool) (m n : ℕ), m ≤ n →
      brouwerPiece kids (brouwerPref σ n) ⊆ brouwerPiece kids (brouwerPref σ m) := by
    intro σ m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => intro x hx; exact hx
    | succ k ih =>
      have e : m + (k + 1) = (m + k) + 1 := by omega
      rw [e, hpref_succ]
      exact Set.Subset.trans (hMono _ _) ih
  have hLvlSingle : ∀ (n : ℕ) (C : Set X) (b : Bool),
      (brouwerStep kids ([C], n) b).2 = n + 1 := by
    intro n C b
    cases b with
    | false =>
      cases hK : kids n C with
      | nil => simp only [brouwerStep, hK]
      | cons a r =>
        cases r with
        | nil => simp only [brouwerStep, hK]
        | cons b0 r' => simp only [brouwerStep, hK]
    | true =>
      cases hK : kids n C with
      | nil => simp only [brouwerStep, hK]
      | cons a r =>
        cases r with
        | nil => simp only [brouwerStep, hK]
        | cons b0 r' => simp only [brouwerStep, hK]
  have hLvlMulti : ∀ (n : ℕ) (C D : Set X) (rest' : List (Set X)) (b : Bool),
      (brouwerStep kids ((C :: D :: rest'), n) b).2 = n := by
    intro n C D rest' b
    cases b <;> simp only [brouwerStep]
  have hLvlMono : ∀ (t : List Bool) (b : Bool),
      (brouwerState kids t).2 ≤ (brouwerState kids (t ++ [b])).2 := by
    intro t b
    rw [hRapp t b]
    cases hL : (brouwerState kids t).1 with
    | nil => exact absurd hL (hInv t).1
    | cons C rest =>
      cases rest with
      | nil =>
        have hS : brouwerState kids t = ([C], (brouwerState kids t).2) := by
          rw [← hL, Prod.mk.eta]
        rw [hS, hLvlSingle]
        exact Nat.le_succ _
      | cons D rest' =>
        have hS : brouwerState kids t = ((C :: D :: rest'), (brouwerState kids t).2) := by
          rw [← hL, Prod.mk.eta]
        rw [hS, hLvlMulti]
  have hLvlPrefMono : ∀ (σ : ℕ → Bool) (m n : ℕ), m ≤ n →
      (brouwerState kids (brouwerPref σ m)).2 ≤
        (brouwerState kids (brouwerPref σ n)).2 := by
    intro σ m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      have e : m + (k + 1) = (m + k) + 1 := by omega
      rw [e, hpref_succ]
      exact Nat.le_trans ih (hLvlMono _ _)
  have hStateFalse : ∀ (t : List Bool) (C D : Set X) (rest' : List (Set X)) (n : ℕ),
      brouwerState kids t = ((C :: D :: rest'), n) →
      brouwerState kids (t ++ [false]) = ([C], n) := by
    intro t C D rest' n hS
    rw [hRapp t false, hS]
    simp only [brouwerStep]
  have hStateTrue : ∀ (t : List Bool) (C D : Set X) (rest' : List (Set X)) (n : ℕ),
      brouwerState kids t = ((C :: D :: rest'), n) →
      brouwerState kids (t ++ [true]) = ((D :: rest'), n) := by
    intro t C D rest' n hS
    rw [hRapp t true, hS]
    simp only [brouwerStep]
  have list_shape2 : ∀ L : List (Set X), 2 ≤ L.length →
      ∃ C D rest', L = C :: D :: rest' := by
    intro L h
    cases L with
    | nil => simp at h
    | cons C rest =>
      cases rest with
      | nil => simp at h
      | cons D rest' => exact ⟨C, D, rest', rfl⟩
  have nat_descent : ∀ L : ℕ → ℕ, ∀ M₀ : ℕ, (∀ m ≥ M₀, L (m + 1) < L m) → False := by
    intro L M₀ h
    have hle : ∀ j, L (M₀ + j) + j ≤ L M₀ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 := h (M₀ + j) (Nat.le_add_right _ _)
        have e : M₀ + (j + 1) = (M₀ + j) + 1 := by omega
        rw [e]
        omega
    have hcon := hle (L M₀ + 1)
    omega
  have nat_event_const : ∀ f : ℕ → ℕ, (∀ m n, m ≤ n → f m ≤ f n) → ∀ B,
      (∀ m, f m ≤ B) → ∃ M₀, ∀ m ≥ M₀, f m = f M₀ := by
    intro f hmono B hB
    classical
    set A : Finset ℕ := (Finset.range (B + 1)).filter (fun v => ∃ m, f m = v) with hA
    have hmem0 : f 0 ∈ A := by
      rw [hA]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB 0)), 0, rfl⟩
    have hne : A.Nonempty := ⟨f 0, hmem0⟩
    set vstar := A.max' hne with hv
    obtain ⟨Mstar, hMstar⟩ : ∃ Mstar, f Mstar = vstar := by
      have hvmem : vstar ∈ A := Finset.max'_mem A hne
      rw [hA] at hvmem
      exact (Finset.mem_filter.mp hvmem).2
    refine ⟨Mstar, fun m hm => ?_⟩
    have h1 : f Mstar ≤ f m := hmono Mstar m hm
    have h2 : f m ≤ vstar := by
      have hfm : f m ∈ A := by
        rw [hA]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hB m)), m, rfl⟩
      exact Finset.le_max' A (f m) hfm
    omega
  have hBranch : ∀ (σ : ℕ → Bool) (M₀ : ℕ) (k : ℕ),
      ∃ M, M₀ ≤ M ∧ k ≤ (brouwerState kids (brouwerPref σ M)).2 ∧
        (brouwerState kids (brouwerPref σ M)).1.length = 1 := by
    intro σ M₀ k
    by_contra hcon
    have hneg : ∀ M, M₀ ≤ M →
        ¬(k ≤ (brouwerState kids (brouwerPref σ M)).2 ∧
          (brouwerState kids (brouwerPref σ M)).1.length = 1) := by
      intro M hM hQ
      exact hcon ⟨M, hM, hQ⟩
    have hdesc : ∀ Mstar : ℕ,
        (∀ m, Mstar ≤ m → 2 ≤ (brouwerState kids (brouwerPref σ m)).1.length) →
        False := by
      intro Mstar hlen
      apply nat_descent (fun m => (brouwerState kids (brouwerPref σ m)).1.length) Mstar
      intro m hm
      obtain ⟨C, D, rest', hshape⟩ := list_shape2 _ (hlen m hm)
      have hS : brouwerState kids (brouwerPref σ m) =
          ((C :: D :: rest'), (brouwerState kids (brouwerPref σ m)).2) := by
        rw [← hshape, Prod.mk.eta]
      have hbit : σ m = true := by
        by_cases hb : σ m = true
        · exact hb
        · exfalso
          have hfalse : σ m = false := by
            cases h2 : σ m with
            | false => rfl
            | true => exact absurd h2 hb
          have hst : brouwerState kids (brouwerPref σ (m + 1)) =
              ([C], (brouwerState kids (brouwerPref σ m)).2) := by
            have e : brouwerPref σ (m + 1) = brouwerPref σ m ++ [σ m] :=
              hpref_succ σ m
            rw [e, hfalse]
            exact hStateFalse (brouwerPref σ m) C D rest' _ hS
          have hL1 : (brouwerState kids (brouwerPref σ (m + 1))).1 = [C] := by rw [hst]
          have hlen1 : (brouwerState kids (brouwerPref σ (m + 1))).1.length = 1 := by
            rw [hL1, List.length_singleton]
          have hge := hlen (m + 1) (Nat.le_succ_of_le hm)
          omega
      have hstT : brouwerState kids (brouwerPref σ (m + 1)) =
          ((D :: rest'), (brouwerState kids (brouwerPref σ m)).2) := by
        have e : brouwerPref σ (m + 1) = brouwerPref σ m ++ [σ m] :=
          hpref_succ σ m
        rw [e, hbit]
        exact hStateTrue (brouwerPref σ m) C D rest' _ hS
      have e1 : (brouwerState kids (brouwerPref σ (m + 1))).1 = D :: rest' := by rw [hstT]
      have e2 : (brouwerState kids (brouwerPref σ m)).1 = C :: D :: rest' := by rw [hS]
      have hlenEq : (brouwerState kids (brouwerPref σ (m + 1))).1.length =
          (brouwerState kids (brouwerPref σ m)).1.length - 1 := by
        simp only [e1, e2, List.length_cons]
        omega
      have h2 := hlen m hm
      change (brouwerState kids (brouwerPref σ (m + 1))).1.length <
        (brouwerState kids (brouwerPref σ m)).1.length
      omega
    by_cases hlev : ∃ M₁, M₀ ≤ M₁ ∧ k ≤ (brouwerState kids (brouwerPref σ M₁)).2
    · obtain ⟨M₁, hM₁, hk₁⟩ := hlev
      have hlen : ∀ m, M₁ ≤ m →
          2 ≤ (brouwerState kids (brouwerPref σ m)).1.length := by
        intro m hm
        have hne0 : (brouwerState kids (brouwerPref σ m)).1.length ≠ 0 := by
          intro h0
          exact (hInv (brouwerPref σ m)).1 (List.eq_nil_of_length_eq_zero h0)
        have hne1 : (brouwerState kids (brouwerPref σ m)).1.length ≠ 1 := by
          intro heq
          exact hneg m (Nat.le_trans hM₁ hm)
            ⟨Nat.le_trans hk₁ (hLvlPrefMono σ M₁ m hm), heq⟩
        omega
      exact hdesc M₁ hlen
    · have hkM₀ : (brouwerState kids (brouwerPref σ M₀)).2 < k := by
        have h1 : ¬ k ≤ (brouwerState kids (brouwerPref σ M₀)).2 :=
          fun h => hlev ⟨M₀, Nat.le_refl _, h⟩
        exact lt_of_not_ge h1
      have hbdd : ∀ m, (brouwerState kids (brouwerPref σ m)).2 ≤ k := by
        intro m
        rcases le_total m M₀ with hm | hm
        · exact Nat.le_trans (hLvlPrefMono σ m M₀ hm) (Nat.le_of_lt hkM₀)
        · have h1 : ¬ k ≤ (brouwerState kids (brouwerPref σ m)).2 :=
            fun h => hlev ⟨m, hm, h⟩
          exact Nat.le_of_lt (lt_of_not_ge h1)
      obtain ⟨Mstar, hMstar⟩ := nat_event_const _
        (fun m n hmn => hLvlPrefMono σ m n hmn) k hbdd
      have hlen : ∀ m, Mstar ≤ m →
          2 ≤ (brouwerState kids (brouwerPref σ m)).1.length := by
        intro m hm
        have hne0 : (brouwerState kids (brouwerPref σ m)).1.length ≠ 0 := by
          intro h0
          exact (hInv (brouwerPref σ m)).1 (List.eq_nil_of_length_eq_zero h0)
        have hne1 : (brouwerState kids (brouwerPref σ m)).1.length ≠ 1 := by
          intro heq
          obtain ⟨C, hCceq⟩ := List.length_eq_one_iff.mp heq
          have hSeq : brouwerState kids (brouwerPref σ m) =
              ([C], (brouwerState kids (brouwerPref σ m)).2) := by
            have hL : (brouwerState kids (brouwerPref σ m)).1 = [C] := hCceq
            rw [← hL, Prod.mk.eta]
          have hstep : (brouwerState kids (brouwerPref σ (m + 1))).2 =
              (brouwerState kids (brouwerPref σ m)).2 + 1 := by
            have e : brouwerPref σ (m + 1) = brouwerPref σ m ++ [σ m] :=
              hpref_succ σ m
            rw [e, hRapp, hSeq, hLvlSingle]
          have hc1 := hMstar (m + 1) (Nat.le_succ_of_le hm)
          have hc0 := hMstar m hm
          omega
        omega
      exact hdesc Mstar hlen
  have hDiamSingle : ∀ (t : List Bool) (Cc : Set X) (n : ℕ),
      brouwerState kids t = ([Cc], n) → ∀ x ∈ brouwerPiece kids t,
        ∀ y ∈ brouwerPiece kids t, dist x y ≤ B * (2⁻¹ : ℝ) ^ n := by
    intro t Cc n hS x hx y hy
    rw [hE_single t Cc n hS] at hx hy
    have hn : (brouwerState kids t).2 = n := by rw [hS]
    have hmesh := (hInv t).2.2.2.2 Cc (by simp [hS]) x hx y hy
    rw [hn] at hmesh
    exact hmesh
  have hexp : ∀ ε > 0, ∃ k : ℕ, B * (2⁻¹ : ℝ) ^ k < ε := by
    intro ε hε
    have hT : Filter.Tendsto (fun k : ℕ => (2⁻¹ : ℝ) ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hT2 : Filter.Tendsto (fun k : ℕ => B * (2⁻¹ : ℝ) ^ k) Filter.atTop
        (nhds (B * 0)) :=
      hT.const_mul B
    rw [mul_zero] at hT2
    exact (hT2.eventually (gt_mem_nhds hε)).exists
  have hInter : ∀ σ : ℕ → Bool,
      (⋂ n, brouwerPiece kids (brouwerPref σ n)).Nonempty := by
    intro σ
    by_contra hcon
    have hempty : ⋂ n, brouwerPiece kids (brouwerPref σ n) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hcon
    have hK0 : IsCompact (brouwerPiece kids (brouwerPref σ 0)) :=
      (hEclopen _).isClosed.isCompact
    have hcov : brouwerPiece kids (brouwerPref σ 0) ⊆
        ⋃ n, (brouwerPiece kids (brouwerPref σ 0) \ brouwerPiece kids (brouwerPref σ n)) := by
      intro x hx
      by_contra hmem
      have hmem' : ∀ n, x ∈ brouwerPiece kids (brouwerPref σ n) := by
        intro n
        by_contra hn
        exact hmem (Set.mem_iUnion.mpr ⟨n, hx, hn⟩)
      have hxI : x ∈ ⋂ n, brouwerPiece kids (brouwerPref σ n) :=
        Set.mem_iInter.mpr hmem'
      rw [hempty] at hxI
      exact Set.notMem_empty x hxI
    obtain ⟨t, ht⟩ := hK0.elim_finite_subcover
      (fun n => brouwerPiece kids (brouwerPref σ 0) \ brouwerPiece kids (brouwerPref σ n))
      (fun n => (hEclopen _).isOpen.sdiff (hEclopen _).isClosed) hcov
    set N : ℕ := t.sup id with hN
    have hNbound : ∀ n ∈ t, n ≤ N := by
      intro n hn
      have h1 : id n ≤ t.sup id := Finset.le_sup hn
      rw [hN]
      exact h1
    have hKNsub : brouwerPiece kids (brouwerPref σ N) ⊆ ∅ := by
      intro x hxN
      have hx0 : x ∈ brouwerPiece kids (brouwerPref σ 0) :=
        hPrefMono σ 0 N (Nat.zero_le _) hxN
      have hxU := ht hx0
      obtain ⟨n, hnU⟩ := Set.mem_iUnion.mp hxU
      obtain ⟨hnt, hmem⟩ := Set.mem_iUnion.mp hnU
      have hxNn : x ∉ brouwerPiece kids (brouwerPref σ n) := hmem.2
      have hsub := hPrefMono σ n N (hNbound n (Finset.mem_coe.mp hnt)) hxN
      exact hxNn hsub
    obtain ⟨x, hx⟩ := hEne (brouwerPref σ N)
    exact Set.notMem_empty x (hKNsub hx)
  have huniq : ∀ (σ : ℕ → Bool) (y z : X),
      (∀ m, y ∈ brouwerPiece kids (brouwerPref σ m)) →
        (∀ m, z ∈ brouwerPiece kids (brouwerPref σ m)) → y = z := by
    intro σ y z hy hz
    have hle : ∀ k : ℕ, dist y z ≤ B * (2⁻¹ : ℝ) ^ k := by
      intro k
      obtain ⟨M, -, hkM, hlenM⟩ := hBranch σ 0 k
      obtain ⟨Cc, hCceq⟩ := List.length_eq_one_iff.mp hlenM
      have hL : (brouwerState kids (brouwerPref σ M)).1 = [Cc] := hCceq
      have hSeq : brouwerState kids (brouwerPref σ M) =
          ([Cc], (brouwerState kids (brouwerPref σ M)).2) := by
        rw [← hL, Prod.mk.eta]
      have hyM : y ∈ Cc := by
        have h1 := hy M
        rw [hE_single _ _ _ hSeq] at h1
        exact h1
      have hzM : z ∈ Cc := by
        have h1 := hz M
        rw [hE_single _ _ _ hSeq] at h1
        exact h1
      have hmesh := (hInv (brouwerPref σ M)).2.2.2.2 Cc (by simp [hL]) y hyM z hzM
      have hpow : (2⁻¹ : ℝ) ^ (brouwerState kids (brouwerPref σ M)).2 ≤ (2⁻¹ : ℝ) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hkM
      calc dist y z ≤ B * (2⁻¹ : ℝ) ^ (brouwerState kids (brouwerPref σ M)).2 := hmesh
        _ ≤ B * (2⁻¹ : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hBpos)
    have h0 : dist y z = 0 := by
      by_contra hne
      have hpos : 0 < dist y z := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
      obtain ⟨k, hk⟩ := hexp (dist y z) hpos
      exact absurd (hle k) (not_le_of_gt hk)
    exact dist_eq_zero.mp h0
  have hex : ∀ σ : ℕ → Bool, ∃ x : X, (∀ m, x ∈ brouwerPiece kids (brouwerPref σ m)) ∧
      ∀ y : X, (∀ m, y ∈ brouwerPiece kids (brouwerPref σ m)) → y = x := by
    intro σ
    obtain ⟨x, hx⟩ := hInter σ
    refine ⟨x, fun m => Set.mem_iInter.mp hx m, fun y hy => huniq σ y x hy ?_⟩
    exact fun m => Set.mem_iInter.mp hx m
  choose f hf using hex
  have hf_mem : ∀ (σ : ℕ → Bool) (m : ℕ), f σ ∈ brouwerPiece kids (brouwerPref σ m) :=
    fun σ m => (hf σ).1 m
  have hf_unique : ∀ (σ : ℕ → Bool) (y : X),
      (∀ m, y ∈ brouwerPiece kids (brouwerPref σ m)) → y = f σ :=
    fun σ y hy => (hf σ).2 y hy
  have hf_cont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro σ
    change Filter.Tendsto f (nhds σ) (nhds (f σ))
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := hexp ε hε
    obtain ⟨M, -, hkM, hlenM⟩ := hBranch σ 0 k
    obtain ⟨Cc, hCceq⟩ := List.length_eq_one_iff.mp hlenM
    have hL : (brouwerState kids (brouwerPref σ M)).1 = [Cc] := hCceq
    have hSeq : brouwerState kids (brouwerPref σ M) =
        ([Cc], (brouwerState kids (brouwerPref σ M)).2) := by
      rw [← hL, Prod.mk.eta]
    have hCdiam : ∀ a ∈ Cc, ∀ b ∈ Cc, dist a b ≤ B * (2⁻¹ : ℝ) ^ k := by
      intro a ha b hb
      have hmesh := (hInv (brouwerPref σ M)).2.2.2.2 Cc (by simp [hL]) a ha b hb
      have hpow : (2⁻¹ : ℝ) ^ (brouwerState kids (brouwerPref σ M)).2 ≤ (2⁻¹ : ℝ) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hkM
      exact le_trans hmesh (mul_le_mul_of_nonneg_left hpow (le_of_lt hBpos))
    set C : Set (ℕ → Bool) := {τ | ∀ i ∈ Finset.range M, τ i = σ i} with hC
    have hCeq : C = ⋂ i ∈ Finset.range M, (fun τ : ℕ → Bool => τ i) ⁻¹' {σ i} := by
      ext τ
      simp [hC]
    have hCnhds : C ∈ nhds σ := by
      rw [hCeq, Filter.biInter_finset_mem]
      intro i _
      exact IsOpen.mem_nhds ((continuous_apply i).isOpen_preimage _ (isOpen_discrete _))
        (Set.mem_singleton_iff.mpr rfl)
    filter_upwards [hCnhds] with τ hτ
    have hτ' : ∀ i ∈ Finset.range M, τ i = σ i := hτ
    have hpref : brouwerPref τ M = brouwerPref σ M := by
      have hagree : ∀ j, j ≤ M → brouwerPref τ j = brouwerPref σ j := by
        intro j
        induction j with
        | zero => intro _; rfl
        | succ j ih =>
          intro hj
          have hjM : j < M := by omega
          have e1 : τ j = σ j := hτ' j (Finset.mem_range.mpr hjM)
          have e2 := ih (by omega)
          rw [hpref_succ τ j, hpref_succ σ j, e2, e1]
      exact hagree M (Nat.le_refl _)
    have hfτ : f τ ∈ Cc := by
      have h1 := hf_mem τ M
      rw [hpref, hE_single _ _ _ hSeq] at h1
      exact h1
    have hfσ : f σ ∈ Cc := by
      have h1 := hf_mem σ M
      rw [hE_single _ _ _ hSeq] at h1
      exact h1
    have hle := hCdiam (f τ) hfτ (f σ) hfσ
    exact lt_of_le_of_lt hle hk
  have hinj : Function.Injective f := by
    intro σ τ hst
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have hexNE : ∃ n, σ n ≠ τ n := ⟨i, hi⟩
    obtain ⟨i₀, hi₀, hmin⟩ : ∃ i₀, σ i₀ ≠ τ i₀ ∧ ∀ j < i₀, σ j = τ j := by
      refine ⟨Nat.find hexNE, Nat.find_spec hexNE, fun j hj => ?_⟩
      by_contra hcon
      exact Nat.find_min hexNE hj hcon
    have hpeq : brouwerPref σ i₀ = brouwerPref τ i₀ := by
      have hagree : ∀ j, j ≤ i₀ → brouwerPref σ j = brouwerPref τ j := by
        intro j
        induction j with
        | zero => intro _; rfl
        | succ j ih =>
          intro hj
          have hjM : j < i₀ := by omega
          have e1 : σ j = τ j := hmin j hjM
          have e2 := ih (by omega)
          rw [hpref_succ σ j, hpref_succ τ j, e2, e1]
      exact hagree i₀ (Nat.le_refl _)
    have eσ : brouwerPref σ (i₀ + 1) = brouwerPref σ i₀ ++ [σ i₀] := hpref_succ σ i₀
    have eτ : brouwerPref τ (i₀ + 1) = brouwerPref τ i₀ ++ [τ i₀] := hpref_succ τ i₀
    have hdisj := (hChild (brouwerPref σ i₀)).2
    cases hb : σ i₀ with
    | false =>
      have hτt : τ i₀ = true := by
        by_cases hτ : τ i₀ = true
        · exact hτ
        · cases h2 : τ i₀ with
          | false =>
            rw [h2] at hi₀
            rw [hb] at hi₀
            exact absurd rfl hi₀
          | true => exact absurd h2 hτ
      have d1 : brouwerPiece kids (brouwerPref σ (i₀ + 1)) =
          brouwerPiece kids (brouwerPref σ i₀ ++ [false]) := by
        rw [eσ, hb]
      have d2 : brouwerPiece kids (brouwerPref τ (i₀ + 1)) =
          brouwerPiece kids (brouwerPref σ i₀ ++ [true]) := by
        rw [eτ, hτt, hpeq]
      have hmσ : f σ ∈ brouwerPiece kids (brouwerPref σ i₀ ++ [false]) := by
        rw [← d1]
        exact hf_mem σ (i₀ + 1)
      have hmτ : f τ ∈ brouwerPiece kids (brouwerPref σ i₀ ++ [true]) := by
        rw [← d2]
        exact hf_mem τ (i₀ + 1)
      have hcon := Set.disjoint_left.mp hdisj hmσ
      rw [hst] at hcon
      exact hcon hmτ
    | true =>
      have hτf : τ i₀ = false := by
        by_cases hτ : τ i₀ = false
        · exact hτ
        · cases h2 : τ i₀ with
          | false => exact absurd h2 hτ
          | true =>
            rw [h2] at hi₀
            rw [hb] at hi₀
            exact absurd rfl hi₀
      have d1 : brouwerPiece kids (brouwerPref σ (i₀ + 1)) =
          brouwerPiece kids (brouwerPref σ i₀ ++ [true]) := by
        rw [eσ, hb]
      have d2 : brouwerPiece kids (brouwerPref τ (i₀ + 1)) =
          brouwerPiece kids (brouwerPref σ i₀ ++ [false]) := by
        rw [eτ, hτf, hpeq]
      have hmσ : f σ ∈ brouwerPiece kids (brouwerPref σ i₀ ++ [true]) := by
        rw [← d1]
        exact hf_mem σ (i₀ + 1)
      have hmτ : f τ ∈ brouwerPiece kids (brouwerPref σ i₀ ++ [false]) := by
        rw [← d2]
        exact hf_mem τ (i₀ + 1)
      have hcon := Set.disjoint_left.mp hdisj hmτ
      rw [← hst] at hcon
      exact hcon hmσ
  have hsurj : Function.Surjective f := by
    intro x
    have hbit' : ∀ t : List Bool, ∃ b : Bool,
        (x ∈ brouwerPiece kids t → x ∈ brouwerPiece kids (t ++ [b])) := by
      intro t
      by_cases h : x ∈ brouwerPiece kids (t ++ [false])
      · exact ⟨false, fun _ => h⟩
      · refine ⟨true, fun hxt => ?_⟩
        have hU := (hChild t).1
        rw [← hU] at hxt
        exact ((Set.mem_union _ _ _).mp hxt).resolve_left h
    choose B hB using hbit'
    let T : ℕ → List Bool :=
      fun n => Nat.rec (motive := fun _ => List Bool) [] (fun _ prev => prev ++ [B prev]) n
    have hT0 : T 0 = [] := rfl
    have hTs : ∀ n, T (n + 1) = T n ++ [B (T n)] := fun n => rfl
    have hE0 : brouwerPiece kids [] = Set.univ := hE_single [] _ _ rfl
    have hTmem : ∀ n, x ∈ brouwerPiece kids (T n) := by
      intro n
      induction n with
      | zero => rw [hT0, hE0]; exact Set.mem_univ x
      | succ n ih => rw [hTs n]; exact hB (T n) ih
    set σ : ℕ → Bool := fun n => B (T n) with hσ
    have hpref : ∀ n, brouwerPref σ n = T n := by
      intro n
      induction n with
      | zero => rw [hT0]; rfl
      | succ n ih =>
        have e : brouwerPref σ (n + 1) = brouwerPref σ n ++ [σ n] := hpref_succ σ n
        rw [e, ih, hTs n]
    have hxmem : ∀ m, x ∈ brouwerPiece kids (brouwerPref σ m) := by
      intro m
      rw [hpref]
      exact hTmem m
    exact ⟨σ, (hf_unique σ x hxmem).symm⟩
  have he : Continuous ⇑(Equiv.ofBijective f ⟨hinj, hsurj⟩) := hf_cont
  exact ⟨(Continuous.homeoOfEquivCompactToT2 he).symm⟩

end MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted
