/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.Chain
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Road coloring theorem

This file proves the road coloring theorem of A. N. Trahtman, "The road coloring problem",
Israel J. Math. 172 (2009) 51–60. The proof follows the reduction of Culik, Karhumäki and Kari:
a recoloring with a stable pair passes to a smaller quotient automaton, and synchronizing words
lift back. Stable pairs come from two bunches into one vertex, or else from Trahtman's lemma on
spanning subgraphs with a unique highest tree, via Kari's minimal-rank argument.
-/

@[expose] public section

namespace MetaMathlibExt

section

namespace RoadColoring

private def rc_adj {V : Type*} {k : ℕ} (delta : V → Fin k → V) (v w : V) : Prop :=
  ∃ a : Fin k, delta v a = w

private def rc_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) : V → Fin k → V :=
  fun v a => delta v (sigma v a)

private def rc_sync {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl delta v word = r

private def rc_strongly {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (rc_adj delta) u v

private def rc_aperiodic {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Prop :=
  ∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
    List.IsChain (rc_adj delta) (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)

private theorem rc_adj_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) :
    rc_adj (rc_recolor delta sigma) = rc_adj delta := by
  funext v w
  apply propext
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨sigma v a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨(sigma v).symm a, by simpa [rc_recolor, Equiv.apply_symm_apply] using ha⟩

private theorem rc_recolor_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma tau : V → Equiv.Perm (Fin k)) :
    rc_recolor (rc_recolor delta sigma) tau =
      rc_recolor delta (fun v => sigma v * tau v) := by
  funext v a
  simp [rc_recolor, Equiv.Perm.mul_apply]

private theorem rc_strongly_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) :
    rc_strongly (rc_recolor delta sigma) ↔ rc_strongly delta := by
  unfold rc_strongly
  rw [rc_adj_recolor]

private theorem rc_aperiodic_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) :
    rc_aperiodic (rc_recolor delta sigma) ↔ rc_aperiodic delta := by
  unfold rc_aperiodic
  rw [rc_adj_recolor]

private theorem rc_exists_word_of_reflTransGen {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    {u v : V} (h : Relation.ReflTransGen (rc_adj delta) u v) :
    ∃ w : List (Fin k), List.foldl delta u w = v := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | tail _ hab ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨a, ha⟩ := hab
    exact ⟨w ++ [a], by rw [List.foldl_append]; simp [hw, ha]⟩

private theorem rc_recolor_realizes_ssg {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (g : V → V) (hg : ∀ v : V, rc_adj delta v (g v)) (a : Fin k) :
    ∃ sigma : V → Equiv.Perm (Fin k),
      ∀ v : V, rc_recolor delta sigma v a = g v := by
  choose c hc using hg
  exact ⟨fun v => Equiv.swap a (c v), fun v => by
    simp [rc_recolor, Equiv.swap_apply_left, hc v]⟩

private theorem rc_automaton_of_regular {V : Type*} (Adj : V → V → Prop) (k : ℕ)
    (e : ∀ v : V, { w : V // Adj v w } ≃ Fin k) :
    ∃ delta : V → Fin k → V,
      (∀ v a, Adj v (delta v a)) ∧
      (∀ v, Function.Injective (delta v)) ∧
      (∀ v w, Adj v w → ∃ a, delta v a = w) ∧
      rc_adj delta = Adj ∧
      ∀ sigma : V → Equiv.Perm (Fin k),
        (∀ v a, Adj v (rc_recolor delta sigma v a)) ∧
        (∀ v, Function.Injective (rc_recolor delta sigma v)) ∧
        (∀ v w, Adj v w → ∃ a, rc_recolor delta sigma v a = w) := by
  refine ⟨fun v a => ((e v).symm a).val, fun v a => ((e v).symm a).property, ?_, ?_, ?_, ?_⟩
  · intro v a b hab
    have h : (e v).symm a = (e v).symm b := Subtype.ext hab
    exact (e v).symm.injective h
  · intro v w hw
    exact ⟨e v ⟨w, hw⟩, by simp⟩
  · funext v w
    apply propext
    constructor
    · rintro ⟨a, rfl⟩
      exact ((e v).symm a).property
    · intro hw
      exact ⟨e v ⟨w, hw⟩, by simp⟩
  · intro sigma
    refine ⟨fun v a => ((e v).symm (sigma v a)).property, ?_, ?_⟩
    · intro v a b hab
      have h : (e v).symm (sigma v a) = (e v).symm (sigma v b) := Subtype.ext hab
      have h2 := (e v).symm.injective h
      exact (sigma v).injective h2
    · intro v w hw
      refine ⟨(sigma v).symm (e v ⟨w, hw⟩), ?_⟩
      change ((e v).symm (sigma v ((sigma v).symm (e v ⟨w, hw⟩)))).val = w
      rw [Equiv.apply_symm_apply]
      exact congrArg Subtype.val (Equiv.symm_apply_apply (e v) ⟨w, hw⟩)

private def rc_stable {V : Type*} {k : ℕ} (delta : V → Fin k → V) (p q : V) : Prop :=
  ∀ u : List (Fin k), ∃ v : List (Fin k),
    List.foldl delta p (u ++ v) = List.foldl delta q (u ++ v)

private theorem rc_stable_refl {V : Type*} {k : ℕ} (delta : V → Fin k → V) (p : V) :
    rc_stable delta p p := fun u => ⟨[], by simp⟩

private theorem rc_stable_symm {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) : rc_stable delta q p :=
  fun u => by obtain ⟨v, hv⟩ := h u; exact ⟨v, hv.symm⟩

private theorem rc_stable_trans {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q s : V} (hpq : rc_stable delta p q) (hqs : rc_stable delta q s) :
    rc_stable delta p s := by
  intro u
  obtain ⟨v1, hv1⟩ := hpq u
  obtain ⟨v2, hv2⟩ := hqs (u ++ v1)
  refine ⟨v1 ++ v2, ?_⟩
  have assoc : (u ++ v1) ++ v2 = u ++ (v1 ++ v2) := List.append_assoc u v1 v2
  have ep : List.foldl delta p (u ++ (v1 ++ v2)) =
      List.foldl delta (List.foldl delta p (u ++ v1)) v2 := by
    rw [← assoc, List.foldl_append]
  have es : List.foldl delta s (u ++ (v1 ++ v2)) =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 := by
    rw [← assoc, List.foldl_append]
  have qe : List.foldl delta q ((u ++ v1) ++ v2) =
      List.foldl delta (List.foldl delta q (u ++ v1)) v2 :=
    List.foldl_append
  have se : List.foldl delta s ((u ++ v1) ++ v2) =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 :=
    List.foldl_append
  have hv2' : List.foldl delta (List.foldl delta q (u ++ v1)) v2 =
      List.foldl delta (List.foldl delta s (u ++ v1)) v2 := by
    rw [← qe, ← se]
    exact hv2
  calc List.foldl delta p (u ++ (v1 ++ v2))
      = List.foldl delta (List.foldl delta p (u ++ v1)) v2 := ep
    _ = List.foldl delta (List.foldl delta q (u ++ v1)) v2 := by rw [hv1]
    _ = List.foldl delta (List.foldl delta s (u ++ v1)) v2 := hv2'
    _ = List.foldl delta s (u ++ (v1 ++ v2)) := es.symm

private theorem rc_stable_foldl {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) (w : List (Fin k)) :
    rc_stable delta (List.foldl delta p w) (List.foldl delta q w) := by
  intro u
  obtain ⟨v, hv⟩ := h (w ++ u)
  refine ⟨v, ?_⟩
  have assoc : (w ++ u) ++ v = w ++ (u ++ v) := List.append_assoc w u v
  have e1 : List.foldl delta p ((w ++ u) ++ v) =
      List.foldl delta (List.foldl delta p w) (u ++ v) := by
    rw [assoc, List.foldl_append, List.foldl_append]
  have e2 : List.foldl delta q ((w ++ u) ++ v) =
      List.foldl delta (List.foldl delta q w) (u ++ v) := by
    rw [assoc, List.foldl_append, List.foldl_append]
  rw [e1] at hv
  rw [e2] at hv
  exact hv

private theorem rc_stable_merge {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {p q : V} (h : rc_stable delta p q) :
    ∃ v : List (Fin k),
      List.foldl delta p v = List.foldl delta q v := by
  obtain ⟨v, hv⟩ := h []
  exact ⟨v, by simpa using hv⟩

private theorem rc_exists_branching {V : Type*} [Fintype V] {k : ℕ}
    (delta : V → Fin k → V) (hcard : 1 < Fintype.card V)
    (hcon : rc_strongly delta) (haper : rc_aperiodic delta) :
    ∃ v a b, delta v a ≠ delta v b := by
  by_contra hncon
  have hno : ∀ v (a b : Fin k), delta v a = delta v b :=
    fun v a b => of_not_not (fun h => hncon ⟨v, a, b, h⟩)
  have hneV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨u₀⟩ := hneV
  obtain ⟨w₀, hne₀⟩ := Fintype.exists_ne_of_one_lt_card hcard u₀
  have hne : u₀ ≠ w₀ := Ne.symm hne₀
  have hk : 0 < k := by
    by_contra hkpos
    have hk0 : k = 0 := by omega
    have hempty : ∀ x y : V, ¬ rc_adj delta x y := by
      intro x y h
      obtain ⟨a, _⟩ := h
      exact Fin.elim0 (hk0 ▸ a)
    have huw : u₀ = w₀ := by
      have h := hcon u₀ w₀
      induction h with
      | refl => rfl
      | tail _ hab _ => exact (hempty _ _ hab).elim
    exact hne huw
  classical
  have a₀ : Fin k := ⟨0, hk⟩
  set g : V → V := fun v => delta v a₀ with hg
  have hgraph : ∀ v w : V, rc_adj delta v w ↔ g v = w := by
    intro v w
    constructor
    · rintro ⟨a, ha⟩
      exact (hno v a a₀).symm.trans ha
    · intro h
      exact ⟨a₀, h⟩
  have hit : ∀ u w : V, ∃ i : ℕ, g^[i] u = w := by
    intro u w
    have h := hcon u w
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hab ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨a, ha⟩ := hab
      refine ⟨i + 1, ?_⟩
      rw [show i + 1 = i.succ from rfl, Function.iterate_succ_apply']
      rw [hi]
      exact (hno _ a₀ a).trans ha
  have hsurj : Function.Surjective g := by
    intro w
    have hne_w : ∃ u : V, u ≠ w := by
      by_contra hcon
      have hall : ∀ u : V, u = w := fun u => of_not_not (fun hne => hcon ⟨u, hne⟩)
      have hle : Fintype.card V ≤ 1 :=
        Fintype.card_le_one_iff.mpr (fun a b => (hall a).trans (hall b).symm)
      omega
    obtain ⟨u, huw⟩ := hne_w
    obtain ⟨i, hi⟩ := hit u w
    cases i with
    | zero =>
      have huv : u = w := hi
      exact absurd huv huw
    | succ j =>
      rw [Function.iterate_succ_apply'] at hi
      exact ⟨g^[j] u, hi⟩
  have hinj : Function.Injective g := Finite.injective_iff_surjective.mpr hsurj
  have hgen : ∀ (w : List V) (u last : V), List.IsChain (rc_adj delta) (u :: w) →
      w.getLast? = some last → g^[w.length] u = last := by
    intro w
    induction w with
    | nil => intro u last _ hlast; simp at hlast
    | cons x xs ih =>
      intro u last hchain hlast
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hhead, htail⟩ := hchain
      have hux : g u = x := (hgraph u x).mp hhead
      cases xs with
      | nil =>
        cases hlast
        have hlen : ([x]).length = 1 := rfl
        rw [hlen, Function.iterate_one]
        exact hux
      | cons y ys =>
        rw [List.getLast?_cons_cons] at hlast
        have hih := ih x last htail hlast
        have hlen : (x :: y :: ys).length = (y :: ys).length + 1 := rfl
        rw [hlen, Function.iterate_succ_apply, hux]
        exact hih
  have hper_eq : ∀ x : V, Function.minimalPeriod g x = Fintype.card V := by
    intro x
    have hxper : x ∈ Function.periodicPts g := hinj.mem_periodicPts x
    have hnpos : 0 < Function.minimalPeriod g x :=
      Function.minimalPeriod_pos_of_mem_periodicPts hxper
    have hsurj' : Function.Surjective
        (fun i : Fin (Function.minimalPeriod g x) => g^[i.val] x) := by
      intro w
      obtain ⟨i, hi⟩ := hit x w
      have hpern : g^[(Function.minimalPeriod g x) * (i / Function.minimalPeriod g x)] x = x :=
        Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (Nat.dvd_mul_right _ _)
      have hdecomp : i % Function.minimalPeriod g x +
          Function.minimalPeriod g x * (i / Function.minimalPeriod g x) = i :=
        Nat.mod_add_div i _
      have hi2 : g^[i % Function.minimalPeriod g x +
          Function.minimalPeriod g x * (i / Function.minimalPeriod g x)] x = w := by
        rw [hdecomp]
        exact hi
      rw [Function.iterate_add_apply, hpern] at hi2
      exact ⟨⟨i % Function.minimalPeriod g x, Nat.mod_lt i hnpos⟩, hi2⟩
    have hfin : Fintype.card V ≤
        Fintype.card (Fin (Function.minimalPeriod g x)) :=
      Fintype.card_le_of_surjective _ hsurj'
    rw [Fintype.card_fin] at hfin
    exact Nat.le_antisymm (Function.minimalPeriod_le_card (f := g) (x := x)) hfin
  obtain ⟨u, w, hchain, hlast, hdiv⟩ := haper _ hcard
  have hfix : g^[w.length] u = u := hgen w u u hchain hlast
  have hdvd : Fintype.card V ∣ w.length := by
    have h := Function.IsPeriodicPt.minimalPeriod_dvd hfix
    rwa [hper_eq u] at h
  exact hdiv hdvd

private theorem rc_exists_merge_of_pairwise_stable {V : Type*} [Nonempty V]
    {k : ℕ} (delta : V → Fin k → V) :
    ∀ S : Finset V, (∀ p ∈ S, ∀ q ∈ S, rc_stable delta p q) →
    ∃ w : List (Fin k), ∃ r : V, ∀ v ∈ S, List.foldl delta v w = r := by
  classical
  obtain ⟨r₀⟩ := (‹Nonempty V› : Nonempty V)
  have key : ∀ m : ℕ, ∀ T : Finset V, T.card ≤ m →
      (∀ p ∈ T, ∀ q ∈ T, rc_stable delta p q) →
      ∃ w : List (Fin k), ∃ r : V, ∀ v ∈ T, List.foldl delta v w = r := by
    intro m
    induction m with
    | zero =>
      intro T hcard h
      have hempty : T = ∅ := Finset.card_eq_zero.mp (by omega)
      exact ⟨[], r₀,
        fun v hv => by rw [hempty] at hv; exact absurd hv (Finset.notMem_empty v)⟩
    | succ m ih =>
      intro T hcard h
      by_cases hle : T.card ≤ 1
      · by_cases hT : T.Nonempty
        · obtain ⟨p, hp⟩ := hT
          refine ⟨[], p, fun v hv => ?_⟩
          have hvp : v = p := Finset.card_le_one_iff.mp hle hv hp
          rw [hvp]
          rfl
        · have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
          exact ⟨[], r₀,
            fun v hv => by rw [hT'] at hv; exact absurd hv (Finset.notMem_empty v)⟩
      · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have hcardE : 0 < (T.erase p).card := by
          rw [Finset.card_erase_of_mem hp]
          omega
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hcardE
        have hqT : q ∈ T := Finset.mem_of_mem_erase hq
        have hne : q ≠ p := Finset.ne_of_mem_erase hq
        obtain ⟨t, ht⟩ := rc_stable_merge delta (h p hp q hqT)
        have hlt : (T.image (fun x => List.foldl delta x t)).card < T.card := by
          by_contra hcon
          have hle2 := Finset.card_image_le (s := T)
            (f := fun x => List.foldl delta x t)
          have heq : (T.image (fun x => List.foldl delta x t)).card = T.card := by
            omega
          have hinj := Finset.card_image_iff.mp heq
          exact hne (hinj (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hqT) ht).symm
        have hstab : ∀ y₁ ∈ T.image (fun x => List.foldl delta x t),
            ∀ y₂ ∈ T.image (fun x => List.foldl delta x t),
            rc_stable delta y₁ y₂ := by
          intro y₁ hy₁ y₂ hy₂
          obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hy₁
          obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hy₂
          exact rc_stable_foldl delta (h x₁ hx₁ x₂ hx₂) t
        obtain ⟨w', r, hr⟩ := ih _ (by omega) hstab
        exact ⟨t ++ w', r, fun v hv => by
          rw [List.foldl_append]
          exact hr _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩
  intro S hS
  exact key S.card S le_rfl hS

private noncomputable def rc_minRank {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V) : ℕ := by
  classical
  exact Nat.find (p := fun n => ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = n)
    ⟨Fintype.card V, [], by simp⟩

private theorem rc_minRank_le {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V) (w : List (Fin k)) :
    rc_minRank delta ≤ (Finset.univ.image (fun v => List.foldl delta v w)).card := by
  classical
  exact Nat.find_min' (p := fun n => ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = n) _ ⟨w, rfl⟩

private theorem rc_minRank_attained {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V) :
    ∃ w : List (Fin k),
      (Finset.univ.image (fun v => List.foldl delta v w)).card = rc_minRank delta := by
  classical
  exact Nat.find_spec (p := fun n => ∃ w : List (Fin k),
    (Finset.univ.image (fun v => List.foldl delta v w)).card = n) _

private theorem rc_image_append {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V) (w u : List (Fin k)) :
    (Finset.univ.image (fun v => List.foldl delta v w)).image
        (fun x => List.foldl delta x u) =
      Finset.univ.image (fun v => List.foldl delta v (w ++ u)) := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, ⟨v, h1⟩, h2⟩
    exact ⟨v, by rw [List.foldl_append, h1]; exact h2⟩
  · rintro ⟨v, h⟩
    refine ⟨List.foldl delta v w, ⟨v, rfl⟩, ?_⟩
    rw [← List.foldl_append]
    exact h

private theorem rc_injOn_of_minRank {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V) (w : List (Fin k))
    (hcard : (Finset.univ.image (fun v => List.foldl delta v w)).card =
      rc_minRank delta) (u : List (Fin k)) :
    Set.InjOn (fun x => List.foldl delta x u)
        (Finset.univ.image (fun v => List.foldl delta v w)) ∧
      (Finset.univ.image (fun v => List.foldl delta v (w ++ u))).card =
        rc_minRank delta := by
  classical
  have hJ : (Finset.univ.image (fun v => List.foldl delta v w)).image
      (fun x => List.foldl delta x u) =
      Finset.univ.image (fun v => List.foldl delta v (w ++ u)) :=
    rc_image_append delta w u
  have hge : rc_minRank delta ≤
      ((Finset.univ.image (fun v => List.foldl delta v w)).image
        (fun x => List.foldl delta x u)).card := by
    rw [hJ]
    exact rc_minRank_le delta (w ++ u)
  have hle : ((Finset.univ.image (fun v => List.foldl delta v w)).image
        (fun x => List.foldl delta x u)).card ≤
      (Finset.univ.image (fun v => List.foldl delta v w)).card :=
    Finset.card_image_le
  have hJcard : ((Finset.univ.image (fun v => List.foldl delta v w)).image
        (fun x => List.foldl delta x u)).card = rc_minRank delta := by
    omega
  refine ⟨Finset.card_image_iff.mp (by omega), by rw [← hJ]; exact hJcard⟩

private theorem rc_stable_of_one_difference {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (C : Finset V) (x y : V)
    (hx : x ∉ C) (hy : y ∉ C) (hxy : x ≠ y)
    (w₁ w₂ : List (Fin k))
    (h1 : Finset.univ.image (fun v => List.foldl delta v w₁) = insert x C)
    (h2 : Finset.univ.image (fun v => List.foldl delta v w₂) = insert y C)
    (hc1 : (Finset.univ.image (fun v => List.foldl delta v w₁)).card =
      rc_minRank delta)
    (hc2 : (Finset.univ.image (fun v => List.foldl delta v w₂)).card =
      rc_minRank delta) :
    rc_stable delta x y := by
  classical
  intro u
  by_contra hcon
  have hnon : ∀ v : List (Fin k),
      List.foldl delta x (u ++ v) ≠ List.foldl delta y (u ++ v) :=
    fun v h => hcon ⟨v, h⟩
  have e1 : ∀ v : List (Fin k), List.foldl delta x (u ++ v) =
      List.foldl delta (List.foldl delta x u) v := by
    intro v
    rw [List.foldl_append]
  have e2 : ∀ v : List (Fin k), List.foldl delta y (u ++ v) =
      List.foldl delta (List.foldl delta y u) v := by
    intro v
    rw [List.foldl_append]
  have hnon' : ∀ v : List (Fin k), List.foldl delta (List.foldl delta x u) v ≠
      List.foldl delta (List.foldl delta y u) v := by
    intro v hmerge
    apply hnon v
    rw [e1, e2]
    exact hmerge
  obtain ⟨hinj1, hcard1⟩ := rc_injOn_of_minRank delta w₁ hc1 u
  obtain ⟨hinj2, hcard2⟩ := rc_injOn_of_minRank delta w₂ hc2 u
  have hxw1 : x ∈ Finset.univ.image (fun v => List.foldl delta v w₁) := by
    rw [h1]
    exact Finset.mem_insert_self x C
  have hyw2 : y ∈ Finset.univ.image (fun v => List.foldl delta v w₂) := by
    rw [h2]
    exact Finset.mem_insert_self y C
  have hCw1 : ∀ c ∈ C,
      c ∈ Finset.univ.image (fun v => List.foldl delta v w₁) := by
    intro c hc
    rw [h1]
    exact Finset.mem_insert_of_mem hc
  have hCw2 : ∀ c ∈ C,
      c ∈ Finset.univ.image (fun v => List.foldl delta v w₂) := by
    intro c hc
    rw [h2]
    exact Finset.mem_insert_of_mem hc
  have hxy' : List.foldl delta x u ≠ List.foldl delta y u := by
    have h := hnon []
    rwa [List.append_nil] at h
  have hxC' : List.foldl delta x u ∉ C.image (fun z => List.foldl delta z u) := by
    intro hmem
    obtain ⟨c, hc, hfc⟩ := Finset.mem_image.mp hmem
    have hceq : c = x :=
      hinj1 (Finset.mem_coe.mpr (hCw1 c hc)) (Finset.mem_coe.mpr hxw1) hfc
    rw [hceq] at hc
    exact hx hc
  have hyC' : List.foldl delta y u ∉ C.image (fun z => List.foldl delta z u) := by
    intro hmem
    obtain ⟨c, hc, hfc⟩ := Finset.mem_image.mp hmem
    have hceq : c = y :=
      hinj2 (Finset.mem_coe.mpr (hCw2 c hc)) (Finset.mem_coe.mpr hyw2) hfc
    rw [hceq] at hc
    exact hy hc
  have hinjJ1 : ∀ a b : V,
      a ∈ (Finset.univ.image (fun v => List.foldl delta v w₁)).image
        (fun z => List.foldl delta z u) →
      b ∈ (Finset.univ.image (fun v => List.foldl delta v w₁)).image
        (fun z => List.foldl delta z u) →
      ∀ v : List (Fin k), List.foldl delta a v = List.foldl delta b v → a = b := by
    intro a b ha hb v heq
    have hJ : (Finset.univ.image (fun v => List.foldl delta v w₁)).image
        (fun z => List.foldl delta z u) =
        Finset.univ.image (fun v => List.foldl delta v (w₁ ++ u)) :=
      rc_image_append delta w₁ u
    rw [hJ] at ha hb
    obtain ⟨hinj, _⟩ := rc_injOn_of_minRank delta (w₁ ++ u) hcard1 v
    exact hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) heq
  have hinjJ2 : ∀ a b : V,
      a ∈ (Finset.univ.image (fun v => List.foldl delta v w₂)).image
        (fun z => List.foldl delta z u) →
      b ∈ (Finset.univ.image (fun v => List.foldl delta v w₂)).image
        (fun z => List.foldl delta z u) →
      ∀ v : List (Fin k), List.foldl delta a v = List.foldl delta b v → a = b := by
    intro a b ha hb v heq
    have hJ : (Finset.univ.image (fun v => List.foldl delta v w₂)).image
        (fun z => List.foldl delta z u) =
        Finset.univ.image (fun v => List.foldl delta v (w₂ ++ u)) :=
      rc_image_append delta w₂ u
    rw [hJ] at ha hb
    obtain ⟨hinj, _⟩ := rc_injOn_of_minRank delta (w₂ ++ u) hcard2 v
    exact hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) heq
  have hxJ1 : List.foldl delta x u ∈
      (Finset.univ.image (fun v => List.foldl delta v w₁)).image
        (fun z => List.foldl delta z u) :=
    Finset.mem_image.mpr ⟨x, hxw1, rfl⟩
  have hyJ2 : List.foldl delta y u ∈
      (Finset.univ.image (fun v => List.foldl delta v w₂)).image
        (fun z => List.foldl delta z u) :=
    Finset.mem_image.mpr ⟨y, hyw2, rfl⟩
  have hCJ1 : ∀ b ∈ C.image (fun z => List.foldl delta z u),
      b ∈ (Finset.univ.image (fun v => List.foldl delta v w₁)).image
        (fun z => List.foldl delta z u) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨c, hCw1 c hc, rfl⟩
  have hCJ2 : ∀ b ∈ C.image (fun z => List.foldl delta z u),
      b ∈ (Finset.univ.image (fun v => List.foldl delta v w₂)).image
        (fun z => List.foldl delta z u) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨c, hCw2 c hc, rfl⟩
  have hno : ∀ a ∈ insert (List.foldl delta y u)
        (insert (List.foldl delta x u) (C.image (fun z => List.foldl delta z u))),
      ∀ b ∈ insert (List.foldl delta y u)
        (insert (List.foldl delta x u) (C.image (fun z => List.foldl delta z u))),
      ∀ v : List (Fin k),
        List.foldl delta a v = List.foldl delta b v → a = b := by
    intro a ha b hb v heq
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact absurd heq.symm (hnon' v)
        · exact hinjJ2 _ _ hyJ2 (hCJ2 _ hb) v heq
    · rw [Finset.mem_insert] at ha
      rcases hb with rfl | hb
      · rcases ha with rfl | ha
        · exact absurd heq (hnon' v)
        · exact hinjJ2 _ _ (hCJ2 _ ha) hyJ2 v heq
      · rw [Finset.mem_insert] at hb
        rcases ha with rfl | ha
        · rcases hb with rfl | hb
          · rfl
          · exact hinjJ1 _ _ hxJ1 (hCJ1 _ hb) v heq
        · rcases hb with rfl | hb
          · exact hinjJ1 _ _ (hCJ1 _ ha) hxJ1 v heq
          · exact hinjJ1 _ _ (hCJ1 _ ha) (hCJ1 _ hb) v heq
  have hsub_eq : insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u)) =
      (Finset.univ.image (fun v => List.foldl delta v w₁)).image
        (fun z => List.foldl delta z u) := by
    ext z
    constructor
    · intro hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Finset.mem_image.mpr ⟨x, hxw1, rfl⟩
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨c, hCw1 c hc, rfl⟩
    · intro hz
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
      rw [h1, Finset.mem_insert] at hc
      rcases hc with rfl | hc
      · rw [Finset.mem_insert]
        exact Or.inl rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have hmin_sub : (insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u))).card = rc_minRank delta := by
    rw [hsub_eq, rc_image_append delta w₁ u]
    exact hcard1
  have hTss : insert (List.foldl delta x u)
        (C.image (fun z => List.foldl delta z u)) ⊂
      insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u))) :=
    ⟨Finset.subset_insert _ _, fun hcon => by
      have ymem : List.foldl delta y u ∈ insert (List.foldl delta y u)
          (insert (List.foldl delta x u)
            (C.image (fun z => List.foldl delta z u))) :=
        Finset.mem_insert_self _ _
      have ynot : List.foldl delta y u ∉ insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u)) := by
        rw [Finset.mem_insert]
        intro h
        rcases h with heq | hmem
        · exact hxy' heq.symm
        · exact hyC' hmem
      exact ynot (hcon ymem)⟩
  obtain ⟨w₀, hw₀⟩ := rc_minRank_attained delta
  have hinjT : Set.InjOn (fun z => List.foldl delta z w₀)
      ↑(insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u)))) := by
    intro a ha b hb hab
    exact hno a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) w₀ hab
  have hTimg : ((insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u)))).image
        (fun z => List.foldl delta z w₀)).card =
      (insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u)))).card :=
    Finset.card_image_iff.mpr hinjT
  have hTsub : (insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u)))).image
        (fun z => List.foldl delta z w₀) ⊆
      Finset.univ.image (fun v => List.foldl delta v w₀) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hTcard_le : (insert (List.foldl delta y u)
        (insert (List.foldl delta x u)
          (C.image (fun z => List.foldl delta z u)))).card ≤
      rc_minRank delta := by
    have h := Finset.card_le_card hTsub
    omega
  have hTgt := Finset.card_lt_card hTss
  omega

private theorem rc_mem_minRank_image {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (hcon : rc_strongly delta) (p : V) :
    ∃ w : List (Fin k),
      (Finset.univ.image (fun v => List.foldl delta v w)).card = rc_minRank delta ∧
      p ∈ Finset.univ.image (fun v => List.foldl delta v w) := by
  classical
  obtain ⟨w₀, hw₀⟩ := rc_minRank_attained delta
  obtain ⟨t, ht⟩ := rc_exists_word_of_reflTransGen delta (hcon (List.foldl delta p w₀) p)
  refine ⟨w₀ ++ t, ?_, ?_⟩
  · have hle1 : ((Finset.univ.image (fun v => List.foldl delta v w₀)).image
        (fun x => List.foldl delta x t)).card ≤ rc_minRank delta := by
      rw [← hw₀]
      exact Finset.card_image_le
    have hle2 : rc_minRank delta ≤
        ((Finset.univ.image (fun v => List.foldl delta v w₀)).image
          (fun x => List.foldl delta x t)).card := by
      rw [rc_image_append delta w₀ t]
      exact rc_minRank_le delta (w₀ ++ t)
    rw [← rc_image_append delta w₀ t]
    exact Nat.le_antisymm hle1 hle2
  · refine Finset.mem_image.mpr ⟨p, Finset.mem_univ p, ?_⟩
    rw [List.foldl_append]
    exact ht

private theorem rc_exists_stable_pair_of_good_letter {V : Type*} [Finite V]
    {k : ℕ} (delta : V → Fin k → V)
    (hcon : rc_strongly delta) (a : Fin k) (f : V → V) (hf : ∀ v, f v = delta v a)
    (L : ℕ) (hL : 1 ≤ L) (r p : V)
    (hper : ∀ v, f^[L] v ∈ Function.periodicPts f)
    (htop : f^[L - 1] p ∉ Function.periodicPts f)
    (hcoll : ∀ v, f^[L - 1] v ∉ Function.periodicPts f → f^[L] v = r) :
    ∃ x y, x ≠ y ∧ rc_stable delta x y := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hrep : ∀ j (v : V),
      List.foldl delta v (List.replicate j a) = f^[j] v := by
    intro j
    induction j with
    | zero =>
      intro v
      rfl
    | succ j ih =>
      intro v
      have ih' := ih (f v)
      rw [List.replicate_succ, List.foldl_cons, ← hf v, ih',
        Function.iterate_succ_apply]
  set N : ℕ := Nat.factorial (Fintype.card V) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
  have hfix : ∀ z ∈ Function.periodicPts f, f^[N] z = z := by
    intro z hz
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hz
    have hmpos : 0 < Function.minimalPeriod f z :=
      Function.minimalPeriod_pos_of_mem_periodicPts hz
    have hmdvd : Function.minimalPeriod f z ∣ n :=
      Function.IsPeriodicPt.minimalPeriod_dvd hn
    have hmle : Function.minimalPeriod f z ≤ Fintype.card V :=
      Function.minimalPeriod_le_card
    have hfact : Function.minimalPeriod f z ∣ N := by
      rw [hN]
      exact Nat.dvd_factorial hmpos hmle
    obtain ⟨t, ht⟩ := hfact
    have hper' : Function.IsPeriodicPt f (Function.minimalPeriod f z * t) z :=
      Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (Nat.dvd_mul_right _ _)
    rw [← ht] at hper'
    exact hper'
  obtain ⟨w, hwcard, hpmem⟩ := rc_mem_minRank_image delta hcon p
  set J : Finset V := Finset.univ.image (fun v => List.foldl delta v w) with hJ
  obtain ⟨hinjA, hcardA⟩ := rc_injOn_of_minRank delta w hwcard
    (List.replicate (L - 1) a)
  obtain ⟨hinjB, hcardB⟩ := rc_injOn_of_minRank delta w hwcard
    (List.replicate (L - 1 + N) a)
  have e1 : J.image (fun z => f^[L - 1] z) =
      Finset.univ.image (fun v => List.foldl delta v
        (w ++ List.replicate (L - 1) a)) := by
    have hb : ∀ z : V, f^[L - 1] z =
        List.foldl delta z (List.replicate (L - 1) a) :=
      fun z => (hrep (L - 1) z).symm
    simp only [hb]
    exact rc_image_append delta w (List.replicate (L - 1) a)
  have e2 : J.image (fun z => f^[L - 1 + N] z) =
      Finset.univ.image (fun v => List.foldl delta v
        (w ++ List.replicate (L - 1 + N) a)) := by
    have hb : ∀ z : V, f^[L - 1 + N] z =
        List.foldl delta z (List.replicate (L - 1 + N) a) :=
      fun z => (hrep (L - 1 + N) z).symm
    simp only [hb]
    exact rc_image_append delta w (List.replicate (L - 1 + N) a)
  have hsum : L - 1 + N = (N - 1) + L := by omega
  have hstep : ∀ z : V, f^[L - 1 + N] z = f^[N - 1] (f^[L] z) := by
    intro z
    rw [hsum, Function.iterate_add_apply]
  have hperimg : ∀ z ∈ J, f^[L - 1] z ∈ Function.periodicPts f →
      f^[L - 1 + N] z = f^[L - 1] z := by
    intro z hz hmem
    have e : L - 1 + N = N + (L - 1) := Nat.add_comm _ _
    rw [e, Function.iterate_add_apply]
    exact hfix _ hmem
  have hnonimg : ∀ z ∈ J, f^[L - 1] z ∉ Function.periodicPts f →
      f^[L - 1 + N] z = f^[N - 1] r := by
    intro z hz hnp
    rw [hstep z, hcoll z hnp]
  have huniq : ∀ z ∈ J, f^[L - 1] z ∉ Function.periodicPts f → z = p := by
    intro z hz hnp
    have hzp : f^[L - 1 + N] z = f^[L - 1 + N] p := by
      rw [hnonimg z hz hnp, hnonimg p hpmem htop]
    have hzp' : List.foldl delta z (List.replicate (L - 1 + N) a) =
        List.foldl delta p (List.replicate (L - 1 + N) a) := by
      rw [hrep (L - 1 + N) z, hrep (L - 1 + N) p]
      exact hzp
    exact hinjB (Finset.mem_coe.mpr hz) (Finset.mem_coe.mpr hpmem) hzp'
  have hrper : r ∈ Function.periodicPts f := by
    have hLp := hper p
    rw [hcoll p htop] at hLp
    exact hLp
  have hr'per : f^[N - 1] r ∈ Function.periodicPts f := by
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hrper
    refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
    have e1 := Function.iterate_add_apply f n (N - 1) r
    have e2 := Function.iterate_add_apply f (N - 1) n r
    rw [Nat.add_comm n (N - 1)] at e1
    rw [e2] at e1
    rw [hn] at e1
    exact e1.symm
  have hxy : f^[L - 1] p ≠ f^[N - 1] r := by
    intro heq
    rw [← heq] at hr'per
    exact htop hr'per
  set C : Finset V := (J.filter
    (fun z => f^[L - 1] z ∈ Function.periodicPts f)).image
    (fun z => f^[L - 1] z) with hC
  have hxC : f^[L - 1] p ∉ C := by
    intro hmem
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hmem
    have hzper : f^[L - 1] z ∈ Function.periodicPts f :=
      (Finset.mem_filter.mp hz).2
    change f^[L - 1] z = f^[L - 1] p at hzx
    rw [hzx] at hzper
    exact htop hzper
  have hr'C : f^[N - 1] r ∉ C := by
    intro hmem
    obtain ⟨z, hz, hzr⟩ := Finset.mem_image.mp hmem
    have hzJ : z ∈ J := (Finset.mem_filter.mp hz).1
    have hzper : f^[L - 1] z ∈ Function.periodicPts f :=
      (Finset.mem_filter.mp hz).2
    change f^[L - 1] z = f^[N - 1] r at hzr
    have e1 : f^[L - 1 + N] z = f^[L - 1 + N] p := by
      rw [hperimg z hzJ hzper, hzr]
      exact (hnonimg p hpmem htop).symm
    have zeq : z = p := hinjB (Finset.mem_coe.mpr hzJ)
      (Finset.mem_coe.mpr hpmem) (by
        change List.foldl delta z (List.replicate (L - 1 + N) a) =
          List.foldl delta p (List.replicate (L - 1 + N) a)
        have h1 := hrep (L - 1 + N) z
        have h2 := hrep (L - 1 + N) p
        rw [h1, h2]
        exact e1)
    have hxp : f^[L - 1] z = f^[L - 1] p :=
      congrArg (fun zz => f^[L - 1] zz) zeq
    rw [hxp] at hzper
    exact htop hzper
  have hJ1eq : J.image (fun z => f^[L - 1] z) = insert (f^[L - 1] p) C := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      by_cases hpa : f^[L - 1] a ∈ Function.periodicPts f
      · rw [Finset.mem_insert]
        exact Or.inr (Finset.mem_image.mpr
          ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, rfl⟩)
      · have hap : a = p := huniq a ha hpa
        subst hap
        rw [Finset.mem_insert]
        exact Or.inl rfl
    · intro hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Finset.mem_image.mpr ⟨p, hpmem, rfl⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1, rfl⟩
  have hJ2eq : J.image (fun z => f^[L - 1 + N] z) = insert (f^[N - 1] r) C := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      by_cases hpa : f^[L - 1] a ∈ Function.periodicPts f
      · rw [Finset.mem_insert, hperimg a ha hpa]
        exact Or.inr (Finset.mem_image.mpr
          ⟨a, Finset.mem_filter.mpr ⟨ha, hpa⟩, rfl⟩)
      · rw [Finset.mem_insert, hnonimg a ha hpa]
        exact Or.inl rfl
    · intro hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Finset.mem_image.mpr ⟨p, hpmem, hnonimg p hpmem htop⟩
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_image.mpr ⟨a, (Finset.mem_filter.mp ha).1,
          hperimg a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2⟩
  have h1 : Finset.univ.image (fun v => List.foldl delta v
      (w ++ List.replicate (L - 1) a)) = insert (f^[L - 1] p) C := by
    rw [← e1]
    exact hJ1eq
  have h2 : Finset.univ.image (fun v => List.foldl delta v
      (w ++ List.replicate (L - 1 + N) a)) = insert (f^[N - 1] r) C := by
    rw [← e2]
    exact hJ2eq
  exact ⟨f^[L - 1] p, f^[N - 1] r, hxy,
    rc_stable_of_one_difference delta C _ _ hxC hr'C hxy _ _ h1 h2 hcardA hcardB⟩

private theorem rc_level_exists {V : Type*} [Finite V] (g : V → V) (v : V) :
    ∃ i : ℕ, g^[i] v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hstep : ∀ a b : ℕ, g^[a] v = g^[b] v → a < b →
      g^[b - a] (g^[a] v) = g^[a] v := by
    intro a b heq hab
    have hd : b = a + (b - a) := by omega
    have e : g^[a + (b - a)] v = g^[b - a] (g^[a] v) := by
      rw [Nat.add_comm a (b - a)]
      exact Function.iterate_add_apply g (b - a) a v
    have hper : g^[b - a] (g^[a] v) = g^[a] v := by
      rw [← e, ← hd]
      exact heq.symm
    exact hper
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card V + 1) => g^[i.1] v) (by
      rw [Fintype.card_fin]
      omega)
  have hxy : x.1 ≠ y.1 := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact ⟨x.1, Function.mem_periodicPts.mpr
      ⟨y.1 - x.1, by omega, hstep x.1 y.1 heq hlt⟩⟩
  · exact ⟨y.1, Function.mem_periodicPts.mpr
      ⟨x.1 - y.1, by omega, hstep y.1 x.1 heq.symm hlt⟩⟩

private noncomputable def rc_level {V : Type*} [Finite V] (g : V → V) (v : V) : ℕ := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact Nat.find (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v)

private noncomputable def rc_root {V : Type*} [Finite V] (g : V → V) (v : V) : V :=
  g^[rc_level g v] v

private theorem rc_level_zero_iff {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_level g v = 0 ↔ v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact Nat.find_eq_zero (p := fun i => g^[i] v ∈ Function.periodicPts g) _

private theorem rc_level_spec {V : Type*} [Finite V] (g : V → V) (v : V) :
    g^[rc_level g v] v ∈ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level
  exact Nat.find_spec (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v)

private theorem rc_level_notMem {V : Type*} [Finite V] (g : V → V) (v : V)
    {m : ℕ} (hm : m < rc_level g v) : g^[m] v ∉ Function.periodicPts g := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level at hm
  exact Nat.find_min (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v) hm

private theorem rc_level_le_of_mem {V : Type*} [Finite V] (g : V → V) (v : V)
    {i : ℕ} (hi : g^[i] v ∈ Function.periodicPts g) :
    rc_level g v ≤ i := by
  classical
  have : Fintype V := Fintype.ofFinite V
  unfold rc_level
  exact Nat.find_min' (p := fun i => g^[i] v ∈ Function.periodicPts g)
    (rc_level_exists g v) hi

private theorem rc_periodic_map {V : Type*} (g : V → V) {z : V}
    (hz : z ∈ Function.periodicPts g) : g z ∈ Function.periodicPts g := by
  obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hz
  refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
  change g^[n] (g z) = g z
  have e1 : g^[n + 1] z = g^[n] (g z) := Function.iterate_add_apply g n 1 z
  have e2 : g^[n + 1] z = g (g^[n] z) := by
    rw [show n + 1 = (n).succ from rfl]
    exact Function.iterate_succ_apply' g n z
  rw [e1] at e2
  rw [e2, hn]

private theorem rc_periodic_iterate {V : Type*} (g : V → V) {z : V}
    (hz : z ∈ Function.periodicPts g) (m : ℕ) :
    g^[m] z ∈ Function.periodicPts g := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    have h := rc_periodic_map g ih
    have e : g (g^[m] z) = g^[m + 1] z := by
      rw [show m + 1 = (m).succ from rfl]
      exact (Function.iterate_succ_apply' g m z).symm
    rwa [← e]

private theorem rc_iterate_succ_right {V : Type*} (g : V → V) (j : ℕ) (v : V) :
    g^[j + 1] v = g^[j] (g v) := Function.iterate_add_apply g j 1 v

private theorem rc_level_step {V : Type*} [Finite V] (g : V → V) (v : V)
    (hv : v ∉ Function.periodicPts g) :
    rc_level g (g v) = rc_level g v - 1 := by
  classical
  have hLpos : 0 < rc_level g v := by
    by_contra hcon
    have h0 : rc_level g v = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hv h0
  have hL : 1 ≤ rc_level g v := hLpos
  have hdecomp : rc_level g v - 1 + 1 = rc_level g v := by omega
  have hmem : g^[rc_level g v - 1] (g v) ∈ Function.periodicPts g := by
    have hspec := rc_level_spec g v
    rw [← hdecomp, rc_iterate_succ_right] at hspec
    exact hspec
  have hle : rc_level g (g v) ≤ rc_level g v - 1 :=
    rc_level_le_of_mem g (g v) hmem
  have hge : rc_level g v - 1 ≤ rc_level g (g v) := by
    by_contra hcon
    have hlt : rc_level g (g v) < rc_level g v - 1 := by omega
    have hnot := rc_level_notMem g v
      (m := rc_level g (g v) + 1) (by omega)
    have heq : g^[rc_level g (g v) + 1] v =
        g^[rc_level g (g v)] (g v) := by
      rw [show rc_level g (g v) + 1 = rc_level g (g v) + 1 from rfl]
      exact (rc_iterate_succ_right g (rc_level g (g v)) v).symm
    rw [heq] at hnot
    exact hnot (rc_level_spec g (g v))
  omega

private theorem rc_root_step {V : Type*} [Finite V] (g : V → V) (v : V)
    (hv : v ∉ Function.periodicPts g) :
    rc_root g (g v) = rc_root g v := by
  classical
  have hLpos : 0 < rc_level g v := by
    by_contra hcon
    have h0 : rc_level g v = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hv h0
  have hdecomp : rc_level g v - 1 + 1 = rc_level g v := by omega
  unfold rc_root
  rw [rc_level_step g v hv]
  have hspec : g^[rc_level g v - 1] (g v) = g^[rc_level g v] v := by
    conv_rhs => rw [← hdecomp]
    exact (rc_iterate_succ_right g _ v).symm
  exact hspec

private theorem rc_root_periodic {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_root g v ∈ Function.periodicPts g :=
  rc_level_spec g v

private theorem rc_level_root_zero {V : Type*} [Finite V] (g : V → V) (v : V) :
    rc_level g (rc_root g v) = 0 := by
  rw [rc_level_zero_iff]
  exact rc_root_periodic g v

private noncomputable def rc_height {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : ℕ :=
  Finset.sup Finset.univ (fun v => rc_level g v)

private noncomputable def rc_cyc {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => v ∈ Function.periodicPts g)).card

private def rc_good {V : Type*} [Fintype V] [DecidableEq V] (g : V → V) : Prop :=
  0 < rc_height g ∧ ∀ v w : V, rc_level g v = rc_height g →
    rc_level g w = rc_height g → rc_root g v = rc_root g w

private theorem rc_level_le_height {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) : rc_level g v ≤ rc_height g := by
  unfold rc_height
  exact Finset.le_sup (Finset.mem_univ v)

private theorem rc_height_attained {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (g : V → V) :
    ∃ p : V, rc_level g p = rc_height g := by
  classical
  unfold rc_height
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty (fun v => rc_level g v)
  exact ⟨p, hp.symm⟩

private theorem rc_cyc_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) : rc_cyc g ≤ Fintype.card V := by
  classical
  unfold rc_cyc
  calc (Finset.univ.filter (fun v => v ∈ Function.periodicPts g)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = Fintype.card V := Finset.card_univ

private theorem rc_iterate_ge_level_periodic {V : Type*} [Finite V]
    (g : V → V) (v : V) {j : ℕ} (hj : rc_level g v ≤ j) :
    g^[j] v ∈ Function.periodicPts g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm (rc_level g v) d, Function.iterate_add_apply]
  exact rc_periodic_iterate g (rc_level_spec g v) d

private theorem rc_iterate_height_periodic {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) : g^[rc_height g] v ∈ Function.periodicPts g :=
  rc_iterate_ge_level_periodic g v (rc_level_le_height g v)

private theorem rc_pred_notMem_of_top {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) {p : V} (hp : rc_level g p = rc_height g)
    (hH : 1 ≤ rc_height g) : g^[rc_height g - 1] p ∉ Function.periodicPts g := by
  intro hmem
  have hle := rc_level_le_of_mem g p hmem
  omega

private theorem rc_level_eq_height_of_pred_notMem {V : Type*} [Fintype V]
    [DecidableEq V] (g : V → V) (L : ℕ) (hL : rc_height g = L)
    (v : V) (hv : g^[L - 1] v ∉ Function.periodicPts g) (hL1 : 1 ≤ L) :
    rc_level g v = L := by
  have hle : rc_level g v ≤ L := by rw [← hL]; exact rc_level_le_height g v
  by_contra hne
  have hlt : rc_level g v < L := by omega
  have hmem : g^[L - 1] v ∈ Function.periodicPts g := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show rc_level g v ≤ L - 1 by omega)
    have hspec := rc_level_spec g v
    have e : L - 1 = rc_level g v + d := hd
    rw [e, Nat.add_comm (rc_level g v) d, Function.iterate_add_apply]
    exact rc_periodic_iterate g hspec d
  exact hv hmem

private theorem rc_good_bridge {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (g : V → V) (hgood : rc_good g) :
    ∃ (L : ℕ) (r p : V), 1 ≤ L ∧ L = rc_height g ∧ rc_level g p = rc_height g ∧
      r = rc_root g p ∧ (∀ v, g^[L] v ∈ Function.periodicPts g) ∧
      g^[L - 1] p ∉ Function.periodicPts g ∧
      (∀ v, g^[L - 1] v ∉ Function.periodicPts g → g^[L] v = r) := by
  classical
  obtain ⟨hHpos, huniq⟩ := hgood
  obtain ⟨p, hp⟩ := rc_height_attained g
  have hH1 : 1 ≤ rc_height g := hHpos
  refine ⟨rc_height g, rc_root g p, p, hH1, rfl, hp, rfl, ?_, ?_, ?_⟩
  · intro v
    exact rc_iterate_height_periodic g v
  · exact rc_pred_notMem_of_top g hp hH1
  · intro v hv
    have hLv : rc_level g v = rc_height g :=
      rc_level_eq_height_of_pred_notMem g (rc_height g) rfl v hv hH1
    have e1 : g^[rc_height g] v = rc_root g v := by
      unfold rc_root
      rw [hLv]
    have e2 : rc_root g v = rc_root g p := huniq v p hLv hp
    rw [e1, e2]

private def rc_stableSetoid {V : Type*} {k : ℕ} (delta : V → Fin k → V) : Setoid V where
  r := rc_stable delta
  iseqv := ⟨rc_stable_refl delta, fun h => rc_stable_symm delta h,
    fun h1 h2 => rc_stable_trans delta h1 h2⟩

private def rc_quot {V : Type*} {k : ℕ} (delta : V → Fin k → V) :
    Quotient (rc_stableSetoid delta) → Fin k → Quotient (rc_stableSetoid delta) :=
  fun q c => Quotient.map' (fun v => delta v c)
    (fun _v _w h => rc_stable_foldl delta h [c]) q

private theorem rc_quot_mk {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (v : V) (c : Fin k) :
    rc_quot delta (Quotient.mk _ v) c = Quotient.mk _ (delta v c) := by
  rfl

private noncomputable instance rc_quotFintype {V : Type*} [Fintype V] {k : ℕ}
    (delta : V → Fin k → V) : Fintype (Quotient (rc_stableSetoid delta)) := by
  classical
  exact Quotient.fintype _

private instance rc_quotNonempty {V : Type*} [Nonempty V] {k : ℕ}
    (delta : V → Fin k → V) : Nonempty (Quotient (rc_stableSetoid delta)) :=
  ⟨Quotient.mk _ (Classical.choice ‹Nonempty V›)⟩

private theorem rc_adj_quot_mk {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    {a b : V} (h : rc_adj delta a b) :
    rc_adj (rc_quot delta) (Quotient.mk _ a) (Quotient.mk _ b) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, by rw [rc_quot_mk]; rw [hc]⟩

private theorem rc_quot_card_lt {V : Type*} [Fintype V] {k : ℕ}
    (delta : V → Fin k → V) {x y : V}
    (hxy : x ≠ y) (hst : rc_stable delta x y) :
    Fintype.card (Quotient (rc_stableSetoid delta)) < Fintype.card V := by
  classical
  apply Fintype.card_lt_of_surjective_not_injective (Quotient.mk _)
  · exact Quotient.mk_surjective
  · intro hinj
    exact hxy (hinj (Quotient.sound hst))

private theorem rc_quot_strongly {V : Type*} {k : ℕ}
    (delta : V → Fin k → V) (hcon : rc_strongly delta) :
    rc_strongly (rc_quot delta) := by
  intro q1 q2
  obtain ⟨v1, hv1⟩ := Quotient.exists_rep q1
  obtain ⟨v2, hv2⟩ := Quotient.exists_rep q2
  subst hv1
  subst hv2
  have h := hcon v1 v2
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih (rc_adj_quot_mk delta hab)

private theorem rc_quot_aperiodic {V : Type*} {k : ℕ}
    (delta : V → Fin k → V) (haper : rc_aperiodic delta) :
    rc_aperiodic (rc_quot delta) := by
  intro d hd
  obtain ⟨u, w, hchain, hlast, hdiv⟩ := haper d hd
  refine ⟨Quotient.mk _ u, w.map (Quotient.mk _), ?_, ?_, ?_⟩
  · have hmap : List.IsChain (fun a b : V =>
        rc_adj (rc_quot delta) (Quotient.mk _ a) (Quotient.mk _ b)) (u :: w) :=
      hchain.imp (fun a b h => rc_adj_quot_mk delta h)
    have h := List.isChain_map_of_isChain (Quotient.mk (rc_stableSetoid delta))
      (fun a b h => h) hmap
    rwa [List.map_cons] at h
  · have hmap : (w.map (Quotient.mk (rc_stableSetoid delta))).getLast? =
        (w.getLast?).map (Quotient.mk (rc_stableSetoid delta)) := by simp
    simp [hmap, hlast]
  · have hlen : (w.map (Quotient.mk (rc_stableSetoid delta))).length = w.length := by
      simp
    rwa [hlen]

private theorem rc_quot_foldl {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (v : V) (w : List (Fin k)) :
    Quotient.mk (rc_stableSetoid delta) (List.foldl delta v w) =
      List.foldl (rc_quot delta) (Quotient.mk _ v) w := by
  induction w generalizing v with
  | nil => rfl
  | cons c t ih =>
    simp only [List.foldl_cons, rc_quot_mk]
    exact ih _

private theorem rc_translate_B_to_delta {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (u : List (Fin k)) (x y : V) (hst : rc_stable delta x y) :
    ∃ u' : List (Fin k),
      List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x u =
        List.foldl delta x u' ∧
      List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y u =
        List.foldl delta y u' := by
  induction u generalizing x y with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons c t ih =>
    have hclass : Quotient.mk (rc_stableSetoid delta) x = Quotient.mk _ y :=
      Quotient.sound hst
    have hsigP : sigma' (Quotient.mk _ y) = sigma' (Quotient.mk _ x) := by
      rw [hclass]
    have hst1 : rc_stable delta (delta x (sigma' (Quotient.mk _ x) c))
        (delta y (sigma' (Quotient.mk _ x) c)) :=
      rc_stable_foldl delta hst [sigma' (Quotient.mk _ x) c]
    obtain ⟨t', ht1, ht2⟩ := ih _ _ hst1
    refine ⟨sigma' (Quotient.mk _ x) c :: t', ?_, ?_⟩
    · change List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          (delta x (sigma' (Quotient.mk _ x) c)) t =
        List.foldl delta (delta x (sigma' (Quotient.mk _ x) c)) t'
      exact ht1
    · change List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          (delta y (sigma' (Quotient.mk _ y) c)) t =
        List.foldl delta (delta y (sigma' (Quotient.mk _ x) c)) t'
      rw [hsigP]
      exact ht2

private theorem rc_translate_delta_to_B {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (u' : List (Fin k)) (x y : V) (hst : rc_stable delta x y) :
    ∃ u : List (Fin k),
      List.foldl delta x u' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x u ∧
      List.foldl delta y u' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y u := by
  induction u' generalizing x y with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons d t' ih =>
    have hclass : Quotient.mk (rc_stableSetoid delta) x = Quotient.mk _ y :=
      Quotient.sound hst
    have hsigP : sigma' (Quotient.mk _ y) = sigma' (Quotient.mk _ x) := by
      rw [hclass]
    have hst1 : rc_stable delta (delta x d) (delta y d) :=
      rc_stable_foldl delta hst [d]
    obtain ⟨u_tail, ht1, ht2⟩ := ih _ _ hst1
    have hBxc : (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x
        ((sigma' (Quotient.mk _ x)).symm d) = delta x d := by
      change delta x (sigma' (Quotient.mk _ x) ((sigma' (Quotient.mk _ x)).symm d)) =
        delta x d
      rw [Equiv.apply_symm_apply]
    have hByc : (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y
        ((sigma' (Quotient.mk _ x)).symm d) = delta y d := by
      change delta y (sigma' (Quotient.mk _ y) ((sigma' (Quotient.mk _ x)).symm d)) =
        delta y d
      rw [hsigP, Equiv.apply_symm_apply]
    refine ⟨(sigma' (Quotient.mk _ x)).symm d :: u_tail, ?_, ?_⟩
    · change List.foldl delta (delta x d) t' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x
            ((sigma' (Quotient.mk _ x)).symm d)) u_tail
      rw [hBxc]
      exact ht1
    · change List.foldl delta (delta y d) t' =
        List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v)))
          ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) y
            ((sigma' (Quotient.mk _ x)).symm d)) u_tail
      rw [hByc]
      exact ht2

private theorem rc_lift_quot_foldl {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    (v : V) (w : List (Fin k)) :
    Quotient.mk (rc_stableSetoid delta)
        (List.foldl (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) v w) =
      List.foldl (rc_recolor (rc_quot delta) sigma') (Quotient.mk _ v) w := by
  induction w generalizing v with
  | nil => rfl
  | cons c t ih =>
    have hstep : Quotient.mk (rc_stableSetoid delta)
        ((rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) v c) =
        (rc_recolor (rc_quot delta) sigma') (Quotient.mk _ v) c := by
      change Quotient.mk (rc_stableSetoid delta)
          (delta v (sigma' (Quotient.mk _ v) c)) =
        rc_quot delta (Quotient.mk _ v) (sigma' (Quotient.mk _ v) c)
      exact rc_quot_mk delta v _
    simp only [List.foldl_cons]
    rw [← hstep]
    exact ih _

private theorem rc_stable_lift {V : Type*} {k : ℕ}
    (delta : V → Fin k → V)
    (sigma' : Quotient (rc_stableSetoid delta) → Equiv.Perm (Fin k))
    {x y : V} (hst : rc_stable delta x y) :
    rc_stable (rc_recolor delta (fun v => sigma' (Quotient.mk _ v))) x y := by
  intro u
  obtain ⟨u', hu1, hu2⟩ := rc_translate_B_to_delta delta sigma' u x y hst
  obtain ⟨v', hv⟩ := rc_stable_merge delta (rc_stable_foldl delta hst u')
  obtain ⟨v, hv1, hv2⟩ := rc_translate_delta_to_B delta sigma' v' _ _
    (rc_stable_foldl delta hst u')
  refine ⟨v, ?_⟩
  rw [List.foldl_append, List.foldl_append, hu1, hu2, ← hv1, ← hv2]
  exact hv

private def rc_isSSG {V : Type*} {k : ℕ} (delta : V → Fin k → V) (g : V → V) : Prop :=
  ∀ v : V, rc_adj delta v (g v)

private theorem rc_update_iterate_agree {V : Type*} [DecidableEq V] (R : V → V)
    (x y : V) (v : V) (havoid : ∀ i : ℕ, R^[i] v ≠ x) (j : ℕ) :
    (Function.update R x y)^[j] v = R^[j] v := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have e1 : (Function.update R x y)^[j + 1] v =
        Function.update R x y ((Function.update R x y)^[j] v) := by
      rw [show j + 1 = (j).succ from rfl]
      exact Function.iterate_succ_apply' _ j v
    have e2 : R^[j + 1] v = R (R^[j] v) := by
      rw [show j + 1 = (j).succ from rfl]
      exact Function.iterate_succ_apply' _ j v
    rw [e1, e2, ih]
    exact Function.update_of_ne (havoid j) y R

private theorem rc_update_periodic {V : Type*} [DecidableEq V] (R : V → V) (x y : V)
    (z : V) (havoid : ∀ i : ℕ, R^[i] z ≠ x) (hper : z ∈ Function.periodicPts R) :
    z ∈ Function.periodicPts (Function.update R x y) := by
  obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hper
  refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
  change (Function.update R x y)^[n] z = z
  rw [rc_update_iterate_agree R x y z havoid n]
  exact hn

private theorem rc_update_periodic_of {V : Type*} [DecidableEq V] (R : V → V)
    (x y : V) (w : V)
    (hagree : ∀ j : ℕ, (Function.update R x y)^[j] w = R^[j] w)
    (hper : w ∈ Function.periodicPts (Function.update R x y)) :
    w ∈ Function.periodicPts R := by
  obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hper
  refine Function.mem_periodicPts.mpr ⟨n, hn_pos, ?_⟩
  change R^[n] w = w
  rw [← hagree n]
  exact hn

private theorem rc_update_level_eq {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (x y : V) (v : V) (havoid : ∀ i : ℕ, R^[i] v ≠ x) :
    rc_level (Function.update R x y) v = rc_level R v := by
  have agree : ∀ j : ℕ, (Function.update R x y)^[j] v = R^[j] v :=
    fun j => rc_update_iterate_agree R x y v havoid j
  have hz : ∀ i : ℕ, R^[i] (R^[rc_level R v] v) ≠ x := by
    intro i
    have e : R^[i] (R^[rc_level R v] v) = R^[rc_level R v + i] v := by
      rw [Nat.add_comm (rc_level R v) i, Function.iterate_add_apply]
    rw [e]
    exact havoid _
  have hagree2 : ∀ j : ℕ, (Function.update R x y)^[j]
      (R^[rc_level (Function.update R x y) v] v) = R^[j]
      (R^[rc_level (Function.update R x y) v] v) := by
    intro j
    have h1 := agree (rc_level (Function.update R x y) v + j)
    rw [Nat.add_comm (rc_level (Function.update R x y) v) j,
      Function.iterate_add_apply, Function.iterate_add_apply,
      agree (rc_level (Function.update R x y) v)] at h1
    exact h1
  have eL : (Function.update R x y)^[rc_level R v] v = R^[rc_level R v] v :=
    agree _
  have h1mem : R^[rc_level R v] v ∈ Function.periodicPts (Function.update R x y) :=
    rc_update_periodic R x y _ hz (rc_level_spec R v)
  rw [← eL] at h1mem
  have eL1 : (Function.update R x y)^[rc_level (Function.update R x y) v] v =
      R^[rc_level (Function.update R x y) v] v := agree _
  have hper1 : R^[rc_level (Function.update R x y) v] v ∈
      Function.periodicPts (Function.update R x y) := by
    rw [← eL1]
    exact rc_level_spec _ v
  exact Nat.le_antisymm
    (rc_level_le_of_mem _ _ h1mem)
    (rc_level_le_of_mem _ _ (rc_update_periodic_of R x y _ hagree2 hper1))

private theorem rc_level_along_orbit {V : Type*} [Finite V] (g : V → V) (v : V) :
    ∀ (i : ℕ), i ≤ rc_level g v →
    rc_level g (g^[i] v) = rc_level g v - i := by
  intro i
  induction i with
  | zero => intro _; simp only [Function.iterate_zero_apply, Nat.sub_zero]
  | succ i ih =>
    intro hi
    have hiL : i ≤ rc_level g v := by omega
    have eih := ih hiL
    have hnon : g^[i] v ∉ Function.periodicPts g := by
      intro hmem
      have h0 : rc_level g (g^[i] v) = 0 := (rc_level_zero_iff g _).mpr hmem
      omega
    have estep := rc_level_step g (g^[i] v) hnon
    have eiter : g^[i + 1] v = g (g^[i] v) := by
      rw [show i + 1 = (i).succ from rfl]
      exact Function.iterate_succ_apply' g i v
    rw [eiter, estep, eih]
    omega

private theorem rc_root_along_orbit {V : Type*} [Finite V] (g : V → V) (v : V)
    {i : ℕ} (hi : i ≤ rc_level g v) :
    rc_root g (g^[i] v) = rc_root g v := by
  unfold rc_root
  rw [rc_level_along_orbit g v i hi, ← Function.iterate_add_apply]
  have hii : rc_level g v - i + i = rc_level g v := by omega
  rw [hii]

private theorem rc_ssg_through_edge {V : Type*} {k : ℕ}
    (delta : V → Fin k → V) (a : Fin k) {v₀ w₀ : V} (h : rc_adj delta v₀ w₀) :
    ∃ g : V → V, (∀ v : V, rc_adj delta v (g v)) ∧ g v₀ = w₀ := by
  classical
  refine ⟨Function.update (fun v => delta v a) v₀ w₀, ?_, Function.update_self _ _ _⟩
  intro v
  by_cases hv : v = v₀
  · subst hv
    rw [Function.update_self]
    exact h
  · rw [Function.update_of_ne hv]
    exact ⟨a, rfl⟩

private theorem rc_height_max_exists {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (a : Fin k) :
    ∃ R : V → V, rc_isSSG delta R ∧
      ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R := by
  classical
  have hne : (Finset.univ.filter
      (fun g : V → V => ∀ v, rc_adj delta v (g v))).Nonempty := by
    refine ⟨fun v => delta v a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro v
    exact ⟨a, rfl⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image _ (fun g => rc_height g) hne
  have hRssg : rc_isSSG delta R := (Finset.mem_filter.mp hRmem).2
  refine ⟨R, hRssg, ?_⟩
  intro g hg
  have hmem : g ∈ Finset.univ.filter
      (fun g : V → V => ∀ v, rc_adj delta v (g v)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩
  exact hRmax g hmem

private theorem rc_cyc_max_exists {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (H : ℕ) (R₀ : V → V)
    (hR₀ : rc_isSSG delta R₀ ∧ rc_height R₀ = H) :
    ∃ R : V → V, rc_isSSG delta R ∧ rc_height R = H ∧
      ∀ g : V → V, rc_isSSG delta g → rc_height g = H → rc_cyc g ≤ rc_cyc R := by
  classical
  have hne : (Finset.univ.filter
      (fun g : V → V => (∀ v, rc_adj delta v (g v)) ∧ rc_height g = H)).Nonempty := by
    refine ⟨R₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR₀.1, hR₀.2⟩⟩
  obtain ⟨R, hRmem, hRmax⟩ := Finset.exists_max_image _ (fun g => rc_cyc g) hne
  obtain ⟨-, hRssg, hRH⟩ := Finset.mem_filter.mp hRmem
  refine ⟨R, hRssg, hRH, ?_⟩
  intro g hg hHg
  have hmem : g ∈ Finset.univ.filter
      (fun g : V → V => (∀ v, rc_adj delta v (g v)) ∧ rc_height g = H) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg, hHg⟩
  exact hRmax g hmem

private theorem rc_lexmax_height_pos {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (a : Fin k)
    (hcon : rc_strongly delta) (haper : rc_aperiodic delta)
    (hcard : 1 < Fintype.card V)
    (R : V → V)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R) :
    1 ≤ rc_height R := by
  classical
  by_contra hcon0
  have hH0 : rc_height R = 0 := by omega
  obtain ⟨v, br_a, br_b, hbr⟩ := rc_exists_branching delta hcard hcon haper
  obtain ⟨g, hg, hgv⟩ := rc_ssg_through_edge delta a ⟨br_a, rfl⟩
  have hg0 : rc_height g = 0 := by
    have hle := hHmax g hg
    omega
  have hper_all : ∀ z : V, z ∈ Function.periodicPts g := by
    intro z
    have hlev : rc_level g z = 0 := by
      have hle := rc_level_le_height g z
      omega
    rwa [rc_level_zero_iff] at hlev
  have hsurj : Function.Surjective g := by
    intro w
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp (hper_all w)
    cases n with
    | zero => omega
    | succ m =>
      exact ⟨g^[m] w, (Function.iterate_succ_apply' g m w).symm.trans hn⟩
  have hinjg : Function.Injective g := Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨u, hu⟩ := hsurj (delta v br_b)
  have hune : u ≠ v := by
    rintro rfl
    exact hbr (hgv.symm.trans hu)
  have hg'ssg : rc_isSSG delta (Function.update g v (delta v br_b)) := by
    intro z
    by_cases hz : z = v
    · subst hz
      rw [Function.update_self]
      exact ⟨br_b, rfl⟩
    · rw [Function.update_of_ne hz]
      exact hg z
  have hcoll : Function.update g v (delta v br_b) u =
      Function.update g v (delta v br_b) v := by
    rw [Function.update_of_ne hune, Function.update_self]
    exact hu
  have hninj : ¬ Function.Injective (Function.update g v (delta v br_b)) := by
    intro hinj
    exact hune (hinj hcoll)
  have hnsurj : ¬ Function.Surjective (Function.update g v (delta v br_b)) :=
    fun hsurj => hninj (Finite.injective_iff_surjective.mpr hsurj)
  obtain ⟨z, hz⟩ : ∃ z, ∀ w, Function.update g v (delta v br_b) w ≠ z := by
    by_contra hcon2
    apply hnsurj
    intro w
    by_contra hcon3
    apply hcon2
    exact ⟨w, fun w' hw' => hcon3 ⟨w', hw'⟩⟩
  have hznonper : z ∉ Function.periodicPts (Function.update g v (delta v br_b)) := by
    intro hper
    obtain ⟨n, hn_pos, hn⟩ := Function.mem_periodicPts.mp hper
    cases n with
    | zero => omega
    | succ m =>
      exact hz _ ((Function.iterate_succ_apply' _ m z).symm.trans hn)
  have hlev : 1 ≤ rc_level (Function.update g v (delta v br_b)) z := by
    by_contra hcon4
    have h0 : rc_level (Function.update g v (delta v br_b)) z = 0 := by omega
    rw [rc_level_zero_iff] at h0
    exact hznonper h0
  have hge1 : 1 ≤ rc_height (Function.update g v (delta v br_b)) :=
    le_trans hlev (rc_level_le_height _ z)
  have hle := hHmax _ hg'ssg
  omega

private def rc_isBunch {V : Type*} {k : ℕ} (delta : V → Fin k → V) (x z : V) : Prop :=
  ∀ a : Fin k, delta x a = z

private theorem rc_stable_of_two_bunches {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (a₀ : Fin k) {x y z : V}
    (hx : rc_isBunch delta x z) (hy : rc_isBunch delta y z) :
    rc_stable delta x y := by
  intro u
  cases u with
  | nil =>
    refine ⟨[a₀], ?_⟩
    have ex : List.foldl delta x [a₀] = z := by
      rw [List.foldl_cons, List.foldl_nil]
      exact hx a₀
    have ey : List.foldl delta y [a₀] = z := by
      rw [List.foldl_cons, List.foldl_nil]
      exact hy a₀
    simpa using ex.trans ey.symm
  | cons a t =>
    refine ⟨[], ?_⟩
    have ex : List.foldl delta x (a :: t) = List.foldl delta z t := by
      rw [List.foldl_cons, hx a]
    have ey : List.foldl delta y (a :: t) = List.foldl delta z t := by
      rw [List.foldl_cons, hy a]
    simpa using ex.trans ey.symm

private theorem rc_bunch_recolor {V : Type*} {k : ℕ} (delta : V → Fin k → V)
    (sigma : V → Equiv.Perm (Fin k)) {x z : V} (h : rc_isBunch delta x z) :
    rc_isBunch (rc_recolor delta sigma) x z := by
  intro a
  exact h (sigma x a)

private theorem rc_height_gt_of_iterate_notMem {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V) (v : V) (L : ℕ) (h : g^[L] v ∉ Function.periodicPts g) :
    L < rc_height g := by
  by_contra hcon
  have h1 := rc_level_le_height g v
  have h2 : rc_height g ≤ L := by omega
  have hle : rc_level g v ≤ L := le_trans h1 h2
  exact h (rc_iterate_ge_level_periodic g v hle)

private theorem rc_cyc_gt_of_subset_ne {V : Type*} [Fintype V] [DecidableEq V]
    (R R' : V → V)
    (hsub : ∀ z : V, z ∈ Function.periodicPts R → z ∈ Function.periodicPts R')
    (z₀ : V) (hmem : z₀ ∈ Function.periodicPts R') (hne : z₀ ∉ Function.periodicPts R) :
    rc_cyc R < rc_cyc R' := by
  classical
  unfold rc_cyc
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hz'⟩
  · intro heq
    apply hne
    have hmem' : z₀ ∈ Finset.univ.filter (fun v => v ∈ Function.periodicPts R) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z₀, hmem⟩
    exact (Finset.mem_filter.mp hmem').2

private theorem rc_path_point_notMem {V : Type*} [Finite V] (R : V → V) (p : V)
    {i : ℕ} (hi : i < rc_level R p) : R^[i] p ∉ Function.periodicPts R := by
  intro hmem
  have h0 : rc_level R (R^[i] p) = 0 := (rc_level_zero_iff R _).mpr hmem
  have hlev := rc_level_along_orbit R p i (by omega)
  omega

private theorem rc_root_of_mem_orbit {V : Type*} [Finite V] (R : V → V) (v x : V)
    (hmem : ∃ i : ℕ, R^[i] v = x) (hxnp : x ∉ Function.periodicPts R) :
    rc_root R x = rc_root R v := by
  obtain ⟨i, hi⟩ := hmem
  have hiL : i ≤ rc_level R v := by
    by_contra hcon
    have hle : rc_level R v ≤ i := by omega
    have h := rc_iterate_ge_level_periodic R v hle
    rw [hi] at h
    exact hxnp h
  have hroot := rc_root_along_orbit R v hiL
  rw [hi] at hroot
  exact hroot

private theorem rc_orbit_avoid_of_root_ne {V : Type*} [Finite V] (R : V → V) (v x : V)
    (hxnp : x ∉ Function.periodicPts R) (hne : rc_root R v ≠ rc_root R x) (i : ℕ) :
    R^[i] v ≠ x :=
  fun heq => hne (rc_root_of_mem_orbit R v x ⟨i, heq⟩ hxnp).symm

private theorem rc_mem_of_periodic_iterate_mem {V : Type*} (g : V → V) (P : V → Prop)
    (hclosed : ∀ a : V, P a → P (g a)) (z : V) (hz : z ∈ Function.periodicPts g)
    (n : ℕ) (hmem : P (g^[n] z)) : P z := by
  obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hz
  have h1N : 1 ≤ N := hNpos
  have hle : n ≤ N * n := by
    calc n = n * 1 := (Nat.mul_one n).symm
    _ ≤ n * N := Nat.mul_le_mul_left n h1N
    _ = N * n := Nat.mul_comm _ _
  have hz_eq : g^[N * n - n] (g^[n] z) = z := by
    have e1 : g^[N * n - n] (g^[n] z) = g^[N * n - n + n] z :=
      (Function.iterate_add_apply g (N * n - n) n z).symm
    have e2 : N * n - n + n = N * n := Nat.sub_add_cancel hle
    have hper : Function.IsPeriodicPt g (N * n) z := hN.mul_const n
    rw [e1, e2]
    exact hper
  have hclosed_it : ∀ j : ℕ, P (g^[j] (g^[n] z)) := by
    intro j
    induction j with
    | zero => simpa using hmem
    | succ j ih =>
      rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply']
      exact hclosed _ ih
  rw [← hz_eq]
  exact hclosed_it (N * n - n)

private theorem rc_ssg_update_edge {V : Type*} [DecidableEq V] {k : ℕ}
    (delta : V → Fin k → V)
    (R : V → V) (hR : rc_isSSG delta R) (x p : V) (hx : rc_adj delta x p) :
    rc_isSSG delta (Function.update R x p) := by
  intro z
  by_cases hz : z = x
  · subst hz
    rw [Function.update_self]
    exact hx
  · rw [Function.update_of_ne hz]
    exact hR z

private theorem rc_exists_other_top {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V) (hH : 1 ≤ rc_height R) (hngR : ¬ rc_good R) (p : V) :
    ∃ q : V, rc_level R q = rc_height R ∧ rc_root R q ≠ rc_root R p := by
  by_contra hcon
  apply hngR
  refine ⟨hH, fun v w hv hw => ?_⟩
  by_contra hne
  by_cases hvp : rc_root R v = rc_root R p
  · exact hcon ⟨w, hw, fun heq => hne (hvp.trans heq.symm)⟩
  · exact hcon ⟨v, hv, hvp⟩

private noncomputable def rc_cycleFin {V : Type*} [DecidableEq V]
    (R : V → V) (r : V) : Finset V :=
  (Finset.range (Function.minimalPeriod R r)).image (fun t => R^[t] r)

private theorem rc_cycleFin_mem {V : Type*} [DecidableEq V]
    (R : V → V) (r z : V) :
    z ∈ rc_cycleFin R r ↔
      ∃ t : ℕ, t < Function.minimalPeriod R r ∧ R^[t] r = z := by
  unfold rc_cycleFin
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.mp ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, Finset.mem_range.mpr ht, rfl⟩

private theorem rc_cycleFin_card {V : Type*} [DecidableEq V]
    (R : V → V) (r : V) :
    (rc_cycleFin R r).card = Function.minimalPeriod R r := by
  unfold rc_cycleFin
  refine (Finset.card_image_of_injOn ?_).trans (Finset.card_range _)
  intro a ha b hb hab
  exact Function.iterate_injOn_Iio_minimalPeriod
    (Finset.mem_range.mp (Finset.mem_coe.mp ha))
    (Finset.mem_range.mp (Finset.mem_coe.mp hb)) hab

private theorem rc_cycleFin_closed {V : Type*} [DecidableEq V]
    (R : V → V) (r : V) (hr : r ∈ Function.periodicPts R)
    (z : V) (hz : z ∈ rc_cycleFin R r) : R z ∈ rc_cycleFin R r := by
  obtain ⟨t, ht, rfl⟩ := (rc_cycleFin_mem R r z).mp hz
  have hmpos : 0 < Function.minimalPeriod R r :=
    Function.minimalPeriod_pos_of_mem_periodicPts hr
  by_cases ht' : t + 1 < Function.minimalPeriod R r
  · refine (rc_cycleFin_mem R r _).mpr
      ⟨t + 1, ht', Function.iterate_succ_apply' R t r⟩
  · have htm : t + 1 = Function.minimalPeriod R r := by omega
    have e : R (R^[t] r) = r := by
      have hper : R^[t + 1] r = r := by
        rw [htm]
        exact Function.iterate_minimalPeriod
      rwa [show t + 1 = t.succ from rfl, Function.iterate_succ_apply'] at hper
    have hr0 : r ∈ rc_cycleFin R r :=
      (rc_cycleFin_mem R r _).mpr ⟨0, hmpos, rfl⟩
    rw [e]
    exact hr0

private theorem rc_cycleFin_absorb {V : Type*} [DecidableEq V]
    (R : V → V) (r : V) (hr : r ∈ Function.periodicPts R)
    (z : V) (hz : z ∈ Function.periodicPts R) (s : ℕ)
    (hmem : R^[s] z ∈ rc_cycleFin R r) : z ∈ rc_cycleFin R r := by
  obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hz
  have h1N : 1 ≤ N := hNpos
  have hle : s ≤ N * s := by
    calc s = 1 * s := (one_mul s).symm
    _ ≤ N * s := Nat.mul_le_mul_right s h1N
  have hP : Function.IsPeriodicPt R (N * s) z := hN.mul_const s
  have hz_eq : R^[N * s - s] (R^[s] z) = z := by
    have e1 : R^[N * s - s] (R^[s] z) = R^[N * s - s + s] z :=
      (Function.iterate_add_apply R (N * s - s) s z).symm
    have e2 : N * s - s + s = N * s := Nat.sub_add_cancel hle
    rw [e1, e2]
    exact hP
  have hclosed_it : ∀ j : ℕ, R^[j] (R^[s] z) ∈ rc_cycleFin R r := by
    intro j
    induction j with
    | zero => simpa using hmem
    | succ j ih =>
      rw [show j + 1 = j.succ from rfl, Function.iterate_succ_apply']
      exact rc_cycleFin_closed R r hr _ ih
  have hfin : R^[N * s - s] (R^[s] z) ∈ rc_cycleFin R r := hclosed_it _
  rw [hz_eq] at hfin
  exact hfin

private theorem rc_path_ne_of_lt {V : Type*} [Finite V] (R : V → V) (p : V) (L : ℕ)
    (hL : rc_level R p = L) {a b : ℕ} (ha : a < L) (hb : b < L) (hne : a ≠ b) :
    R^[a] p ≠ R^[b] p := by
  intro heq
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hxper : R^[a] p ∈ Function.periodicPts R := by
      refine Function.mem_periodicPts.mpr ⟨b - a, by omega, ?_⟩
      have e : R^[b - a] (R^[a] p) = R^[b] p := by
        have hdec : b = (b - a) + a := by omega
        conv_rhs => rw [hdec]
        exact (Function.iterate_add_apply R (b - a) a p).symm
      rw [← heq] at e
      exact e
    exact rc_path_point_notMem R p (by omega) hxper
  · have hxper : R^[b] p ∈ Function.periodicPts R := by
      refine Function.mem_periodicPts.mpr ⟨a - b, by omega, ?_⟩
      have e : R^[a - b] (R^[b] p) = R^[a] p := by
        have hdec : a = (a - b) + b := by omega
        conv_rhs => rw [hdec]
        exact (Function.iterate_add_apply R (a - b) b p).symm
      rw [heq] at e
      exact e
    exact rc_path_point_notMem R p (by omega) hxper

private theorem rc_Zpred_closed_tree {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (j : ℕ) (x : V)
    (hxper : x ∈ Function.periodicPts R) (hrL : R^[L] p = rc_root R p)
    (s : ℕ) (hs : s < L) :
    ((∃ s' : ℕ, s' < L ∧ R^[s'] p = Function.update R x p (R^[s] p)) ∨
      (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = Function.update R x p (R^[s] p))) := by
  have hne : R^[s] p ≠ x := by
    intro heq
    have hnp : R^[s] p ∉ Function.periodicPts R :=
      rc_path_point_notMem R p (by omega)
    exact hnp (by rw [heq]; exact hxper)
  have eR' : Function.update R x p (R^[s] p) = R (R^[s] p) :=
    Function.update_of_ne hne _ _
  rw [eR']
  by_cases hsL : s + 1 < L
  · refine Or.inl ⟨s + 1, hsL, Function.iterate_succ_apply' R s p⟩
  · refine Or.inr ⟨0, Nat.zero_le j, ?_⟩
    have hsL' : s + 1 = L := by omega
    have e2 : R (R^[s] p) = R^[L] p := by
      rw [← hsL']
      exact (Function.iterate_succ_apply' R s p).symm
    rw [e2, hrL, Function.iterate_zero_apply]

private theorem rc_Zpred_closed_cycle {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (h0L : 0 < L)
    (t : ℕ) (ht : t ≤ j) :
    ((∃ s : ℕ, s < L ∧ R^[s] p = Function.update R x p (R^[t] (rc_root R p))) ∨
      (∃ t' : ℕ, t' ≤ j ∧ R^[t'] (rc_root R p) =
        Function.update R x p (R^[t] (rc_root R p)))) := by
  by_cases htj : t = j
  · rw [htj, hxj, Function.update_self]
    refine Or.inl ⟨0, h0L, ?_⟩
    simp
  · have hne : R^[t] (rc_root R p) ≠ x := by
      intro heq
      rw [← hxj] at heq
      have htm : t < Function.minimalPeriod R (rc_root R p) := by omega
      have htu : t = j :=
        Function.iterate_injOn_Iio_minimalPeriod htm hjm heq
      exact htj htu
    have eR' : Function.update R x p (R^[t] (rc_root R p)) =
        R (R^[t] (rc_root R p)) :=
      Function.update_of_ne hne _ _
    rw [eR']
    have efin : R^[t + 1] (rc_root R p) = R (R^[t] (rc_root R p)) :=
      Function.iterate_succ_apply' R t _
    exact Or.inr ⟨t + 1, by omega, efin⟩

private theorem rc_Zmem_cycle_le {V : Type*} [Finite V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (hrper : rc_root R p ∈ Function.periodicPts R)
    (u : ℕ) (hum : u < Function.minimalPeriod R (rc_root R p))
    (hmem : ((∃ s : ℕ, s < L ∧ R^[s] p = R^[u] (rc_root R p)) ∨
      (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = R^[u] (rc_root R p)))) :
    u ≤ j := by
  rcases hmem with ⟨s, hs, heq⟩ | ⟨t, ht, heq⟩
  · exfalso
    have hnp : R^[s] p ∉ Function.periodicPts R :=
      rc_path_point_notMem R p (by omega)
    have hper : R^[s] p ∈ Function.periodicPts R := by
      rw [heq]
      exact rc_periodic_iterate R hrper u
    exact hnp hper
  · have htm : t < Function.minimalPeriod R (rc_root R p) := by omega
    have htu : t = u :=
      Function.iterate_injOn_Iio_minimalPeriod htm hum heq
    omega

private theorem rc_R'_agree_tree {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (x : V) (hxper : x ∈ Function.periodicPts R) :
    ∀ s : ℕ, s ≤ L → (Function.update R x p)^[s] p = R^[s] p := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s ≤ L := by omega
    have ih' := ih hs'
    have hne : R^[s] p ≠ x := by
      intro heq
      have hnp : R^[s] p ∉ Function.periodicPts R :=
        rc_path_point_notMem R p (show s < rc_level R p by omega)
      exact hnp (by rw [heq]; exact hxper)
    have e1 : (Function.update R x p)^[s + 1] p =
        Function.update R x p ((Function.update R x p)^[s] p) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : R^[s + 1] p = R (R^[s] p) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e1, e2, ih', Function.update_of_ne hne]

private theorem rc_R'_agree_cycle {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (r : V)
    (j : ℕ) (hjm : j < Function.minimalPeriod R r)
    (x p : V) (hxj : R^[j] r = x) :
    ∀ s : ℕ, s ≤ j → (Function.update R x p)^[s] r = R^[s] r := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s ≤ j := by omega
    have ih' := ih hs'
    have hne : R^[s] r ≠ x := by
      intro heq
      rw [← hxj] at heq
      have hsm : s < Function.minimalPeriod R r := by omega
      have hsu : s = j :=
        Function.iterate_injOn_Iio_minimalPeriod hsm hjm heq
      omega
    have e1 : (Function.update R x p)^[s + 1] r =
        Function.update R x p ((Function.update R x p)^[s] r) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : R^[s + 1] r = R (R^[s] r) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e1, e2, ih', Function.update_of_ne hne]

private theorem rc_caseC_setup {V : Type*} [Finite V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (x : V) (i : ℕ) (hi : R^[i] p = x) (hiL : L ≤ i) :
    ∃ j : ℕ, j < Function.minimalPeriod R (rc_root R p) ∧
      R^[j] (rc_root R p) = x ∧ x ∈ Function.periodicPts R := by
  have hxper : x ∈ Function.periodicPts R := by
    have h := rc_iterate_ge_level_periodic R p (show rc_level R p ≤ i by omega)
    rw [hi] at h
    exact h
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hL]
  have hxp : R^[i - L] (rc_root R p) = x := by
    have e : R^[i] p = R^[i - L] (R^[L] p) := by
      have hdec : i = (i - L) + L := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply R (i - L) L p
    rw [hi, hrL] at e
    exact e.symm
  refine ⟨(i - L) % Function.minimalPeriod R (rc_root R p), ?_, ?_, hxper⟩
  · exact Nat.mod_lt _ (Function.minimalPeriod_pos_of_mem_periodicPts
      (rc_root_periodic R p))
  · have e : R^[(i - L) % Function.minimalPeriod R (rc_root R p)] (rc_root R p) =
        R^[i - L] (rc_root R p) :=
      Function.iterate_mod_minimalPeriod_eq
    rw [e]
    exact hxp

private theorem rc_caseC1 {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hx : rc_adj delta x p) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (hC1 : L + j + 1 < Function.minimalPeriod R (rc_root R p)) :
    False := by
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hp]
  set y := R^[j + 1] (rc_root R p) with hy
  have hj1m : j + 1 < Function.minimalPeriod R (rc_root R p) := by omega
  have hagree_y : ∀ s : ℕ, s ≤ Function.minimalPeriod R (rc_root R p) - j - 1 →
      (Function.update R x p)^[s] y = R^[s] y := by
    intro s
    induction s with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      have hs' : s ≤ Function.minimalPeriod R (rc_root R p) - j - 1 := by omega
      have ih' := ih hs'
      have hne : R^[s] y ≠ x := by
        intro heq
        have e : R^[s] y = R^[j + 1 + s] (rc_root R p) := by
          rw [hy]
          have hdec : j + 1 + s = s + (j + 1) := by omega
          rw [hdec]
          exact (Function.iterate_add_apply R s (j + 1) _).symm
        rw [e, ← hxj] at heq
        have h1 : j + 1 + s < Function.minimalPeriod R (rc_root R p) := by omega
        exact (by omega : j + 1 + s ≠ j)
          (Function.iterate_injOn_Iio_minimalPeriod h1 hjm heq)
      have e1 : (Function.update R x p)^[s + 1] y =
          Function.update R x p ((Function.update R x p)^[s] y) := by
        rw [show s + 1 = s.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      have e2 : R^[s + 1] y = R (R^[s] y) := by
        rw [show s + 1 = s.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      rw [e1, e2, ih', Function.update_of_ne hne]
  have hY : (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1] y =
      rc_root R p := by
    rw [hagree_y _ le_rfl]
    have e : R^[Function.minimalPeriod R (rc_root R p) - j - 1] y =
        R^[Function.minimalPeriod R (rc_root R p)] (rc_root R p) := by
      rw [hy]
      have hdec : Function.minimalPeriod R (rc_root R p) =
          (Function.minimalPeriod R (rc_root R p) - j - 1) + (j + 1) := by omega
      conv_rhs => rw [hdec]
      exact (Function.iterate_add_apply R
        (Function.minimalPeriod R (rc_root R p) - j - 1) (j + 1) _).symm
    rw [e]
    have hmper : R^[Function.minimalPeriod R (rc_root R p)] (rc_root R p) =
        rc_root R p :=
      Function.iterate_minimalPeriod
    exact hmper
  have hagree_r : ∀ s : ℕ, s ≤ j →
      (Function.update R x p)^[s] (rc_root R p) = R^[s] (rc_root R p) :=
    fun s hs => rc_R'_agree_cycle R _ j hjm x p hxj s hs
  have e2a : (Function.update R x p)^[j] (rc_root R p) = x := by
    rw [rc_R'_agree_cycle R _ j hjm x p hxj j le_rfl]
    exact hxj
  have e2 : (Function.update R x p)^[j + 1] (rc_root R p) = p := by
    have e : (Function.update R x p)^[j + 1] (rc_root R p) =
        Function.update R x p ((Function.update R x p)^[j] (rc_root R p)) := by
      rw [show j + 1 = j.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e, e2a]
    exact Function.update_self _ _ _
  have e3 : (Function.update R x p)^[L] p = rc_root R p := by
    rw [rc_R'_agree_tree R p L hp x hxper L le_rfl, hrL]
  have hrper' : rc_root R p ∈ Function.periodicPts (Function.update R x p) := by
    refine Function.mem_periodicPts.mpr ⟨j + 1 + L, by omega, ?_⟩
    have e1 : (Function.update R x p)^[j + 1 + L] (rc_root R p) =
        (Function.update R x p)^[L] ((Function.update R x p)^[j + 1] (rc_root R p)) := by
      have hdec : j + 1 + L = L + (j + 1) := by omega
      rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    have hret : (Function.update R x p)^[j + 1 + L] (rc_root R p) = rc_root R p := by
      rw [e1, e2]
      exact e3
    exact hret
  have hlev_y : rc_level (Function.update R x p) y =
      Function.minimalPeriod R (rc_root R p) - j - 1 := by
    apply le_antisymm
    · exact rc_level_le_of_mem _ _ (by rw [hY]; exact hrper')
    · by_contra hcon
      have hlt : rc_level (Function.update R x p) y <
          Function.minimalPeriod R (rc_root R p) - j - 1 := by omega
      have hspec := rc_level_spec (Function.update R x p) y
      have hle : rc_level (Function.update R x p) y ≤
          Function.minimalPeriod R (rc_root R p) - j - 1 := by omega
      have eag : (Function.update R x p)^[rc_level (Function.update R x p) y] y =
          R^[rc_level (Function.update R x p) y] y :=
        hagree_y _ hle
      have hPclosed : ∀ a : V,
          (∃ t : ℕ, (Function.update R x p)^[t] (rc_root R p) = a) →
          ∃ t : ℕ, (Function.update R x p)^[t] (rc_root R p) =
            Function.update R x p a := by
        intro a ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        have e : (Function.update R x p)^[t + 1] (rc_root R p) =
            Function.update R x p ((Function.update R x p)^[t] (rc_root R p)) := by
          rw [show t + 1 = t.succ from rfl]
          exact Function.iterate_succ_apply' _ _ _
        rw [e, ht]
      have hmemP : (∃ t : ℕ, (Function.update R x p)^[t] (rc_root R p) =
          (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1 -
            rc_level (Function.update R x p) y]
            ((Function.update R x p)^[rc_level (Function.update R x p) y] y)) := by
        have e : (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1 -
              rc_level (Function.update R x p) y]
              ((Function.update R x p)^[rc_level (Function.update R x p) y] y) =
            (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - j - 1] y := by
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
        rw [e, hY]
        refine ⟨0, ?_⟩
        simp
      have hconP := rc_mem_of_periodic_iterate_mem _ _ hPclosed _ hspec _ hmemP
      obtain ⟨t, ht⟩ := hconP
      have hZall : ∀ u : ℕ,
          ((∃ s : ℕ, s < L ∧ R^[s] p = (Function.update R x p)^[u] (rc_root R p)) ∨
            (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) =
              (Function.update R x p)^[u] (rc_root R p))) := by
        intro u
        induction u with
        | zero =>
          refine Or.inr ⟨0, Nat.zero_le j, ?_⟩
          simp
        | succ u ih =>
          have e : (Function.update R x p)^[u + 1] (rc_root R p) =
              Function.update R x p ((Function.update R x p)^[u] (rc_root R p)) := by
            rw [show u + 1 = u.succ from rfl]
            exact Function.iterate_succ_apply' _ _ _
          rw [e]
          rcases ih with ⟨s, hs, heq⟩ | ⟨w, hw, heq⟩
          · have h := rc_Zpred_closed_tree R p L hp j x hxper hrL s hs
            rw [heq] at h
            exact h
          · have h := rc_Zpred_closed_cycle R p L j hjm x hxj hH w hw
            rw [heq] at h
            exact h
      have hZt := hZall t
      rw [ht] at hZt
      have epos : (Function.update R x p)^[rc_level (Function.update R x p) y] y =
          R^[j + 1 + rc_level (Function.update R x p) y] (rc_root R p) := by
        rw [eag]
        have e1 : R^[rc_level (Function.update R x p) y] y =
            R^[rc_level (Function.update R x p) y] (R^[j + 1] (rc_root R p)) :=
          congrArg _ hy
        have hdec : j + 1 + rc_level (Function.update R x p) y =
            rc_level (Function.update R x p) y + (j + 1) := by omega
        rw [hdec, e1]
        exact (Function.iterate_add_apply R _ _ _).symm
      rw [epos] at hZt
      have hpos : j + 1 + rc_level (Function.update R x p) y <
          Function.minimalPeriod R (rc_root R p) := by omega
      have hle2 := rc_Zmem_cycle_le R p L hp j hjm hrper _ hpos hZt
      omega
  have hgt : L < rc_height (Function.update R x p) := by
    have h1 := rc_level_le_height (Function.update R x p) y
    omega
  have hle := hHmax _ (rc_ssg_update_edge delta R hR x p hx)
  omega

private theorem rc_R'_to_root {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hL : rc_level R p = L)
    (x : V) (hxper : x ∈ Function.periodicPts R) :
    (Function.update R x p)^[L] p = rc_root R p := by
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hL]
  rw [rc_R'_agree_tree R p L hL x hxper L le_rfl, hrL]

private theorem rc_R'_to_p {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (r : V) (j : ℕ) (hjm : j < Function.minimalPeriod R r)
    (x p : V) (hxj : R^[j] r = x) :
    (Function.update R x p)^[j + 1] r = p := by
  have e2a : (Function.update R x p)^[j] r = x := by
    rw [rc_R'_agree_cycle R r j hjm x p hxj j le_rfl]
    exact hxj
  have e : (Function.update R x p)^[j + 1] r =
      Function.update R x p ((Function.update R x p)^[j] r) := by
    rw [show j + 1 = j.succ from rfl]
    exact Function.iterate_succ_apply' _ _ _
  rw [e, e2a]
  exact Function.update_self _ _ _

private theorem rc_caseC2_tree_per {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (s : ℕ) (hs : s < L) :
    R^[s] p ∈ Function.periodicPts (Function.update R x p) := by
  have hpos : 0 < L + j + 1 := by omega
  refine Function.mem_periodicPts.mpr ⟨L + j + 1, hpos, ?_⟩
  have step1 : (Function.update R x p)^[L - s] (R^[s] p) = rc_root R p := by
    have a1 := rc_R'_agree_tree R p L hp x hxper s (by omega)
    have a2 := rc_R'_to_root R p L hp x hxper
    have hdec : L = (L - s) + s := by omega
    have e : (Function.update R x p)^[L] p =
        (Function.update R x p)^[L - s] ((Function.update R x p)^[s] p) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, a1] at a2
    exact a2
  have step2 : (Function.update R x p)^[(L - s) + (j + 1)] (R^[s] p) = p := by
    have e : (Function.update R x p)^[(L - s) + (j + 1)] (R^[s] p) =
        (Function.update R x p)^[j + 1]
          ((Function.update R x p)^[L - s] (R^[s] p)) := by
      have hdec : (L - s) + (j + 1) = (j + 1) + (L - s) := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, step1]
    exact rc_R'_to_p R _ j hjm x p hxj
  have hdec : L + j + 1 = s + ((L - s) + (j + 1)) := by omega
  have e : (Function.update R x p)^[L + j + 1] (R^[s] p) =
      (Function.update R x p)^[s]
        ((Function.update R x p)^[(L - s) + (j + 1)] (R^[s] p)) := by
    conv_lhs => rw [hdec]
    exact Function.iterate_add_apply _ _ _ _
  have hfin : (Function.update R x p)^[L + j + 1] (R^[s] p) = R^[s] p := by
    rw [e, step2]
    exact rc_R'_agree_tree R p L hp x hxper s (by omega)
  exact hfin

private theorem rc_caseC2_seg_per {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (t : ℕ) (ht : t ≤ j) :
    R^[t] (rc_root R p) ∈ Function.periodicPts (Function.update R x p) := by
  have hpos : 0 < L + j + 1 := by omega
  refine Function.mem_periodicPts.mpr ⟨L + j + 1, hpos, ?_⟩
  have step1 : (Function.update R x p)^[j - t] (R^[t] (rc_root R p)) = x := by
    have a1 := rc_R'_agree_cycle R _ j hjm x p hxj t ht
    have a2 : (Function.update R x p)^[j] (rc_root R p) = x := by
      rw [rc_R'_agree_cycle R _ j hjm x p hxj j le_rfl]
      exact hxj
    have hdec : j = (j - t) + t := by omega
    have e : (Function.update R x p)^[j] (rc_root R p) =
        (Function.update R x p)^[j - t]
          ((Function.update R x p)^[t] (rc_root R p)) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, a1] at a2
    exact a2
  have step2 : (Function.update R x p)^[(j - t) + 1] (R^[t] (rc_root R p)) = p := by
    have e : (Function.update R x p)^[(j - t) + 1] (R^[t] (rc_root R p)) =
        Function.update R x p
          ((Function.update R x p)^[j - t] (R^[t] (rc_root R p))) := by
      rw [show (j - t) + 1 = ((j - t)).succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e, step1]
    exact Function.update_self _ _ _
  have step3 : (Function.update R x p)^[(j - t) + 1 + L] (R^[t] (rc_root R p)) =
      rc_root R p := by
    have e : (Function.update R x p)^[(j - t) + 1 + L] (R^[t] (rc_root R p)) =
        (Function.update R x p)^[L]
          ((Function.update R x p)^[(j - t) + 1] (R^[t] (rc_root R p))) := by
      have hdec : (j - t) + 1 + L = L + ((j - t) + 1) := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    rw [e, step2]
    exact rc_R'_to_root R p L hp x hxper
  have hdec : L + j + 1 = t + ((j - t) + 1 + L) := by omega
  have e : (Function.update R x p)^[L + j + 1] (R^[t] (rc_root R p)) =
      (Function.update R x p)^[t]
        ((Function.update R x p)^[(j - t) + 1 + L] (R^[t] (rc_root R p))) := by
    conv_lhs => rw [hdec]
    exact Function.iterate_add_apply _ _ _ _
  have hfin : (Function.update R x p)^[L + j + 1] (R^[t] (rc_root R p)) =
      R^[t] (rc_root R p) := by
    rw [e, step3]
    exact rc_R'_agree_cycle R _ j hjm x p hxj t ht
  exact hfin

private theorem rc_update_iterate_one {V : Type*} [DecidableEq V]
    (R : V → V) (x p v : V) :
    (Function.update R x p)^[1] v = Function.update R x p v := by
  rw [show (1 : ℕ) = Nat.succ 0 from rfl, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

private theorem rc_update_agree_upto {V : Type*} [DecidableEq V]
    (R : V → V) (x w v : V) (N : ℕ)
    (havoid : ∀ s : ℕ, s < N → R^[s] v ≠ x) :
    ∀ s : ℕ, s ≤ N → (Function.update R x w)^[s] v = R^[s] v := by
  intro s
  induction s with
  | zero => intro _; rfl
  | succ s ih =>
    intro hs
    have hs' : s ≤ N := by omega
    have ih' := ih hs'
    have hne : R^[s] v ≠ x := havoid s (by omega)
    have e1 : (Function.update R x w)^[s + 1] v =
        Function.update R x w ((Function.update R x w)^[s] v) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : R^[s + 1] v = R (R^[s] v) := by
      rw [show s + 1 = s.succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e1, e2, ih', Function.update_of_ne hne]

private theorem rc_caseC2_qagree {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (q : V) (L : ℕ) (hq_top : rc_level R q = L)
    (x p : V) (hxper : x ∈ Function.periodicPts R) :
    ∀ s : ℕ, s ≤ L → (Function.update R x p)^[s] q = R^[s] q := by
  apply rc_update_agree_upto R x p q L _
  intro s' hs' heq
  have hnp : R^[s'] q ∉ Function.periodicPts R :=
    rc_path_point_notMem R q (show s' < rc_level R q by omega)
  exact hnp (by rw [heq]; exact hxper)

private theorem rc_caseC2_offcycle {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (L : ℕ) (p : V)
    (q : V) (hq_top : rc_level R q = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (hqC : rc_root R q ∉ rc_cycleFin R (rc_root R p)) :
    rc_level (Function.update R x p) q = L := by
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have havoid : ∀ i : ℕ, R^[i] q ≠ x := by
    intro i heq
    by_cases hiL : i < L
    · have hnp : R^[i] q ∉ Function.periodicPts R :=
        rc_path_point_notMem R q (show i < rc_level R q by omega)
      exact hnp (by rw [heq]; exact hxper)
    · have hper_i : R^[i] q ∈ Function.periodicPts R :=
        rc_iterate_ge_level_periodic R q (show rc_level R q ≤ i by omega)
      have e : R^[i] q = R^[i - L] (rc_root R q) := by
        have hLq : R^[L] q = rc_root R q := by
          unfold rc_root
          rw [hq_top]
        have hdec : i = (i - L) + L := by omega
        conv_lhs => rw [hdec]
        rw [← hLq]
        exact Function.iterate_add_apply R (i - L) L q
      have hmem : R^[i - L] (rc_root R q) ∈ rc_cycleFin R (rc_root R p) := by
        rw [← e, heq]
        exact (rc_cycleFin_mem R _ _).mpr ⟨j, hjm, hxj⟩
      exact hqC (rc_cycleFin_absorb R _ hrper _ (rc_root_periodic R q) _ hmem)
  have hlev : rc_level (Function.update R x p) q = L := by
    rw [rc_update_level_eq R x p q havoid]
    exact hq_top
  exact hlev

private theorem rc_caseC2_oncycle_gt {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (q : V) (hq_top : rc_level R q = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hx : rc_adj delta x p) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (t : ℕ) (htm : t < Function.minimalPeriod R (rc_root R p))
    (htq : R^[t] (rc_root R p) = rc_root R q) (hgt : j < t) :
    False := by
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hp]
  have hLq : R^[L] q = rc_root R q := by
    unfold rc_root
    rw [hq_top]
  have hagT : ∀ s : ℕ, s ≤ Function.minimalPeriod R (rc_root R p) - t →
      (Function.update R x p)^[s] (R^[t] (rc_root R p)) =
        R^[s] (R^[t] (rc_root R p)) := by
    apply rc_update_agree_upto R x p _ (Function.minimalPeriod R (rc_root R p) - t) _
    intro s' hs' heq
    have e : R^[s'] (R^[t] (rc_root R p)) = R^[t + s'] (rc_root R p) := by
      have hdec : t + s' = s' + t := by omega
      rw [hdec]
      exact (Function.iterate_add_apply R s' t _).symm
    rw [e, ← hxj] at heq
    have h1 : t + s' < Function.minimalPeriod R (rc_root R p) := by omega
    exact (by omega : t + s' ≠ j)
      (Function.iterate_injOn_Iio_minimalPeriod h1 hjm heq)
  have hland : (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - t]
      (R^[t] (rc_root R p)) = rc_root R p := by
    rw [hagT _ le_rfl]
    have e : R^[Function.minimalPeriod R (rc_root R p) - t] (R^[t] (rc_root R p)) =
        R^[Function.minimalPeriod R (rc_root R p)] (rc_root R p) := by
      have hdec : Function.minimalPeriod R (rc_root R p) =
          (Function.minimalPeriod R (rc_root R p) - t) + t := by omega
      conv_rhs => rw [hdec]
      exact (Function.iterate_add_apply R
        (Function.minimalPeriod R (rc_root R p) - t) t _).symm
    rw [e]
    exact Function.iterate_minimalPeriod
  have hclosedZ : ∀ a : V, ((∃ s : ℕ, s < L ∧ R^[s] p = a) ∨
      (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) = a)) →
      ((∃ s : ℕ, s < L ∧ R^[s] p = Function.update R x p a) ∨
        (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) = Function.update R x p a)) := by
    intro a ha
    rcases ha with ⟨s, hs, heq⟩ | ⟨w, hw, heq⟩
    · have h := rc_Zpred_closed_tree R p L hp j x hxper hrL s hs
      rw [heq] at h
      exact h
    · have h := rc_Zpred_closed_cycle R p L j hjm x hxj hH w hw
      rw [heq] at h
      exact h
  have hLq' : (Function.update R x p)^[L] q = R^[t] (rc_root R p) := by
    rw [rc_caseC2_qagree R q L hq_top x p hxper L le_rfl, hLq, ← htq]
  have hnper : (Function.update R x p)^[L] q ∉
      Function.periodicPts (Function.update R x p) := by
    intro hmem
    have hmemZ : ((∃ s : ℕ, s < L ∧ R^[s] p =
        (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - t]
          ((Function.update R x p)^[L] q)) ∨
        (∃ w : ℕ, w ≤ j ∧ R^[w] (rc_root R p) =
          (Function.update R x p)^[Function.minimalPeriod R (rc_root R p) - t]
            ((Function.update R x p)^[L] q))) := by
      rw [hLq', hland]
      exact Or.inr ⟨0, Nat.zero_le j, by simp⟩
    have hZP := rc_mem_of_periodic_iterate_mem _ _ hclosedZ _ hmem _ hmemZ
    rcases hZP with ⟨s, hs, heq⟩ | ⟨w, hw, heq⟩
    · have hnp : R^[s] p ∉ Function.periodicPts R :=
        rc_path_point_notMem R p (by omega)
      rw [hLq'] at heq
      have hper : R^[s] p ∈ Function.periodicPts R := by
        rw [heq]
        exact rc_periodic_iterate R hrper t
      exact hnp hper
    · rw [hLq'] at heq
      have hwm : w < Function.minimalPeriod R (rc_root R p) := by omega
      have hwt : w = t :=
        Function.iterate_injOn_Iio_minimalPeriod hwm htm heq
      omega
  have hlev : L < rc_level (Function.update R x p) q := by
    by_contra hcon
    have hle : rc_level (Function.update R x p) q ≤ L := by omega
    exact hnper (rc_iterate_ge_level_periodic _ _ hle)
  have hgt2 : L < rc_height (Function.update R x p) := by
    have h1 := rc_level_le_height (Function.update R x p) q
    omega
  have hle := hHmax _ (rc_ssg_update_edge delta R hR x p hx)
  omega

private theorem rc_caseC2_cyc {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V) (L : ℕ)
    (p : V) (hp : rc_level R p = L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hperT : ∀ s : ℕ, s < L →
      R^[s] p ∈ Function.periodicPts (Function.update R x p))
    (hperS : ∀ t : ℕ, t ≤ j →
      R^[t] (rc_root R p) ∈ Function.periodicPts (Function.update R x p))
    (hC2 : Function.minimalPeriod R (rc_root R p) < L + j + 1) :
    rc_cyc R < rc_cyc (Function.update R x p) := by
  classical
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hCcard : (rc_cycleFin R (rc_root R p)).card =
      Function.minimalPeriod R (rc_root R p) := rc_cycleFin_card _ _
  have hCsub : rc_cycleFin R (rc_root R p) ⊆
      Finset.univ.filter (fun v => v ∈ Function.periodicPts R) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
    obtain ⟨t, ht, rfl⟩ := (rc_cycleFin_mem R _ _).mp hz
    exact rc_periodic_iterate R hrper t
  have hTinj : Set.InjOn (fun s => R^[s] p) ↑(Finset.range L) := by
    intro a ha b hb hab
    have ha' : a < L := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < L := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    by_contra hne
    exact rc_path_ne_of_lt R p L hp ha' hb' hne hab
  have hTcard : ((Finset.range L).image (fun s => R^[s] p)).card = L := by
    rw [Finset.card_image_of_injOn hTinj, Finset.card_range]
  have hSinj : Set.InjOn (fun t => R^[t] (rc_root R p))
      ↑(Finset.range (j + 1)) := by
    intro a ha b hb hab
    have ha' : a < j + 1 := Finset.mem_range.mp (Finset.mem_coe.mp ha)
    have hb' : b < j + 1 := Finset.mem_range.mp (Finset.mem_coe.mp hb)
    have ham : a < Function.minimalPeriod R (rc_root R p) := by omega
    have hbm : b < Function.minimalPeriod R (rc_root R p) := by omega
    exact Function.iterate_injOn_Iio_minimalPeriod ham hbm hab
  have hScard : ((Finset.range (j + 1)).image
      (fun t => R^[t] (rc_root R p))).card = j + 1 := by
    rw [Finset.card_image_of_injOn hSinj, Finset.card_range]
  have hTSdisj : Disjoint ((Finset.range L).image (fun s => R^[s] p))
      ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p))) := by
    rw [Finset.disjoint_left]
    intro z hzT hzS
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzT
    obtain ⟨t, ht, htz⟩ := Finset.mem_image.mp hzS
    have hsm : s < L := Finset.mem_range.mp hs
    have hper : R^[s] p ∈ Function.periodicPts R := by
      rw [← htz]
      exact rc_periodic_iterate R hrper t
    exact rc_path_point_notMem R p (by omega) hper
  have hZcard : (((Finset.range L).image (fun s => R^[s] p)) ∪
      ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p)))).card =
      L + (j + 1) := by
    rw [Finset.card_union_of_disjoint hTSdisj, hTcard, hScard]
  have hZsub : (((Finset.range L).image (fun s => R^[s] p)) ∪
      ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p)))) ⊆
      Finset.univ.filter
        (fun v => v ∈ Function.periodicPts (Function.update R x p)) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
    rcases Finset.mem_union.mp hz with hzT | hzS
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzT
      exact hperT s (Finset.mem_range.mp hs)
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzS
      have htm : t < j + 1 := Finset.mem_range.mp ht
      exact hperS t (by omega)
  have hSCsub : (Finset.univ.filter (fun v => v ∈ Function.periodicPts R)) \
      rc_cycleFin R (rc_root R p) ⊆
      Finset.univ.filter
        (fun v => v ∈ Function.periodicPts (Function.update R x p)) := by
    intro z hz
    have hzS := (Finset.mem_sdiff.mp hz).1
    have hzC := (Finset.mem_sdiff.mp hz).2
    have hzp : z ∈ Function.periodicPts R := (Finset.mem_filter.mp hzS).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ z, ?_⟩
    apply rc_update_periodic R x p z _ hzp
    intro i heq
    have hxC : x ∈ rc_cycleFin R (rc_root R p) :=
      (rc_cycleFin_mem R _ _).mpr ⟨j, hjm, hxj⟩
    have hmem : R^[i] z ∈ rc_cycleFin R (rc_root R p) := by
      rw [heq]
      exact hxC
    exact hzC (rc_cycleFin_absorb R _ hrper z hzp i hmem)
  have hdisj : Disjoint ((Finset.univ.filter (fun v => v ∈ Function.periodicPts R)) \
      rc_cycleFin R (rc_root R p))
      (((Finset.range L).image (fun s => R^[s] p)) ∪
        ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p)))) := by
    rw [Finset.disjoint_left]
    intro z hzSC hzZ
    have hzC : z ∉ rc_cycleFin R (rc_root R p) := (Finset.mem_sdiff.mp hzSC).2
    have hzP : z ∈ Function.periodicPts R :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hzSC).1).2
    rcases Finset.mem_union.mp hzZ with hzT | hzS
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hzT
      have hsm : s < L := Finset.mem_range.mp hs
      exact rc_path_point_notMem R p (by omega) hzP
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hzS
      have htm0 : t < j + 1 := Finset.mem_range.mp ht
      exact hzC ((rc_cycleFin_mem R _ _).mpr ⟨t, by omega, rfl⟩)
  have hUsub : (((Finset.univ.filter (fun v => v ∈ Function.periodicPts R)) \
      rc_cycleFin R (rc_root R p)) ∪
      (((Finset.range L).image (fun s => R^[s] p)) ∪
        ((Finset.range (j + 1)).image (fun t => R^[t] (rc_root R p))))) ⊆
      Finset.univ.filter
        (fun v => v ∈ Function.periodicPts (Function.update R x p)) :=
    Finset.union_subset hSCsub hZsub
  have hcard := Finset.card_le_card hUsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hCsub, hZcard,
    hCcard] at hcard
  unfold rc_cyc
  omega

private theorem rc_caseA_offorbit {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (x : V) (hx : rc_adj delta x p) (havoid : ∀ i : ℕ, R^[i] p ≠ x) :
    False := by
  classical
  have hR'ssg : rc_isSSG delta (Function.update R x p) :=
    rc_ssg_update_edge delta R hR x p hx
  have hRx : Function.update R x p x = p := Function.update_self _ _ _
  have hagree_p : ∀ s : ℕ, (Function.update R x p)^[s] p = R^[s] p :=
    fun s => rc_update_iterate_agree R x p p havoid s
  have hLp : (Function.update R x p)^[L] x = R^[L - 1] p := by
    have hdec : L = (L - 1) + 1 := by omega
    have e1 : (Function.update R x p)^[L] x =
        (Function.update R x p)^[L - 1] ((Function.update R x p) x) := by
      conv_lhs => rw [hdec]
      rw [Function.iterate_add_apply, rc_update_iterate_one]
    rw [e1, hRx, hagree_p]
  have hnper : R^[L - 1] p ∉ Function.periodicPts R := by
    intro hmem
    have h0 := (rc_level_zero_iff R _).mpr hmem
    have h := rc_level_along_orbit R p (L - 1) (by omega)
    omega
  have havoid2 : ∀ i : ℕ, R^[i] (R^[L - 1] p) ≠ x := by
    intro i heq
    have e : R^[i] (R^[L - 1] p) = R^[L - 1 + i] p := by
      rw [show L - 1 + i = i + (L - 1) from by omega]
      exact (Function.iterate_add_apply R i (L - 1) p).symm
    rw [e] at heq
    exact havoid _ heq
  have hnper' : R^[L - 1] p ∉ Function.periodicPts (Function.update R x p) := by
    intro hmem
    apply hnper
    exact rc_update_periodic_of R x p _
      (fun j => rc_update_iterate_agree R x p _ havoid2 j) hmem
  have hgt : L < rc_height (Function.update R x p) :=
    rc_height_gt_of_iterate_notMem _ x L (by rwa [hLp])
  have hle := hHmax _ hR'ssg
  omega

private theorem rc_caseB_tree {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (q : V) (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (x : V) (hx : rc_adj delta x p)
    (i : ℕ) (hi : R^[i] p = x) (hiL : i < L) :
    False := by
  classical
  have hxnp : x ∉ Function.periodicPts R := by
    rw [← hi]
    exact rc_path_point_notMem R p (by omega)
  have hpnp : p ∉ Function.periodicPts R := by
    intro hmem
    have h0 := (rc_level_zero_iff R p).mpr hmem
    omega
  have hR'ssg : rc_isSSG delta (Function.update R x p) :=
    rc_ssg_update_edge delta R hR x p hx
  have hRx : Function.update R x p x = p := Function.update_self _ _ _
  have hagree : ∀ s : ℕ, s ≤ i → (Function.update R x p)^[s] p = R^[s] p := by
    apply rc_update_agree_upto R x p p i _
    intro s hs heq
    exact rc_path_ne_of_lt R p L hp (by omega) hiL (by omega) (heq.trans hi.symm)
  have hRip : (Function.update R x p)^[i] p = x := by
    rw [hagree i le_rfl, hi]
  have hper_p' : p ∈ Function.periodicPts (Function.update R x p) := by
    refine Function.mem_periodicPts.mpr ⟨i + 1, by omega, ?_⟩
    change (Function.update R x p)^[i + 1] p = p
    have e : (Function.update R x p)^[i + 1] p =
        Function.update R x p ((Function.update R x p)^[i] p) := by
      rw [show i + 1 = i.succ from rfl]
      exact Function.iterate_succ_apply' _ i p
    rw [e, hRip, hRx]
  have hsub : ∀ z : V, z ∈ Function.periodicPts R →
      z ∈ Function.periodicPts (Function.update R x p) := by
    intro z hz
    refine rc_update_periodic R x p z ?_ hz
    intro t heq
    have h1 := rc_periodic_iterate R hz t
    rw [heq] at h1
    exact hxnp h1
  have hcyc : rc_cyc R < rc_cyc (Function.update R x p) :=
    rc_cyc_gt_of_subset_ne R _ hsub p hper_p' hpnp
  have hrootx : rc_root R x = rc_root R p := by
    rw [← hi]
    exact rc_root_along_orbit R p (by omega)
  have hneq : rc_root R q ≠ rc_root R x := by
    rw [hrootx]
    exact hq_root
  have havoid_q : ∀ t : ℕ, R^[t] q ≠ x := by
    intro t
    exact rc_orbit_avoid_of_root_ne R q x hxnp hneq t
  have hlevq : rc_level (Function.update R x p) q = L := by
    rw [rc_update_level_eq R x p q havoid_q]
    exact hq_top
  have hght : L ≤ rc_height (Function.update R x p) := by
    have h1 := rc_level_le_height (Function.update R x p) q
    omega
  by_cases hgt : L < rc_height (Function.update R x p)
  · have hle := hHmax _ hR'ssg
    omega
  · have heqH : rc_height (Function.update R x p) = rc_height R := by omega
    have hle := hCmax _ hR'ssg heqH
    omega

private theorem rc_caseC2_oncycle_le {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (p : V) (L : ℕ) (hp : rc_level R p = L) (hH : 1 ≤ L)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (q : V) (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (s : ℕ) (hsj : s ≤ j)
    (hsq : R^[s] (rc_root R p) = rc_root R q) :
    rc_level (Function.update R x p) q = L := by
  classical
  have hrper : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  have hcP : x ∈ Function.periodicPts R := hxper
  have hnper_q : R^[L - 1] q ∉ Function.periodicPts R :=
    rc_path_point_notMem R q (by omega)
  have hLq : R^[L] q = rc_root R q := by
    unfold rc_root
    rw [hq_top]
  have hrL : R^[L] p = rc_root R p := by
    unfold rc_root
    rw [hp]
  have hagree_q : ∀ t : ℕ, t ≤ L →
      (Function.update R x p)^[t] q = R^[t] q :=
    rc_caseC2_qagree R q L hq_top x p hxper
  have hag : (Function.update R x p)^[L - 1] q = R^[L - 1] q :=
    hagree_q (L - 1) (by omega)
  have hclosed : ∀ a : V, ((∃ s' : ℕ, s' < L ∧ R^[s'] p = a) ∨
      (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = a)) →
      ((∃ s' : ℕ, s' < L ∧ R^[s'] p = Function.update R x p a) ∨
        (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) = Function.update R x p a)) := by
    intro a ha
    rcases ha with ⟨s', hs', heq⟩ | ⟨t, ht, heq⟩
    · have hne : R^[s'] p ≠ x := by
        intro hcon
        have hnp : R^[s'] p ∉ Function.periodicPts R :=
          rc_path_point_notMem R p (by omega)
        exact hnp (by rw [hcon]; exact hxper)
      have eR' : Function.update R x p (R^[s'] p) = R (R^[s'] p) :=
        Function.update_of_ne hne _ _
      by_cases hsL : s' + 1 < L
      · refine Or.inl ⟨s' + 1, hsL, ?_⟩
        rw [← heq, eR']
        exact Function.iterate_succ_apply' R s' p
      · refine Or.inr ⟨0, Nat.zero_le j, ?_⟩
        rw [← heq, eR']
        have hsL' : s' + 1 = L := by omega
        have e2 : R (R^[s'] p) = R^[L] p := by
          rw [← hsL']
          exact (Function.iterate_succ_apply' R s' p).symm
        rw [e2, hrL, Function.iterate_zero_apply]
    · by_cases htj : t = j
      · subst htj
        rw [hxj] at heq
        refine Or.inl ⟨0, by omega, ?_⟩
        rw [← heq, Function.iterate_zero_apply, Function.update_self]
      · have hne : R^[t] (rc_root R p) ≠ x := by
          intro hcon
          have htm : t < Function.minimalPeriod R (rc_root R p) := by omega
          exact htj (Function.iterate_injOn_Iio_minimalPeriod htm hjm
            (hcon.trans hxj.symm))
        have eR' : Function.update R x p (R^[t] (rc_root R p)) =
            R (R^[t] (rc_root R p)) := Function.update_of_ne hne _ _
        refine Or.inr ⟨t + 1, by omega, ?_⟩
        rw [← heq, eR']
        exact Function.iterate_succ_apply' R t _
  have hstep : (Function.update R x p)^[1] (R^[L - 1] q) = rc_root R q := by
    rw [rc_update_iterate_one]
    have hne : R^[L - 1] q ≠ x := by
      intro hcon
      exact hnper_q (by rw [hcon]; exact hxper)
    have eR' : Function.update R x p (R^[L - 1] q) = R (R^[L - 1] q) :=
      Function.update_of_ne hne _ _
    have hdec : L = (L - 1) + 1 := by omega
    have e2 : R (R^[L - 1] q) = R^[L] q := by
      conv_rhs => rw [hdec]
      exact (Function.iterate_succ_apply' R (L - 1) q).symm
    rw [eR', e2, hLq]
  have hnper'_q : R^[L - 1] q ∉
      Function.periodicPts (Function.update R x p) := by
    intro hmem
    rw [← hag] at hmem
    have hmemZ : ((∃ s' : ℕ, s' < L ∧ R^[s'] p =
        (Function.update R x p)^[1] ((Function.update R x p)^[L - 1] q)) ∨
        (∃ t : ℕ, t ≤ j ∧ R^[t] (rc_root R p) =
          (Function.update R x p)^[1] ((Function.update R x p)^[L - 1] q))) := by
      rw [hag, hstep]
      exact Or.inr ⟨s, hsj, hsq⟩
    have hZP := rc_mem_of_periodic_iterate_mem _ _ hclosed _ hmem 1 hmemZ
    rcases hZP with ⟨s', hs', heqZ⟩ | ⟨t, ht, heqZ⟩
    · rw [hag] at heqZ
      have e3 : R (R^[s'] p) = R^[s' + 1] p :=
        (Function.iterate_succ_apply' R s' p).symm
      have eL : R^[L] q = R^[s' + 1] p := by
        have e1 : R (R^[L - 1] q) = R (R^[s'] p) := congrArg R heqZ.symm
        have e2 : R (R^[L - 1] q) = R^[L] q := by
          have hdec : L = (L - 1) + 1 := by omega
          conv_rhs => rw [hdec]
          exact (Function.iterate_succ_apply' R (L - 1) q).symm
        rwa [e2, e3] at e1
      have hperL : R^[s' + 1] p ∈ Function.periodicPts R := by
        rw [← eL, hLq]
        exact rc_root_periodic R q
      have hsL' : s' + 1 = L := by
        by_contra hc
        have hlt : s' + 1 < L := by omega
        exact rc_path_point_notMem R p (by omega) hperL
      have hroot_eq : rc_root R q = rc_root R p := by
        have e4 : R^[L] q = R^[L] p := by
          rw [eL, hsL']
        rw [hLq] at e4
        rw [hrL] at e4
        exact e4
      exact hq_root hroot_eq
    · rw [hag] at heqZ
      have hperS : R^[t] (rc_root R p) ∈ Function.periodicPts R :=
        rc_periodic_iterate R hrper t
      rw [heqZ] at hperS
      exact hnper_q hperS
  have hrper' : rc_root R p ∈
      Function.periodicPts (Function.update R x p) := by
    refine Function.mem_periodicPts.mpr ⟨L + j + 1, by omega, ?_⟩
    change (Function.update R x p)^[L + j + 1] (rc_root R p) = rc_root R p
    have e1 : (Function.update R x p)^[L + j + 1] (rc_root R p) =
        (Function.update R x p)^[L] ((Function.update R x p)^[j + 1]
          (rc_root R p)) := by
      have hdec : L + j + 1 = L + (j + 1) := by omega
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    have e2 : (Function.update R x p)^[j + 1] (rc_root R p) = p :=
      rc_R'_to_p R _ j hjm x p hxj
    have e3 : (Function.update R x p)^[L] p = rc_root R p := by
      rw [rc_R'_agree_tree R p L hp x hxper L le_rfl, hrL]
    rw [e1, e2, e3]
  have hsper : (Function.update R x p)^[s] (rc_root R p) ∈
      Function.periodicPts (Function.update R x p) :=
    rc_periodic_iterate _ hrper' s
  have eag : (Function.update R x p)^[s] (rc_root R p) = R^[s] (rc_root R p) :=
    rc_R'_agree_cycle R _ j hjm x p hxj s hsj
  have hLper : (Function.update R x p)^[L] q ∈
      Function.periodicPts (Function.update R x p) := by
    rw [hagree_q L le_rfl, hLq, ← hsq, ← eag]
    exact hsper
  apply le_antisymm
  · exact rc_level_le_of_mem _ _ hLper
  · by_contra hc
    have hle : rc_level (Function.update R x p) q ≤ L - 1 := by omega
    have hper := rc_iterate_ge_level_periodic _ _ hle
    rw [hag] at hper
    exact hnper'_q hper

private theorem rc_caseC2_gt_false {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (q : V) (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (j : ℕ) (hjm : j < Function.minimalPeriod R (rc_root R p))
    (x : V) (hx : rc_adj delta x p) (hxj : R^[j] (rc_root R p) = x)
    (hxper : x ∈ Function.periodicPts R)
    (hC2 : Function.minimalPeriod R (rc_root R p) < L + j + 1) :
    False := by
  classical
  have hR'ssg : rc_isSSG delta (Function.update R x p) :=
    rc_ssg_update_edge delta R hR x p hx
  have hperT : ∀ s : ℕ, s < L →
      R^[s] p ∈ Function.periodicPts (Function.update R x p) :=
    fun s hs => rc_caseC2_tree_per R p L hp j hjm x hxj hxper s hs
  have hperS : ∀ t : ℕ, t ≤ j →
      R^[t] (rc_root R p) ∈ Function.periodicPts (Function.update R x p) :=
    fun t ht => rc_caseC2_seg_per R p L hp j hjm x hxj hxper t ht
  have hcyc : rc_cyc R < rc_cyc (Function.update R x p) :=
    rc_caseC2_cyc R L p hp j hjm x hxj hperT hperS hC2
  have hght : L ≤ rc_height (Function.update R x p) := by
    by_cases hC : rc_root R q ∈ rc_cycleFin R (rc_root R p)
    · obtain ⟨s, hsm, hs⟩ := (rc_cycleFin_mem R _ _).mp hC
      by_cases hsj : s ≤ j
      · have h1 := rc_level_le_height (Function.update R x p) q
        have hlev := rc_caseC2_oncycle_le R p L hp hH j hjm x hxj hxper q
          hq_top hq_root s hsj hs
        omega
      · have hgt' : j < s := by omega
        have hfalse := rc_caseC2_oncycle_gt delta R hR hHmax L hL hH p hp q
          hq_top j hjm x hx hxj hxper s hsm hs hgt'
        exact False.elim hfalse
    · have h1 := rc_level_le_height (Function.update R x p) q
      have hlev := rc_caseC2_offcycle R L p q hq_top j hjm x hxj hxper hC
      omega
  by_cases hgt : L < rc_height (Function.update R x p)
  · have hle := hHmax _ hR'ssg
    omega
  · have heqH : rc_height (Function.update R x p) = rc_height R := by omega
    have hle := hCmax _ hR'ssg heqH
    omega

private theorem rc_inedge_lemma {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V) (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (hngR : ¬ rc_good R)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (x : V) (hx : rc_adj delta x p) :
    x ∈ Function.periodicPts R ∧ R^[L + 1] x = rc_root R p := by
  classical
  have hH' : 1 ≤ rc_height R := by omega
  obtain ⟨q, hq_top, hq_root⟩ := rc_exists_other_top R hH' hngR p
  have hq_topL : rc_level R q = L := by omega
  by_cases horb : ∃ i : ℕ, R^[i] p = x
  · obtain ⟨i, hi⟩ := horb
    by_cases hiL : i < L
    · exfalso
      exact rc_caseB_tree delta R hR hHmax hCmax L hL hH p hp q hq_topL
        hq_root x hx i hi hiL
    · obtain ⟨j, hjm, hxj, hxper⟩ :=
        rc_caseC_setup R p L hp x i hi (by omega)
      rcases lt_trichotomy (L + j + 1)
          (Function.minimalPeriod R (rc_root R p)) with hlt | heq | hgt
      · exfalso
        exact rc_caseC1 delta R hR hHmax L hL hH p hp j hjm x hx hxj hxper hlt
      · refine ⟨hxper, ?_⟩
        have hper_m : R^[Function.minimalPeriod R (rc_root R p)]
            (rc_root R p) = rc_root R p :=
          Function.iterate_minimalPeriod
        have e : R^[L + 1] x = R^[L + 1 + j] (rc_root R p) := by
          rw [← hxj]
          have hdec : L + 1 + j = (L + 1) + j := by omega
          rw [hdec]
          exact (Function.iterate_add_apply R (L + 1) j _).symm
        have heq2 : L + 1 + j = Function.minimalPeriod R (rc_root R p) := by
          omega
        rw [e, heq2, hper_m]
      · exfalso
        exact rc_caseC2_gt_false delta R hR hHmax hCmax L hL hH p hp q
          hq_topL hq_root j hjm x hx hxj hxper hgt
  · exfalso
    have havoid : ∀ i : ℕ, R^[i] p ≠ x := fun i hi => horb ⟨i, hi⟩
    exact rc_caseA_offorbit delta R hR hHmax L hL hH p hp x hx havoid

private theorem rc_bunch_of_lexmax {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V)
    (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (hnone : ∀ g : V → V, rc_isSSG delta g → ¬ rc_good g)
    (hcon : rc_strongly delta) (hcard : 1 < Fintype.card V)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (b : V) (hb : R^[L - 1] p = b) :
    ∀ a : Fin k, delta b a = rc_root R p := by
  classical
  have hH' : 1 ≤ rc_height R := by omega
  have hbnp : b ∉ Function.periodicPts R := by
    rw [← hb]
    exact rc_path_point_notMem R p (by omega)
  have hrootb : rc_root R b = rc_root R p := by
    rw [← hb]
    exact rc_root_along_orbit R p (by omega)
  obtain ⟨q, hq_top, hq_root⟩ := rc_exists_other_top R hH' (hnone R hR) p
  have hq_topL : rc_level R q = L := by omega
  intro a
  by_contra hne
  set v : V := delta b a with hvdef
  have hadj : rc_adj delta b v := ⟨a, hvdef.symm⟩
  have hR'ssg : rc_isSSG delta (Function.update R b v) :=
    rc_ssg_update_edge delta R hR b v hadj
  have hRb' : Function.update R b v b = v := Function.update_self _ _ _
  have hsub : ∀ z : V, z ∈ Function.periodicPts R →
      z ∈ Function.periodicPts (Function.update R b v) := by
    intro z hz
    refine rc_update_periodic R b v z ?_ hz
    intro t heq
    have h1 := rc_periodic_iterate R hz t
    rw [heq] at h1
    exact hbnp h1
  by_cases horb : ∃ i : ℕ, R^[i] v = b
  · obtain ⟨i, hi, hmin⟩ :
      ∃ i : ℕ, R^[i] v = b ∧ ∀ t : ℕ, t < i → R^[t] v ≠ b := by
      refine ⟨Nat.find (p := fun i => R^[i] v = b) horb,
        Nat.find_spec (p := fun i => R^[i] v = b) horb,
        fun t ht => Nat.find_min (p := fun i => R^[i] v = b) horb ht⟩
    have hRi : (Function.update R b v)^[i] v = b := by
      have e := rc_update_agree_upto R b v v i (fun s hs => hmin s hs) i le_rfl
      rw [e]
      exact hi
    have hstep : (Function.update R b v)^[i + 1] v = v := by
      have e : (Function.update R b v)^[i + 1] v =
          Function.update R b v ((Function.update R b v)^[i] v) := by
        rw [show i + 1 = i.succ from rfl]
        exact Function.iterate_succ_apply' _ i v
      rw [e, hRi, hRb']
    have hvper' : v ∈ Function.periodicPts (Function.update R b v) :=
      Function.mem_periodicPts.mpr ⟨i + 1, by omega, hstep⟩
    have hbper' : b ∈ Function.periodicPts (Function.update R b v) := by
      have e1 : (Function.update R b v)^[i + 1] b =
          (Function.update R b v)^[i + 1] ((Function.update R b v)^[i] v) :=
        congrArg _ hRi.symm
      have f1 : (Function.update R b v)^[(i + 1) + i] v =
          (Function.update R b v)^[i + 1] ((Function.update R b v)^[i] v) :=
        Function.iterate_add_apply _ _ _ _
      have f2 : (Function.update R b v)^[i + (i + 1)] v =
          (Function.update R b v)^[i] ((Function.update R b v)^[i + 1] v) :=
        Function.iterate_add_apply _ _ _ _
      have e2 : (Function.update R b v)^[i + 1]
          ((Function.update R b v)^[i] v) =
          (Function.update R b v)^[i] ((Function.update R b v)^[i + 1] v) := by
        have hdec : (i + 1) + i = i + (i + 1) := by omega
        rw [← f1, hdec]
        exact f2
      have hmem : (Function.update R b v)^[i + 1] b = b := by
        rw [e1, e2, hstep, hRi]
      exact Function.mem_periodicPts.mpr ⟨i + 1, by omega, hmem⟩
    have hneq : rc_root R q ≠ rc_root R b := by
      rw [hrootb]
      exact hq_root
    have havoid_q : ∀ t : ℕ, R^[t] q ≠ b := by
      intro t
      exact rc_orbit_avoid_of_root_ne R q b hbnp hneq t
    have hlevq : rc_level (Function.update R b v) q = L := by
      rw [rc_update_level_eq R b v q havoid_q]
      exact hq_topL
    have hght : L ≤ rc_height (Function.update R b v) := by
      have h1 := rc_level_le_height (Function.update R b v) q
      omega
    have hcyc : rc_cyc R < rc_cyc (Function.update R b v) :=
      rc_cyc_gt_of_subset_ne R _ hsub b hbper' hbnp
    by_cases hgt : L < rc_height (Function.update R b v)
    · have hle := hHmax _ hR'ssg
      omega
    · have heqH : rc_height (Function.update R b v) = rc_height R := by omega
      have hle := hCmax _ hR'ssg heqH
      omega
  · have havoid : ∀ i : ℕ, R^[i] v ≠ b := fun i hi => horb ⟨i, hi⟩
    have hagree_v : ∀ s : ℕ, (Function.update R b v)^[s] v = R^[s] v :=
      fun s => rc_update_iterate_agree R b v v havoid s
    have hagree_p : ∀ s : ℕ, s ≤ L - 1 →
        (Function.update R b v)^[s] p = R^[s] p := by
      apply rc_update_agree_upto R b v p (L - 1) _
      intro s hs heq
      rw [← hb] at heq
      exact rc_path_ne_of_lt R p L hp (by omega) (by omega) (by omega) heq
    have hLm1 : (Function.update R b v)^[L - 1] p = b := by
      rw [hagree_p (L - 1) le_rfl]
      exact hb
    have hLp : (Function.update R b v)^[L] p = v := by
      have hdec : L = (L - 1) + 1 := by omega
      have e : (Function.update R b v)^[L] p =
          Function.update R b v ((Function.update R b v)^[L - 1] p) := by
        conv_lhs => rw [hdec]
        rw [show (L - 1) + 1 = ((L - 1)).succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      rw [e, hLm1, hRb']
    by_cases hvper : v ∈ Function.periodicPts R
    · have hbper'_no : b ∉ Function.periodicPts (Function.update R b v) := by
        intro hmem
        obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hmem
        have hNb : (Function.update R b v)^[N] b = R^[N - 1] v := by
          have hdec : N = (N - 1) + 1 := by omega
          have e : (Function.update R b v)^[N] b =
              (Function.update R b v)^[N - 1] ((Function.update R b v) b) := by
            conv_lhs => rw [hdec]
            rw [Function.iterate_add_apply, rc_update_iterate_one]
          rw [e, hRb']
          exact hagree_v (N - 1)
        have hperNv : R^[N - 1] v ∈ Function.periodicPts R :=
          rc_periodic_iterate R hvper (N - 1)
        have hNb_eq : (Function.update R b v)^[N] b = b := hN
        rw [← hNb] at hperNv
        rw [hNb_eq] at hperNv
        exact hbnp hperNv
      have hvper' : v ∈ Function.periodicPts (Function.update R b v) :=
        rc_update_periodic R b v v havoid hvper
      have hlevp : rc_level (Function.update R b v) p = L := by
        apply le_antisymm
        · exact rc_level_le_of_mem _ _ (by rwa [hLp])
        · by_contra hc
          have hle : rc_level (Function.update R b v) p ≤ L - 1 := by omega
          have hper := rc_iterate_ge_level_periodic _ _ hle
          rw [hLm1] at hper
          exact hbper'_no hper
      have hrootp' : rc_root (Function.update R b v) p = v := by
        unfold rc_root
        rw [hlevp]
        exact hLp
      have hcyc_le : rc_cyc R ≤ rc_cyc (Function.update R b v) := by
        unfold rc_cyc
        apply Finset.card_le_card
        intro z hz
        have hzP : z ∈ Function.periodicPts R := (Finset.mem_filter.mp hz).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hzP⟩
      have hght : L ≤ rc_height (Function.update R b v) := by
        have h1 := rc_level_le_height (Function.update R b v) p
        omega
      by_cases hgt2 : L < rc_height (Function.update R b v)
      · have hle := hHmax _ hR'ssg
        omega
      · have heqH : rc_height (Function.update R b v) = L := by omega
        have hHmax' : ∀ g : V → V, rc_isSSG delta g →
            rc_height g ≤ rc_height (Function.update R b v) := by
          intro g hg
          have hle := hHmax g hg
          omega
        have hCmax' : ∀ g : V → V, rc_isSSG delta g →
            rc_height g = rc_height (Function.update R b v) →
            rc_cyc g ≤ rc_cyc (Function.update R b v) := by
          intro g hg heq
          have h1 : rc_height g = rc_height R := by omega
          have h2 := hCmax g hg h1
          omega
        have hngR' : ¬ rc_good (Function.update R b v) :=
          hnone _ hR'ssg
        obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hcard p
        have hedge : ∃ x, rc_adj delta x p := by
          have hpath := hcon w p
          induction hpath with
          | refl => exact absurd rfl hw
          | tail _ hab _ => exact ⟨_, hab⟩
        obtain ⟨xx, hxx⟩ := hedge
        obtain ⟨hxper, hBx⟩ := rc_inedge_lemma delta R hR hHmax hCmax
          (hnone R hR) L hL hH p hp xx hxx
        obtain ⟨-, hBx'⟩ := rc_inedge_lemma delta _ hR'ssg hHmax' hCmax'
          hngR' L heqH hH p hlevp xx hxx
        have hag : (Function.update R b v)^[L + 1] xx = R^[L + 1] xx := by
          apply rc_update_iterate_agree R b v xx _
          intro t heq
          have h1 := rc_periodic_iterate R hxper t
          rw [heq] at h1
          exact hbnp h1
        rw [hrootp'] at hBx'
        rw [hag, hBx] at hBx'
        have hvv : v = rc_root R p := hBx'.symm
        rw [hvdef] at hne
        exact hne hvv
    · have hnper' : (Function.update R b v)^[L] p ∉
          Function.periodicPts (Function.update R b v) := by
        intro hmem
        rw [hLp] at hmem
        exact hvper (rc_update_periodic_of R b v v hagree_v hmem)
      have hgt : L < rc_height (Function.update R b v) :=
        rc_height_gt_of_iterate_notMem _ p L hnper'
      have hle := hHmax _ hR'ssg
      omega

private theorem rc_injOn_periodicPts {V : Type*} (f : V → V) :
    Set.InjOn f ↑(Function.periodicPts f) := by
  intro a ha b hb hab
  obtain ⟨Na, hNa, hNaP⟩ := Function.mem_periodicPts.mp ha
  obtain ⟨Nb, hNb, hNbP⟩ := Function.mem_periodicPts.mp hb
  have hM : f^[Na * Nb] a = a := hNaP.mul_const Nb
  have hM2 : f^[Na * Nb] b = b := by
    have h := hNbP.mul_const Na
    rwa [Nat.mul_comm] at h
  have hNpos : 0 < Na * Nb := Nat.mul_pos hNa hNb
  have e1 : f^[Na * Nb] a = f^[Na * Nb - 1] (f a) := by
    have hdec : Na * Nb = (Na * Nb - 1) + 1 := by omega
    conv_lhs => rw [hdec]
    exact Function.iterate_succ_apply f (Na * Nb - 1) a
  have e2 : f^[Na * Nb] b = f^[Na * Nb - 1] (f b) := by
    have hdec : Na * Nb = (Na * Nb - 1) + 1 := by omega
    conv_lhs => rw [hdec]
    exact Function.iterate_succ_apply f (Na * Nb - 1) b
  rw [hab] at e1
  rw [← e2, hM, hM2] at e1
  exact e1

private theorem rc_on_cycle_of_hit {V : Type*} [Finite V]
    (R : V → V) (r : V) (hrper : r ∈ Function.periodicPts R)
    (m : ℕ) (hm : m = Function.minimalPeriod R r)
    (c : V) (hc : R^[m - 1] r = c)
    (z : V) (hz : z ∈ Function.periodicPts R) (i : ℕ) (hi : R^[i] z = c) :
    ∃ t : ℕ, t < m ∧ R^[t] r = z := by
  obtain ⟨N, hNpos, hN⟩ := Function.mem_periodicPts.mp hz
  have hNz : R^[N] z = z := hN
  have hNN : ∀ k : ℕ, R^[N * k] z = z := fun k => hN.mul_const k
  have hi' : R^[i % N] z = c := by
    have e : R^[i] z = R^[i % N] z := by
      have hdec : i % N + N * (i / N) = i := Nat.mod_add_div i N
      conv_lhs => rw [← hdec]
      rw [Function.iterate_add_apply]
      exact congrArg (R^[i % N] ·) (hNN (i / N))
    rw [← e]
    exact hi
  have hz2 : z = R^[N - i % N] c := by
    have hdec : N = (N - i % N) + i % N := by
      have hlt : i % N < N := Nat.mod_lt _ hNpos
      omega
    have e : R^[N] z = R^[N - i % N] (R^[i % N] z) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply R (N - i % N) (i % N) z
    rw [hNz, hi'] at e
    exact e
  have e2 : R^[N - i % N] c = R^[N - i % N + (m - 1)] r := by
    rw [← hc]
    exact (Function.iterate_add_apply R (N - i % N) (m - 1) r).symm
  rw [e2] at hz2
  have hmpos : 0 < m := by
    rw [hm]
    exact Function.minimalPeriod_pos_of_mem_periodicPts hrper
  refine ⟨(N - i % N + (m - 1)) % m, Nat.mod_lt _ hmpos, ?_⟩
  have hm' : (N - i % N + (m - 1)) % m =
      (N - i % N + (m - 1)) % Function.minimalPeriod R r := by
    rw [← hm]
  have e3 := Function.iterate_mod_minimalPeriod_eq (f := R) (x := r)
    (n := N - i % N + (m - 1))
  rw [hm', e3]
  exact hz2.symm

private theorem rc_B3_Rc {V : Type*} (R : V → V) (r : V)
    (hrper : r ∈ Function.periodicPts R)
    (m : ℕ) (hm : m = Function.minimalPeriod R r)
    (c : V) (hc : R^[m - 1] r = c) :
    R c = r := by
  have hmpos : 0 < m := by
    rw [hm]
    exact Function.minimalPeriod_pos_of_mem_periodicPts hrper
  have hper_m : R^[m] r = r := by
    rw [hm]
    exact Function.iterate_minimalPeriod
  have hdec : m = (m - 1) + 1 := by omega
  have e2 : R^[m] r = R (R^[m - 1] r) := by
    conv_lhs => rw [hdec]
    exact Function.iterate_succ_apply' R (m - 1) r
  rw [hper_m] at e2
  rw [hc] at e2
  exact e2.symm

private theorem rc_B3_Psub {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (r : V) (hrper : r ∈ Function.periodicPts R)
    (m : ℕ) (hm : m = Function.minimalPeriod R r)
    (c u : V) (hc : R^[m - 1] r = c)
    (hrper' : r ∈ Function.periodicPts (Function.update R c u)) :
    ∀ z : V, z ∈ Function.periodicPts R →
      z ∈ Function.periodicPts (Function.update R c u) := by
  classical
  intro z hz
  by_cases hit : ∃ i : ℕ, R^[i] z = c
  · obtain ⟨i, hi⟩ := hit
    obtain ⟨t, htm, htz⟩ :=
      rc_on_cycle_of_hit R r hrper m hm c hc z hz i hi
    have hmpos : 0 < m := by
      rw [hm]
      exact Function.minimalPeriod_pos_of_mem_periodicPts hrper
    have eag : (Function.update R c u)^[t] r = R^[t] r :=
      rc_R'_agree_cycle R r (m - 1) (by omega) c u hc t (by omega)
    have hper := rc_periodic_iterate _ hrper' t
    rw [eag, htz] at hper
    exact hper
  · have havoid : ∀ i : ℕ, R^[i] z ≠ c := fun i hi => hit ⟨i, hi⟩
    exact rc_update_periodic R c u z havoid hz

private theorem rc_B3_cyc_strict {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (c u r : V)
    (hRc : R c = r) (hcP : c ∈ Function.periodicPts R)
    (hu : u ≠ r)
    (hsub : ∀ z : V, z ∈ Function.periodicPts R →
      z ∈ Function.periodicPts (Function.update R c u))
    (heq : Function.periodicPts (Function.update R c u) =
      Function.periodicPts R) :
    False := by
  classical
  have hR'c : Function.update R c u c = u := Function.update_self _ _ _
  have hmapR' : ∀ z ∈ Function.periodicPts R,
      Function.update R c u z ∈ Function.periodicPts R := by
    intro z hz
    have h := rc_periodic_map (Function.update R c u) (hsub z hz)
    rwa [heq] at h
  have hinjR : Set.InjOn R ↑(Function.periodicPts R) :=
    rc_injOn_periodicPts R
  have hinjR' : Set.InjOn (Function.update R c u) ↑(Function.periodicPts R) := by
    have h := rc_injOn_periodicPts (Function.update R c u)
    rwa [heq] at h
  have hsig_inj : Function.Injective
      (fun z : ↥(Function.periodicPts R) =>
        (⟨Function.update R c u z.val, hmapR' z.val z.property⟩ :
          ↥(Function.periodicPts R))) := by
    intro a b hab
    have e : Function.update R c u a.val = Function.update R c u b.val :=
      congrArg Subtype.val hab
    have h := hinjR' a.property b.property e
    exact Subtype.ext h
  have hsig_surj := Finite.injective_iff_surjective.mp hsig_inj
  have htau_c : R c ∈ Function.periodicPts R :=
    rc_periodic_map R hcP
  obtain ⟨z, hz⟩ := hsig_surj ⟨R c, htau_c⟩
  have hzz : Function.update R c u z.val = R c := congrArg Subtype.val hz
  by_cases hzc : z.val = c
  · rw [hzc, hR'c, hRc] at hzz
    exact hu hzz
  · have hag : Function.update R c u z.val = R z.val :=
      Function.update_of_ne hzc _ _
    rw [hag] at hzz
    have hzz2 : z.val = c := hinjR z.property hcP hzz
    exact hzc hzz2

private theorem rc_B3_reduce {V : Type*} [Finite V] [DecidableEq V]
    (R : V → V) (r : V) (hrper : r ∈ Function.periodicPts R)
    (m : ℕ) (hm : m = Function.minimalPeriod R r) (hmpos : 0 < m)
    (c u : V) (hc : R^[m - 1] r = c) (hcP : c ∈ Function.periodicPts R)
    (hrper' : r ∈ Function.periodicPts (Function.update R c u))
    (w : V) (hw_np : w ∉ Function.periodicPts R)
    (hw_orb : ∃ t : ℕ, (Function.update R c u)^[t] r = w) :
    ∃ s : ℕ, R^[s] u = w := by
  classical
  obtain ⟨t, ht⟩ := hw_orb
  obtain ⟨N', hN'pos, hN'⟩ := Function.mem_periodicPts.mp hrper'
  have hpow : ∀ k : ℕ, (Function.update R c u)^[N' * k] r = r := fun k =>
    hN'.mul_const k
  have hmod : (Function.update R c u)^[t % N'] r = w := by
    have hdec : t = N' * (t / N') + t % N' := by
      have := Nat.mod_add_div t N'
      omega
    have e : (Function.update R c u)^[t] r =
        (Function.update R c u)^[N' * (t / N')]
          ((Function.update R c u)^[t % N'] r) := by
      conv_lhs => rw [hdec]
      exact Function.iterate_add_apply _ _ _ _
    have e2 : (Function.update R c u)^[N' * (t / N')]
        ((Function.update R c u)^[t % N'] r) =
        (Function.update R c u)^[t % N'] r := by
      have f1 := Function.iterate_add_apply (Function.update R c u)
        (N' * (t / N')) (t % N') r
      have f2 := Function.iterate_add_apply (Function.update R c u)
        (t % N') (N' * (t / N')) r
      rw [Nat.add_comm (t % N') (N' * (t / N'))] at f2
      rw [f1] at f2
      rw [hpow (t / N')] at f2
      exact f2
    rw [e2] at e
    rw [← e]
    exact ht
  have hge : m ≤ t % N' := by
    by_contra hcon
    have hlt : t % N' < m := by omega
    have eag := rc_R'_agree_cycle R r (m - 1) (by omega) c u hc (t % N')
      (by omega)
    rw [hmod] at eag
    have hper : R^[t % N'] r ∈ Function.periodicPts R :=
      rc_periodic_iterate R hrper _
    rw [← eag] at hper
    exact hw_np hper
  have hmc : (Function.update R c u)^[m - 1] r = c := by
    have eag := rc_R'_agree_cycle R r (m - 1) (by omega) c u hc (m - 1) le_rfl
    rwa [hc] at eag
  have hmR' : (Function.update R c u)^[m] r = u := by
    have hdec : m = (m - 1) + 1 := by omega
    have e : (Function.update R c u)^[m] r =
        Function.update R c u ((Function.update R c u)^[m - 1] r) := by
      conv_lhs => rw [hdec]
      rw [show (m - 1) + 1 = ((m - 1)).succ from rfl]
      exact Function.iterate_succ_apply' _ _ _
    rw [e, hmc]
    exact Function.update_self _ _ _
  have hex : ∃ s : ℕ, (Function.update R c u)^[s] u = w :=
    ⟨t % N' - m, by
      have hdec : t % N' = (t % N' - m) + m := by omega
      have e : (Function.update R c u)^[t % N'] r =
          (Function.update R c u)^[t % N' - m]
            ((Function.update R c u)^[m] r) := by
        conv_lhs => rw [hdec]
        exact Function.iterate_add_apply _ _ _ _
      rw [hmR'] at e
      exact e.symm.trans hmod⟩
  obtain ⟨s, hs, hmins⟩ :
      ∃ s : ℕ, (Function.update R c u)^[s] u = w ∧
        ∀ t' : ℕ, t' < s → (Function.update R c u)^[t'] u ≠ w := by
    refine ⟨Nat.find (p := fun s => (Function.update R c u)^[s] u = w) hex,
      Nat.find_spec (p := fun s => (Function.update R c u)^[s] u = w) hex,
      fun t' ht' =>
        Nat.find_min (p := fun s => (Function.update R c u)^[s] u = w) hex
          ht'⟩
  have hseg : ∀ i' : ℕ, i' ≤ s → (Function.update R c u)^[i'] u ≠ c := by
    intro i' hi' hcon
    have hlt : i' < s := by
      by_contra hc
      have heq : i' = s := by omega
      rw [heq, hs] at hcon
      have hcR : w ∈ Function.periodicPts R := by
        rw [hcon]
        exact hcP
      exact hw_np hcR
    have hback : (Function.update R c u)^[s - i' - 1] u = w := by
      have e1 : (Function.update R c u)^[s] u =
          (Function.update R c u)^[s - i' - 1]
            ((Function.update R c u)^[i' + 1] u) := by
        have hdec : s = (s - i' - 1) + (i' + 1) := by omega
        conv_lhs => rw [hdec]
        exact Function.iterate_add_apply _ _ _ _
      have e2 : (Function.update R c u)^[i' + 1] u = u := by
        have e : (Function.update R c u)^[i' + 1] u =
            Function.update R c u ((Function.update R c u)^[i'] u) := by
          rw [show i' + 1 = i'.succ from rfl]
          exact Function.iterate_succ_apply' _ _ _
        rw [e, hcon]
        exact Function.update_self _ _ _
      rw [e2] at e1
      rw [← e1]
      exact hs
    have hne := hmins (s - i' - 1) (by omega)
    exact hne hback
  have hagree : ∀ t' : ℕ, t' ≤ s →
      (Function.update R c u)^[t'] u = R^[t'] u := by
    intro t'
    induction t' with
    | zero => intro _; rfl
    | succ k ih =>
      intro ht'
      have hks : k ≤ s := by omega
      have ih' := ih hks
      have hne : R^[k] u ≠ c := by
        intro hcon
        have hcon' : (Function.update R c u)^[k] u = c := by
          rw [ih']
          exact hcon
        exact hseg k hks hcon'
      have e1 : (Function.update R c u)^[k + 1] u =
          Function.update R c u ((Function.update R c u)^[k] u) := by
        rw [show k + 1 = k.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      have e2 : R^[k + 1] u = R (R^[k] u) := by
        rw [show k + 1 = k.succ from rfl]
        exact Function.iterate_succ_apply' _ _ _
      rw [e1, e2, ih', Function.update_of_ne hne]
  rw [hagree s le_rfl] at hs
  exact ⟨s, hs⟩

private theorem rc_B3_height {V : Type*} [Fintype V] [DecidableEq V]
    (R : V → V) (p q : V) (L : ℕ) (hp : rc_level R p = L)
    (hq_top : rc_level R q = L) (hq_root : rc_root R q ≠ rc_root R p)
    (hH : 1 ≤ L)
    (r : V) (hr : rc_root R p = r) (hrper : r ∈ Function.periodicPts R)
    (m : ℕ) (hm : m = Function.minimalPeriod R r) (hmpos : 0 < m)
    (c u : V) (hc : R^[m - 1] r = c) (hcP : c ∈ Function.periodicPts R)
    (hrper' : r ∈ Function.periodicPts (Function.update R c u)) :
    L ≤ rc_height (Function.update R c u) := by
  classical
  have hLp : R^[L] p = r := by
    have h : rc_root R p = R^[L] p := by
      unfold rc_root
      rw [hp]
    rw [hr] at h
    exact h.symm
  have hLq : R^[L] q = rc_root R q := by
    unfold rc_root
    rw [hq_top]
  have hbnp : R^[L - 1] p ∉ Function.periodicPts R :=
    rc_path_point_notMem R p (by omega)
  have hzq_np : R^[L - 1] q ∉ Function.periodicPts R :=
    rc_path_point_notMem R q (by omega)
  have hag_p : (Function.update R c u)^[L - 1] p = R^[L - 1] p :=
    rc_update_agree_upto R c u p (L - 1) (by
      intro s hs heq
      have hnp : R^[s] p ∉ Function.periodicPts R :=
        rc_path_point_notMem R p (by omega)
      exact hnp (by rw [heq]; exact hcP)) (L - 1) le_rfl
  have hag_q : (Function.update R c u)^[L - 1] q = R^[L - 1] q :=
    rc_update_agree_upto R c u q (L - 1) (by
      intro s hs heq
      have hnp : R^[s] q ∉ Function.periodicPts R :=
        rc_path_point_notMem R q (by omega)
      exact hnp (by rw [heq]; exact hcP)) (L - 1) le_rfl
  by_cases hboth : (Function.update R c u)^[L - 1] p ∈
      Function.periodicPts (Function.update R c u) ∧
      (Function.update R c u)^[L - 1] q ∈
        Function.periodicPts (Function.update R c u)
  · exfalso
    obtain ⟨hbb, hqq⟩ := hboth
    rw [hag_p] at hbb
    rw [hag_q] at hqq
    have hA : rc_root R u = r := by
      have hRb : (Function.update R c u) (R^[L - 1] p) = r := by
        have hne : R^[L - 1] p ≠ c := by
          intro hcon
          have hmem : R^[L - 1] p ∈ Function.periodicPts R := by
            rw [hcon]
            exact hcP
          exact hbnp hmem
        have eR' : Function.update R c u (R^[L - 1] p) = R (R^[L - 1] p) :=
          Function.update_of_ne hne _ _
        have e2 : R (R^[L - 1] p) = R^[L] p := by
          have hdec : L = (L - 1) + 1 := by omega
          conv_rhs => rw [hdec]
          exact (Function.iterate_succ_apply' R (L - 1) p).symm
        rw [eR', e2, hLp]
      obtain ⟨Nb, hNbpos, hNb⟩ := Function.mem_periodicPts.mp hbb
      have hNb_eq : (Function.update R c u)^[Nb] (R^[L - 1] p) =
          R^[L - 1] p := hNb
      have e_orb : (Function.update R c u)^[Nb - 1] r = R^[L - 1] p := by
        have hdec : Nb = (Nb - 1) + 1 := by omega
        have e : (Function.update R c u)^[Nb] (R^[L - 1] p) =
            (Function.update R c u)^[Nb - 1]
              ((Function.update R c u) (R^[L - 1] p)) := by
          conv_lhs => rw [hdec]
          rw [Function.iterate_add_apply, rc_update_iterate_one]
        rw [hRb] at e
        rw [hNb_eq] at e
        exact e.symm
      obtain ⟨s, hs⟩ := rc_B3_reduce R r hrper m hm hmpos c u hc hcP
        hrper' _ hbnp ⟨Nb - 1, e_orb⟩
      have hsL : s ≤ rc_level R u := by
        by_contra hcon
        have hle : rc_level R u ≤ s := by omega
        have hper := rc_iterate_ge_level_periodic R u hle
        rw [hs] at hper
        exact hbnp hper
      have e2 := rc_root_along_orbit R u hsL
      rw [hs] at e2
      have hrb : rc_root R (R^[L - 1] p) = r := by
        have e3 := rc_root_along_orbit R p (by omega : L - 1 ≤ rc_level R p)
        rw [hr] at e3
        exact e3
      rw [hrb] at e2
      exact e2.symm
    have hB : rc_root R u = rc_root R q := by
      have hRzq : R (R^[L - 1] q) = rc_root R q := by
        have e2 : R (R^[L - 1] q) = R^[L] q := by
          have hdec : L = (L - 1) + 1 := by omega
          conv_rhs => rw [hdec]
          exact (Function.iterate_succ_apply' R (L - 1) q).symm
        rw [e2, hLq]
      have hR'zq : (Function.update R c u) (R^[L - 1] q) = rc_root R q := by
        have hne : R^[L - 1] q ≠ c := by
          intro hcon
          have hmem : R^[L - 1] q ∈ Function.periodicPts R := by
            rw [hcon]
            exact hcP
          exact hzq_np hmem
        have eR' : Function.update R c u (R^[L - 1] q) = R (R^[L - 1] q) :=
          Function.update_of_ne hne _ _
        rw [eR', hRzq]
      obtain ⟨Nq, hNqpos, hNq⟩ := Function.mem_periodicPts.mp hqq
      have hNq_eq : (Function.update R c u)^[Nq] (R^[L - 1] q) =
          R^[L - 1] q := hNq
      have hrootq_per' : rc_root R q ∈
          Function.periodicPts (Function.update R c u) := by
        have hmem : (Function.update R c u)^[Nq] (rc_root R q) =
            rc_root R q := by
          have f1 := Function.iterate_add_apply (Function.update R c u)
            Nq 1 (R^[L - 1] q)
          have f2 := Function.iterate_add_apply (Function.update R c u)
            1 Nq (R^[L - 1] q)
          rw [Nat.add_comm 1 Nq] at f2
          rw [rc_update_iterate_one] at f1 f2
          rw [hR'zq] at f1
          rw [hNq_eq] at f2
          rw [hR'zq] at f2
          rw [f1] at f2
          exact f2
        exact Function.mem_periodicPts.mpr ⟨Nq, hNqpos, hmem⟩
      by_cases hhit : ∃ i : ℕ, R^[i] (R^[L - 1] q) = c
      · obtain ⟨iq, hiq, hminq⟩ :
          ∃ iq : ℕ, R^[iq] (R^[L - 1] q) = c ∧
            ∀ t' : ℕ, t' < iq → R^[t'] (R^[L - 1] q) ≠ c := by
          have hex : ∃ iq : ℕ, R^[iq] (R^[L - 1] q) = c := hhit
          refine ⟨Nat.find (p := fun iq => R^[iq] (R^[L - 1] q) = c) hex,
            Nat.find_spec (p := fun iq => R^[iq] (R^[L - 1] q) = c) hex,
            fun t' ht' =>
              Nat.find_min (p := fun iq => R^[iq] (R^[L - 1] q) = c) hex
                ht'⟩
        have hiqR' : (Function.update R c u)^[iq] (R^[L - 1] q) = c := by
          have eag := rc_update_agree_upto R c u (R^[L - 1] q) iq
            (fun s hs => hminq s hs) iq le_rfl
          rwa [eag]
        have hiqmod : (Function.update R c u)^[iq % Nq] (R^[L - 1] q) = c := by
          have hdec : iq = Nq * (iq / Nq) + iq % Nq := by
            have := Nat.mod_add_div iq Nq
            omega
          have e : (Function.update R c u)^[iq] (R^[L - 1] q) =
              (Function.update R c u)^[Nq * (iq / Nq)]
                ((Function.update R c u)^[iq % Nq] (R^[L - 1] q)) := by
            conv_lhs => rw [hdec]
            exact Function.iterate_add_apply _ _ _ _
          have hpow : (Function.update R c u)^[Nq * (iq / Nq)]
              (R^[L - 1] q) = R^[L - 1] q :=
            hNq.mul_const (iq / Nq)
          have e2 : (Function.update R c u)^[Nq * (iq / Nq)]
              ((Function.update R c u)^[iq % Nq] (R^[L - 1] q)) =
              (Function.update R c u)^[iq % Nq] (R^[L - 1] q) := by
            have f1 := Function.iterate_add_apply (Function.update R c u)
              (Nq * (iq / Nq)) (iq % Nq) (R^[L - 1] q)
            have f2 := Function.iterate_add_apply (Function.update R c u)
              (iq % Nq) (Nq * (iq / Nq)) (R^[L - 1] q)
            rw [Nat.add_comm (iq % Nq) (Nq * (iq / Nq))] at f2
            rw [f1] at f2
            rw [hpow] at f2
            exact f2
          rw [e2] at e
          rw [hiqR'] at e
          exact e.symm
        have hzc : (Function.update R c u)^[Nq - iq % Nq] c =
            R^[L - 1] q := by
          have hdec : Nq = (Nq - iq % Nq) + iq % Nq := by
            have hlt : iq % Nq < Nq := Nat.mod_lt _ hNqpos
            omega
          have e : (Function.update R c u)^[Nq] (R^[L - 1] q) =
              (Function.update R c u)^[Nq - iq % Nq]
                ((Function.update R c u)^[iq % Nq] (R^[L - 1] q)) := by
            conv_lhs => rw [hdec]
            exact Function.iterate_add_apply _ _ _ _
          rw [hiqmod] at e
          rw [hNq_eq] at e
          exact e.symm
        have hcr : (Function.update R c u)^[m - 1] r = c := by
          have eag := rc_R'_agree_cycle R r (m - 1) (by omega) c u hc
            (m - 1) le_rfl
          rwa [hc] at eag
        have hzr : (Function.update R c u)^[Nq - iq % Nq + (m - 1)] r =
            R^[L - 1] q := by
          have e : (Function.update R c u)^[Nq - iq % Nq + (m - 1)] r =
              (Function.update R c u)^[Nq - iq % Nq]
                ((Function.update R c u)^[m - 1] r) :=
            Function.iterate_add_apply _ _ _ _
          rw [e, hcr]
          exact hzc
        obtain ⟨s, hs⟩ := rc_B3_reduce R r hrper m hm hmpos c u hc hcP
          hrper' _ hzq_np ⟨Nq - iq % Nq + (m - 1), hzr⟩
        have hsL : s ≤ rc_level R u := by
          by_contra hcon
          have hle : rc_level R u ≤ s := by omega
          have hper := rc_iterate_ge_level_periodic R u hle
          rw [hs] at hper
          exact hzq_np hper
        have e2 := rc_root_along_orbit R u hsL
        rw [hs] at e2
        have hrb : rc_root R (R^[L - 1] q) = rc_root R q := by
          have e3 := rc_root_along_orbit R q (by omega : L - 1 ≤ rc_level R q)
          exact e3
        rw [hrb] at e2
        exact e2.symm
      · exfalso
        exact hzq_np (rc_update_periodic_of R c u _ (by
          intro j
          exact rc_update_iterate_agree R c u (R^[L - 1] q)
            (fun i hi => hhit ⟨i, hi⟩) j) hqq)
    have hcontra : rc_root R q = rc_root R p := by
      have e1 : rc_root R p = rc_root R u := hr.trans hA.symm
      exact (e1.trans hB).symm
    exact hq_root hcontra
  · have hnb : (Function.update R c u)^[L - 1] p ∉
        Function.periodicPts (Function.update R c u) ∨
        (Function.update R c u)^[L - 1] q ∉
          Function.periodicPts (Function.update R c u) := by
      by_contra hcon
      have h1 : (Function.update R c u)^[L - 1] p ∈
          Function.periodicPts (Function.update R c u) := by
        by_contra hcon1
        exact hcon (Or.inl hcon1)
      have h2 : (Function.update R c u)^[L - 1] q ∈
          Function.periodicPts (Function.update R c u) := by
        by_contra hcon2
        exact hcon (Or.inr hcon2)
      exact hboth ⟨h1, h2⟩
    rcases hnb with hn | hn
    · have hlev : L ≤ rc_level (Function.update R c u) p := by
        by_contra hcon
        have hle : rc_level (Function.update R c u) p ≤ L - 1 := by omega
        have hper := rc_iterate_ge_level_periodic _ _ hle
        exact hn hper
      exact le_trans hlev (rc_level_le_height _ _)
    · have hlev : L ≤ rc_level (Function.update R c u) q := by
        by_contra hcon
        have hle : rc_level (Function.update R c u) q ≤ L - 1 := by omega
        have hper := rc_iterate_ge_level_periodic _ _ hle
        exact hn hper
      exact le_trans hlev (rc_level_le_height _ _)

private theorem rc_B3_false {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V)
    (R : V → V) (hR : rc_isSSG delta R)
    (hHmax : ∀ g : V → V, rc_isSSG delta g → rc_height g ≤ rc_height R)
    (hCmax : ∀ g : V → V, rc_isSSG delta g → rc_height g = rc_height R →
      rc_cyc g ≤ rc_cyc R)
    (hnone : ∀ g : V → V, rc_isSSG delta g → ¬ rc_good g)
    (hcon : rc_strongly delta) (hcard : 1 < Fintype.card V)
    (L : ℕ) (hL : rc_height R = L) (hH : 1 ≤ L)
    (p : V) (hp : rc_level R p = L)
    (hno2 : ∀ z x y : V, rc_isBunch delta x z → rc_isBunch delta y z → x = y) :
    False := by
  classical
  have hH' : 1 ≤ rc_height R := by omega
  have hrper0 : rc_root R p ∈ Function.periodicPts R := rc_root_periodic R p
  set m : ℕ := Function.minimalPeriod R (rc_root R p) with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact Function.minimalPeriod_pos_of_mem_periodicPts hrper0
  set c : V := R^[m - 1] (rc_root R p) with hcdef
  have hcP : c ∈ Function.periodicPts R := by
    rw [hcdef]
    exact rc_periodic_iterate R hrper0 (m - 1)
  have hRc : R c = rc_root R p :=
    rc_B3_Rc R _ hrper0 m hmdef c hcdef.symm
  have hcb : c ≠ R^[L - 1] p := by
    intro hcon
    have hnp : R^[L - 1] p ∉ Function.periodicPts R :=
      rc_path_point_notMem R p (by omega)
    have hmem : R^[L - 1] p ∈ Function.periodicPts R := by
      rw [← hcon]
      exact hcP
    exact hnp hmem
  have hbunch : rc_isBunch delta (R^[L - 1] p) (rc_root R p) :=
    rc_bunch_of_lexmax delta R hR hHmax hCmax hnone hcon hcard
      L hL hH p hp _ rfl
  have hcbunch : ¬ rc_isBunch delta c (rc_root R p) := by
    intro hc2
    exact hcb (hno2 _ c _ hc2 hbunch)
  have hex : ∃ a : Fin k, delta c a ≠ rc_root R p := by
    by_contra hc2
    have hb : rc_isBunch delta c (rc_root R p) := by
      intro a
      by_contra ha
      exact hc2 ⟨a, ha⟩
    exact hcbunch hb
  obtain ⟨aa, haa⟩ := hex
  set u : V := delta c aa with hudef
  have hu : u ≠ rc_root R p := haa
  have hR'ssg : rc_isSSG delta (Function.update R c u) :=
    rc_ssg_update_edge delta R hR c u ⟨aa, hudef.symm⟩
  have hag_p : (Function.update R c u)^[L] p = rc_root R p := by
    have eag : (Function.update R c u)^[L] p = R^[L] p :=
      rc_update_agree_upto R c u p L (by
        intro s hs heq
        have hnp : R^[s] p ∉ Function.periodicPts R :=
          rc_path_point_notMem R p (by omega)
        exact hnp (by rw [heq]; exact hcP)) L le_rfl
    rw [eag]
    unfold rc_root
    rw [hp]
  by_cases hrper' : rc_root R p ∈
      Function.periodicPts (Function.update R c u)
  · have hsub : ∀ z : V, z ∈ Function.periodicPts R →
        z ∈ Function.periodicPts (Function.update R c u) :=
      rc_B3_Psub R _ hrper0 m hmdef c u hcdef.symm hrper'
    have hcyc : rc_cyc R < rc_cyc (Function.update R c u) := by
      by_cases heq : Function.periodicPts (Function.update R c u) =
          Function.periodicPts R
      · exfalso
        exact rc_B3_cyc_strict R c u _ hRc hcP hu hsub heq
      · have hss : Finset.univ.filter (fun v => v ∈ Function.periodicPts R) ⊂
            Finset.univ.filter (fun v =>
              v ∈ Function.periodicPts (Function.update R c u)) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro z hz
            have hzP : z ∈ Function.periodicPts R :=
              (Finset.mem_filter.mp hz).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hsub z hzP⟩
          · intro hcon
            apply heq
            have hcoe : (Finset.univ.filter (fun v =>
                v ∈ Function.periodicPts (Function.update R c u)) : Set V) =
                (Finset.univ.filter
                  (fun v => v ∈ Function.periodicPts R) : Set V) :=
              congrArg _ hcon.symm
            rw [Finset.coe_filter, Finset.coe_filter] at hcoe
            simpa using hcoe
        have hcardlt := Finset.card_lt_card hss
        unfold rc_cyc
        exact hcardlt
    obtain ⟨qq, hq_top, hq_root⟩ := rc_exists_other_top R hH' (hnone R hR) p
    have hq_topL : rc_level R qq = L := by omega
    have hght : L ≤ rc_height (Function.update R c u) :=
      rc_B3_height R p qq L hp hq_topL hq_root hH _ rfl hrper0 m hmdef
        hmpos c u hcdef.symm hcP hrper'
    by_cases hgt : L < rc_height (Function.update R c u)
    · have hle := hHmax _ hR'ssg
      omega
    · have heqH : rc_height (Function.update R c u) = rc_height R := by omega
      have hle := hCmax _ hR'ssg heqH
      omega
  · have hnper' : (Function.update R c u)^[L] p ∉
        Function.periodicPts (Function.update R c u) := by
      rwa [hag_p]
    have hgt : L < rc_height (Function.update R c u) :=
      rc_height_gt_of_iterate_notMem _ p L hnper'
    have hle := hHmax _ hR'ssg
    omega

private theorem rc_exists_good_ssg {V : Type*} [Fintype V] [DecidableEq V]
    {k : ℕ} (delta : V → Fin k → V)
    (hcon : rc_strongly delta) (haper : rc_aperiodic delta)
    (hcard : 1 < Fintype.card V)
    (hno2 : ∀ z x y : V, rc_isBunch delta x z → rc_isBunch delta y z → x = y) :
    ∃ g : V → V, (∀ v : V, rc_adj delta v (g v)) ∧ rc_good g := by
  classical
  have hpos : 0 < Fintype.card V := by omega
  have hneV : Nonempty V := Fintype.card_pos_iff.mp hpos
  have hk : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    obtain ⟨v₀⟩ := hneV
    obtain ⟨w₀, hne₀⟩ := Fintype.exists_ne_of_one_lt_card hcard v₀
    have hne : v₀ ≠ w₀ := Ne.symm hne₀
    have hempty : ∀ x y : V, ¬ rc_adj delta x y := by
      intro x y h
      obtain ⟨a, _⟩ := h
      exact Fin.elim0 (hk0' ▸ a)
    have heq : v₀ = w₀ := by
      have h := hcon v₀ w₀
      induction h with
      | refl => rfl
      | tail _ hab _ => exact (hempty _ _ hab).elim
    exact hne heq
  obtain ⟨a₀⟩ : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨R, hR, hHmax⟩ := rc_height_max_exists delta a₀
  obtain ⟨R', hR', hHR', hCmax⟩ :=
    rc_cyc_max_exists delta (rc_height R) R ⟨hR, rfl⟩
  have hHmax' : ∀ g : V → V, rc_isSSG delta g →
      rc_height g ≤ rc_height R' := by
    intro g hg
    have hle := hHmax g hg
    omega
  have hCmax' : ∀ g : V → V, rc_isSSG delta g →
      rc_height g = rc_height R' → rc_cyc g ≤ rc_cyc R' := by
    intro g hg heq
    have heq2 : rc_height g = rc_height R := by omega
    exact hCmax g hg heq2
  have hH : 1 ≤ rc_height R' :=
    rc_lexmax_height_pos delta a₀ hcon haper hcard R' hHmax'
  obtain ⟨p, hp⟩ := @rc_height_attained V _ _ hneV R'
  by_contra hnone
  have hnone' : ∀ g : V → V, rc_isSSG delta g → ¬ rc_good g := by
    intro g hg hgg
    exact hnone ⟨g, hg, hgg⟩
  exact rc_B3_false delta R' hR' hHmax' hCmax' hnone' hcon hcard
    (rc_height R') rfl hH p hp hno2

private theorem rc_exists_stable_recolor {V : Type*} [Fintype V] [Nonempty V]
    {k : ℕ} (delta : V → Fin k → V) (a₀ : Fin k)
    (hcon : rc_strongly delta) (haper : rc_aperiodic delta)
    (hcard : 1 < Fintype.card V) :
    ∃ sigma1 : V → Equiv.Perm (Fin k), ∃ x y : V, x ≠ y ∧
      rc_stable (rc_recolor delta sigma1) x y := by
  classical
  by_cases h2 : ∃ z x y : V, x ≠ y ∧ rc_isBunch delta x z ∧ rc_isBunch delta y z
  · obtain ⟨z, x, y, hne, hxb, hyb⟩ := h2
    exact ⟨fun _ => 1, x, y, hne,
      rc_stable_of_two_bunches _ a₀ (rc_bunch_recolor _ _ hxb)
        (rc_bunch_recolor _ _ hyb)⟩
  · have hno2 : ∀ z x y : V, rc_isBunch delta x z → rc_isBunch delta y z →
      x = y := by
      intro z x y hx hy
      by_contra hne
      exact h2 ⟨z, x, y, hne, hx, hy⟩
    obtain ⟨g, hg_adj, hgood⟩ := rc_exists_good_ssg delta hcon haper hcard hno2
    obtain ⟨sigma1, hsigma1⟩ := rc_recolor_realizes_ssg delta g hg_adj a₀
    have hAcon : rc_strongly (rc_recolor delta sigma1) :=
      (rc_strongly_recolor delta sigma1).mpr hcon
    obtain ⟨L, r, p, hL, _hLeq, _hplev, _hrroot, hper, htop, hcoll⟩ :=
      rc_good_bridge g hgood
    obtain ⟨x, y, hne, hst⟩ := rc_exists_stable_pair_of_good_letter
      (rc_recolor delta sigma1) hAcon a₀ g
      (fun v => (hsigma1 v).symm) L hL r p hper htop hcoll
    exact ⟨sigma1, x, y, hne, hst⟩

private theorem rc_sync_recolor_bounded {k : ℕ} (m : ℕ) :
    ∀ {V : Type*} [Fintype V] [Nonempty V], Fintype.card V ≤ m →
    ∀ (delta : V → Fin k → V), rc_strongly delta → rc_aperiodic delta →
    ∃ sigma : V → Equiv.Perm (Fin k), rc_sync (rc_recolor delta sigma) := by
  induction m with
  | zero =>
    intro V _ _ hcard delta hcon haper
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
    omega
  | succ m ih =>
    intro V _ _ hcard delta hcon haper
    classical
    by_cases h1 : Fintype.card V = 1
    · obtain ⟨r, hr⟩ := Fintype.card_eq_one_iff.mp h1
      exact ⟨fun _ => 1, [], r, fun v => hr v⟩
    · have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
      have hlt1 : 1 < Fintype.card V := by omega
      have hk : 0 < k := by
        by_contra hk0
        have hk0' : k = 0 := by omega
        obtain ⟨v₀⟩ : Nonempty V := inferInstance
        obtain ⟨w₀, hne₀⟩ := Fintype.exists_ne_of_one_lt_card hlt1 v₀
        have hne : v₀ ≠ w₀ := Ne.symm hne₀
        have hempty : ∀ x y : V, ¬ rc_adj delta x y := by
          intro x y h
          obtain ⟨a, _⟩ := h
          exact Fin.elim0 (hk0' ▸ a)
        have heq : v₀ = w₀ := by
          have h := hcon v₀ w₀
          induction h with
          | refl => rfl
          | tail _ hab _ => exact (hempty _ _ hab).elim
        exact hne heq
      obtain ⟨sigma1, x, y, hne, hst⟩ :=
        rc_exists_stable_recolor delta ⟨0, hk⟩ hcon haper hlt1
      have hAcon : rc_strongly (rc_recolor delta sigma1) :=
        (rc_strongly_recolor delta sigma1).mpr hcon
      have hAaper : rc_aperiodic (rc_recolor delta sigma1) :=
        (rc_aperiodic_recolor delta sigma1).mpr haper
      have hQlt : Fintype.card
          (Quotient (rc_stableSetoid (rc_recolor delta sigma1))) < Fintype.card V :=
        rc_quot_card_lt _ hne hst
      have hQle : Fintype.card
          (Quotient (rc_stableSetoid (rc_recolor delta sigma1))) ≤ m := by omega
      obtain ⟨sigma', w', r', hw'⟩ := ih hQle (rc_quot (rc_recolor delta sigma1))
        (rc_quot_strongly _ hAcon) (rc_quot_aperiodic _ hAaper)
      obtain ⟨y₀, hy₀⟩ := Quotient.exists_rep r'
      have hpair : ∀ s₁ ∈ Finset.univ.image
            (fun v => List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v w'),
          ∀ s₂ ∈ Finset.univ.image
            (fun v => List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v w'),
          rc_stable (rc_recolor (rc_recolor delta sigma1)
            (fun v => sigma' (Quotient.mk _ v))) s₁ s₂ := by
        intro s₁ hs₁ s₂ hs₂
        obtain ⟨v₁, _, rfl⟩ := Finset.mem_image.mp hs₁
        obtain ⟨v₂, _, rfl⟩ := Finset.mem_image.mp hs₂
        have e1 : Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₁ w') = r' := by
          rw [rc_lift_quot_foldl]
          exact hw' _
        have e2 : Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₂ w') = r' := by
          rw [rc_lift_quot_foldl]
          exact hw' _
        have hsame : Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₁ w') =
            Quotient.mk (rc_stableSetoid (rc_recolor delta sigma1))
            (List.foldl (rc_recolor (rc_recolor delta sigma1)
              (fun v => sigma' (Quotient.mk _ v))) v₂ w') := by
          rw [e1, e2]
        exact rc_stable_lift _ _ (Quotient.exact hsame)
      obtain ⟨vbar, rfin, hfin⟩ :=
        rc_exists_merge_of_pairwise_stable _ _ hpair
      refine ⟨fun v => sigma1 v * sigma' (Quotient.mk _ v), w' ++ vbar, rfin, ?_⟩
      intro v
      rw [← rc_recolor_recolor, List.foldl_append]
      exact hfin _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)

private theorem rc_exists_sync_recolor {k : ℕ} {V : Type*} [Finite V] [Nonempty V]
    (delta : V → Fin k → V) (hcon : rc_strongly delta)
    (haper : rc_aperiodic delta) :
    ∃ sigma : V → Equiv.Perm (Fin k), rc_sync (rc_recolor delta sigma) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact rc_sync_recolor_bounded (Fintype.card V) le_rfl delta hcon haper

end RoadColoring

/-- **Road coloring theorem for a finite vertex type.** Let $V$ be a finite nonempty set and let
$\to$ be a relation on $V$, viewed as a directed graph on $V$ without parallel edges (loops
allowed). Suppose that the graph is strongly connected (for all $u, v \in V$ there is a directed
walk, possibly of length $0$, from $u$ to $v$), aperiodic (for every integer $d > 1$ there is a
closed directed walk of positive length not divisible by $d$), and of constant positive
out-degree (there is $k > 0$ such that every vertex has exactly $k$ out-neighbours). Then there
exist a natural number $\ell$ and a map $\delta : V \times \{0, \dots, \ell - 1\} \to V$ such that
for every $v \in V$ the map $c \mapsto \delta(v, c)$ is a bijection from $\{0, \dots, \ell - 1\}$
onto the out-neighbours of $v$, together with a word $c_1 \cdots c_m$ over $\{0, \dots, \ell - 1\}$
and a vertex $r$ such that following the labels $c_1, \dots, c_m$ in order from any vertex $v$
ends at $r$.

This form only assumes that $V$ is finite, as a property, rather than being given a finite set of
all its elements as data. -/
theorem roadColoring' :
    ∀ {V : Type*} [Finite V] [Nonempty V]
      (Adj : V → V → Prop),
      (∀ u v : V, Relation.ReflTransGen Adj u v) →
      (∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
        List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)) →
      (∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) →
      ∃ (k : ℕ) (trans : V → Fin k → V),
        (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
        (∀ v : V, Function.Injective (trans v)) ∧
        (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
        ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r := by
  intro V _ _ Adj hcon haper hreg
  obtain ⟨k, hk, he⟩ := hreg
  have e : ∀ v : V, { w : V // Adj v w } ≃ Fin k :=
    fun v => Classical.choice (he v)
  obtain ⟨delta, hadj_mem, hinj, hcov, hadj_eq, hrecol⟩ :=
    RoadColoring.rc_automaton_of_regular Adj k e
  have hcon' : RoadColoring.rc_strongly delta := by
    intro u v
    rw [hadj_eq]
    exact hcon u v
  have haper' : RoadColoring.rc_aperiodic delta := by
    intro d hd
    obtain ⟨u, w, hchain, hlast, hdiv⟩ := haper d hd
    rw [← hadj_eq] at hchain
    exact ⟨u, w, hchain, hlast, hdiv⟩
  obtain ⟨sigma, word, r, hsync⟩ :=
    RoadColoring.rc_exists_sync_recolor delta hcon' haper'
  exact ⟨k, RoadColoring.rc_recolor delta sigma, (hrecol sigma).1,
    (hrecol sigma).2.1, (hrecol sigma).2.2, word, r, hsync⟩

/-- **Road coloring theorem.** Let $V$ be a finite nonempty set and let $\to$ be a relation
on $V$, viewed as a directed graph on $V$ without parallel edges (loops allowed). Suppose that the
graph is strongly connected (for all $u, v \in V$ there is a directed walk, possibly of length $0$,
from $u$ to $v$), aperiodic (for every integer $d > 1$ there is a closed directed walk of positive
length not divisible by $d$), and of constant positive out-degree (there is $k > 0$ such that
every vertex has exactly $k$ out-neighbours). Then there exist a natural number $\ell$ and a map
$\delta : V \times \{0, \dots, \ell - 1\} \to V$ such that for every $v \in V$ the map
$c \mapsto \delta(v, c)$ is a bijection from $\{0, \dots, \ell - 1\}$ onto the out-neighbours of
$v$, together with a word $c_1 \cdots c_m$ over $\{0, \dots, \ell - 1\}$ and a vertex $r$ such
that following the labels $c_1, \dots, c_m$ in order from any vertex $v$ ends at $r$.

Proves `Wanted` entry `roadColoring`.

Source: https://en.wikipedia.org/wiki/Road_coloring_theorem
-/
theorem roadColoring :
    ∀ {V : Type*} [Fintype V] [Nonempty V]
      (Adj : V → V → Prop),
      (∀ u v : V, Relation.ReflTransGen Adj u v) →
      (∀ d : ℕ, 1 < d → ∃ (u : V) (w : List V),
        List.IsChain Adj (u :: w) ∧ w.getLast? = some u ∧ ¬ (d ∣ w.length)) →
      (∃ k : ℕ, 0 < k ∧ ∀ v : V, Nonempty ({ w : V // Adj v w } ≃ Fin k)) →
      ∃ (k : ℕ) (trans : V → Fin k → V),
        (∀ v : V, ∀ c : Fin k, Adj v (trans v c)) ∧
        (∀ v : V, Function.Injective (trans v)) ∧
        (∀ (v w : V), Adj v w → ∃ c : Fin k, trans v c = w) ∧
        ∃ (word : List (Fin k)) (r : V), ∀ v : V, List.foldl trans v word = r := by
  intro V _ _ Adj hcon haper hreg
  exact roadColoring' Adj hcon haper hreg

end
end MetaMathlibExt
