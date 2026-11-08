/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite iteration to least and greatest fixed points on `Finset`s
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.FixedPoints

/-!
# Finite iteration to least and greatest fixed points on `Finset`s

For a monotone functional `f : Finset α → Finset α` on a finite type,
`Finset.lfpFin f` and `Finset.gfpFin f` compute the least and
greatest fixed points of `f` by iterating `f` from `∅` respectively
`Finset.univ` for `Fintype.card α` steps; the iteration has
stabilized by then, by a cardinality argument on the strictly
monotone chain (`Finset.lfpFin_fixed`, `Finset.gfpFin_fixed`), and
Park-style lemmas (`Finset.lfpFin_le`, `Finset.le_gfpFin`) identify
the results as the least and greatest fixed points.  Bridge lemmas
(`Finset.mem_finset_iterate_iff`, `Finset.mem_lfpFin_iff_lfp` and
their duals) identify the finite iterates with the iterates of a
predicate functional and hence with its Knaster-Tarski fixed points
`OrderHom.lfp` and `OrderHom.gfp` from `Mathlib.Order.FixedPoints`;
upstream Mathlib has those `OrderHom` fixed points but no
`Fintype.card`-bounded iterate API on `Finset`s, hence this module.
-/

@[expose] public section

namespace Finset

section FiniteIteration

variable {α : Type*} [Fintype α]

/-- The least fixed point of a `Finset` functional on a finite type,
computed by iterating from `∅` for `Fintype.card α` steps.  For a
monotone functional the iteration has stabilized by then
(`lfpFin_fixed`). -/
def lfpFin (f : Finset α → Finset α) : Finset α :=
  f^[Fintype.card α] ∅

/-- The greatest fixed point of a `Finset` functional on a finite type,
computed by iterating from `Finset.univ` for `Fintype.card α` steps.
For a monotone functional the iteration has stabilized by then
(`gfpFin_fixed`). -/
def gfpFin (f : Finset α → Finset α) : Finset α :=
  f^[Fintype.card α] Finset.univ

/-- The iterates of a monotone `Finset` functional from `∅` stabilize
within `Fintype.card α` steps: the chain is increasing, and until it
stabilizes each step strictly increases the cardinality, which is
bounded by `Fintype.card α`. -/
theorem lfpFin_fixed {f : Finset α → Finset α} (hf : Monotone f) :
    f (lfpFin f) = lfpFin f := by
  classical
  have hsucc : ∀ n, f^[n + 1] (∅ : Finset α) = f (f^[n] ∅) :=
    fun n => Function.iterate_succ_apply' f n _
  have hmono_chain : ∀ n, f^[n] (∅ : Finset α) ⊆ f^[n + 1] ∅ := by
    intro n
    induction n with
    | zero => exact Finset.empty_subset _
    | succ n ih =>
        rw [hsucc n] at ih
        rw [hsucc (n + 1), hsucc n]
        exact hf ih
  have hex : ∃ n, n ≤ Fintype.card α ∧ f^[n + 1] (∅ : Finset α) = f^[n] ∅ := by
    by_contra h
    push Not at h
    have hssub : ∀ n, n ≤ Fintype.card α →
        f^[n] (∅ : Finset α) ⊂ f^[n + 1] ∅ :=
      fun n hn => Finset.ssubset_iff_subset_ne.mpr
        ⟨hmono_chain n, fun heq => h n hn heq.symm⟩
    have hcard : ∀ n, n ≤ Fintype.card α + 1 →
        n ≤ (f^[n] (∅ : Finset α)).card := by
      intro n hn
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
          have ih' := ih (by omega)
          have hlt := Finset.card_lt_card (hssub n (by omega))
          omega
    have h1 := hcard (Fintype.card α + 1) le_rfl
    have h2 := Finset.card_le_univ (f^[Fintype.card α + 1] (∅ : Finset α))
    omega
  obtain ⟨n, hn, hstab⟩ := hex
  have hstable : ∀ m, n ≤ m → f^[m] (∅ : Finset α) = f^[n] ∅ := by
    intro m hnm
    obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    induction k with
    | zero => rfl
    | succ k ih =>
        have e1 : f^[n + (k + 1)] (∅ : Finset α) = f (f^[n + k] ∅) :=
          hsucc _
        rw [e1, ih (by omega), ← hsucc n, hstab]
  show f (f^[Fintype.card α] (∅ : Finset α)) = f^[Fintype.card α] ∅
  rw [← hsucc, hstable _ (by omega), hstable _ hn]

/-- The iterates of a monotone `Finset` functional from `Finset.univ`
stabilize within `Fintype.card α` steps: the chain is decreasing, and
until it stabilizes each step strictly decreases the cardinality. -/
theorem gfpFin_fixed {f : Finset α → Finset α} (hf : Monotone f) :
    f (gfpFin f) = gfpFin f := by
  classical
  have hsucc : ∀ n, f^[n + 1] (Finset.univ : Finset α) = f (f^[n] Finset.univ) :=
    fun n => Function.iterate_succ_apply' f n _
  have hmono_chain : ∀ n,
      f^[n + 1] (Finset.univ : Finset α) ⊆ f^[n] Finset.univ := by
    intro n
    induction n with
    | zero => exact Finset.subset_univ _
    | succ n ih =>
        rw [hsucc n] at ih
        rw [hsucc (n + 1), hsucc n]
        exact hf ih
  have hex : ∃ n, n ≤ Fintype.card α ∧
      f^[n + 1] (Finset.univ : Finset α) = f^[n] Finset.univ := by
    by_contra h
    push Not at h
    have hssub : ∀ n, n ≤ Fintype.card α →
        f^[n + 1] (Finset.univ : Finset α) ⊂ f^[n] Finset.univ :=
      fun n hn => Finset.ssubset_iff_subset_ne.mpr ⟨hmono_chain n, h n hn⟩
    have hcard : ∀ n, n ≤ Fintype.card α + 1 →
        (f^[n] (Finset.univ : Finset α)).card + n ≤ Fintype.card α := by
      intro n hn
      induction n with
      | zero => simp
      | succ n ih =>
          have ih' := ih (by omega)
          have hlt := Finset.card_lt_card (hssub n (by omega))
          omega
    have hfin := hcard (Fintype.card α + 1) le_rfl
    omega
  obtain ⟨n, hn, hstab⟩ := hex
  have hstable : ∀ m, n ≤ m →
      f^[m] (Finset.univ : Finset α) = f^[n] Finset.univ := by
    intro m hnm
    obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    induction k with
    | zero => rfl
    | succ k ih =>
        have e1 : f^[n + (k + 1)] (Finset.univ : Finset α) =
            f (f^[n + k] Finset.univ) := hsucc _
        rw [e1, ih (by omega), ← hsucc n, hstab]
  show f (f^[Fintype.card α] (Finset.univ : Finset α)) =
    f^[Fintype.card α] Finset.univ
  rw [← hsucc, hstable _ (by omega), hstable _ hn]

/-- `lfpFin f` is contained in every pre-fixed point of `f`: every
iterate from `∅` is, by induction. -/
theorem lfpFin_le {f : Finset α → Finset α} (hf : Monotone f)
    {Z : Finset α} (hZ : f Z ⊆ Z) : lfpFin f ⊆ Z := by
  have key : ∀ n, f^[n] (∅ : Finset α) ⊆ Z := by
    intro n
    induction n with
    | zero => exact Finset.empty_subset _
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (hf ih).trans hZ
  exact key _

/-- Every post-fixed point of `f` is contained in `gfpFin f`: it is
contained in every iterate from `Finset.univ`, by induction. -/
theorem le_gfpFin {f : Finset α → Finset α} (hf : Monotone f)
    {Z : Finset α} (hZ : Z ⊆ f Z) : Z ⊆ gfpFin f := by
  have key : ∀ n, Z ⊆ f^[n] (Finset.univ : Finset α) := by
    intro n
    induction n with
    | zero => exact Finset.subset_univ _
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hZ.trans (hf ih)
  exact key _

end FiniteIteration

section Bridge

variable {α : Type*}

/-- Bridge between finite iterates from `∅`: if a `Finset` functional
`f` and a predicate functional `F` agree on membership predicates, then
their iterates from `∅` and `⊥` agree at every step. -/
theorem mem_finset_iterate_iff {F : (α → Prop) → α → Prop}
    {f : Finset α → Finset α}
    (hbridge : ∀ Z s, s ∈ f Z ↔ F (fun t => t ∈ Z) s) :
    ∀ n s, s ∈ f^[n] ∅ ↔ (F^[n] (fun _ => False)) s := by
  intro n
  induction n with
  | zero =>
      intro s
      show s ∈ (∅ : Finset α) ↔ False
      simp
  | succ n ih =>
      intro s
      have hfun : (fun t => t ∈ f^[n] (∅ : Finset α)) =
          F^[n] (fun _ => False) :=
        funext fun t => propext (ih t)
      simp only [Function.iterate_succ_apply']
      rw [hbridge, hfun]

variable [Fintype α]

/-- Bridge between finite iterates from `Finset.univ`: if a `Finset`
functional `f` and a predicate functional `F` agree on membership
predicates, then their iterates from `Finset.univ` and `⊤` agree at
every step. -/
theorem mem_finset_iterate_univ_iff {F : (α → Prop) → α → Prop}
    {f : Finset α → Finset α}
    (hbridge : ∀ Z s, s ∈ f Z ↔ F (fun t => t ∈ Z) s) :
    ∀ n s, s ∈ f^[n] Finset.univ ↔ (F^[n] (fun _ => True)) s := by
  intro n
  induction n with
  | zero =>
      intro s
      show s ∈ (Finset.univ : Finset α) ↔ True
      simp
  | succ n ih =>
      intro s
      have hfun : (fun t => t ∈ f^[n] (Finset.univ : Finset α)) =
          F^[n] (fun _ => True) :=
        funext fun t => propext (ih t)
      simp only [Function.iterate_succ_apply']
      rw [hbridge, hfun]

/-- Convergence for least fixed points: under the bridge hypothesis,
`lfpFin f` computes the least fixed point of `F`.  One inclusion is
iteration into the fixed point; the other is Park induction, where the
`Fintype.card α`-th `F`-iterate is pre-fixed because the
corresponding `f`-iterate has stabilized (`lfpFin_fixed`), transported
across the bridge. -/
theorem mem_lfpFin_iff_lfp {F : (α → Prop) → α → Prop}
    {f : Finset α → Finset α}
    (hfm : Monotone f) (hFm : Monotone F)
    (hbridge : ∀ Z s, s ∈ f Z ↔ F (fun t => t ∈ Z) s) (s : α) :
    s ∈ lfpFin f ↔
      (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).lfp s := by
  have hpre : F (F^[Fintype.card α] (fun _ => False)) ≤
      F^[Fintype.card α] (fun _ => False) := by
    intro t ht
    have h1 : (F^[Fintype.card α + 1] (fun _ => False)) t := by
      simp only [Function.iterate_succ_apply']
      exact ht
    have h2 : t ∈ f^[Fintype.card α + 1] (∅ : Finset α) :=
      (mem_finset_iterate_iff hbridge _ t).mpr h1
    have h3 : f^[Fintype.card α + 1] (∅ : Finset α) =
        f^[Fintype.card α] ∅ := by
      rw [Function.iterate_succ_apply']
      exact lfpFin_fixed hfm
    rw [h3] at h2
    exact (mem_finset_iterate_iff hbridge _ t).mp h2
  have hle1 : (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).lfp ≤
      F^[Fintype.card α] (fun _ => False) := by
    apply OrderHom.lfp_le
    exact hpre
  have hle2 : ∀ n, F^[n] (fun _ => False) ≤
      (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).lfp := by
    intro n
    induction n with
    | zero =>
        intro t ht
        exact False.elim ht
    | succ n ih =>
        intro t ht
        simp only [Function.iterate_succ_apply'] at ht
        have ht2 : F (⟨F, hFm⟩ :
            (α → Prop) →o (α → Prop)).lfp t :=
          hFm ih t ht
        rw [← OrderHom.map_lfp
          (⟨F, hFm⟩ : (α → Prop) →o (α → Prop))]
        exact ht2
  constructor
  · intro hs
    exact hle2 _ s ((mem_finset_iterate_iff hbridge _ s).mp hs)
  · intro hs
    exact (mem_finset_iterate_iff hbridge _ s).mpr (hle1 s hs)

/-- Convergence for greatest fixed points: under the bridge hypothesis,
`gfpFin f` computes the greatest fixed point of `F`, dually to
`mem_lfpFin_iff_lfp`. -/
theorem mem_gfpFin_iff_gfp {F : (α → Prop) → α → Prop}
    {f : Finset α → Finset α}
    (hfm : Monotone f) (hFm : Monotone F)
    (hbridge : ∀ Z s, s ∈ f Z ↔ F (fun t => t ∈ Z) s) (s : α) :
    s ∈ gfpFin f ↔
      (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).gfp s := by
  have hpost : F^[Fintype.card α] (fun _ => True) ≤
      F (F^[Fintype.card α] (fun _ => True)) := by
    intro t ht
    have h2 : t ∈ f^[Fintype.card α] (Finset.univ : Finset α) :=
      (mem_finset_iterate_univ_iff hbridge _ t).mpr ht
    have h3 : f^[Fintype.card α + 1] (Finset.univ : Finset α) =
        f^[Fintype.card α] Finset.univ := by
      rw [Function.iterate_succ_apply']
      exact gfpFin_fixed hfm
    have h2' : t ∈ f^[Fintype.card α + 1]
        (Finset.univ : Finset α) := by
      rwa [h3]
    have h1 : (F^[Fintype.card α + 1] (fun _ => True)) t :=
      (mem_finset_iterate_univ_iff hbridge _ t).mp h2'
    simpa only [Function.iterate_succ_apply'] using h1
  have hge1 : F^[Fintype.card α] (fun _ => True) ≤
      (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).gfp := by
    apply OrderHom.le_gfp
    exact hpost
  have hge2 : ∀ n,
      (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).gfp ≤
        F^[n] (fun _ => True) := by
    intro n
    induction n with
    | zero =>
        intro t _
        exact trivial
    | succ n ih =>
        intro t ht
        simp only [Function.iterate_succ_apply']
        have ht2 : (⟨F, hFm⟩ : (α → Prop) →o (α → Prop))
            (⟨F, hFm⟩ : (α → Prop) →o (α → Prop)).gfp t := by
          rw [OrderHom.map_gfp]
          exact ht
        exact hFm ih t ht2
  constructor
  · intro hs
    exact hge1 s ((mem_finset_iterate_univ_iff hbridge _ s).mp hs)
  · intro hs
    exact (mem_finset_iterate_univ_iff hbridge _ s).mpr (hge2 _ s hs)

end Bridge

end Finset
