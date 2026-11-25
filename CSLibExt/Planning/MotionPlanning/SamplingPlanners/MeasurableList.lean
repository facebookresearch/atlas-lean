/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners
public import Mathlib.Data.List.OfFn
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

@[expose] public section

/-! # Measurable finite lists

Finite lists carry the length-stratified σ-algebra: a set of lists is measurable
exactly when its preimage under every `List.ofFn` stratum inclusion is
measurable. This file proves the resulting measurability library — `cons`,
`length`, `append`, `map`, `filter`, `foldl`, structural recursion, decidable
equality and membership tests, `dedup`, and existential membership events — and
states the oracle measurability bundle used by the sampling-based planners.

The planners are deterministic functions of explicit sample lists, and their
lift to i.i.d. streams reads raw prefixes and filters with each planner's
own collision test. The lemmas here supply the per-stratum measurability facts
that lift needs, with no continuity assumptions on the parameters.
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- The length-stratified σ-algebra on finite lists: a set of lists is measurable
when, for every length `n`, the set of `n`-tuples whose list lies in it is
measurable in the product σ-algebra. Equivalently, `List α` carries the
disjoint-union σ-algebra of the strata `Fin n → α`. -/
scoped instance listMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (List α) :=
  ⨅ n : ℕ, MeasurableSpace.map (fun v : Fin n → α => List.ofFn v) inferInstance

/-- Measurable sets of lists are exactly those measurable on every length stratum. -/
theorem measurableSet_list_iff {α : Type*} [MeasurableSpace α] {s : Set (List α)} :
    MeasurableSet s ↔ ∀ n : ℕ, MeasurableSet ((fun v : Fin n → α => List.ofFn v) ⁻¹' s) := by
  unfold listMeasurableSpace
  simp only [MeasurableSpace.measurableSet_iInf]
  apply forall_congr'
  intro n
  rfl

/-- Each stratum inclusion `List.ofFn` is measurable. -/
theorem measurable_list_ofFn {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (fun v : Fin n → α => List.ofFn v) := by
  intro t ht
  rw [measurableSet_list_iff] at ht
  exact ht n

/-- `List.ofFn` is injective on each length stratum. -/
private theorem injective_list_ofFn {α : Type*} (n : ℕ) :
    Function.Injective (fun v : Fin n → α => List.ofFn v) :=
  fun _ _ h => List.ofFn_inj.mp h

/-- Every list is `List.ofFn` of its lookup function on its length stratum. -/
private theorem exists_list_eq_ofFn {α : Type*} (l : List α) :
    ∃ n : ℕ, ∃ v : Fin n → α, List.ofFn v = l :=
  ⟨l.length, l.get, List.ofFn_get l⟩

/-- Each length stratum includes into lists as a measurable embedding. -/
private theorem measurableEmbedding_list_ofFn {α : Type*} [MeasurableSpace α]
    (n : ℕ) :
    MeasurableEmbedding (fun v : Fin n → α => List.ofFn v) :=
  ⟨injective_list_ofFn n, measurable_list_ofFn n, by
    intro s hs
    rw [measurableSet_list_iff]
    intro m
    by_cases h : m = n
    · subst h
      rw [Set.preimage_image_eq _ (injective_list_ofFn _)]
      exact hs
    · have hempty : (fun v : Fin m → α => List.ofFn v) ⁻¹'
          ((fun v : Fin n → α => List.ofFn v) '' s) = ∅ := by
        ext v
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨w, -, hvw⟩
          have hlen := congrArg List.length hvw
          rw [List.length_ofFn, List.length_ofFn] at hlen
          exact h hlen.symm
        · intro hfalse
          exact hfalse.elim
      rw [hempty]
      exact MeasurableSet.empty⟩

/-- The stratum inclusion into a product with lists is a measurable embedding. -/
private theorem measurableEmbedding_prod_ofFn {α δ : Type*} [MeasurableSpace α]
    [MeasurableSpace δ] (n : ℕ) :
    MeasurableEmbedding (Prod.map (id : δ → δ)
      (fun v : Fin n → α => List.ofFn v)) :=
  MeasurableEmbedding.prodMap MeasurableEmbedding.id
    (measurableEmbedding_list_ofFn n)

/-- A function out of `List α` is measurable once it is measurable on every stratum. -/
theorem measurable_list_of_ofFn {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {f : List α → γ} (hf : ∀ n : ℕ, Measurable (fun v : Fin n → α => f (List.ofFn v))) :
    Measurable f := by
  intro t ht
  rw [measurableSet_list_iff]
  intro n
  exact hf n ht

/-- A function out of `δ × List α` is measurable once it is measurable on every
stratum `δ × (Fin n → α)`. -/
theorem measurable_prod_list_of_ofFn {α δ γ : Type*} [MeasurableSpace α] [MeasurableSpace δ]
    [MeasurableSpace γ] {f : δ × List α → γ}
    (hf : ∀ n : ℕ, Measurable (fun p : δ × (Fin n → α) => f (p.1, List.ofFn p.2))) :
    Measurable f := by
  intro t ht
  have hunion : f ⁻¹' t = ⋃ n : ℕ, Prod.map (id : δ → δ)
      (fun v : Fin n → α => List.ofFn v) ''
      ((fun p : δ × (Fin n → α) => f (p.1, List.ofFn p.2)) ⁻¹' t) := by
    ext ⟨d, l⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro h
      obtain ⟨n, v, rfl⟩ := exists_list_eq_ofFn l
      exact ⟨n, (d, v), h, rfl⟩
    · rintro ⟨n, x, hx, heq⟩
      obtain ⟨d', v⟩ := x
      rw [← heq]
      exact hx
  rw [hunion]
  apply MeasurableSet.iUnion
  intro n
  exact (measurableEmbedding_prod_ofFn n).measurableSet_image.mpr (hf n ht)

/-- A function out of a pair of lists is measurable once it is measurable on
every pair of length strata. -/
private theorem measurable_list_list_of_ofFn {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {f : List α × List β → γ}
    (hf : ∀ m n : ℕ, Measurable (fun p : (Fin m → α) × (Fin n → β) =>
      f (List.ofFn p.1, List.ofFn p.2))) :
    Measurable f := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : List α × (Fin n → β) =>
      f (p.1, List.ofFn p.2)) := by
    intro n
    have hswap : Measurable (fun q : (Fin n → β) × List α =>
        f (q.2, List.ofFn q.1)) := by
      have hstrat2 : ∀ m : ℕ, Measurable (fun r : (Fin n → β) × (Fin m → α) =>
          f (List.ofFn r.2, List.ofFn r.1)) := by
        intro m
        have h2 : (fun r : (Fin n → β) × (Fin m → α) =>
              f (List.ofFn r.2, List.ofFn r.1))
            = (fun p : (Fin m → α) × (Fin n → β) =>
              f (List.ofFn p.1, List.ofFn p.2)) ∘ Prod.swap := by
          funext r
          cases r
          rfl
        rw [h2]
        exact (hf m n).comp measurable_swap
      exact measurable_prod_list_of_ofFn hstrat2
    have h1 : (fun p : List α × (Fin n → β) => f (p.1, List.ofFn p.2))
        = (fun q : (Fin n → β) × List α => f (q.2, List.ofFn q.1)) ∘
          Prod.swap := by
      funext p
      cases p
      rfl
    rw [h1]
    exact hswap.comp measurable_swap
  exact measurable_prod_list_of_ofFn hstrat

/-- `List.cons` is jointly measurable. -/
theorem measurable_list_cons {α : Type*} [MeasurableSpace α] :
    Measurable (fun p : α × List α => p.1 :: p.2) := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : α × (Fin n → α) =>
      p.1 :: List.ofFn p.2) := by
    intro n
    have hconsmap : Measurable (fun p : α × (Fin n → α) =>
        (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
      apply Measurable.of_eval
      intro i
      obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
      · have h0 : ∀ c : α × (Fin n → α),
            (Fin.cons c.1 c.2 : Fin (n + 1) → α) 0 = c.1 :=
          fun c => Fin.cons_zero _ _
        simp only [h0]
        exact measurable_fst
      · have hs : ∀ c : α × (Fin n → α),
            (Fin.cons c.1 c.2 : Fin (n + 1) → α) j.succ = c.2 j :=
          fun c => Fin.cons_succ _ _ _
        simp only [hs]
        exact (measurable_pi_apply j).comp measurable_snd
    have hfun : (fun p : α × (Fin n → α) => p.1 :: List.ofFn p.2)
        = (fun v : Fin (n + 1) → α => List.ofFn v) ∘
          (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
      funext p
      show p.1 :: List.ofFn p.2 = List.ofFn (Fin.cons p.1 p.2 : Fin (n + 1) → α)
      rw [List.ofFn_succ, Fin.cons_zero]
      congr 1
    rw [hfun]
    exact (measurable_list_ofFn (n + 1)).comp hconsmap
  exact measurable_prod_list_of_ofFn hstrat

/-- `List.length` is measurable (the codomain `ℕ` is discrete). -/
theorem measurable_list_length {α : Type*} [MeasurableSpace α] :
    Measurable (List.length : List α → ℕ) := by
  have hstrat : ∀ n : ℕ, Measurable (fun v : Fin n → α =>
      (List.ofFn v).length) := by
    intro n
    have hfun : (fun v : Fin n → α => (List.ofFn v).length) = fun _ => n := by
      funext v
      show (List.ofFn v).length = n
      exact List.length_ofFn
    rw [hfun]
    exact measurable_const
  exact measurable_list_of_ofFn hstrat

/-- `List.append` is jointly measurable. -/
theorem measurable_list_append {α : Type*} [MeasurableSpace α] :
    Measurable (fun p : List α × List α => p.1 ++ p.2) := by
  have hstrat : ∀ m n : ℕ, Measurable (fun p : (Fin m → α) × (Fin n → α) =>
      List.ofFn p.1 ++ List.ofFn p.2) := by
    intro m n
    induction m with
    | zero =>
        have h0 : ∀ p : (Fin 0 → α) × (Fin n → α), List.ofFn p.1 = [] :=
          fun p => List.length_eq_zero_iff.mp (List.length_ofFn (f := p.1))
        have hfun : (fun p : (Fin 0 → α) × (Fin n → α) =>
              List.ofFn p.1 ++ List.ofFn p.2)
            = fun p => List.ofFn p.2 := by
          funext p
          show List.ofFn p.1 ++ List.ofFn p.2 = List.ofFn p.2
          rw [h0 p]
          exact List.nil_append _
        rw [hfun]
        exact (measurable_list_ofFn n).comp measurable_snd
    | succ m ih =>
        have htail : Measurable (fun p : (Fin (m + 1) → α) × (Fin n → α) =>
            (fun i : Fin m => p.1 i.succ)) := by
          apply Measurable.of_eval
          intro i
          exact (measurable_pi_apply i.succ).comp measurable_fst
        have hpair : Measurable (fun p : (Fin (m + 1) → α) × (Fin n → α) =>
            ((fun i : Fin m => p.1 i.succ), p.2)) :=
          htail.prodMk measurable_snd
        have hFm : Measurable (fun p : (Fin (m + 1) → α) × (Fin n → α) =>
            List.ofFn (fun i : Fin m => p.1 i.succ) ++ List.ofFn p.2) :=
          ih.comp hpair
        have hhead : Measurable
            (fun p : (Fin (m + 1) → α) × (Fin n → α) => p.1 0) :=
          (measurable_pi_apply 0).comp measurable_fst
        have hfun : (fun p : (Fin (m + 1) → α) × (Fin n → α) =>
              List.ofFn p.1 ++ List.ofFn p.2)
            = (fun q : α × List α => q.1 :: q.2) ∘
              (fun p : (Fin (m + 1) → α) × (Fin n → α) =>
                (p.1 0, List.ofFn (fun i : Fin m => p.1 i.succ) ++
                  List.ofFn p.2)) := by
          funext p
          show List.ofFn p.1 ++ List.ofFn p.2
            = p.1 0 :: (List.ofFn (fun i : Fin m => p.1 i.succ) ++ List.ofFn p.2)
          simp only [List.ofFn_succ, List.cons_append]
        rw [hfun]
        exact measurable_list_cons.comp (hhead.prodMk hFm)
  exact measurable_list_list_of_ofFn hstrat

/-- `List.map` with a jointly measurable parametrized function is measurable. -/
theorem measurable_list_map {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace δ] {f : δ × α → β} (hf : Measurable f) :
    Measurable (fun p : δ × List α => p.2.map (fun a => f (p.1, a))) := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : δ × (Fin n → α) =>
      (List.ofFn p.2).map (fun a => f (p.1, a))) := by
    intro n
    have hinner : Measurable (fun p : δ × (Fin n → α) =>
        (fun i : Fin n => f (p.1, p.2 i))) := by
      apply Measurable.of_eval
      intro i
      exact hf.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp
        measurable_snd))
    have hfun : (fun p : δ × (Fin n → α) =>
          (List.ofFn p.2).map (fun a => f (p.1, a)))
        = (fun v : Fin n → β => List.ofFn v) ∘
          (fun p : δ × (Fin n → α) => fun i : Fin n => f (p.1, p.2 i)) := by
      funext p
      show (List.ofFn p.2).map (fun a => f (p.1, a))
        = List.ofFn fun i : Fin n => f (p.1, p.2 i)
      exact List.map_ofFn
    rw [hfun]
    exact (measurable_list_ofFn n).comp hinner
  exact measurable_prod_list_of_ofFn hstrat

/-- `List.filter` with a jointly measurable parametrized test is measurable. -/
theorem measurable_list_filter {α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ]
    {q : δ × α → Bool} (hq : Measurable q) :
    Measurable (fun p : δ × List α => p.2.filter (fun a => q (p.1, a))) := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : δ × (Fin n → α) =>
      (List.ofFn p.2).filter (fun a => q (p.1, a))) := by
    intro n
    induction n with
    | zero =>
        have h0 : ∀ p : δ × (Fin 0 → α), List.ofFn p.2 = [] :=
          fun p => List.length_eq_zero_iff.mp (List.length_ofFn (f := p.2))
        have hfun : (fun p : δ × (Fin 0 → α) =>
              (List.ofFn p.2).filter (fun a => q (p.1, a)))
            = fun _ => [] := by
          funext p
          show (List.ofFn p.2).filter (fun a => q (p.1, a)) = []
          rw [h0 p]
          exact List.filter_nil
        rw [hfun]
        exact measurable_const
    | succ n ih =>
        have htail : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            (fun i : Fin n => p.2 i.succ)) := by
          apply Measurable.of_eval
          intro i
          exact (measurable_pi_apply i.succ).comp measurable_snd
        have hpair : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            (p.1, fun i : Fin n => p.2 i.succ)) :=
          measurable_fst.prodMk htail
        have hFn : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            (List.ofFn (fun i : Fin n => p.2 i.succ)).filter
              (fun a => q (p.1, a))) :=
          ih.comp hpair
        have hhead : Measurable (fun p : δ × (Fin (n + 1) → α) => p.2 0) :=
          (measurable_pi_apply 0).comp measurable_snd
        have hqhead : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            q (p.1, p.2 0)) :=
          hq.comp (measurable_fst.prodMk hhead)
        have hcond : MeasurableSet
            {p : δ × (Fin (n + 1) → α) | q (p.1, p.2 0) = true} := by
          have hpre : {p : δ × (Fin (n + 1) → α) | q (p.1, p.2 0) = true}
              = (fun p : δ × (Fin (n + 1) → α) => q (p.1, p.2 0)) ⁻¹' {true} :=
            rfl
          rw [hpre]
          exact hqhead (measurableSet_singleton true)
        have hconsF : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            p.2 0 :: (List.ofFn (fun i : Fin n => p.2 i.succ)).filter
              (fun a => q (p.1, a))) :=
          measurable_list_cons.comp (hhead.prodMk hFn)
        have hfun : (fun p : δ × (Fin (n + 1) → α) =>
              (List.ofFn p.2).filter (fun a => q (p.1, a)))
            = fun p => if q (p.1, p.2 0) = true
              then p.2 0 :: (List.ofFn (fun i : Fin n => p.2 i.succ)).filter
                (fun a => q (p.1, a))
              else (List.ofFn (fun i : Fin n => p.2 i.succ)).filter
                (fun a => q (p.1, a)) := by
          funext p
          show (List.ofFn p.2).filter (fun a => q (p.1, a))
            = if q (p.1, p.2 0) = true
              then p.2 0 :: (List.ofFn (fun i : Fin n => p.2 i.succ)).filter
                (fun a => q (p.1, a))
              else (List.ofFn (fun i : Fin n => p.2 i.succ)).filter
                (fun a => q (p.1, a))
          simp only [List.ofFn_succ, List.filter_cons]
        rw [hfun]
        exact Measurable.ite hcond hconsF hFn
  exact measurable_prod_list_of_ofFn hstrat

/-- `List.foldl` with a jointly measurable parametrized step is measurable in the
parameter, the initial accumulator and the list. -/
theorem measurable_list_foldl {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace δ] {g : δ × β × α → β} (hg : Measurable g) :
    Measurable (fun p : δ × β × List α => p.2.2.foldl (fun b a => g (p.1, b, a)) p.2.1) := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : (δ × β) × (Fin n → α) =>
      (List.ofFn p.2).foldl (fun b a => g (p.1.1, b, a)) p.1.2) := by
    intro n
    induction n with
    | zero =>
        have h0 : ∀ p : (δ × β) × (Fin 0 → α), List.ofFn p.2 = [] :=
          fun p => List.length_eq_zero_iff.mp (List.length_ofFn (f := p.2))
        have hfun : (fun p : (δ × β) × (Fin 0 → α) =>
              (List.ofFn p.2).foldl (fun b a => g (p.1.1, b, a)) p.1.2)
            = fun p => p.1.2 := by
          funext p
          show (List.ofFn p.2).foldl (fun b a => g (p.1.1, b, a)) p.1.2 = p.1.2
          rw [h0 p]
          exact List.foldl_nil
        rw [hfun]
        exact measurable_snd.comp measurable_fst
    | succ n ih =>
        have htail : Measurable (fun p : (δ × β) × (Fin (n + 1) → α) =>
            (fun i : Fin n => p.2 i.succ)) := by
          apply Measurable.of_eval
          intro i
          exact (measurable_pi_apply i.succ).comp measurable_snd
        have hhead : Measurable (fun p : (δ × β) × (Fin (n + 1) → α) =>
            p.2 0) :=
          (measurable_pi_apply 0).comp measurable_snd
        have hstep : Measurable (fun p : (δ × β) × (Fin (n + 1) → α) =>
            g (p.1.1, p.1.2, p.2 0)) :=
          hg.comp ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_snd.comp measurable_fst).prodMk hhead))
        have hT : Measurable (fun p : (δ × β) × (Fin (n + 1) → α) =>
            ((p.1.1, g (p.1.1, p.1.2, p.2 0)),
              fun i : Fin n => p.2 i.succ)) :=
          ((measurable_fst.comp measurable_fst).prodMk hstep).prodMk htail
        have hfun : (fun p : (δ × β) × (Fin (n + 1) → α) =>
              (List.ofFn p.2).foldl (fun b a => g (p.1.1, b, a)) p.1.2)
            = (fun q : (δ × β) × (Fin n → α) =>
              (List.ofFn q.2).foldl (fun b a => g (q.1.1, b, a)) q.1.2) ∘
              (fun p : (δ × β) × (Fin (n + 1) → α) =>
                ((p.1.1, g (p.1.1, p.1.2, p.2 0)),
                  fun i : Fin n => p.2 i.succ)) := by
          funext p
          show (List.ofFn p.2).foldl (fun b a => g (p.1.1, b, a)) p.1.2
            = (List.ofFn (fun i : Fin n => p.2 i.succ)).foldl
              (fun b a => g (p.1.1, b, a)) (g (p.1.1, p.1.2, p.2 0))
          simp only [List.ofFn_succ, List.foldl_cons]
        rw [hfun]
        exact ih.comp hT
  have hG : Measurable (fun q : (δ × β) × List α =>
      q.2.foldl (fun b a => g (q.1.1, b, a)) q.1.2) :=
    measurable_prod_list_of_ofFn hstrat
  have hFeq : (fun p : δ × β × List α =>
        p.2.2.foldl (fun b a => g (p.1, b, a)) p.2.1)
      = (fun q : (δ × β) × List α =>
        q.2.foldl (fun b a => g (q.1.1, b, a)) q.1.2) ∘
        ⇑(MeasurableEquiv.prodAssoc (α := δ) (β := β)
          (γ := List α)).symm := by
    funext p
    obtain ⟨d, b, l⟩ := p
    rfl
  rw [hFeq]
  exact hG.comp (MeasurableEquiv.prodAssoc (α := δ) (β := β)
    (γ := List α)).symm.measurable

/-- Structural recursion on a list with measurable base and step is measurable. -/
theorem measurable_list_rec {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace δ] {nil : δ → β} {cons : δ × α × List α × β → β}
    (hnil : Measurable nil) (hcons : Measurable cons) :
    Measurable (fun p : δ × List α =>
      List.rec (motive := fun _ => β) (nil p.1) (fun a l ih => cons (p.1, a, l, ih)) p.2) := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : δ × (Fin n → α) =>
      List.rec (motive := fun _ => β) (nil p.1)
        (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2)) := by
    intro n
    induction n with
    | zero =>
        have hfun : (fun p : δ × (Fin 0 → α) =>
              List.rec (motive := fun _ => β) (nil p.1)
                (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2))
            = fun p => nil p.1 := by
          funext p
          show List.rec (motive := fun _ => β) (nil p.1)
              (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2) = nil p.1
          have hnil0 : List.ofFn p.2 = [] :=
            List.length_eq_zero_iff.mp (List.length_ofFn (f := p.2))
          calc List.rec (motive := fun _ => β) (nil p.1)
                  (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2)
                = List.rec (motive := fun _ => β) (nil p.1)
                  (fun a l ih => cons (p.1, a, l, ih)) [] := by rw [hnil0]
            _ = nil p.1 := rfl
        rw [hfun]
        exact hnil.comp measurable_fst
    | succ n ih =>
        have htail : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            (fun i : Fin n => p.2 i.succ)) := by
          apply Measurable.of_eval
          intro i
          exact (measurable_pi_apply i.succ).comp measurable_snd
        have hpair : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            (p.1, fun i : Fin n => p.2 i.succ)) :=
          measurable_fst.prodMk htail
        have hR : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            List.rec (motive := fun _ => β) (nil p.1)
              (fun a l ih2 => cons (p.1, a, l, ih2))
              (List.ofFn (fun i : Fin n => p.2 i.succ))) :=
          ih.comp hpair
        have hof : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            List.ofFn (fun i : Fin n => p.2 i.succ)) :=
          (measurable_list_ofFn n).comp htail
        have hhead : Measurable (fun p : δ × (Fin (n + 1) → α) => p.2 0) :=
          (measurable_pi_apply 0).comp measurable_snd
        have hT : Measurable (fun p : δ × (Fin (n + 1) → α) =>
            (p.1, p.2 0, List.ofFn (fun i : Fin n => p.2 i.succ),
              List.rec (motive := fun _ => β) (nil p.1)
                (fun a l ih2 => cons (p.1, a, l, ih2))
                (List.ofFn (fun i : Fin n => p.2 i.succ)))) :=
          measurable_fst.prodMk (hhead.prodMk (hof.prodMk hR))
        have hfun : (fun p : δ × (Fin (n + 1) → α) =>
              List.rec (motive := fun _ => β) (nil p.1)
                (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2))
            = cons ∘ (fun p : δ × (Fin (n + 1) → α) =>
              (p.1, p.2 0, List.ofFn (fun i : Fin n => p.2 i.succ),
                List.rec (motive := fun _ => β) (nil p.1)
                  (fun a l ih2 => cons (p.1, a, l, ih2))
                  (List.ofFn (fun i : Fin n => p.2 i.succ)))) := by
          funext p
          show List.rec (motive := fun _ => β) (nil p.1)
              (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2)
            = cons (p.1, p.2 0, List.ofFn (fun i : Fin n => p.2 i.succ),
              List.rec (motive := fun _ => β) (nil p.1)
                (fun a l ih2 => cons (p.1, a, l, ih2))
                (List.ofFn (fun i : Fin n => p.2 i.succ)))
          calc List.rec (motive := fun _ => β) (nil p.1)
                  (fun a l ih => cons (p.1, a, l, ih)) (List.ofFn p.2)
                = List.rec (motive := fun _ => β) (nil p.1)
                  (fun a l ih => cons (p.1, a, l, ih))
                  (p.2 0 :: List.ofFn (fun i : Fin n => p.2 i.succ)) := by
                rw [List.ofFn_succ]
            _ = cons (p.1, p.2 0, List.ofFn (fun i : Fin n => p.2 i.succ),
                List.rec (motive := fun _ => β) (nil p.1)
                  (fun a l ih2 => cons (p.1, a, l, ih2))
                  (List.ofFn (fun i : Fin n => p.2 i.succ))) := rfl
        rw [hfun]
        exact hcons.comp hT
  exact measurable_prod_list_of_ofFn hstrat

/-- The equality test is measurable on a space with measurable diagonal. -/
theorem measurable_decide_eq {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    [DecidableEq α] : Measurable (fun p : α × α => decide (p.1 = p.2)) := by
  have heq : (fun p : α × α => decide (p.1 = p.2))
      = fun p => if p.1 = p.2 then true else false := by
    funext p
    by_cases h : p.1 = p.2 <;> simp [h]
  rw [heq]
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd)
    measurable_const measurable_const

/-- The membership test is jointly measurable on a space with measurable diagonal. -/
theorem measurable_list_mem {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    [DecidableEq α] : Measurable (fun p : α × List α => decide (p.1 ∈ p.2)) := by
  have hstrat : ∀ n : ℕ, Measurable (fun p : α × (Fin n → α) =>
      decide (p.1 ∈ List.ofFn p.2)) := by
    intro n
    induction n with
    | zero =>
        have hfun : (fun p : α × (Fin 0 → α) => decide (p.1 ∈ List.ofFn p.2))
            = fun _ => false := by
          funext p
          show decide (p.1 ∈ List.ofFn p.2) = false
          simp
        rw [hfun]
        exact measurable_const
    | succ n ih =>
        have htail : Measurable (fun p : α × (Fin (n + 1) → α) =>
            (fun i : Fin n => p.2 i.succ)) := by
          apply Measurable.of_eval
          intro i
          exact (measurable_pi_apply i.succ).comp measurable_snd
        have hpair : Measurable (fun p : α × (Fin (n + 1) → α) =>
            (p.1, fun i : Fin n => p.2 i.succ)) :=
          measurable_fst.prodMk htail
        have hMn : Measurable (fun p : α × (Fin (n + 1) → α) =>
            decide (p.1 ∈ List.ofFn (fun i : Fin n => p.2 i.succ))) :=
          ih.comp hpair
        have hhead : Measurable (fun p : α × (Fin (n + 1) → α) => p.2 0) :=
          (measurable_pi_apply 0).comp measurable_snd
        have hcond : MeasurableSet {p : α × (Fin (n + 1) → α) | p.1 = p.2 0} :=
          measurableSet_eq_fun measurable_fst hhead
        have hfun : (fun p : α × (Fin (n + 1) → α) =>
              decide (p.1 ∈ List.ofFn p.2))
            = fun p => if p.1 = p.2 0 then true
              else decide (p.1 ∈ List.ofFn (fun i : Fin n => p.2 i.succ)) := by
          funext p
          show decide (p.1 ∈ List.ofFn p.2)
            = if p.1 = p.2 0 then true
              else decide (p.1 ∈ List.ofFn (fun i : Fin n => p.2 i.succ))
          rw [List.ofFn_succ]
          by_cases h : p.1 = p.2 0 <;> simp [h, List.mem_cons]
        rw [hfun]
        exact Measurable.ite hcond measurable_const hMn
  exact measurable_prod_list_of_ofFn hstrat

/-- Duplicate removal is measurable on a space with measurable diagonal. -/
theorem measurable_list_dedup {α : Type*} [MeasurableSpace α] [MeasurableEq α]
    [DecidableEq α] : Measurable (List.dedup : List α → List α) := by
  have hstrat : ∀ n : ℕ, Measurable (fun v : Fin n → α =>
      (List.ofFn v).dedup) := by
    intro n
    induction n with
    | zero =>
        have h0 : ∀ v : Fin 0 → α, List.ofFn v = [] :=
          fun v => List.length_eq_zero_iff.mp (List.length_ofFn (f := v))
        have hfun : (fun v : Fin 0 → α => (List.ofFn v).dedup)
            = fun _ => [] := by
          funext v
          show (List.ofFn v).dedup = []
          rw [h0 v]
          exact List.dedup_nil
        rw [hfun]
        exact measurable_const
    | succ n ih =>
        have htail : Measurable
            (fun v : Fin (n + 1) → α => (fun i : Fin n => v i.succ)) := by
          apply Measurable.of_eval
          intro i
          exact measurable_pi_apply i.succ
        have hDn : Measurable (fun v : Fin (n + 1) → α =>
            (List.ofFn (fun i : Fin n => v i.succ)).dedup) :=
          ih.comp htail
        have hhead : Measurable (fun v : Fin (n + 1) → α => v 0) :=
          measurable_pi_apply 0
        have hcons : Measurable (fun v : Fin (n + 1) → α =>
            v 0 :: (List.ofFn (fun i : Fin n => v i.succ)).dedup) :=
          measurable_list_cons.comp (hhead.prodMk hDn)
        have hmem : MeasurableSet {p : α × List α | p.1 ∈ p.2} := by
          have hpre : {p : α × List α | p.1 ∈ p.2}
              = (fun p : α × List α => decide (p.1 ∈ p.2)) ⁻¹' {true} := by
            ext p
            simp
          rw [hpre]
          exact measurable_list_mem (measurableSet_singleton true)
        have hpairmem : Measurable (fun v : Fin (n + 1) → α =>
            (v 0, List.ofFn (fun i : Fin n => v i.succ))) :=
          hhead.prodMk ((measurable_list_ofFn n).comp htail)
        have hcond : MeasurableSet {v : Fin (n + 1) → α |
            v 0 ∈ List.ofFn (fun i : Fin n => v i.succ)} := by
          have hpre : {v : Fin (n + 1) → α |
                v 0 ∈ List.ofFn (fun i : Fin n => v i.succ)}
              = (fun v : Fin (n + 1) → α =>
                (v 0, List.ofFn (fun i : Fin n => v i.succ))) ⁻¹'
                {p : α × List α | p.1 ∈ p.2} := rfl
          rw [hpre]
          exact hpairmem hmem
        have hfun : (fun v : Fin (n + 1) → α => (List.ofFn v).dedup)
            = fun v => if v 0 ∈ List.ofFn (fun i : Fin n => v i.succ)
              then (List.ofFn (fun i : Fin n => v i.succ)).dedup
              else v 0 :: (List.ofFn (fun i : Fin n => v i.succ)).dedup := by
          funext v
          show (List.ofFn v).dedup
            = if v 0 ∈ List.ofFn (fun i : Fin n => v i.succ)
              then (List.ofFn (fun i : Fin n => v i.succ)).dedup
              else v 0 :: (List.ofFn (fun i : Fin n => v i.succ)).dedup
          rw [List.ofFn_succ]
          by_cases h : v 0 ∈ List.ofFn (fun i : Fin n => v i.succ)
          · rw [List.dedup_cons_of_mem h, ite_eq_left h]
          · rw [List.dedup_cons_of_notMem h, ite_eq_right h]
        rw [hfun]
        exact Measurable.ite hcond hDn hcons
  exact measurable_list_of_ofFn hstrat

/-- The event that some entry of a list lies in a measurable set is measurable. -/
theorem measurableSet_list_exists_mem {α : Type*} [MeasurableSpace α] {A : Set α}
    (hA : MeasurableSet A) : MeasurableSet {l : List α | ∃ a ∈ l, a ∈ A} := by
  rw [measurableSet_list_iff]
  intro n
  have hset : (fun v : Fin n → α => List.ofFn v) ⁻¹'
        {l : List α | ∃ a ∈ l, a ∈ A}
      = ⋃ i : Fin n, (fun v : Fin n → α => v i) ⁻¹' A := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ham, haA⟩
      rw [List.mem_ofFn] at ham
      obtain ⟨i, rfl⟩ := ham
      exact ⟨i, haA⟩
    · rintro ⟨i, hi⟩
      exact ⟨v i, List.mem_ofFn.mpr ⟨i, rfl⟩, hi⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  exact (measurable_pi_apply i) hA

/-- Measurability of the oracle primitives, kept separate from `Oracles`: the
collision test is measurable and the local planner, steering function and cost
are jointly measurable (with the discrete σ-algebras on `Bool` and `ℚ`). -/
structure OraclesMeasurable {C : Type} [MeasurableSpace C] (O : Oracles C) : Prop where
  /-- The collision test is measurable. -/
  free : Measurable O.free
  /-- The local planner is jointly measurable. -/
  link : Measurable (fun p : C × C => O.link p.1 p.2)
  /-- The steering function is jointly measurable. -/
  steer : Measurable (fun p : C × C => O.steer p.1 p.2)
  /-- The cost is jointly measurable. -/
  cost : Measurable (fun p : C × C => O.cost p.1 p.2)

end Cslib.Planning.MotionPlanning.SamplingPlanners
