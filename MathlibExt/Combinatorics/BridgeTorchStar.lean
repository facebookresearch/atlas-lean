/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.BridgeTorchTwo
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bridge and torch on star graphs

The optimal time is bounded below by the cost of sending the slowest remaining people
in batches and above by the ordinary bridge time. Enough torches attain the lower bound.
-/

set_option autoImplicit false

namespace MetaMathlibExt.BridgeTorchGeneralizations

@[expose] public section

open Finset

/-- **Movement in the star model.** Consider the star graph $\mathcal{S}(k)$ with center $o$ and
leaves $u_0, \dots, u_{k-1}$, and $n$ persons $0, \dots, n-1$, where person $p$ has crossing time
$p + 1$. A movement consists of a set $P$ of persons, a leaf $u_j$ and a direction: the persons in
$P$ carry one torch along the edge $\{o, u_j\}$, outward from $o$ to $u_j$ or inward from $u_j$ to
$o$. No condition is imposed on $P$ here (it may even be empty); which movements may be made
together is part of the definition of a legal step.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
structure StarMove (n k : ℕ) where
  /-- The persons crossing together. -/
  persons : Finset (Fin n)
  /-- The leaf of the edge traversed. -/
  leaf : Fin k
  /-- Whether the movement goes from the center to the leaf. -/
  outward : Bool
  deriving DecidableEq

/-- **Start vertex of a star movement.** Let $\mathcal{S}(k)$ be the star graph with center $o$
and $k$ leaves. A movement in the star model on $\mathcal{S}(k)$ along the edge $\{o, u\}$ between
the center $o$ and a leaf $u$ starts at $o$ if it goes outward (from the center to the leaf) and
at $u$ otherwise.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def StarMove.src {n k : ℕ} (m : StarMove n k) : Option (Fin k) :=
  if m.outward then none else some m.leaf

/-- **End vertex of a star movement.** In the star model on the star graph with center $o$ and
leaves $u_0, \dots, u_{k-1}$, a torch-movement along the edge $\{o, u_\ell\}$ ends at the leaf
$u_\ell$ if it goes outward from $o$, and at the center $o$ otherwise.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def StarMove.dst {n k : ℕ} (m : StarMove n k) : Option (Fin k) :=
  if m.outward then some m.leaf else none

/-- **Legal parallel steps in the star model.** Let $\mathcal{S}(k)$ be the star graph with a
center and $k$ leaves. Consider a configuration of the star model on $\mathcal{S}(k)$ with $n$
persons, given by the vertex $\mathrm{pos}(p)$ of each person $p$ and the number $\mathrm{tor}(v)$
of torches at each vertex $v$. A parallel step, a list of star movements, is legal from this
configuration when every movement carries one or two persons, all standing at the movement's
start vertex; the movements of the step carry pairwise disjoint sets of persons and traverse
pairwise distinct edges; and for every vertex $v$, at most $\mathrm{tor}(v)$ movements of the
step start at $v$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def IsStarStep {n k : ℕ} (pos : Fin n → Option (Fin k)) (tor : Option (Fin k) → ℕ)
    (step : List (StarMove n k)) : Prop :=
  (∀ m ∈ step, 1 ≤ m.persons.card ∧ m.persons.card ≤ 2 ∧ ∀ p ∈ m.persons, pos p = m.src) ∧
    (step.map StarMove.leaf).Nodup ∧ step.Pairwise (fun a b => Disjoint a.persons b.persons) ∧
    ∀ v, (step.filter fun m => m.src = v).length ≤ tor v

instance {n k : ℕ} (pos : Fin n → Option (Fin k)) (tor : Option (Fin k) → ℕ)
    (step : List (StarMove n k)) : Decidable (IsStarStep pos tor step) := by
  unfold IsStarStep; infer_instance

/-- **Positions after a step in the star model.** Given the vertex $\mathrm{pos}(p)$ of each person
$p$ and a step $S$, a finite list of movements, the position of $p$ after $S$ is the end vertex of
the first movement of $S$ whose persons include $p$ (its leaf if the movement is outward, the
center if it is inward), and $\mathrm{pos}(p)$ if no movement of $S$ includes $p$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def starStepPos {n k : ℕ} (pos : Fin n → Option (Fin k)) (step : List (StarMove n k)) :
    Fin n → Option (Fin k) :=
  fun p => match step.find? (fun m => decide (p ∈ m.persons)) with
    | some m => m.dst
    | none => pos p

/-- **Torch counts after a step in the star model.** Given the number $\mathrm{tor}(v)$ of torches
at each vertex $v$ of the star graph and a step $S$, a finite list of movements, the number of
torches at $v$ after $S$ is $\max(\mathrm{tor}(v) - a, 0) + b$, where $a$ is the number of
movements of $S$ that start at $v$ and $b$ is the number of movements of $S$ that end at $v$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def starStepTorch {n k : ℕ} (tor : Option (Fin k) → ℕ) (step : List (StarMove n k)) :
    Option (Fin k) → ℕ :=
  fun v => tor v - (step.filter fun m => m.src = v).length +
    (step.filter fun m => m.dst = v).length

/-- **Duration of a step in the star model.** A step is a finite list of movements carried out in
parallel. Its duration is the largest crossing time $p + 1$ of a person $p$ moving in one of its
movements, and $0$ if no person moves.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def starStepDuration {n k : ℕ} (step : List (StarMove n k)) : ℕ :=
  (step.map fun m => m.persons.sup fun p => (p : ℕ) + 1).foldr max 0

/-- **Legal runs in the star model.** A configuration of the star model assigns to each person $p$
a vertex $\mathrm{pos}(p)$ of the star graph $\mathcal{S}(k)$ and to each vertex $v$ a number
$\mathrm{tor}(v)$ of torches. A finite sequence $\sigma = (S_1, \dots, S_\ell)$ of steps, each a
finite list of movements, is a legal run from the configuration $(\mathrm{pos}, \mathrm{tor})$
when each step $S_i$ is legal from the configuration reached after $S_1, \dots, S_{i-1}$ (a step
updates the positions of the persons and the torch counts) and every person is at a leaf in the
configuration reached after all of $\sigma$. In particular, the empty sequence is a legal run
exactly when every person already stands at a leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def starRunFrom {n k : ℕ} :
    (Fin n → Option (Fin k)) → (Option (Fin k) → ℕ) → List (List (StarMove n k)) → Bool
  | pos, _, [] => decide (∀ p, (pos p).isSome)
  | pos, tor, step :: σ =>
      decide (IsStarStep pos tor step) &&
        starRunFrom (starStepPos pos step) (starStepTorch tor step) σ

/-- **Star schedules.** Consider the star model on the star graph $\mathcal{S}(k)$, which has a
center and $k$ leaves, with $n$ persons and $t$ torches. A finite list $\sigma$ of parallel steps
(each a list of star movements) is a star schedule when the following holds. Start from the
configuration with every person and all $t$ torches at the center and no torch at any leaf, and
apply the steps of $\sigma$ in order, where a step moves the persons of each of its movements to
the movement's end vertex and moves one torch from the start vertex to the end vertex of each
movement. Every step must be legal from the configuration it is applied to, and in the final
configuration every person is at some leaf.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
def IsStarSchedule (n k t : ℕ) (σ : List (List (StarMove n k))) : Prop :=
  starRunFrom (fun _ => none) (fun v => if v = none then t else 0) σ = true

/-- **Optimal time in the star model.** For $n$ persons, $k$ edges and $t$ torches, $T(n, k, t)$
is the smallest total duration of a star schedule, where the total duration of a schedule is the
sum of the durations of its steps. If no star schedule exists (for example when $n \ge 1$ and
$k = 0$ or $t = 0$), then $T(n, k, t) = 0$ by convention.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25. -/
noncomputable def starTime (n k t : ℕ) : ℕ :=
  sInf {d | ∃ σ, IsStarSchedule n k t σ ∧ (σ.map starStepDuration).sum = d}

/-- **Every star schedule bounds the optimal time.** Let $T(n, k, t)$ be the optimal time of
the star model with $n$ persons, $k$ edges and $t$ torches. For every star schedule $\sigma$ with
$n$ persons, $k$ edges and $t$ torches, $T(n, k, t)$ is at most the total duration of $\sigma$,
the sum of the durations of its steps.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25, definition of `T(n, k, t)`. -/
theorem starTime_le {n k t : ℕ} {σ : List (List (StarMove n k))}
    (hσ : IsStarSchedule n k t σ) : starTime n k t ≤ (σ.map starStepDuration).sum :=
  Nat.sInf_le ⟨σ, hσ, rfl⟩

/-- **Two persons crossing a one-edge star.** In the star model with $2$ persons (crossing times
$1$ and $2$), a star graph with $1$ edge and $1$ torch, the sequence of one step consisting of a
single movement that carries both persons and the torch from the center to the leaf is a star
schedule, and its total duration is $2$.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25, characteristic example. -/
theorem isStarSchedule_two_one_one :
    IsStarSchedule 2 1 1 [[⟨Finset.univ, 0, true⟩]] ∧
      ([[(⟨Finset.univ, 0, true⟩ : StarMove 2 1)]].map starStepDuration).sum = 2 := by
  unfold IsStarSchedule
  constructor <;> decide

/-- **Example: no return from a leaf without a torch.** In the star model on the star graph
with a center and a single leaf, with one person, suppose the person stands at the leaf, the only
torch is at the center and no torch is at the leaf. Then the parallel step consisting of the
single movement that carries the person from the leaf back to the center is not legal.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Section 4, Definition 25, characteristic example. -/
theorem not_isStarStep_return_without_torch :
    ¬ IsStarStep (fun _ : Fin 1 => (some 0 : Option (Fin 1)))
      (fun v => if v = none then 1 else 0) [⟨Finset.univ, 0, false⟩] := by
  decide

private def passengers {n k : ℕ} : List (StarMove n k) → Finset (Fin n)
  | [] => ∅
  | m :: ms => m.persons ∪ passengers ms

private theorem mem_passengers {n k : ℕ} {p : Fin n} {step : List (StarMove n k)} :
    p ∈ passengers step ↔ ∃ m ∈ step, p ∈ m.persons := by
  induction step with
  | nil => simp [passengers]
  | cons m ms ih => simp [passengers, ih]

private theorem passengers_card {n k : ℕ} {step : List (StarMove n k)}
    (h : ∀ m ∈ step, m.persons.card ≤ 2) : (passengers step).card ≤ 2 * step.length := by
  induction step with
  | nil => simp [passengers]
  | cons m ms ih =>
    have hm := h m (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simpa only [passengers, List.length_cons] using
      (card_union_le m.persons (passengers ms)).trans (by omega)

private theorem duration_ge {n k : ℕ} {p : Fin n} {step : List (StarMove n k)}
    (hp : p ∈ passengers step) : p.val + 1 ≤ starStepDuration step := by
  induction step with
  | nil => simp [passengers] at hp
  | cons m ms ih =>
    rcases mem_union.mp hp with hm | hms
    · exact le_max_of_le_left (Finset.le_sup (f := fun i : Fin n => i.val + 1) hm)
    · exact le_max_of_le_right (ih hms)

private theorem sum_departures {α β : Type*} [DecidableEq β] [Fintype β]
    (f : α → β) (l : List α) :
    (∑ v, (l.filter fun a => f a = v).length) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h (v : β) : ((a :: l).filter fun x => f x = v).length =
        (if f a = v then 1 else 0) + (l.filter fun x => f x = v).length := by
      by_cases hv : f a = v <;> simp [hv, Nat.add_comm]
    simp [h, Finset.sum_add_distrib, ih, Nat.add_comm]

private theorem run_capacity {n k t : ℕ} {pos : Fin n → Option (Fin k)}
    {tor : Option (Fin k) → ℕ} {σ : List (List (StarMove n k))}
    (ht : ∑ v, tor v = t) (hσ : starRunFrom pos tor σ = true) :
    ∀ step ∈ σ, (passengers step).card ≤ 2 * min k t := by
  induction σ generalizing pos tor with
  | nil => simp
  | cons st σ ih =>
    simp only [starRunFrom, Bool.and_eq_true, decide_eq_true_eq] at hσ
    obtain ⟨legal, tail⟩ := hσ
    have h₁ : st.length ≤ k := by
      have h := Finset.card_le_univ (st.map StarMove.leaf).toFinset
      simpa [List.toFinset_card_of_nodup legal.2.1] using h
    have h₂ : st.length ≤ t := by
      rw [← sum_departures StarMove.src st, ← ht]
      exact Finset.sum_le_sum fun v _ => legal.2.2.2 v
    have htor : ∑ v, starStepTorch tor st v = t := by
      simp only [starStepTorch, Finset.sum_add_distrib, Finset.sum_tsub_distrib univ
        (fun v _ => legal.2.2.2 v), sum_departures, ht]
      omega
    intro step hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact (passengers_card fun a ha => (legal.1 a ha).2.1).trans
        (Nat.mul_le_mul_left 2 (le_min h₁ h₂))
    · exact ih htor tail step hs

private theorem run_covers {n k : ℕ} {pos : Fin n → Option (Fin k)}
    {tor : Option (Fin k) → ℕ} {σ : List (List (StarMove n k))}
    (hσ : starRunFrom pos tor σ = true) (p : Fin n) (hp : pos p = none) :
    ∃ step ∈ σ, p ∈ passengers step := by
  induction σ generalizing pos tor with
  | nil =>
    simp only [starRunFrom, decide_eq_true_eq] at hσ
    simpa [hp] using hσ p
  | cons st σ ih =>
    by_cases hm : p ∈ passengers st
    · exact ⟨st, by simp, hm⟩
    · simp only [starRunFrom, Bool.and_eq_true] at hσ
      have hfind : st.find? (fun m => decide (p ∈ m.persons)) = none := by
        apply List.find?_eq_none.mpr
        simpa [mem_passengers] using hm
      obtain ⟨s, hs, h⟩ := ih hσ.2 (by simpa [starStepPos, hfind] using hp)
      exact ⟨s, List.mem_cons_of_mem _ hs, h⟩

-- Remove the step carrying the slowest member of F. Its cost is at least |F|,
-- and at most 2m people lose their covering step.
private theorem cover_bound {n k m : ℕ} (s : ℕ) (F : Finset (Fin n))
    (σ : List (List (StarMove n k)))
    (hcap : ∀ st ∈ σ, (passengers st).card ≤ 2 * m)
    (hcov : ∀ p ∈ F, ∃ st ∈ σ, p ∈ passengers st) :
    (s : ℝ) * F.card - m * s * (s - 1 : ℝ) ≤ (σ.map starStepDuration).sum := by
  induction s generalizing F σ with
  | zero => simp
  | succ s ih =>
    by_cases he : F.Nonempty
    · let p := F.max' he
      obtain ⟨st, hst, hp⟩ := hcov p (F.max'_mem he)
      have hcard : F.card ≤ p.val + 1 := by
        calc F.card = (F.image Fin.val).card := (card_image_of_injective _ Fin.val_injective).symm
             _ ≤ (range (p.val + 1)).card := card_le_card (by
               intro a ha
               obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
               exact mem_range.mpr (Nat.lt_succ_of_le (F.le_max' i hi)))
             _ = _ := card_range _
      have hc := hcap st hst
      obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hst
      have hrest := ih (F \ passengers st) (l ++ r) (by
        intro a ha
        apply hcap
        simpa only [List.mem_append, List.mem_cons] using
          (List.mem_append.mp ha).imp_right (Or.inr (a := a = st))) (by
        intro i hi
        obtain ⟨hF, hst⟩ := mem_sdiff.mp hi
        obtain ⟨a, ha, h⟩ := hcov i hF
        have hne : a ≠ st := by rintro rfl; exact hst h
        exact ⟨a, by simpa [hne] using ha, h⟩)
      have hdiff : F.card ≤ (F \ passengers st).card + 2 * m :=
        (card_le_card (show F ⊆ (F \ passengers st) ∪ passengers st by
          intro i hi
          by_cases h : i ∈ passengers st <;> simp [hi, h])).trans
          ((card_union_le _ _).trans (Nat.add_le_add_left hc _))
      have hd : (F.card : ℝ) ≤ starStepDuration st := by
        exact_mod_cast hcard.trans (duration_ge hp)
      have hr : (F.card : ℝ) ≤ (F \ passengers st).card + 2 * (m : ℝ) := by
        exact_mod_cast hdiff
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        Nat.cast_add, Nat.cast_succ] at hrest ⊢
      nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) s)]
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp only [card_empty, Nat.cast_zero, mul_zero, Nat.cast_succ]
      have : 0 ≤ (m : ℝ) * (s + 1) * s := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) (σ.map starStepDuration).sum]

private def bridgePeople (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  univ.filter fun p => p.val + 1 ∈ A

private theorem bridge_image {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n) :
    (bridgePeople n A).image (fun p => p.val + 1) = A := by
  ext i
  simp only [bridgePeople, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hi
    have bounds := mem_Icc.mp (hA hi)
    have hid : i - 1 + 1 = i := by omega
    exact ⟨⟨i - 1, by omega⟩, hid ▸ hi, hid⟩

-- Use a single edge and keep one torch on the active side of the bridge.
private theorem simulate_bridge {n k : ℕ} (leaf : Fin k) {σ : List (Finset ℕ)}
    {L : Finset ℕ} {side : Bool} {pos : Fin n → Option (Fin k)} {tor : Option (Fin k) → ℕ}
    (hL : L ⊆ Icc 1 n) (hpos : ∀ p, pos p = if p.val + 1 ∈ L then none else some leaf)
    (htor : 0 < tor (if side then none else some leaf))
    (hσ : bridgeScheduleFrom 2 (Icc 1 n) L side σ = true) :
    ∃ τ, starRunFrom pos tor τ = true ∧ (τ.map starStepDuration).sum ≤ scheduleCost σ := by
  induction σ generalizing L side pos tor with
  | nil =>
    simp only [bridgeScheduleFrom, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hσ
    exact ⟨[], by simp [starRunFrom, hpos, hσ.1], by simp [scheduleCost]⟩
  | cons A σ ih =>
    let next := if side then L \ A else L ∪ A
    have ⟨⟨hne, hc, hsub⟩, htail⟩ :
        (A.Nonempty ∧ A.card ≤ 2 ∧ A ⊆ (if side then L else Icc 1 n \ L)) ∧
          bridgeScheduleFrom 2 (Icc 1 n) next (!side) σ = true := by
      cases side <;> simpa [bridgeScheduleFrom, next] using hσ
    have hA : A ⊆ Icc 1 n := by
      cases side
      · exact hsub.trans sdiff_subset
      · exact hsub.trans hL
    let a : StarMove n k := ⟨bridgePeople n A, leaf, side⟩
    have hcard : a.persons.card = A.card := by
      rw [← bridge_image hA, card_image_of_injective]
      intro i j h
      exact Fin.ext (Nat.add_right_cancel h)
    have hm (p : Fin n) : p ∈ a.persons ↔ p.val + 1 ∈ A := by simp [a, bridgePeople]
    have legal : IsStarStep pos tor [a] := by
      refine ⟨?_, by simp, by simp, ?_⟩
      · simp only [List.mem_singleton, forall_eq, hcard]
        refine ⟨hne.card_pos, hc, ?_⟩
        intro p hp
        have := hsub ((hm p).mp hp)
        cases side <;> simp_all [a, StarMove.src]
      · intro v
        by_cases h : a.src = v
        · subst v
          simpa [a, StarMove.src] using (Nat.succ_le_of_lt htor)
        · simp [h]
    have hnext : next ⊆ Icc 1 n := by
      cases side
      · exact union_subset hL hA
      · exact sdiff_subset.trans hL
    have hpos' (p : Fin n) : starStepPos pos [a] p =
        if p.val + 1 ∈ next then none else some leaf := by
      by_cases hp : p.val + 1 ∈ A
      · have ha := (hm p).2 hp
        have hs := hsub hp
        cases side <;> simp_all [starStepPos, StarMove.dst, next, a, bridgePeople]
      · have ha : p ∉ a.persons := fun h => hp ((hm p).1 h)
        cases side <;> simp [starStepPos, ha, hpos, next, hp]
    have htor' : 0 < starStepTorch tor [a] (if !side then none else some leaf) := by
      cases side <;> simp [starStepTorch, a, StarMove.src, StarMove.dst]
    obtain ⟨τ, hr, hcost⟩ := ih hnext hpos' htor' htail
    refine ⟨[a] :: τ, by simp [starRunFrom, legal, hr], ?_⟩
    have hd : starStepDuration [a] ≤ A.sup id := by
      simp only [starStepDuration, List.map_cons, List.map_nil, List.foldr_cons,
        List.foldr_nil, Nat.zero_le, max_eq_left]
      exact Finset.sup_le fun p hp => Finset.le_sup (f := id) ((hm p).mp hp)
    exact Nat.add_le_add hd hcost

-- Positivity of the known bridge optimum rules out the empty set of schedules.
private theorem bridge_witness {n : ℕ} (hn : 2 ≤ n) :
    ∃ σ, IsBridgeSchedule 2 n σ ∧ scheduleCost σ = bridgeTime 2 n := by
  apply Nat.sInf_mem (s := {d | ∃ σ, IsBridgeSchedule 2 n σ ∧ scheduleCost σ = d})
  by_contra! h
  have hz : bridgeTime 2 n = 0 := by simp [bridgeTime, h]
  have hform := bridgeTime_two_closed_form n hn
  rw [hz, Nat.cast_zero] at hform
  have hsign : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := neg_one_pow_eq_or ..
  have h₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rcases hsign with h | h <;> nlinarith [sq_nonneg (n : ℝ)]

private theorem duration_le {n k a : ℕ} (st : List (StarMove n k))
    (h : ∀ x ∈ st, ∀ p ∈ x.persons, p.val < a) : starStepDuration st ≤ a := by
  induction st with
  | nil => exact Nat.zero_le _
  | cons x st ih =>
    apply max_le
    · exact Finset.sup_le fun p hp => h x (by simp) p hp
    · exact ih fun y hy => h y (by simp [hy])

-- Pair consecutive people in the interval [cut, a), one pair per leaf.
private theorem batch_step {n k m a : ℕ} (ha : a ≤ n) (hk : m ≤ k)
    (pos : Fin n → Option (Fin k)) (tor : Option (Fin k) → ℕ)
    (hpos : ∀ p : Fin n, pos p = none ↔ p.val < a) (htor : (a + 1) / 2 ≤ tor none) :
    let cut := a - 2 * m
    ∃ st : List (StarMove n k), IsStarStep pos tor st ∧
      (∀ p : Fin n, starStepPos pos st p = none ↔ p.val < cut) ∧
      (cut + 1) / 2 ≤ starStepTorch tor st none ∧ starStepDuration st ≤ a := by
  intro cut
  let b := (a - cut + 1) / 2
  have hcut : cut = a - 2 * m := rfl
  have hb : b ≤ k := by dsimp [b]; omega
  let move (j : Fin b) : StarMove n k :=
    ⟨univ.filter (fun p : Fin n => cut + 2 * j.val ≤ p.val ∧
      p.val < cut + 2 * j.val + 2 ∧ p.val < a), ⟨j.val, lt_of_lt_of_le j.isLt hb⟩, true⟩
  let st := List.ofFn move
  have hmem (j : Fin b) (p : Fin n) : p ∈ (move j).persons ↔
      cut + 2 * j.val ≤ p.val ∧ p.val < cut + 2 * j.val + 2 ∧ p.val < a := by simp [move]
  have hsrc (x) (hx : x ∈ st) : x.src = none := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    rfl
  have hdst (x) (hx : x ∈ st) : x.dst ≠ none := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    simp [move, StarMove.dst]
  have ht : st.length ≤ tor none := by simp only [st, List.length_ofFn]; dsimp [b]; omega
  have hfilter : (st.filter fun x => x.src = none) = st :=
    List.filter_eq_self.mpr fun x hx => by simp [hsrc x hx]
  refine ⟨st, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    have hj : j.val < (a - cut + 1) / 2 := j.isLt
    have hlo : cut + 2 * j.val < a := by omega
    have hex : (move j).persons.Nonempty :=
      ⟨⟨cut + 2 * j.val, lt_of_lt_of_le hlo ha⟩, (hmem _ _).2 ⟨le_rfl, by dsimp; omega, hlo⟩⟩
    refine ⟨hex.card_pos, ?_, fun p hp => (hpos p).2 ((hmem _ _).1 hp).2.2⟩
    have hsub : ((move j).persons.image Fin.val) ⊆
        Ico (cut + 2 * j.val) (cut + 2 * j.val + 2) := by
      intro i hi
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
      exact mem_Ico.mpr ⟨((hmem _ _).1 hp).1, ((hmem _ _).1 hp).2.1⟩
    simpa [card_image_of_injective _ Fin.val_injective] using card_le_card hsub
  · rw [List.map_ofFn, List.nodup_iff_pairwise_ne, List.pairwise_ofFn]
    intro i j hij heq
    exact (Fin.ne_of_lt hij) (Fin.ext (congrArg (Fin.val (n := k)) heq))
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    apply disjoint_left.mpr
    intro p hi hj
    have hl := ((hmem j p).1 hj).1
    have hu := ((hmem i p).1 hi).2.1
    change i.val < j.val at hij
    omega
  · intro v
    cases v with
    | none => simpa [hfilter] using ht
    | some v =>
      have : (st.filter fun x => x.src = some v) = [] :=
        List.filter_eq_nil_iff.mpr fun x hx => by simp [hsrc x hx]
      simp [this]
  · intro p
    unfold starStepPos
    split
    next x hx =>
      obtain ⟨j, hj⟩ := List.mem_ofFn.mp (List.mem_of_find?_eq_some hx)
      have hp : p ∈ x.persons := by simpa only [decide_eq_true_eq] using List.find?_some hx
      have hc := ((hmem j p).1 (hj ▸ hp)).1
      simp [hdst x (List.mem_of_find?_eq_some hx)]
      omega
    next hx =>
      rw [hpos]
      have hnone := List.find?_eq_none.mp hx
      constructor
      · intro hp
        by_contra! hge
        let j : Fin b := ⟨(p.val - cut) / 2, by dsimp [b]; omega⟩
        have hj : p ∈ (move j).persons := (hmem _ _).2 (by dsimp [j]; omega)
        exact hnone (move j) (List.mem_ofFn.mpr ⟨j, rfl⟩) (by simpa using hj)
      · omega
  · have : (st.filter fun x => x.dst = none) = [] :=
      List.filter_eq_nil_iff.mpr fun x hx => by simp [hdst x hx]
    simp only [starStepTorch, hfilter, this, List.length_nil, Nat.add_zero, st, List.length_ofFn]
    dsimp [b]
    omega
  · apply duration_le
    intro x hx p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact ((hmem _ _).1 hp).2.2

-- Repeat the outward step until the remaining interval is empty.
private theorem batch_run {n k m : ℕ} (hk : m ≤ k) (s a : ℕ) (ha : a ≤ n)
    (hi : a ≤ 2 * m * s) (lo : s = 0 ∨ 2 * m * (s - 1) < a)
    (pos : Fin n → Option (Fin k)) (tor : Option (Fin k) → ℕ)
    (hpos : ∀ p : Fin n, pos p = none ↔ p.val < a) (htor : (a + 1) / 2 ≤ tor none) :
    ∃ σ, starRunFrom pos tor σ = true ∧
      ((σ.map starStepDuration).sum : ℝ) ≤ s * a - m * s * (s - 1 : ℝ) := by
  induction s generalizing a pos tor with
  | zero =>
    have hzero : a = 0 := by simpa using hi
    refine ⟨[], ?_, by simp⟩
    simp only [starRunFrom, decide_eq_true_eq]
    intro p
    cases hp : pos p with
    | none => simpa [hzero] using (hpos p).1 hp
    | some v => rfl
  | succ s ih =>
    have hlo : 2 * m * s < a := by simpa using lo
    rw [Nat.mul_succ] at hi
    obtain ⟨st, legal, hp, ht, hd⟩ := batch_step ha hk pos tor hpos htor
    have hsmall : a - 2 * m ≤ n := by omega
    have hnext : s = 0 ∨ 2 * m * (s - 1) < a - 2 * m := by
      cases s with
      | zero => exact Or.inl rfl
      | succ s => simp only [Nat.mul_succ] at hlo; exact Or.inr (by simp; omega)
    obtain ⟨σ, hr, hc⟩ := ih _ hsmall (by omega) hnext _ _ hp ht
    refine ⟨st :: σ, by simp [starRunFrom, legal, hr], ?_⟩
    have hcost : (starStepDuration st : ℝ) ≤ a := by exact_mod_cast hd
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_succ]
    cases s with
    | zero =>
      simp at hc
      simpa [hc] using hcost
    | succ s =>
      have hma : 2 * m ≤ a := by rw [Nat.mul_succ] at hlo; omega
      rw [Nat.cast_sub hma] at hc
      push_cast at hc ⊢
      linarith only [hcost, hc]

private theorem batch_formula {n m q r : ℕ} (hm : 0 < m)
    (he : n = 2 * m * q + r) (hr : r < 2 * m) :
    let s := ⌈(n : ℚ) / (2 * m)⌉₊
    ((s * n : ℕ) : ℝ) - m * s * (s - 1) = (n : ℝ) ^ 2 / (4 * m) + n / 2 +
        r * (2 * m - r) / (4 * m) ∧
      (n : ℝ) ^ 2 / (4 * m) + n / 2 ≤ ((s * n : ℕ) : ℝ) - m * s * (s - 1) := by
  intro s
  have hden : 0 < 2 * (m : ℚ) := by positivity
  have hnq : (n : ℚ) = 2 * m * q + r := by exact_mod_cast he
  have hnr : (n : ℝ) = 2 * m * q + r := by exact_mod_cast he
  suffices heq : ((s * n : ℕ) : ℝ) - m * s * (s - 1) =
      (n : ℝ) ^ 2 / (4 * m) + n / 2 + r * (2 * m - r) / (4 * m) by
    refine ⟨heq, ?_⟩
    rw [heq]
    have hdiff : (r : ℝ) ≤ 2 * m := by exact_mod_cast hr.le
    exact le_add_of_nonneg_right (by positivity)
  by_cases hz : r = 0
  · subst r
    have hs : s = q := by
      have : (n : ℚ) / (2 * m) = q := (div_eq_iff hden.ne').2 (by simpa [mul_comm] using hnq)
      simp [s, this]
    rw [hs, Nat.cast_mul, hnr]
    push_cast
    field_simp
    ring
  · have hrq : (r : ℚ) < 2 * m := by exact_mod_cast hr
    have hrpos : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_ne_zero hz
    have hs : s = q + 1 := by
      apply (Nat.ceil_eq_iff (Nat.succ_ne_zero q)).2
      simp only [Nat.add_one_sub_one, Nat.cast_succ, lt_div_iff₀ hden, div_le_iff₀ hden]
      constructor <;> linarith
    rw [hs, Nat.cast_mul, hnr]
    push_cast
    field_simp
    ring

/-- **Bridge and torch on star graphs.** Consider the star model with $n \ge 2$ persons of crossing
times $1, \dots, n$, $k \ge 1$ edges and $t \ge 1$ torches, let $T(n, k, t)$ be its optimal time,
and let $m = \min(k, t)$ and $s = \lceil n/(2m) \rceil$. Let $T(n)$ be the optimal crossing time
of $n$ persons with crossing times $1, \dots, n$ on a bridge of capacity $2$ with one torch. Then
$$sn - ms(s-1) \le T(n, k, t) \le T(n),$$
and the left inequality is an equality whenever $t \ge \lceil n/2 \rceil$. Moreover, for all
natural numbers $q$ and $r$ with $n = 2mq + r$ and $r < 2m$,
$$sn - ms(s-1) = \frac{n^2}{4m} + \frac{n}{2} + \frac{r(2m-r)}{4m},$$
and this is at least $n^2/(4m) + n/2$.

For $n \ge 2$ the closed form $T(n) = n^2/4 + 3n - 5 + ((-1)^n - 1)/8$ is Theorem 1 of the same
paper.

Source: Thang Pang Ern and Gerard Sayson, *Some Generalizations of the Bridge
and Torch Problem*, Journal of Integer Sequences 29 (2026), Article 26.5.6,
Theorem 26 (`jis-2026-26.5.6-thm-26`). -/
public theorem starTime_bounds (n k t : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    let m := min k t
    let s := ⌈(n : ℚ) / (2 * m)⌉₊
    ((s * n : ℕ) : ℝ) - m * s * (s - 1) ≤ starTime n k t ∧
      starTime n k t ≤ bridgeTime 2 n ∧
      ((n + 1) / 2 ≤ t → (starTime n k t : ℝ) = (s * n : ℕ) - m * s * (s - 1)) ∧
      ∀ q r : ℕ, n = 2 * m * q + r → r < 2 * m →
        ((s * n : ℕ) : ℝ) - m * s * (s - 1) = (n : ℝ) ^ 2 / (4 * m) + n / 2 +
            r * (2 * m - r) / (4 * m) ∧
          (n : ℝ) ^ 2 / (4 * m) + n / 2 ≤ ((s * n : ℕ) : ℝ) - m * s * (s - 1) := by
  intro m s
  have hm : 0 < m := lt_min hk ht
  let pos : Fin n → Option (Fin k) := fun _ => none
  let tor : Option (Fin k) → ℕ := fun v => if v = none then t else 0
  have hp (p : Fin n) : pos p = none ↔ p.val < n := by simp [pos]
  obtain ⟨σ, hσ, heσ⟩ := bridge_witness hn
  let leaf : Fin k := ⟨0, hk⟩
  obtain ⟨τ, hτ, hcost⟩ := simulate_bridge (side := true) (pos := pos) (tor := tor) leaf
    (Subset.rfl) (fun p => by simp [pos, Nat.succ_le_of_lt p.isLt])
    (by simpa [tor] using (show 0 < t from ht)) hσ
  have hupper : starTime n k t ≤ bridgeTime 2 n :=
    (starTime_le (show IsStarSchedule n k t τ from hτ)).trans (heσ ▸ hcost)
  obtain ⟨τ', hτ', heτ'⟩ := Nat.sInf_mem
    (s := {d | ∃ τ, IsStarSchedule n k t τ ∧ (τ.map starStepDuration).sum = d})
    ⟨_, τ, hτ, rfl⟩
  change (τ'.map starStepDuration).sum = starTime n k t at heτ'
  have hrun : starRunFrom pos tor τ' = true := hτ'
  have hlow := cover_bound (m := m) s univ τ'
    (run_capacity (by simp [tor] : ∑ v, tor v = t) hrun)
    (fun p _ => run_covers hrun p rfl)
  simp only [card_univ, Fintype.card_fin, heτ'] at hlow
  refine ⟨by simpa [Nat.cast_mul] using hlow, hupper, ?_, fun q r => batch_formula hm⟩
  intro hmany
  have hden : 0 < 2 * (m : ℚ) := by positivity
  have hnq : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < s := Nat.ceil_pos.mpr (div_pos hnq hden)
  have ⟨hlo, hhi⟩ := (Nat.ceil_eq_iff hs.ne').mp (show ⌈(n : ℚ) / (2 * m)⌉₊ = s from rfl)
  have hi : n ≤ 2 * m * s := by
    exact_mod_cast (mul_comm (s : ℚ) _ ▸ (div_le_iff₀ hden).mp hhi)
  have lo : 2 * m * (s - 1) < n := by
    exact_mod_cast (mul_comm ((s - 1 : ℕ) : ℚ) _ ▸ (lt_div_iff₀ hden).mp hlo)
  obtain ⟨ρ, hρ, hc⟩ := batch_run (m := m) (min_le_left k t) s n le_rfl hi (Or.inr lo) pos tor hp
    (by simpa [tor] using hmany)
  have hle : (starTime n k t : ℝ) ≤ (ρ.map starStepDuration).sum := by
    exact_mod_cast starTime_le (show IsStarSchedule n k t ρ from hρ)
  simpa only [Nat.cast_mul] using le_antisymm (hle.trans hc) hlow

end

end MetaMathlibExt.BridgeTorchGeneralizations
