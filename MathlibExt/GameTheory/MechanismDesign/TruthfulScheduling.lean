/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith

/-!
# Truthful scheduling on unrelated machines

The finite unrelated-machines scheduling model: machine `i` privately
knows its processing times `t i j ≥ 0`; a direct-revelation mechanism is an
allocation rule with payments to the machines, utility is payment minus
true load, and the objective is the makespan. The module defines loads,
makespan and the optimal makespan, dominant-strategy truthfulness and weak
monotonicity on the nonnegative type space, and the MinWork mechanism
(each task to a fastest machine, the winner of a task paid the
second-fastest time for it).

Main declarations: `load`, `makespanOf`, `optMakespan`, `IsTruthful`,
`IsWeaklyMonotone`, `minWork`, `minWorkPayment`, `IsApproximate`.
Main theorems: `isWeaklyMonotone_of_isTruthful` (every truthful allocation
rule is weakly monotone), `isTruthful_minWork` (MinWork with per-task
second-price payments is truthful), `isApproximate_minWork` (MinWork is
an `n`-approximation, `n` the number of machines).

References: N. Nisan and A. Ronen, "Algorithmic mechanism design",
*Games and Economic Behavior* 35(1–2), 2001, §4 (the task scheduling
problem, the MinWork mechanism and its approximation ratio);
G. Christodoulou, E. Koutsoupias and A. Kovács, "A proof of the
Nisan–Ronen conjecture", arXiv:2301.11905, §2.1 (the mechanism-design
setting) and §2.2, Definition 2 (weak monotonicity). Lower bounds on the
approximation ratio are out of scope.
-/

set_option autoImplicit false

namespace MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling

@[expose] public section

/-- Load of machine `i` under allocation `A`, for finitely many tasks: its total processing
time for the tasks assigned to it. -/
noncomputable def load {Machine Task : Type*} [Fintype Task]
    [DecidableEq Machine] (t : Machine → Task → ℝ) (A : Task → Machine)
    (i : Machine) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => A j = i), t i j

/-- Makespan of an allocation: the largest machine load. -/
noncomputable def makespanOf {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine] [Nonempty Machine]
    (t : Machine → Task → ℝ) (A : Task → Machine) : ℝ :=
  (Finset.univ.image (load t A)).max'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Optimal makespan: the least makespan over all allocations. -/
noncomputable def optMakespan {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine] [DecidableEq Task]
    [Nonempty Machine] (t : Machine → Task → ℝ) : ℝ :=
  ((Finset.univ : Finset (Task → Machine)).image (makespanOf t)).min'
    (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Truthfulness (dominant strategies) on the nonnegative type space:
with true type profile `t` (nonnegative processing times), no machine
gains by unilaterally reporting a different nonnegative row `b`. Utility
is payment received minus true load. -/
def IsTruthful {Machine Task : Type*} [Fintype Task] [DecidableEq Machine]
    (A : (Machine → Task → ℝ) → Task → Machine)
    (P : (Machine → Task → ℝ) → Machine → ℝ) : Prop :=
  ∀ (t : Machine → Task → ℝ), (∀ i j, 0 ≤ t i j) →
    ∀ (i : Machine) (b : Task → ℝ), (∀ j, 0 ≤ b j) →
      P (Function.update t i b) i - load t (A (Function.update t i b)) i ≤
        P t i - load t (A t) i

/-- Weak monotonicity of an allocation rule on the nonnegative type
space, for finitely many tasks: if only machine `i`'s row changes from `t` to `t'` (both
nonnegative), then `t`-load of the old bundle minus `t`-load of the new
bundle is at most the same difference measured with `t'`. -/
def IsWeaklyMonotone {Machine Task : Type*} [Fintype Task]
    [DecidableEq Machine] (A : (Machine → Task → ℝ) → Task → Machine) :
    Prop :=
  ∀ (t t' : Machine → Task → ℝ), (∀ i j, 0 ≤ t i j) →
    (∀ i j, 0 ≤ t' i j) → ∀ (i : Machine), (∀ k ≠ i, t' k = t k) →
      load t (A t) i - load t (A t') i ≤ load t' (A t) i - load t' (A t') i

/-- A fastest machine for task `j` at profile `t` (chosen classically). -/
noncomputable def fastest {Machine Task : Type*} [Fintype Machine]
    [Nonempty Machine] (t : Machine → Task → ℝ) (j : Task) : Machine :=
  Classical.choose (Finset.univ.exists_min_image (fun i => t i j)
    Finset.univ_nonempty)

/-- The MinWork allocation: every task goes to a fastest machine for it. -/
noncomputable def minWork {Machine Task : Type*} [Fintype Machine]
    [Nonempty Machine] (t : Machine → Task → ℝ) : Task → Machine :=
  fun j => fastest t j

/-- MinWork payment: for each task it wins, machine `i` is paid the
fastest processing time among the other machines (per-task second price). -/
noncomputable def minWorkPayment {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine] [Nonempty Machine]
    [Nontrivial Machine] (t : Machine → Task → ℝ) (i : Machine) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => minWork t j = i),
    ((Finset.univ.erase i).image (fun k => t k j)).min'
      (Finset.image_nonempty.mpr
        (by obtain ⟨k, hk⟩ := exists_ne i; exact
          ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩))

/-- `c`-approximation: on every nonnegative processing-time profile (the
type space of the model), the allocation rule's makespan is at most `c`
times optimal. -/
def IsApproximate {Machine Task : Type*} [Fintype Machine] [Fintype Task]
    [DecidableEq Machine] [DecidableEq Task] [Nonempty Machine] (c : ℝ)
    (A : (Machine → Task → ℝ) → Task → Machine) : Prop :=
  ∀ t, (∀ i j, 0 ≤ t i j) → makespanOf t (A t) ≤ c * optMakespan t

/-- For finitely many tasks, loads are nonnegative when all processing times are
nonnegative. -/
theorem load_nonneg {Machine Task : Type*} [Fintype Task]
    [DecidableEq Machine] {t : Machine → Task → ℝ} (ht : ∀ i j, 0 ≤ t i j)
    (A : Task → Machine) (i : Machine) :
    0 ≤ load t A i := by
  exact Finset.sum_nonneg (fun j _ => ht i j)

/-- Each machine's load is at most the makespan of the allocation. -/
theorem load_le_makespanOf {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine] [Nonempty Machine]
    (t : Machine → Task → ℝ) (A : Task → Machine) (i : Machine) :
    load t A i ≤ makespanOf t A := by
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

/-- For finitely many tasks and finitely many machines, at least one, the optimal makespan is
at most the makespan of any allocation. -/
theorem optMakespan_le {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine] [DecidableEq Task]
    [Nonempty Machine] (t : Machine → Task → ℝ) (A : Task → Machine) :
    optMakespan t ≤ makespanOf t A := by
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ A))

/-- A fastest machine's processing time is minimal among all machines. -/
theorem fastest_spec {Machine Task : Type*} [Fintype Machine]
    [Nonempty Machine] (t : Machine → Task → ℝ) (j : Task)
    (k : Machine) :
    t (fastest t j) j ≤ t k j := by
  have h := Classical.choose_spec
    (Finset.univ.exists_min_image (fun i => t i j) Finset.univ_nonempty)
  exact h.2 k (Finset.mem_univ k)

/-- Every truthful allocation rule is weakly monotone: adding the two
truthfulness inequalities (deviating from `t` to `t'` and back) cancels the
payments and leaves weak monotonicity. -/
theorem isWeaklyMonotone_of_isTruthful {Machine Task : Type*}
    [Fintype Task] [DecidableEq Machine]
    {A : (Machine → Task → ℝ) → Task → Machine}
    {P : (Machine → Task → ℝ) → Machine → ℝ} (hA : IsTruthful A P) :
    IsWeaklyMonotone A := by
  intro t t' ht ht' i h
  have h1 : Function.update t i (t' i) = t' := by
    funext k
    by_cases hk : k = i
    · rw [hk]
      exact Function.update_self i (t' i) t
    · rw [Function.update_of_ne hk]
      exact (h k hk).symm
  have h2 : Function.update t' i (t i) = t := by
    funext k
    by_cases hk : k = i
    · rw [hk]
      exact Function.update_self i (t i) t'
    · rw [Function.update_of_ne hk]
      exact h k hk
  have e1 := hA t ht i (t' i) (fun j => ht' i j)
  rw [h1] at e1
  have e2 := hA t' ht' i (t i) (fun j => ht i j)
  rw [h2] at e2
  linarith

/-- A sum over `s` splits into the part outside `t` and the intersection. -/
private theorem sum_sdiff_add_sum_inter {Task : Type*} [DecidableEq Task]
    (s t : Finset Task) (f : Task → ℝ) :
    ∑ x ∈ s \ t, f x + ∑ x ∈ s ∩ t, f x = ∑ x ∈ s, f x := by
  have hunion : s \ t ∪ s ∩ t = s := Finset.sdiff_union_inter s t
  have hdisj : Disjoint (s \ t) (s ∩ t) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_sdiff] at hx1
    rw [Finset.mem_inter] at hx2
    exact hx1.2 hx2.2
  have h := Finset.sum_union (s₁ := s \ t) (s₂ := s ∩ t) (f := f) hdisj
  rw [hunion] at h
  exact h.symm

/-- `min'` depends only on the set, not the nonemptiness proof. -/
private theorem min'_of_eq {α : Type*} [LinearOrder α] {s t : Finset α}
    (h : s = t) (H1 : s.Nonempty) (H2 : t.Nonempty) :
    s.min' H1 = t.min' H2 := by
  subst h
  rfl

/-- MinWork with per-task second-price payments is truthful. -/
theorem isTruthful_minWork {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine]
    [Nonempty Machine] [Nontrivial Machine] :
    IsTruthful (Machine := Machine) (Task := Task) minWork minWorkPayment := by
  classical
  intro t ht i b hb
  have hagree : ∀ k : Machine, k ≠ i → Function.update t i b k = t k :=
    fun k hk => Function.update_of_ne hk b t
  have hne : ∀ j : Task,
      ((Finset.univ.erase i).image (fun k => t k j)).Nonempty :=
    fun j => Finset.image_nonempty.mpr (by
      obtain ⟨k, hk⟩ := exists_ne i
      exact ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩)
  have hutil : ∀ u : Machine → Task → ℝ, (∀ k ≠ i, u k = t k) →
      minWorkPayment u i - load t (minWork u) i
      = ∑ j ∈ Finset.univ.filter (fun j => minWork u j = i),
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j) := by
    intro u hu
    unfold minWorkPayment load
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have himg : (Finset.univ.erase i).image (fun k => u k j)
        = (Finset.univ.erase i).image (fun k => t k j) := by
      apply Finset.image_congr
      intro k hk
      simp only [Finset.mem_coe, Finset.mem_erase] at hk
      exact congrFun (hu k hk.1) j
    congr 1
    exact min'_of_eq himg _ _
  have hLHS := hutil (Function.update t i b) hagree
  have hRHS := hutil t (fun k _ => rfl)
  rw [hLHS, hRHS]
  set W : Finset Task := Finset.univ.filter (fun j => minWork t j = i) with hWdef
  set W' : Finset Task :=
    Finset.univ.filter (fun j => minWork (Function.update t i b) j = i) with hW'def
  have hneg : ∀ j ∈ W' \ W,
      ((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j ≤ 0 := by
    intro j hj
    rw [hW'def, hWdef, Finset.mem_sdiff] at hj
    obtain ⟨-, hjlose⟩ := hj
    have hne_i : minWork t j ≠ i := by
      intro hcon
      apply hjlose
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hcon⟩
    have hfast_ne : fastest t j ≠ i := hne_i
    have hmem_erase : fastest t j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hfast_ne, Finset.mem_univ _⟩
    have hmem_img : t (fastest t j) j
        ∈ (Finset.univ.erase i).image (fun k => t k j) :=
      Finset.mem_image_of_mem _ hmem_erase
    have hle1 : ((Finset.univ.erase i).image (fun k => t k j)).min' (hne j)
        ≤ t (fastest t j) j :=
      Finset.min'_le _ _ hmem_img
    have hle2 : t (fastest t j) j ≤ t i j := fastest_spec t j i
    linarith
  have hpos : ∀ j ∈ W \ W',
      0 ≤ ((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j := by
    intro j hj
    rw [hWdef, hW'def, Finset.mem_sdiff] at hj
    obtain ⟨hjwin, -⟩ := hj
    rw [Finset.mem_filter] at hjwin
    have hwin : fastest t j = i := hjwin.2
    have hge : t i j
        ≤ ((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) := by
      apply Finset.le_min' _ _ _ _
      intro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
      calc t i j = t (fastest t j) j := by rw [hwin]
        _ ≤ t k j := fastest_spec t j k
    linarith
  have e1 : (∑ j ∈ W' \ W,
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j))
      + (∑ j ∈ W ∩ W',
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j))
      = ∑ j ∈ W',
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j) := by
    have h := sum_sdiff_add_sum_inter W' W
      (fun j => ((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j)
    rwa [Finset.inter_comm W' W] at h
  have e2 : (∑ j ∈ W \ W',
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j))
      + (∑ j ∈ W ∩ W',
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j))
      = ∑ j ∈ W,
        (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j) :=
    sum_sdiff_add_sum_inter W W' _
  have na : (∑ j ∈ W' \ W,
      (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j)) ≤ 0 :=
    Finset.sum_nonpos (fun j hj => hneg j hj)
  have pb : 0 ≤ (∑ j ∈ W \ W',
      (((Finset.univ.erase i).image (fun k => t k j)).min' (hne j) - t i j)) :=
    Finset.sum_nonneg (fun j hj => hpos j hj)
  linarith

/-- MinWork is an `n`-approximation where `n` is the number of machines. -/
theorem isApproximate_minWork {Machine Task : Type*} [Fintype Machine]
    [Fintype Task] [DecidableEq Machine] [DecidableEq Task]
    [Nonempty Machine] :
    IsApproximate (Machine := Machine) (Task := Task) (Fintype.card Machine : ℝ)
      minWork := by
  intro t ht
  have hmem := Finset.min'_mem
    ((Finset.univ : Finset (Task → Machine)).image (makespanOf t))
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
  obtain ⟨Astar, -, hAstar⟩ := Finset.mem_image.mp hmem
  have hAstar' : makespanOf t Astar = optMakespan t := hAstar
  have h1 : ∀ i : Machine, load t (minWork t) i
      ≤ ∑ j ∈ Finset.univ.filter (fun j => minWork t j = i), t (Astar j) j := by
    intro i
    unfold load
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_filter] at hj
    have hji : fastest t j = i := hj.2
    calc t i j = t (fastest t j) j := by rw [hji]
      _ ≤ t (Astar j) j := fastest_spec t j (Astar j)
  have h2 : ∀ i : Machine,
      (∑ j ∈ Finset.univ.filter (fun j => minWork t j = i), t (Astar j) j)
        ≤ ∑ j ∈ Finset.univ, t (Astar j) j := by
    intro i
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j _ _
    exact ht (Astar j) j
  have hfib : ∀ A : Task → Machine,
      (∑ j ∈ Finset.univ, t (A j) j) = ∑ k ∈ Finset.univ, load t A k := by
    intro A
    have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := A) (fun j _ => Finset.mem_univ (A j)) (fun j => t (A j) j)
    calc (∑ j ∈ Finset.univ, t (A j) j)
        = ∑ k ∈ Finset.univ,
          ∑ j ∈ Finset.univ.filter (fun j => A j = k), t (A j) j := h.symm
      _ = ∑ k ∈ Finset.univ, load t A k := by
          apply Finset.sum_congr rfl
          intro k _
          unfold load
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_filter] at hj
          rw [hj.2]
  have h4 : (∑ k ∈ Finset.univ, load t Astar k)
      ≤ (Fintype.card Machine : ℝ) * makespanOf t Astar := by
    calc (∑ k ∈ Finset.univ, load t Astar k)
        ≤ ∑ k ∈ Finset.univ, makespanOf t Astar := by
          apply Finset.sum_le_sum
          intro k _
          exact load_le_makespanOf t Astar k
      _ = (Fintype.card Machine : ℝ) * makespanOf t Astar := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← hAstar']
  unfold makespanOf
  apply Finset.max'_le _ _ _ _
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨i, -, rfl⟩ := hy
  calc load t (minWork t) i
      ≤ ∑ j ∈ Finset.univ.filter (fun j => minWork t j = i), t (Astar j) j := h1 i
    _ ≤ ∑ j ∈ Finset.univ, t (Astar j) j := h2 i
    _ = ∑ k ∈ Finset.univ, load t Astar k := hfib Astar
    _ ≤ (Fintype.card Machine : ℝ) * makespanOf t Astar := h4

end

end MathlibExt.GameTheory.MechanismDesign.TruthfulScheduling
