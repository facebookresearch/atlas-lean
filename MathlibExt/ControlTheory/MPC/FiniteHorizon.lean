/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Finite-horizon constrained optimization: attainment

For discrete dynamics `x (k+1) = f (x k) (u k)` with `f` continuous, a
compact input set `Us` (in a Hausdorff input space), closed state and
terminal constraint sets `Xs`, `Xf`, and continuous stage and terminal
costs, the `N`-step cost attains its minimum on the feasible input
sequences whenever one exists (`MPC.exists_optimal`). This is the
standard finite-horizon problem: controls are finite sequences
`u : Fin N → U` in the product topology, the trajectory is
`x 0 = x₀`, `x (k+1) = f (x k) (u k)`, feasibility constrains every
input to `Us`, every state `x k` with `k < N` (including `x₀`) to
`Xs`, and the terminal state `x N` to `Xf`; the cost is
`∑ k : Fin N, ℓ (x k) (u k) + V (x N)`. The proof is the extreme value
theorem: each trajectory point depends continuously on `u`, so the
feasible set is a closed, hence compact, subset of the compact
product `Us ^ (Fin N)` and the cost is continuous on it. At `N = 0`
feasibility is exactly `x₀ ∈ Xf` (the empty control sequence exists
even when `Us` is empty) and the cost is `V x₀`.
The shifted-and-appended input sequence gives recursive feasibility:
feasibility at a state implies feasibility at its successor when the
terminal set is contained in the state constraint set and the terminal
feedback keeps terminal states admissible and inside the terminal set.

Provenance: the finite-horizon model-predictive-control attainment
fact.
-/

open Set

@[expose] public section

namespace ControlTheory

namespace MPC

/-- State trajectory of the discrete dynamics `x (k+1) = f (x k) (u k)`
from initial state `x₀` under the finite input sequence
`u : Fin N → U`, evaluated at time `k ≤ N`. -/
def traj {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ} (u : Fin N → U) :
    (k : ℕ) → k ≤ N → X
  | 0, _ => x₀
  | k + 1, h => f (traj f x₀ u k (Nat.le_of_succ_le h)) (u ⟨k, h⟩)

/-- Feasibility over horizon `N` in the standard finite-horizon form:
every input `u k` lies in `Us`, every state `x k` for `k < N` lies in
the state constraint set `Xs`, and the terminal state `x N` lies in
`Xf`. -/
def Feasible {X U : Type*} (f : X → U → X) (x₀ : X) (Us : Set U)
    (Xs Xf : Set X) (N : ℕ) (u : Fin N → U) : Prop :=
  (∀ k, u k ∈ Us) ∧
    (∀ k (hk : k < N), traj f x₀ u k (Nat.le_of_lt hk) ∈ Xs) ∧
    traj f x₀ u N le_rfl ∈ Xf

/-- Finite-horizon cost: sum of stage costs `ℓ (x k) (u k)` over
`k : Fin N` plus terminal cost `V (x N)`. -/
def Cost {X U : Type*} (f : X → U → X) (ℓ : X → U → ℝ) (V : X → ℝ)
    (x₀ : X) (N : ℕ) (u : Fin N → U) : ℝ :=
  (∑ k : Fin N, ℓ (traj f x₀ u k (Nat.le_of_lt k.2)) (u k)) +
    V (traj f x₀ u N le_rfl)

private theorem traj_continuous {X U : Type*} [TopologicalSpace X]
    [TopologicalSpace U]
    {f : X → U → X} (hf : Continuous fun p : X × U => f p.1 p.2)
    (x₀ : X) {N : ℕ} :
    ∀ (k : ℕ) (h : k ≤ N),
    Continuous fun u : Fin N → U => traj f x₀ u k h := by
  intro k
  induction k with
  | zero =>
    intro h
    simpa [traj] using continuous_const
  | succ k ih =>
    intro h
    have hcont : Continuous ((fun p : X × U => f p.1 p.2) ∘
      (fun u : Fin N → U => (traj f x₀ u k (Nat.le_of_succ_le h), u (⟨k, h⟩ : Fin N)))) :=
      hf.comp ((ih (Nat.le_of_succ_le h)).prodMk (continuous_apply (⟨k, h⟩ : Fin N)))
    have heq : ((fun p : X × U => f p.1 p.2) ∘
        (fun u : Fin N → U => (traj f x₀ u k (Nat.le_of_succ_le h), u (⟨k, h⟩ : Fin N)))) =
        (fun u : Fin N → U => traj f x₀ u (k + 1) h) := by
      funext u
      simp [traj]
    rw [heq] at hcont
    exact hcont

private theorem cost_continuous {X U : Type*} [TopologicalSpace X]
    [TopologicalSpace U]
    {f : X → U → X} (hf : Continuous fun p : X × U => f p.1 p.2)
    {ℓ : X → U → ℝ} (hℓ : Continuous fun p : X × U => ℓ p.1 p.2)
    {V : X → ℝ} (hV : Continuous V) (x₀ : X) (N : ℕ) :
    Continuous fun u : Fin N → U => Cost f ℓ V x₀ N u := by
  unfold Cost
  apply Continuous.add
  · apply continuous_finsetSum _ (fun k _ => ?_)
    exact hℓ.comp ((traj_continuous hf x₀ k.val (Nat.le_of_lt k.2)).prodMk (continuous_apply k))
  · exact hV.comp (traj_continuous hf x₀ N le_rfl)

/-- Finite-horizon constrained optimizer attainment: with continuous
dynamics `f`,
compact input set `Us` (in a Hausdorff input space), closed state and
terminal constraint sets, continuous stage and terminal costs, and at
least one feasible finite input sequence, the `N`-step problem attains
its minimum. The feasible set is a closed, hence compact, subset of
the compact product `Us ^ (Fin N)`, and the cost is continuous on it;
this is the extreme value theorem. -/
theorem exists_optimal {X U : Type*} [TopologicalSpace X]
    [TopologicalSpace U] [T2Space U]
    {f : X → U → X} (hf : Continuous fun p : X × U => f p.1 p.2)
    {Us : Set U} (hU : IsCompact Us)
    {Xs Xf : Set X} (hXs : IsClosed Xs) (hXf : IsClosed Xf)
    {ℓ : X → U → ℝ} (hℓ : Continuous fun p : X × U => ℓ p.1 p.2)
    {V : X → ℝ} (hV : Continuous V) (x₀ : X) (N : ℕ)
    (hfeas : ∃ u, Feasible f x₀ Us Xs Xf N u) :
    ∃ u, Feasible f x₀ Us Xs Xf N u ∧
      ∀ v, Feasible f x₀ Us Xs Xf N v →
        Cost f ℓ V x₀ N u ≤ Cost f ℓ V x₀ N v := by
  have hUclosed : IsClosed Us := hU.isClosed
  have hPi : IsClosed (univ.pi fun _ : Fin N => Us) :=
    isClosed_set_pi (fun a _ => hUclosed)
  have hPreX : ∀ k : Fin N,
      IsClosed ((fun u : Fin N → U => traj f x₀ u k.val (Nat.le_of_lt k.2)) ⁻¹' Xs) :=
    fun k => hXs.preimage (traj_continuous hf x₀ k.val (Nat.le_of_lt k.2))
  have hPreF : IsClosed ((fun u : Fin N → U => traj f x₀ u N le_rfl) ⁻¹' Xf) :=
    hXf.preimage (traj_continuous hf x₀ N le_rfl)
  have hInter : IsClosed (⋂ k : Fin N,
      (fun u : Fin N → U => traj f x₀ u k.val (Nat.le_of_lt k.2)) ⁻¹' Xs) :=
    isClosed_iInter hPreX
  have hset_eq : {u : Fin N → U | Feasible f x₀ Us Xs Xf N u} =
      (univ.pi fun _ : Fin N => Us) ∩
      ((⋂ k : Fin N, (fun u : Fin N → U => traj f x₀ u k.val (Nat.le_of_lt k.2)) ⁻¹' Xs) ∩
        ((fun u : Fin N → U => traj f x₀ u N le_rfl) ⁻¹' Xf)) := by
    ext u
    simp only [Feasible, mem_ofPred_eq, mem_inter_iff, mem_pi, mem_univ,
      mem_preimage, mem_iInter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i _ => h1 i, ?_, h3⟩
      intro k
      exact h2 k.val k.2
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun i => h1 i trivial, ?_, h3⟩
      intro k hk
      exact h2 ⟨k, hk⟩
  have hClosed : IsClosed {u : Fin N → U | Feasible f x₀ Us Xs Xf N u} := by
    rw [hset_eq]
    exact hPi.inter (hInter.inter hPreF)
  have hCompactBase : IsCompact (univ.pi fun _ : Fin N => Us) :=
    isCompact_univ_pi (fun _ => hU)
  have hSub : {u : Fin N → U | Feasible f x₀ Us Xs Xf N u} ⊆
      univ.pi fun _ : Fin N => Us := by
    intro u hu
    simp only [mem_pi, mem_univ]
    obtain ⟨h1, _, _⟩ := hu
    intro i _
    exact h1 i
  have hCompact : IsCompact {u : Fin N → U | Feasible f x₀ Us Xs Xf N u} :=
    hCompactBase.of_isClosed_subset hClosed hSub
  have hNonempty : {u : Fin N → U | Feasible f x₀ Us Xs Xf N u}.Nonempty := by
    obtain ⟨w, hw⟩ := hfeas
    exact ⟨w, hw⟩
  have hCont : ContinuousOn (fun u : Fin N → U => Cost f ℓ V x₀ N u)
      {u : Fin N → U | Feasible f x₀ Us Xs Xf N u} :=
    (cost_continuous hf hℓ hV x₀ N).continuousOn
  obtain ⟨u, hu_mem, hmin⟩ := hCompact.exists_isMinOn hNonempty hCont
  refine ⟨u, hu_mem, fun v hv => ?_⟩
  exact isMinOn_iff.mp hmin v hv

/-- The shifted input sequence used for recursive feasibility: it drops
the first input, shifts the remaining ones, and appends the terminal
feedback `κ` applied to the terminal state. -/
def shiftAppend {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ}
    (u : Fin N → U) (κ : X → U) : Fin N → U :=
  fun k => if h : k.val + 1 < N then u ⟨k.val + 1, h⟩
    else κ (traj f x₀ u N le_rfl)

private theorem traj_zero {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ}
    (u : Fin N → U) (h : 0 ≤ N) :
    traj f x₀ u 0 h = x₀ :=
  rfl

private theorem traj_succ {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ}
    (u : Fin N → U) (k : ℕ) (h : k + 1 ≤ N) :
    traj f x₀ u (k + 1) h =
      f (traj f x₀ u k (Nat.le_of_succ_le h)) (u ⟨k, h⟩) :=
  rfl

private theorem traj_proof_irrel {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ}
    (u : Fin N → U) (k : ℕ) (h1 h2 : k ≤ N) :
    traj f x₀ u k h1 = traj f x₀ u k h2 :=
  rfl

/-- The trajectory under the shifted sequence, started from the first
successor state, agrees with the original trajectory shifted by one. -/
theorem traj_shiftAppend {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ}
    (hN : 1 ≤ N) (u : Fin N → U) (κ : X → U) (k : ℕ) (hk : k + 1 ≤ N) :
    traj f (f x₀ (u ⟨0, hN⟩)) (shiftAppend f x₀ u κ) k (Nat.le_of_succ_le hk) =
      traj f x₀ u (k + 1) hk := by
  have aux : ∀ (k : ℕ) (hk : k + 1 ≤ N),
      traj f (f x₀ (u ⟨0, hN⟩)) (shiftAppend f x₀ u κ) k (Nat.le_of_succ_le hk) =
        traj f x₀ u (k + 1) hk := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [traj_zero, traj_succ, traj_zero]
    | succ k ih =>
      intro hk
      rw [traj_succ, traj_succ]
      have hlt : k + 1 < N := by omega
      have hsh : ∀ (h : k < N), shiftAppend f x₀ u κ ⟨k, h⟩ = u ⟨k + 1, hk⟩ := by
        intro h
        simp only [shiftAppend]
        rw [dite_eq_left hlt]
      rw [hsh _, ih (Nat.le_of_succ_le hk)]
  exact aux k hk

private theorem traj_shiftAppend_gen {X U : Type*} (f : X → U → X) (x₀ : X) {N : ℕ}
    (hN : 1 ≤ N) (u : Fin N → U) (κ : X → U) (k : ℕ) (hk : k + 1 ≤ N)
    (h1 : k ≤ N) (h2 : k + 1 ≤ N) :
    traj f (f x₀ (u ⟨0, hN⟩)) (shiftAppend f x₀ u κ) k h1 =
      traj f x₀ u (k + 1) h2 :=
  (traj_proof_irrel _ _ _ k h1 (Nat.le_of_succ_le hk)).trans
    ((traj_shiftAppend f x₀ hN u κ k hk).trans
      (traj_proof_irrel _ _ _ (k + 1) hk h2))

/-- Recursive feasibility by shift and append: if the terminal set
`Xf` is contained in the state constraint set, and the terminal feedback
`κ` keeps terminal states admissible and inside `Xf`, then feasibility
at `x₀` over horizon `N ≥ 1` implies feasibility at the successor state
`f x₀ (u 0)` under the shifted-and-appended sequence. -/
theorem feasible_shift {X U : Type*} (f : X → U → X) (x₀ : X)
    (Us : Set U) (Xs Xf : Set X) {N : ℕ} (hN : 1 ≤ N)
    (hsub : Xf ⊆ Xs) (κ : X → U)
    (hκU : ∀ x ∈ Xf, κ x ∈ Us)
    (hκf : ∀ x ∈ Xf, f x (κ x) ∈ Xf)
    (u : Fin N → U) (hu : Feasible f x₀ Us Xs Xf N u) :
    Feasible f (f x₀ (u ⟨0, hN⟩)) Us Xs Xf N (shiftAppend f x₀ u κ) := by
  obtain ⟨hU, hX, hXf⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp only [shiftAppend]
    split
    · exact hU _
    · exact hκU _ hXf
  · intro k hk
    have hk' : k + 1 ≤ N := by omega
    have heq : traj f (f x₀ (u ⟨0, hN⟩)) (shiftAppend f x₀ u κ) k (Nat.le_of_lt hk) =
        traj f x₀ u (k + 1) hk' :=
      traj_shiftAppend_gen f x₀ hN u κ k hk' _ _
    rw [heq]
    by_cases h : k + 1 < N
    · exact hX (k + 1) h
    · have hEq : k + 1 = N := by omega
      subst hEq
      exact hsub hXf
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [traj_succ]
    have hneg : ¬ (n + 1 < n + 1) := by omega
    have hw : ∀ (h : n < n + 1),
        shiftAppend f x₀ u κ ⟨n, h⟩ = κ (traj f x₀ u (n + 1) le_rfl) := by
      intro h
      simp only [shiftAppend]
      rw [dite_eq_right hneg]
    rw [hw _]
    have heq : traj f (f x₀ (u ⟨0, hN⟩)) (shiftAppend f x₀ u κ) n
        (Nat.le_of_succ_le le_rfl) =
        traj f x₀ u (n + 1) le_rfl :=
      traj_shiftAppend_gen f x₀ hN u κ n le_rfl _ _
    rw [heq]
    exact hκf _ hXf

end MPC

end ControlTheory
