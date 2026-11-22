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

Provenance: the finite-horizon model-predictive-control attainment
fact; control-theory roadmap leaf `SSC-S03.T01` (clause `SSC-S03.c01`).
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

/-- Finite-horizon constrained optimizer attainment (roadmap leaf
`SSC-S03.T01`, clause `SSC-S03.c01`): with continuous dynamics `f`,
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

end MPC

end ControlTheory
