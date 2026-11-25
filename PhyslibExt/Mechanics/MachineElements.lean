/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Machine elements: ideal gear trains and the four-bar linkage

Kinematics and load transmission of ideal gear trains, and the local regular branch of a planar
four-bar linkage with its velocity map.

## i. Overview

A finite parallel-axis gear train: shafts `0, …, n`, all oriented along one common axis
direction, and meshes `k = 0, …, n - 1`, mesh `k` joining the upstream shaft `k` to the
downstream shaft `k + 1`. Mesh `k` has a gear with `driverTeeth` teeth on the upstream shaft
and a gear with `drivenTeeth` teeth on the downstream shaft; the names record these positions,
not the direction of power flow. Both counts are positive integers (`ℕ+`), and in an internal
mesh the downstream gear is the ring (internal gear) with strictly more teeth than the upstream
pinion, so every mesh is a realizable gear pair: an internal pair with equal counts would have
zero center distance. Angular velocities `ω j` are signed about the common axis direction.

Model inputs:

* rigid ideal no-slip gears: across mesh `k` the downstream speed is the signed ratio
  `sense * driverTeeth / drivenTeeth` times the upstream speed, where the sense is `-1` for
  an external mesh (the sense of rotation reverses) and `1` for an internal (ring-gear)
  mesh (the sense is kept);
* power-into-component signs: `a k` is the torque the upstream shaft applies to mesh `k` and
  `b k` the torque the downstream shaft applies to mesh `k`, both about the common axis
  direction, so the power into mesh `k` is `a k * ω k + b k * ω (k + 1)`;
* the ideal lossless port convention: a mesh absorbs no power on any motion of its two shafts
  allowed by its no-slip constraint; the port torques may have either sign, so power can flow
  through a mesh in either direction, and in an internal mesh the ring can drive the pinion as
  well as the pinion the ring;
* massless rigid shafts in equilibrium: the external torque applied to shaft `j`, whose power
  into the train is that torque times `ω j`, equals the sum of the torques shaft `j` applies
  to its meshes (`shaftLoad`).

Results: the speed of the last shaft is the product of the signed mesh ratios times the speed
of the first shaft; the product equals `(-1) ^ (number of external meshes)` times the ratio of
the tooth-count products, so it is nonzero and its sign is set by the parity of the external
meshes; each mesh carries the torque relation `a k + ratio * b k = 0`; the total power
into the train through its shaft ports vanishes; and for a train loaded only at its first and
last shafts the port torques satisfy `τ_in + R * τ_out = 0`, so `τ_out = -τ_in / R`.

Non-goals: backlash, tooth-contact stress, friction losses, inertia, planetary trains, and any
empirical adequacy or system safety claim.

Section C treats a planar four-bar linkage with positive link lengths: the ground link of length
`a` from the input pivot `O₂ = (0, 0)` to the output pivot `O₄ = (a, 0)`, the input crank `b` at
the angle `θ₂`, the coupler `c` at `θ₃` and the output rocker `d` at `θ₄`, all angles measured
counterclockwise from the ground direction `O₂ → O₄`. The vector loop
`b u(θ₂) + c u(θ₃) = a e₁ + d u(θ₄)`, with `u(θ) = (cos θ, sin θ)`, gives the two planar
loop-closure equations.

Model inputs for the linkage:

* rigid links and ideal revolute joints; the loop-closure equations are the model;
* the input angle `θ₂` is prescribed and `(θ₃, θ₄)` are the two dependent angles;
* regularity: the Jacobian of the closure residuals in the dependent angles is invertible at the
  configuration; its determinant is `c d sin (θ₃ - θ₄)`, which vanishes exactly at the
  dead-center configurations where coupler and rocker are collinear.

At a closed regular configuration the implicit function theorem gives a local branch
`θ₂ ↦ (θ₃, θ₄)`, which near the configuration is exactly the set of closed configurations and
whose derivative is the velocity map `ω₃ = b sin (θ₄ - θ₂) / (c sin (θ₃ - θ₄)) ω₂`,
`ω₄ = b sin (θ₃ - θ₂) / (d sin (θ₃ - θ₄)) ω₂`; these ratios solve the differentiated loop
equations. A ground link longer than the other three links together admits no closed
configuration. The global Grashof or full-crank classification is not a hypothesis of the local
branch and is not treated, nor are branch selection across dead centers, joint clearance and
dynamics.

## ii. Key results

- `Mechanics.MachineElements.IsNoSlip.last_eq`, `Mechanics.MachineElements.exists_isNoSlip`:
  the last shaft turns at the train ratio times the first; the no-slip constraints admit a
  motion with any first-shaft speed.
- `Mechanics.MachineElements.trainRatio_eq`, `Mechanics.MachineElements.trainRatio_ne_zero`,
  `Mechanics.MachineElements.trainRatio_pos_iff`: the train ratio is
  `(-1) ^ (number of external meshes)` times the ratio of the tooth-count products, and its sign
  is set by the parity of the external meshes.
- `Mechanics.MachineElements.IsLossless.mesh_torque`, `Mechanics.MachineElements.power_balance`,
  `Mechanics.MachineElements.torque_relation`, `Mechanics.MachineElements.torque_out_eq`: the
  torque relation of each ideal mesh, the total power balance, and the port torque relation
  `τ_out = -τ_in / R`.
- `Mechanics.MachineElements.orientation_swap`: reversing the orientation of the last shaft
  negates the ratio.
- `Mechanics.MachineElements.FourBar.det_dependentJacobian`,
  `Mechanics.MachineElements.FourBar.det_dependentJacobian_eq_zero_iff`: the dependent-angle
  Jacobian determinant of a four-bar linkage is `c d sin (θ₃ - θ₄)`, zero exactly at the dead
  centers.
- `Mechanics.MachineElements.FourBar.exists_local_branch`,
  `Mechanics.MachineElements.FourBar.velocityRatio_spec`: at a closed regular configuration the
  nearby closed configurations are the graph of a local branch, whose derivative is the velocity
  map solving the differentiated loop equations.
- `Mechanics.MachineElements.FourBar.not_isClosed_of_lt_ground`: a ground link longer than the
  other three links together admits no closed configuration.

## iii. Table of contents

- A. Meshes and the train ratio
- B. Port torques and power
- C. Four-bar loop closure and the local branch

## iv. References

- J. J. Uicker, G. R. Pennock and J. E. Shigley, *Theory of Machines and Mechanisms*,
  5th edition, 2017 (gear trains and train value; position and velocity analysis of the
  four-bar linkage, transmission angle and dead-center positions).
- R. G. Budynas and J. K. Nisbett, *Shigley's Mechanical Engineering Design*, 10th edition,
  2015 (gear trains; power transmitted by an ideal train).
- R. L. Norton, *Design of Machinery*, McGraw-Hill (vector loop equations of the four-bar
  linkage; toggle positions).
-/

@[expose] public section

namespace Mechanics.MachineElements

/-! ## A. Meshes and the train ratio -/

/-- Mesh kind: an external mesh reverses the sense of rotation, an internal (ring-gear) mesh
keeps it. -/
inductive MeshKind
  | external
  | internal
  deriving DecidableEq

/-- Sense factor of a mesh kind: `-1` for an external mesh, `1` for an internal mesh. -/
def MeshKind.sense : MeshKind → ℝ
  | .external => -1
  | .internal => 1

/-- One mesh: `driverTeeth` teeth on the gear on the upstream shaft, `drivenTeeth` teeth on the
gear on the downstream shaft, both positive, and the mesh kind. The names record positions, not
the direction of power flow. In an internal mesh the downstream gear is the ring and has strictly
more teeth than the upstream pinion. -/
structure Mesh where
  driverTeeth : ℕ+
  drivenTeeth : ℕ+
  kind : MeshKind
  /-- In an internal mesh the ring, on the downstream shaft, has strictly more teeth than the
  pinion on the upstream shaft. -/
  driverTeeth_lt_drivenTeeth_of_internal : kind = MeshKind.internal → driverTeeth < drivenTeeth

/-- Signed angular-speed ratio of a mesh, downstream over upstream:
`sense * driverTeeth / drivenTeeth`. -/
noncomputable def Mesh.ratio (g : Mesh) : ℝ :=
  g.kind.sense * (((g.driverTeeth : ℕ) : ℝ) / (g.drivenTeeth : ℕ))

variable {n : ℕ}

/-- Number of external meshes of the train. -/
def externalCount (m : Fin n → Mesh) : ℕ :=
  (Finset.univ.filter fun k => (m k).kind = MeshKind.external).card

/-- Train ratio: the product of the signed mesh ratios. -/
noncomputable def trainRatio (m : Fin n → Mesh) : ℝ :=
  ∏ k, (m k).ratio

/-- No-slip kinematics: across every mesh the downstream shaft speed is the mesh ratio times
the upstream shaft speed. -/
def IsNoSlip (m : Fin n → Mesh) (ω : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin n, ω k.succ = (m k).ratio * ω k.castSucc

/-- Induction on the number of meshes for `IsNoSlip.last_eq`. -/
private lemma last_eq_aux (n : ℕ) (m : Fin n → Mesh) (ω : Fin (n + 1) → ℝ)
    (h : IsNoSlip m ω) : ω (Fin.last n) = trainRatio m * ω 0 := by
  induction n with
  | zero =>
    have hlast : Fin.last 0 = (0 : Fin 1) := by
      apply Fin.ext
      simp
    have hprod : trainRatio m = 1 := by
      unfold trainRatio
      simp
    rw [hlast, hprod]
    simp
  | succ n ih =>
    let m' : Fin n → Mesh := fun k => m k.castSucc
    let ω' : Fin (n + 1) → ℝ := fun j => ω j.castSucc
    have h' : IsNoSlip m' ω' := by
      intro k
      simp only [m', ω']
      have hk : (k.castSucc.succ : Fin (n + 2)) = k.succ.castSucc := by
        apply Fin.ext
        simp
      have hkk := h k.castSucc
      rw [hk] at hkk
      exact hkk
    have ihH := ih m' ω' h'
    simp only [m', ω'] at ihH
    have h0 : ((0 : Fin (n + 1)).castSucc : Fin (n + 2)) = 0 := by
      apply Fin.ext
      simp
    rw [h0] at ihH
    have hLastSucc : ((Fin.last n).succ : Fin (n + 2)) = Fin.last (n + 1) := Fin.succ_last n
    have hStep := h (Fin.last n)
    rw [hLastSucc] at hStep
    have hProd : trainRatio m = trainRatio m' * (m (Fin.last n)).ratio := by
      unfold trainRatio m'
      rw [Fin.prod_univ_castSucc]
    rw [hProd]
    rw [hStep]
    rw [ihH]
    ring

/-- Induction on the number of meshes for `exists_isNoSlip`, extending the motion by
`Fin.snoc`. -/
private lemma exists_aux (n : ℕ) (m : Fin n → Mesh) (ω₀ : ℝ) :
    ∃ ω : Fin (n + 1) → ℝ, IsNoSlip m ω ∧ ω 0 = ω₀ := by
  induction n with
  | zero =>
    refine ⟨fun _ => ω₀, ?_, rfl⟩
    intro k
    exact k.elim0
  | succ n ih =>
    let m' : Fin n → Mesh := fun k => m k.castSucc
    obtain ⟨ω', hω', h0'⟩ := ih m'
    let x : ℝ := (m (Fin.last n)).ratio * ω' (Fin.last n)
    let ω : Fin (n + 2) → ℝ := Fin.snoc (α := fun _ => ℝ) ω' x
    have h_last : ω (Fin.last (n + 1)) = x := by
      simp only [ω]
      exact Fin.snoc_last (α := fun _ => ℝ) x ω'
    have h_cast : ∀ i : Fin (n + 1), ω i.castSucc = ω' i := by
      intro i
      simp only [ω]
      exact Fin.snoc_castSucc (α := fun _ => ℝ) x ω' i
    have h0 : ω 0 = ω₀ := by
      have h00 : ((0 : Fin (n + 1)).castSucc : Fin (n + 2)) = 0 := by
        apply Fin.ext
        simp
      have hcc := h_cast 0
      rw [h00] at hcc
      rw [hcc, h0']
    refine ⟨ω, ?_, h0⟩
    intro k
    refine Fin.lastCases ?_ ?_ k
    · have hSucc : ((Fin.last n).succ : Fin (n + 2)) = Fin.last (n + 1) := Fin.succ_last n
      rw [hSucc, h_last]
      have hcast := h_cast (Fin.last n)
      unfold x
      rw [← hcast]
    · intro i
      have hk1 : ((i.castSucc.succ : Fin (n + 2))) = i.succ.castSucc := by
        apply Fin.ext
        simp
      rw [hk1]
      rw [h_cast, h_cast]
      have hi := hω' i
      simp only [m'] at hi
      exact hi

/-- For speeds satisfying the no-slip constraints, the speed of the last shaft is the train ratio
times the speed of the first shaft. -/
lemma IsNoSlip.last_eq {m : Fin n → Mesh} {ω : Fin (n + 1) → ℝ} (h : IsNoSlip m ω) :
    ω (Fin.last n) = trainRatio m * ω 0 := by
  exact last_eq_aux n m ω h

/-- The no-slip constraints admit a motion with any prescribed first-shaft speed. -/
lemma exists_isNoSlip (m : Fin n → Mesh) (ω₀ : ℝ) :
    ∃ ω : Fin (n + 1) → ℝ, IsNoSlip m ω ∧ ω 0 = ω₀ := by
  exact exists_aux n m ω₀

/-- The train ratio is `(-1) ^ (number of external meshes)` times the product of the upstream
tooth counts `driverTeeth` over the product of the downstream tooth counts `drivenTeeth`. -/
lemma trainRatio_eq (m : Fin n → Mesh) :
    trainRatio m = (-1) ^ externalCount m *
      ((∏ k, (((m k).driverTeeth : ℕ) : ℝ)) / ∏ k, (((m k).drivenTeeth : ℕ) : ℝ)) := by
  unfold trainRatio externalCount Mesh.ratio
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_div_distrib]
  congr 1
  have hSense : ∀ k : Fin n, (m k).kind.sense =
      (if (m k).kind = MeshKind.external then (-1:ℝ) else 1) := by
    intro k
    cases (m k).kind with
    | external => simp [MeshKind.sense]
    | internal => simp [MeshKind.sense]
  have h1 : (∏ k, (m k).kind.sense) =
      ∏ k, (if (m k).kind = MeshKind.external then (-1:ℝ) else 1) :=
    Finset.prod_congr rfl (fun k _ => hSense k)
  rw [h1]
  have h2 : (∏ k, (if (m k).kind = MeshKind.external then (-1:ℝ) else 1)) =
      Finset.prod (Finset.univ.filter fun k => (m k).kind = MeshKind.external)
        (fun _ => (-1:ℝ)) := by
    rw [← Finset.prod_filter]
  rw [h2]
  rw [Finset.prod_const]

/-- The train ratio is nonzero. -/
lemma trainRatio_ne_zero {m : Fin n → Mesh} : trainRatio m ≠ 0 := by
  unfold trainRatio
  rw [Finset.prod_ne_zero_iff]
  intro k _
  unfold Mesh.ratio
  apply mul_ne_zero
  · cases (m k).kind with
    | external => simp [MeshKind.sense]
    | internal => simp [MeshKind.sense]
  · apply div_ne_zero
    · exact_mod_cast (m k).driverTeeth.ne_zero
    · exact_mod_cast (m k).drivenTeeth.ne_zero

/-- The train ratio is positive exactly when the number of external meshes is even; so, on a
no-slip motion with nonzero first-shaft speed, the last shaft turns in the sense of the first
exactly when that number is even. -/
lemma trainRatio_pos_iff {m : Fin n → Mesh} :
    0 < trainRatio m ↔ Even (externalCount m) := by
  rw [trainRatio_eq]
  have hPos :
      0 < (∏ k, (((m k).driverTeeth : ℕ) : ℝ)) / ∏ k, (((m k).drivenTeeth : ℕ) : ℝ) := by
    apply div_pos
    · apply Finset.prod_pos
      intro k _
      exact_mod_cast (m k).driverTeeth.pos
    · apply Finset.prod_pos
      intro k _
      exact_mod_cast (m k).drivenTeeth.pos
  rw [mul_pos_iff_of_pos_right hPos]
  constructor
  · intro hPow
    by_contra hNotEven
    have hOdd : Odd (externalCount m) := (Nat.not_even_iff_odd).mp hNotEven
    have hEq : (-1:ℝ) ^ externalCount m = -1 := hOdd.neg_one_pow
    rw [hEq] at hPow
    norm_num at hPow
  · intro hEven
    have hEq : (-1:ℝ) ^ externalCount m = 1 := hEven.neg_one_pow
    rw [hEq]
    norm_num

/-! ## B. Port torques and power -/

/-- Ideal lossless port convention: mesh `k` absorbs no power, `a k * w + b k * w'`, on any
motion `(w, w')` of its upstream and downstream shafts allowed by its no-slip constraint
`w' = ratio * w`. The port torques may have either sign, so power may enter the mesh through
either shaft. -/
def IsLossless (m : Fin n → Mesh) (a b : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, ∀ w : ℝ, a k * w + b k * ((m k).ratio * w) = 0

/-- External torque on shaft `j` of massless rigid shafts in equilibrium: the sum of the
torques shaft `j` applies to the meshes it is the upstream shaft of (`a k` when `j` is upstream
of mesh `k`) and to the meshes it is the downstream shaft of (`b k` when `j` is downstream of
mesh `k`). -/
def shaftLoad (a b : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  (∑ k : Fin n, if k.castSucc = j then a k else 0) +
    ∑ k : Fin n, if k.succ = j then b k else 0

/-- Torque relation of an ideal lossless mesh: `a k + ratio * b k = 0`. -/
lemma IsLossless.mesh_torque {m : Fin n → Mesh} {a b : Fin n → ℝ} (h : IsLossless m a b)
    (k : Fin n) : a k + (m k).ratio * b k = 0 := by
  have h1 := h k 1
  simp only [mul_one] at h1
  have hc : b k * (m k).ratio = (m k).ratio * b k := mul_comm _ _
  rw [hc] at h1
  exact h1

/-- Total power balance: for lossless meshes, on every no-slip motion the power into the train
through its shaft ports, `∑ j, shaftLoad a b j * ω j`, vanishes. -/
lemma power_balance {m : Fin n → Mesh} {a b : Fin n → ℝ} {ω : Fin (n + 1) → ℝ}
    (hl : IsLossless m a b) (hω : IsNoSlip m ω) :
    ∑ j, shaftLoad a b j * ω j = 0 := by
  unfold shaftLoad
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_mul]
  have h1 : ∀ k : Fin n, (∑ j, (if k.castSucc = j then a k else 0) * ω j) = a k * ω k.castSucc := by
    intro k
    have heq : ∀ j : Fin (n+1), (if k.castSucc = j then a k else 0) * ω j =
        (if k.castSucc = j then a k * ω j else 0) := by
      intro j
      by_cases hj : k.castSucc = j
      · simp [hj]
      · simp [hj]
    simp only [heq]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∀ k : Fin n, (∑ j, (if k.succ = j then b k else 0) * ω j) = b k * ω k.succ := by
    intro k
    have heq : ∀ j : Fin (n+1), (if k.succ = j then b k else 0) * ω j =
        (if k.succ = j then b k * ω j else 0) := by
      intro j
      by_cases hj : k.succ = j
      · simp [hj]
      · simp [hj]
    simp only [heq]
    rw [Finset.sum_ite_eq]
    simp
  have e1 : (∑ j, ∑ k : Fin n, (if k.castSucc = j then a k else 0) * ω j) =
      ∑ k, a k * ω k.castSucc := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact h1 k
  have e2 : (∑ j, ∑ k : Fin n, (if k.succ = j then b k else 0) * ω j) =
      ∑ k, b k * ω k.succ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact h2 k
  rw [e1, e2]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k _
  have hlk := hl k (ω k.castSucc)
  have hwk := hω k
  rw [hwk]
  exact hlk

/-- Port torque relation of a train with lossless meshes, loaded only at its first and last shafts:
`τ_in + R * τ_out = 0`. -/
lemma torque_relation {m : Fin n → Mesh} {a b : Fin n → ℝ} (hl : IsLossless m a b)
    (htwo : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ Fin.last n → shaftLoad a b j = 0) :
    shaftLoad a b 0 + trainRatio m * shaftLoad a b (Fin.last n) = 0 := by
  obtain ⟨ω, hω, h0⟩ := exists_isNoSlip m 1
  have hLast : ω (Fin.last n) = trainRatio m * 1 := by
    have h := IsNoSlip.last_eq hω
    rw [h0] at h
    exact h
  have hPower : ∑ j, shaftLoad a b j * ω j = 0 := power_balance hl hω
  by_cases h01 : (0 : Fin (n + 1)) = Fin.last n
  · have hSingle : (∑ j, shaftLoad a b j * ω j) = shaftLoad a b 0 * ω 0 := by
      apply Finset.sum_eq_single (0 : Fin (n+1))
      · intro b _ hb
        have hb_last : b ≠ Fin.last n := by
          intro heq
          apply hb
          rw [heq, ← h01]
        have hsb := htwo b hb hb_last
        simp [hsb]
      · intro hcon
        simp at hcon
    rw [hSingle] at hPower
    rw [h0] at hPower
    rw [mul_one] at hPower
    rw [← h01]
    rw [hPower]
    simp
  · have hPair : (∑ j, shaftLoad a b j * ω j) =
        shaftLoad a b 0 * ω 0 + shaftLoad a b (Fin.last n) * ω (Fin.last n) := by
      have hSub :
          Finset.sum (Finset.univ : Finset (Fin (n+1))) (fun j => shaftLoad a b j * ω j) =
          Finset.sum ({0, Fin.last n} : Finset (Fin (n+1))) (fun j => shaftLoad a b j * ω j) := by
        apply Eq.symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        have hx0 : x ≠ 0 := fun heq => hx (Or.inl heq)
        have hxl : x ≠ Fin.last n := fun heq => hx (Or.inr heq)
        have hsb := htwo x hx0 hxl
        simp [hsb]
      have hPairSum :
          Finset.sum ({0, Fin.last n} : Finset (Fin (n+1))) (fun j => shaftLoad a b j * ω j) =
          shaftLoad a b 0 * ω 0 + shaftLoad a b (Fin.last n) * ω (Fin.last n) :=
        Finset.sum_pair h01
      rw [hSub, hPairSum]
    rw [hPair] at hPower
    rw [h0, hLast] at hPower
    simp only [mul_one] at hPower
    have hComm :
        shaftLoad a b (Fin.last n) * trainRatio m = trainRatio m * shaftLoad a b (Fin.last n) :=
      mul_comm _ _
    rw [hComm] at hPower
    simpa using hPower

/-- For lossless meshes and a train loaded only at its first and last shafts, the output port
torque is `τ_out = -τ_in / R`. -/
lemma torque_out_eq {m : Fin n → Mesh} {a b : Fin n → ℝ} (hl : IsLossless m a b)
    (htwo : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ Fin.last n → shaftLoad a b j = 0) :
    shaftLoad a b (Fin.last n) = -shaftLoad a b 0 / trainRatio m := by
  have hR : trainRatio m ≠ 0 := trainRatio_ne_zero
  have hRel : shaftLoad a b 0 + trainRatio m * shaftLoad a b (Fin.last n) = 0 :=
    torque_relation hl htwo
  rw [eq_div_iff hR]
  have hC : trainRatio m * shaftLoad a b (Fin.last n) =
      shaftLoad a b (Fin.last n) * trainRatio m := mul_comm _ _
  linarith [hRel, hC]

/-- Swapping the orientation of the last shaft negates its signed speed, so the reoriented
speed follows the negated ratio; keeping the old sign is rejected on every no-slip motion with a
nonzero first-shaft speed. -/
lemma orientation_swap {m : Fin n → Mesh} {ω : Fin (n + 1) → ℝ} (hω : IsNoSlip m ω)
    (h0 : ω 0 ≠ 0) :
    -ω (Fin.last n) = -trainRatio m * ω 0 ∧ -ω (Fin.last n) ≠ trainRatio m * ω 0 := by
  have hLast : ω (Fin.last n) = trainRatio m * ω 0 := IsNoSlip.last_eq hω
  have hR : trainRatio m ≠ 0 := trainRatio_ne_zero
  constructor
  · rw [hLast]
    ring
  · rw [hLast]
    intro hCon
    have hZero : trainRatio m * ω 0 = 0 := by linarith [hCon]
    have hNe : trainRatio m * ω 0 ≠ 0 := mul_ne_zero hR h0
    exact hNe hZero

/-! ## C. Four-bar loop closure and the local branch -/

section FourBarLinkage

open Filter
open scoped Topology

/-- A planar four-bar linkage with positive link lengths: ground `a`, input crank `b`, coupler
`c`, output rocker `d`. -/
structure FourBar where
  /-- Ground link length `a`, from the input pivot to the output pivot. -/
  ground : ℝ
  /-- Input crank length `b`. -/
  crank : ℝ
  /-- Coupler length `c`. -/
  coupler : ℝ
  /-- Output rocker length `d`. -/
  rocker : ℝ
  ground_pos : 0 < ground
  crank_pos : 0 < crank
  coupler_pos : 0 < coupler
  rocker_pos : 0 < rocker

namespace FourBar

variable (L : FourBar)

/-- The two planar loop-closure residuals `b u(θ₂) + c u(θ₃) - d u(θ₄) - a e₁`, horizontal and
vertical components. -/
noncomputable def closure (θ₂ θ₃ θ₄ : ℝ) : ℝ × ℝ :=
  (L.crank * Real.cos θ₂ + L.coupler * Real.cos θ₃ - L.rocker * Real.cos θ₄ - L.ground,
    L.crank * Real.sin θ₂ + L.coupler * Real.sin θ₃ - L.rocker * Real.sin θ₄)

/-- A closed configuration: both loop-closure equations hold. -/
def IsClosed (θ₂ θ₃ θ₄ : ℝ) : Prop :=
  L.closure θ₂ θ₃ θ₄ = 0

/-- Jacobian matrix of the loop-closure residuals in the two dependent angles `(θ₃, θ₄)`. -/
noncomputable def dependentJacobian (θ₃ θ₄ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(L.coupler * Real.sin θ₃), L.rocker * Real.sin θ₄;
    L.coupler * Real.cos θ₃, -(L.rocker * Real.cos θ₄)]

/-- Velocity ratios `ω₃ / ω₂ = b sin (θ₄ - θ₂) / (c sin (θ₃ - θ₄))` and
`ω₄ / ω₂ = b sin (θ₃ - θ₂) / (d sin (θ₃ - θ₄))`. With `a / 0 = 0` both are `0` at a dead center,
`sin (θ₃ - θ₄) = 0`; the intended domain is the regular configurations. -/
noncomputable def velocityRatio (θ₂ θ₃ θ₄ : ℝ) : ℝ × ℝ :=
  (L.crank * Real.sin (θ₄ - θ₂) / (L.coupler * Real.sin (θ₃ - θ₄)),
    L.crank * Real.sin (θ₃ - θ₂) / (L.rocker * Real.sin (θ₃ - θ₄)))

/-- Partial derivative of the closure residuals in the input angle `θ₂`. -/
lemma hasDerivAt_closure_crank (θ₂ θ₃ θ₄ : ℝ) :
    HasDerivAt (fun θ => L.closure θ θ₃ θ₄)
      (-(L.crank * Real.sin θ₂), L.crank * Real.cos θ₂) θ₂ := by
  have h1 : HasDerivAt (fun θ => L.crank * Real.cos θ + L.coupler * Real.cos θ₃ -
      L.rocker * Real.cos θ₄ - L.ground) (L.crank * -Real.sin θ₂) θ₂ :=
    ((((Real.hasDerivAt_cos θ₂).const_mul L.crank).add_const _).sub_const _).sub_const _
  have h2 : HasDerivAt (fun θ => L.crank * Real.sin θ + L.coupler * Real.sin θ₃ -
      L.rocker * Real.sin θ₄) (L.crank * Real.cos θ₂) θ₂ :=
    (((Real.hasDerivAt_sin θ₂).const_mul L.crank).add_const _).sub_const _
  have h := h1.prodMk h2
  rw [mul_neg] at h
  exact h

/-- Partial derivative in the coupler angle `θ₃`: the first column of `dependentJacobian`. -/
lemma hasDerivAt_closure_coupler (θ₂ θ₃ θ₄ : ℝ) :
    HasDerivAt (fun θ => L.closure θ₂ θ θ₄)
      (-(L.coupler * Real.sin θ₃), L.coupler * Real.cos θ₃) θ₃ := by
  have h1 : HasDerivAt (fun θ => L.crank * Real.cos θ₂ + L.coupler * Real.cos θ -
      L.rocker * Real.cos θ₄ - L.ground) (L.coupler * -Real.sin θ₃) θ₃ :=
    ((((Real.hasDerivAt_cos θ₃).const_mul L.coupler).const_add _).sub_const _).sub_const _
  have h2 : HasDerivAt (fun θ => L.crank * Real.sin θ₂ + L.coupler * Real.sin θ -
      L.rocker * Real.sin θ₄) (L.coupler * Real.cos θ₃) θ₃ :=
    (((Real.hasDerivAt_sin θ₃).const_mul L.coupler).const_add _).sub_const _
  have h := h1.prodMk h2
  rw [mul_neg] at h
  exact h

/-- Partial derivative in the rocker angle `θ₄`: the second column of `dependentJacobian`. -/
lemma hasDerivAt_closure_rocker (θ₂ θ₃ θ₄ : ℝ) :
    HasDerivAt (fun θ => L.closure θ₂ θ₃ θ)
      (L.rocker * Real.sin θ₄, -(L.rocker * Real.cos θ₄)) θ₄ := by
  have h1 : HasDerivAt (fun θ => L.crank * Real.cos θ₂ + L.coupler * Real.cos θ₃ -
      L.rocker * Real.cos θ - L.ground) (-(L.rocker * -Real.sin θ₄)) θ₄ :=
    (((Real.hasDerivAt_cos θ₄).const_mul L.rocker).const_sub _).sub_const _
  have h2 : HasDerivAt (fun θ => L.crank * Real.sin θ₂ + L.coupler * Real.sin θ₃ -
      L.rocker * Real.sin θ) (-(L.rocker * Real.cos θ₄)) θ₄ :=
    ((Real.hasDerivAt_sin θ₄).const_mul L.rocker).const_sub _
  have h := h1.prodMk h2
  rw [mul_neg, neg_neg] at h
  exact h

/-- The dependent-angle Jacobian determinant is `c d sin (θ₃ - θ₄)`. -/
lemma det_dependentJacobian (θ₃ θ₄ : ℝ) :
    (L.dependentJacobian θ₃ θ₄).det = L.coupler * L.rocker * Real.sin (θ₃ - θ₄) := by
  simp [dependentJacobian, Matrix.det_fin_two, Real.sin_sub]
  ring

/-- Dead centers: the dependent-angle determinant vanishes exactly when coupler and rocker are
collinear, `θ₃ - θ₄ = n π`. -/
lemma det_dependentJacobian_eq_zero_iff (θ₃ θ₄ : ℝ) :
    (L.dependentJacobian θ₃ θ₄).det = 0 ↔ ∃ n : ℤ, (n : ℝ) * Real.pi = θ₃ - θ₄ := by
  rw [det_dependentJacobian, mul_eq_zero, mul_eq_zero, Real.sin_eq_zero_iff]
  simp [L.coupler_pos.ne', L.rocker_pos.ne']

/-- At a regular configuration the velocity ratios solve the differentiated loop equations
`-b sin θ₂ - c sin θ₃ r₃ + d sin θ₄ r₄ = 0` and `b cos θ₂ + c cos θ₃ r₃ - d cos θ₄ r₄ = 0`. -/
lemma velocityRatio_spec {θ₂ θ₃ θ₄ : ℝ} (hreg : (L.dependentJacobian θ₃ θ₄).det ≠ 0) :
    -(L.crank * Real.sin θ₂) - L.coupler * Real.sin θ₃ * (L.velocityRatio θ₂ θ₃ θ₄).1 +
        L.rocker * Real.sin θ₄ * (L.velocityRatio θ₂ θ₃ θ₄).2 = 0 ∧
      L.crank * Real.cos θ₂ + L.coupler * Real.cos θ₃ * (L.velocityRatio θ₂ θ₃ θ₄).1 -
        L.rocker * Real.cos θ₄ * (L.velocityRatio θ₂ θ₃ θ₄).2 = 0 := by
  rw [det_dependentJacobian] at hreg
  have hc : L.coupler ≠ 0 := L.coupler_pos.ne'
  have hd : L.rocker ≠ 0 := L.rocker_pos.ne'
  have hs : Real.sin (θ₃ - θ₄) ≠ 0 := fun h => hreg (by rw [h, mul_zero])
  simp only [velocityRatio]
  constructor
  · field_simp
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring
  · field_simp
    rw [Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring

/-- The derivative of the closure residuals on the product domain `input × dependent` at
`(θ₂, θ₃, θ₄)`. -/
private noncomputable def closureDeriv (θ₂ θ₃ θ₄ : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  ((L.crank • ((-Real.sin θ₂) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
        L.coupler • ((-Real.sin θ₃) • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) -
        L.rocker • ((-Real.sin θ₄) • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))).prod
      ((L.crank • (Real.cos θ₂ • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) +
        L.coupler • (Real.cos θ₃ • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) -
        L.rocker • (Real.cos θ₄ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))

/-- The closure residuals are strictly differentiable on the product domain. -/
private lemma hasStrictFDerivAt_closure (θ₂ θ₃ θ₄ : ℝ) :
    HasStrictFDerivAt (fun p : ℝ × ℝ × ℝ => L.closure p.1 p.2.1 p.2.2)
      (L.closureDeriv θ₂ θ₃ θ₄) ((θ₂, θ₃, θ₄) : ℝ × ℝ × ℝ) := by
  have hx1 := hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((θ₂, θ₃, θ₄) : ℝ × ℝ × ℝ))
  have hx3 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := ((θ₂, θ₃, θ₄) : ℝ × ℝ × ℝ))).fst
  have hx4 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := ((θ₂, θ₃, θ₄) : ℝ × ℝ × ℝ))).snd
  have hd1 := ((((Real.hasStrictDerivAt_cos θ₂).comp_hasStrictFDerivAt _ hx1).const_mul
      L.crank).add (((Real.hasStrictDerivAt_cos θ₃).comp_hasStrictFDerivAt _ hx3).const_mul
      L.coupler)).sub (((Real.hasStrictDerivAt_cos θ₄).comp_hasStrictFDerivAt _ hx4).const_mul
      L.rocker) |>.sub_const L.ground
  have hd2 := ((((Real.hasStrictDerivAt_sin θ₂).comp_hasStrictFDerivAt _ hx1).const_mul
      L.crank).add (((Real.hasStrictDerivAt_sin θ₃).comp_hasStrictFDerivAt _ hx3).const_mul
      L.coupler)).sub (((Real.hasStrictDerivAt_sin θ₄).comp_hasStrictFDerivAt _ hx4).const_mul
      L.rocker)
  exact hd1.prodMk hd2

/-- Cramer's-rule inverse of the dependent-angle partial derivative, for the determinant
`c d (sin θ₃ cos θ₄ - cos θ₃ sin θ₄)`. -/
private noncomputable def dependentInverse (θ₃ θ₄ : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (((L.coupler * L.rocker * (Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄))⁻¹ *
        -(L.rocker * Real.cos θ₄)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ((L.coupler * L.rocker * (Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄))⁻¹ *
        -(L.rocker * Real.sin θ₄)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (((L.coupler * L.rocker * (Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄))⁻¹ *
        -(L.coupler * Real.cos θ₃)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ((L.coupler * L.rocker * (Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄))⁻¹ *
        -(L.coupler * Real.sin θ₃)) • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- At a nonzero determinant, `dependentInverse` inverts the dependent-angle partial derivative
on both sides. -/
private lemma dependentInverse_spec (θ₂ : ℝ) {θ₃ θ₄ : ℝ}
    (hs' : Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄ ≠ 0) :
    (L.closureDeriv θ₂ θ₃ θ₄ ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) ∘L
        L.dependentInverse θ₃ θ₄ = ContinuousLinearMap.id ℝ (ℝ × ℝ) ∧
      L.dependentInverse θ₃ θ₄ ∘L
        (L.closureDeriv θ₂ θ₃ θ₄ ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) =
        ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  have hc0 : L.coupler ≠ 0 := L.coupler_pos.ne'
  have hd0 : L.rocker ≠ 0 := L.rocker_pos.ne'
  have hΔ : L.coupler * L.rocker * (Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc0 hd0) hs'
  constructor
  · refine ContinuousLinearMap.ext fun v => ?_
    obtain ⟨p, q⟩ := v
    refine Prod.ext ?_ ?_ <;> simp [closureDeriv, dependentInverse] <;> field_simp <;> ring
  · refine ContinuousLinearMap.ext fun v => ?_
    obtain ⟨p, q⟩ := v
    refine Prod.ext ?_ ?_ <;> simp [closureDeriv, dependentInverse] <;> field_simp <;> ring

/-- Local regular branch and velocity map: at a closed configuration with invertible
dependent-angle Jacobian there is a map `ψ` from input angles to dependent angles through the
configuration such that, near the configuration, the closed configurations are exactly the graph
of `ψ`; near `θ₂` every `(θ, ψ θ)` is closed; and `ψ` has derivative the velocity ratios at
`θ₂`. -/
lemma exists_local_branch {θ₂ θ₃ θ₄ : ℝ} (hc : L.IsClosed θ₂ θ₃ θ₄)
    (hreg : (L.dependentJacobian θ₃ θ₄).det ≠ 0) :
    ∃ ψ : ℝ → ℝ × ℝ, ψ θ₂ = (θ₃, θ₄) ∧
      (∀ᶠ p : ℝ × ℝ × ℝ in 𝓝 (θ₂, θ₃, θ₄), L.IsClosed p.1 p.2.1 p.2.2 ↔ ψ p.1 = p.2) ∧
      (∀ᶠ θ in 𝓝 θ₂, L.IsClosed θ (ψ θ).1 (ψ θ).2) ∧
      HasDerivAt ψ (L.velocityRatio θ₂ θ₃ θ₄) θ₂ := by
  have hc0 : L.coupler ≠ 0 := L.coupler_pos.ne'
  have hd0 : L.rocker ≠ 0 := L.rocker_pos.ne'
  rw [det_dependentJacobian] at hreg
  have hs : Real.sin (θ₃ - θ₄) ≠ 0 := fun h => hreg (by rw [h, mul_zero])
  have hs' : Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄ ≠ 0 := by
    rw [← Real.sin_sub]
    exact hs
  have hΔ : L.coupler * L.rocker * (Real.sin θ₃ * Real.cos θ₄ - Real.cos θ₃ * Real.sin θ₄) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc0 hd0) hs'
  -- the residual is strictly differentiable, with an invertible dependent-angle partial
  have hf := L.hasStrictFDerivAt_closure θ₂ θ₃ θ₄
  obtain ⟨hJg, hgJ⟩ := L.dependentInverse_spec θ₂ hs'
  have hJinv := ContinuousLinearMap.IsInvertible.of_inverse hJg hgJ
  have hJinvEq := ContinuousLinearMap.inverse_eq hJg hgJ
  have hf0 : (fun p : ℝ × ℝ × ℝ => L.closure p.1 p.2.1 p.2.2) ((θ₂, θ₃, θ₄) : ℝ × ℝ × ℝ) = 0 :=
    hc
  -- the implicit function theorem on the product domain gives the branch
  refine ⟨hf.implicitFunctionOfProdDomain hJinv, ?_, ?_, ?_, ?_⟩
  · have := (hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hJinv).self_of_nhds
    exact this.mp rfl
  · filter_upwards [hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hJinv] with p hp
    rw [← hp]
    exact ⟨fun h => h.trans hf0.symm, fun h => h.trans hf0⟩
  · filter_upwards [hf.eventually_apply_implicitFunctionOfProdDomain hJinv] with θ hθ
    exact hθ.trans hf0
  · -- its derivative `-J⁻¹ ∂F/∂θ₂` is the velocity-ratio vector
    have hD := (hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hJinv).hasFDerivAt.hasDerivAt
    convert hD using 1
    rw [hJinvEq]
    refine Prod.ext ?_ ?_ <;>
      simp [dependentInverse, closureDeriv, velocityRatio, Real.sin_sub] <;> field_simp <;> ring

/-- Incompatible lengths: a ground link longer than the other three links together admits no
closed configuration. -/
lemma not_isClosed_of_lt_ground (h : L.crank + L.coupler + L.rocker < L.ground)
    (θ₂ θ₃ θ₄ : ℝ) : ¬ L.IsClosed θ₂ θ₃ θ₄ := by
  intro hcl
  have hx := congrArg Prod.fst hcl
  simp only [closure, Prod.fst_zero] at hx
  have h2 := mul_le_mul_of_nonneg_left (Real.cos_le_one θ₂) L.crank_pos.le
  have h3 := mul_le_mul_of_nonneg_left (Real.cos_le_one θ₃) L.coupler_pos.le
  have h4 := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ₄) L.rocker_pos.le
  linarith

end FourBar

end FourBarLinkage

end Mechanics.MachineElements

end
