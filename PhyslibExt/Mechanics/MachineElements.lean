/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Signed ideal gear-train ratio and port power

## i. Overview

A finite parallel-axis gear train: shafts `0, …, n`, all oriented along one common axis
direction, and meshes `k = 0, …, n - 1`, mesh `k` joining the upstream shaft `k` to the
downstream shaft `k + 1`. Mesh `k` has a driver gear with `driverTeeth` teeth on the upstream
shaft and a driven gear with `drivenTeeth` teeth on the downstream shaft. Angular velocities
`ω j` are signed about the common axis direction.

Model inputs:

* rigid ideal no-slip gears: across mesh `k` the downstream speed is the signed ratio
  `sense * driverTeeth / drivenTeeth` times the upstream speed, where the sense is `-1` for
  an external mesh (the sense of rotation reverses) and `1` for an internal (ring-gear)
  mesh (the sense is kept);
* power-into-component signs: `a k` is the torque the upstream shaft applies to mesh `k` and
  `b k` the torque the downstream shaft applies to mesh `k`, both about the common axis
  direction, so the power into mesh `k` is `a k * ω k + b k * ω (k + 1)`;
* the ideal lossless port convention: a mesh absorbs no power on any motion of its two shafts
  allowed by its no-slip constraint;
* massless rigid shafts in equilibrium: the external torque applied to shaft `j`, whose power
  into the train is that torque times `ω j`, equals the sum of the torques shaft `j` applies
  to its meshes (`shaftLoad`).

Results: the speed of the last shaft is the product of the signed mesh ratios times the speed
of the first shaft; the product equals `(-1) ^ (number of external meshes)` times the ratio of
the tooth-count products, so with positive tooth counts its sign is set by the parity of the
external meshes; each mesh carries the torque relation `a k + ratio * b k = 0`; the total power
into the train through its shaft ports vanishes; and for a train loaded only at its first and
last shafts the port torques satisfy `τ_in + R * τ_out = 0`, so `τ_out = -τ_in / R`.

Non-goals: backlash, tooth-contact stress, friction losses, inertia, planetary trains, and any
empirical adequacy or system safety claim.

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

## iii. Table of contents

- A. Meshes and the train ratio
- B. Port torques and power

## iv. References

- J. J. Uicker, G. R. Pennock and J. E. Shigley, *Theory of Machines and Mechanisms*,
  5th edition, 2017 (gear trains and train value).
- R. G. Budynas and J. K. Nisbett, *Shigley's Mechanical Engineering Design*, 10th edition,
  2015 (gear trains; power transmitted by an ideal train).
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

/-- One mesh: `driverTeeth` teeth on the driver gear (upstream shaft), `drivenTeeth` teeth on
the driven gear (downstream shaft), and the mesh kind. -/
structure Mesh where
  driverTeeth : ℕ
  drivenTeeth : ℕ
  kind : MeshKind

/-- Signed angular-speed ratio of a mesh, downstream over upstream:
`sense * driverTeeth / drivenTeeth`. -/
noncomputable def Mesh.ratio (g : Mesh) : ℝ :=
  g.kind.sense * ((g.driverTeeth : ℝ) / g.drivenTeeth)

variable {n : ℕ}

/-- Every tooth count of the train is positive. -/
def PositiveTeeth (m : Fin n → Mesh) : Prop :=
  ∀ k, 0 < (m k).driverTeeth ∧ 0 < (m k).drivenTeeth

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

/-- The speed of the last shaft is the train ratio times the speed of the first shaft. -/
lemma IsNoSlip.last_eq {m : Fin n → Mesh} {ω : Fin (n + 1) → ℝ} (h : IsNoSlip m ω) :
    ω (Fin.last n) = trainRatio m * ω 0 := by
  exact last_eq_aux n m ω h

/-- The no-slip constraints admit a motion with any prescribed first-shaft speed. -/
lemma exists_isNoSlip (m : Fin n → Mesh) (ω₀ : ℝ) :
    ∃ ω : Fin (n + 1) → ℝ, IsNoSlip m ω ∧ ω 0 = ω₀ := by
  exact exists_aux n m ω₀

/-- The train ratio is `(-1) ^ (number of external meshes)` times the product of the driver
tooth counts over the product of the driven tooth counts. -/
lemma trainRatio_eq (m : Fin n → Mesh) :
    trainRatio m = (-1) ^ externalCount m *
      ((∏ k, ((m k).driverTeeth : ℝ)) / ∏ k, ((m k).drivenTeeth : ℝ)) := by
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

/-- With positive tooth counts the train ratio is nonzero. -/
lemma trainRatio_ne_zero {m : Fin n → Mesh} (h : PositiveTeeth m) : trainRatio m ≠ 0 := by
  unfold trainRatio
  rw [Finset.prod_ne_zero_iff]
  intro k _
  unfold Mesh.ratio
  apply mul_ne_zero
  · cases (m k).kind with
    | external => simp [MeshKind.sense]
    | internal => simp [MeshKind.sense]
  · apply div_ne_zero
    · exact_mod_cast ne_of_gt (h k).1
    · exact_mod_cast ne_of_gt (h k).2

/-- With positive tooth counts the last shaft turns in the sense of the first exactly when the
number of external meshes is even. -/
lemma trainRatio_pos_iff {m : Fin n → Mesh} (h : PositiveTeeth m) :
    0 < trainRatio m ↔ Even (externalCount m) := by
  rw [trainRatio_eq]
  have hPos : 0 < (∏ k, ((m k).driverTeeth : ℝ)) / ∏ k, ((m k).drivenTeeth : ℝ) := by
    apply div_pos
    · apply Finset.prod_pos
      intro k _
      exact_mod_cast (h k).1
    · apply Finset.prod_pos
      intro k _
      exact_mod_cast (h k).2
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
`w' = ratio * w`. -/
def IsLossless (m : Fin n → Mesh) (a b : Fin n → ℝ) : Prop :=
  ∀ k : Fin n, ∀ w : ℝ, a k * w + b k * ((m k).ratio * w) = 0

/-- External torque on shaft `j` of massless rigid shafts in equilibrium: the sum of the
torques shaft `j` applies to the meshes it drives (`a k` when `j` is upstream of mesh `k`)
and to the meshes that drive it (`b k` when `j` is downstream of mesh `k`). -/
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

/-- Total power balance: on every no-slip motion the power into the train through its shaft
ports, `∑ j, shaftLoad a b j * ω j`, vanishes. -/
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

/-- Port torque relation of a train loaded only at its first and last shafts:
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

/-- With positive tooth counts the output port torque is `τ_out = -τ_in / R`. -/
lemma torque_out_eq {m : Fin n → Mesh} {a b : Fin n → ℝ} (ht : PositiveTeeth m)
    (hl : IsLossless m a b)
    (htwo : ∀ j : Fin (n + 1), j ≠ 0 → j ≠ Fin.last n → shaftLoad a b j = 0) :
    shaftLoad a b (Fin.last n) = -shaftLoad a b 0 / trainRatio m := by
  have hR : trainRatio m ≠ 0 := trainRatio_ne_zero ht
  have hRel : shaftLoad a b 0 + trainRatio m * shaftLoad a b (Fin.last n) = 0 :=
    torque_relation hl htwo
  rw [eq_div_iff hR]
  have hC : trainRatio m * shaftLoad a b (Fin.last n) =
      shaftLoad a b (Fin.last n) * trainRatio m := mul_comm _ _
  linarith [hRel, hC]

/-- Swapping the orientation of the last shaft negates its signed speed, so the reoriented
speed follows the negated ratio; keeping the old sign is rejected on every motion with a
nonzero first-shaft speed. -/
lemma orientation_swap {m : Fin n → Mesh} {ω : Fin (n + 1) → ℝ} (ht : PositiveTeeth m)
    (hω : IsNoSlip m ω) (h0 : ω 0 ≠ 0) :
    -ω (Fin.last n) = -trainRatio m * ω 0 ∧ -ω (Fin.last n) ≠ trainRatio m * ω 0 := by
  have hLast : ω (Fin.last n) = trainRatio m * ω 0 := IsNoSlip.last_eq hω
  have hR : trainRatio m ≠ 0 := trainRatio_ne_zero ht
  constructor
  · rw [hLast]
    ring
  · rw [hLast]
    intro hCon
    have hZero : trainRatio m * ω 0 = 0 := by linarith [hCon]
    have hNe : trainRatio m * ω 0 ≠ 0 := mul_ne_zero hR h0
    exact hNe hZero

end Mechanics.MachineElements

end
