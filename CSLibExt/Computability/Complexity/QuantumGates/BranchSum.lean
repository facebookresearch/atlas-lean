/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.CircuitSemantics
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Kept-index branch sum: acceptance over orthogonal index branches

An index register of `t` qubits is prepared in the superposition
`∑ r, α r • |r⟩` and kept untouched while a branch circuit selected by a
classical label map `λ` acts on an `m`-qubit work register (the low `m`
qubits, so the output qubit `0` lies in the work register). The final state
is the branch sum `∑ r, α r • (ψ r ⊗ |r⟩)` whose branches stay orthogonal,
so the acceptance probability is the classical mixture
`∑ r, ‖α r‖² • acceptProb (ψ r)`: branch phases are irrelevant, and grouped
by label it is `∑ l, q l • acceptProb (φ l)` with
`q l = ∑ r with λ r = l, ‖α r‖²`. A reject label whose branch state has
acceptance `0` contributes `0`. Shared support for deferred-measurement
arguments (coin values grouped by label) and Shor base sampling (sampled
base values as the index).

Source: M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum
Information, Cambridge University Press, 2000, Chapter 4 (controlled
operations and measurement).
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false

/-- **Branch state over a kept index register.** For amplitudes
`α : Fin (2 ^ t) → ℂ` and work-register states `ψ r` on `m` qubits, the
state `∑ r, α r • (ψ r ⊗ |r⟩)` on `m + t` qubits: branch `r` occupies the
basis states whose high `t` bits are `r`. -/
noncomputable def branchState {m t : ℕ} (α : Fin (2 ^ t) → ℂ)
    (ψ : Fin (2 ^ t) → (Fin (2 ^ m) → ℂ)) : Fin (2 ^ (m + t)) → ℂ :=
  ∑ r, α r • tensorProd (ψ r) (Pi.single r 1)

private theorem divLt_twoPow {m t : ℕ} (s : Fin (2 ^ (m + t))) :
    s.val / 2 ^ m < 2 ^ t := by
  rw [Nat.div_lt_iff_lt_mul (pow_pos (by decide : (0 : ℕ) < 2) _)]
  calc s.val < 2 ^ (m + t) := s.isLt
    _ = 2 ^ t * 2 ^ m := by rw [pow_add, Nat.mul_comm]

private theorem memBound_parts {m t : ℕ} (r : Fin (2 ^ t)) (w : Fin (2 ^ m)) :
    r.val * 2 ^ m + w.val < 2 ^ (m + t) := by
  have hr : r.val < 2 ^ t := r.isLt
  have hw : w.val < 2 ^ m := w.isLt
  calc r.val * 2 ^ m + w.val < 2 ^ t * 2 ^ m := by
        have h1 : r.val * 2 ^ m + w.val < (r.val + 1) * 2 ^ m := by
          rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left hw _
        exact h1.trans_le (Nat.mul_le_mul_right _ hr)
    _ = 2 ^ (m + t) := by rw [pow_add, Nat.mul_comm]

private theorem star_mul_self_re (z : ℂ) :
    (starRingEnd ℂ z * z).re = Complex.normSq z := by
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]

private def branchToParts (m t : ℕ) (s : Fin (2 ^ (m + t))) : Fin (2 ^ t) × Fin (2 ^ m) :=
  (⟨s.val / 2 ^ m, divLt_twoPow s⟩,
    ⟨s.val % 2 ^ m, Nat.mod_lt _ (pow_pos (by decide : (0 : ℕ) < 2) _)⟩)

private def branchOfParts (m t : ℕ) (p : Fin (2 ^ t) × Fin (2 ^ m)) : Fin (2 ^ (m + t)) :=
  ⟨p.1.val * 2 ^ m + p.2.val, memBound_parts p.1 p.2⟩

private theorem divPart_add {m t : ℕ} (r : Fin (2 ^ t)) (w : Fin (2 ^ m)) :
    (r.val * 2 ^ m + w.val) / 2 ^ m = r.val := by
  rw [Nat.mul_comm r.val (2 ^ m), Nat.mul_add_div (pow_pos (by decide : (0 : ℕ) < 2) _) _ _,
    Nat.div_eq_zero_iff.mpr (Or.inr w.isLt), Nat.add_zero]

private theorem modPart_add {m t : ℕ} (r : Fin (2 ^ t)) (w : Fin (2 ^ m)) :
    (r.val * 2 ^ m + w.val) % 2 ^ m = w.val :=
  Nat.mul_add_mod_of_lt w.isLt

private theorem branchParts_leftInv (m t : ℕ) (s : Fin (2 ^ (m + t))) :
    branchOfParts m t (branchToParts m t s) = s := by
  refine Fin.ext_iff.mpr ?_
  exact Nat.div_add_mod' _ _

private theorem branchParts_rightInv (m t : ℕ) (p : Fin (2 ^ t) × Fin (2 ^ m)) :
    branchToParts m t (branchOfParts m t p) = p := by
  refine Prod.ext ?_ ?_ <;> refine Fin.ext_iff.mpr ?_
  · exact divPart_add p.1 p.2
  · exact modPart_add p.1 p.2

private def branchPartsEquiv (m t : ℕ) :
    Fin (2 ^ (m + t)) ≃ Fin (2 ^ t) × Fin (2 ^ m) where
  toFun := branchToParts m t
  invFun := branchOfParts m t
  left_inv := branchParts_leftInv m t
  right_inv := branchParts_rightInv m t

private theorem branchState_entry {m t : ℕ} (α : Fin (2 ^ t) → ℂ)
    (ψ : Fin (2 ^ t) → (Fin (2 ^ m) → ℂ)) (s : Fin (2 ^ (m + t)))
    (r : Fin (2 ^ t)) (w : Fin (2 ^ m))
    (hr : r.val = s.val / 2 ^ m) (hw : w.val = s.val % 2 ^ m) :
    branchState α ψ s = α r * ψ r w := by
  have hdiv : ∀ h : s.val / 2 ^ m < 2 ^ t, (⟨s.val / 2 ^ m, h⟩ : Fin (2 ^ t)) = r :=
    fun h => Fin.ext_iff.mpr hr.symm
  have hmod : ∀ h : s.val % 2 ^ m < 2 ^ m, (⟨s.val % 2 ^ m, h⟩ : Fin (2 ^ m)) = w :=
    fun h => Fin.ext_iff.mpr hw.symm
  simp only [branchState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tensorProd,
    Pi.single_apply]
  rw [Finset.sum_eq_single r]
  · rw [ite_eq_left (hdiv _), mul_one, hmod _]
  · intro x _ hx
    have hne : ∀ h : s.val / 2 ^ m < 2 ^ t, (⟨s.val / 2 ^ m, h⟩ : Fin (2 ^ t)) ≠ x := by
      intro h hcon
      exact hx ((hdiv h).symm.trans hcon).symm
    rw [ite_eq_right (hne _), mul_zero, mul_zero]
  · simp

/-- Entry of a branch state at the basis index with work part `w` and index
part `r` encoded as `r * 2 ^ m + w`. -/
theorem branchState_apply {m t : ℕ} (α : Fin (2 ^ t) → ℂ)
    (ψ : Fin (2 ^ t) → (Fin (2 ^ m) → ℂ)) (r : Fin (2 ^ t)) (w : Fin (2 ^ m)) :
    branchState α ψ ⟨r.val * 2 ^ m + w.val, by
      have hr : r.val < 2 ^ t := r.isLt
      have hw : w.val < 2 ^ m := w.isLt
      calc r.val * 2 ^ m + w.val < 2 ^ t * 2 ^ m := by
            have h1 : r.val * 2 ^ m + w.val < (r.val + 1) * 2 ^ m := by
              rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left hw _
            exact h1.trans_le (Nat.mul_le_mul_right _ hr)
        _ = 2 ^ (m + t) := by rw [pow_add, Nat.mul_comm]⟩ = α r * ψ r w := by
  exact branchState_entry α ψ _ r w (divPart_add r w).symm (modPart_add r w).symm

/-- **Branch states are orthogonal-branch mixtures for the norm:**
`sqNorm` of a branch state is `∑ r, ‖α r‖² • sqNorm (ψ r)`. -/
theorem sqNorm_branchState {m t : ℕ} (α : Fin (2 ^ t) → ℂ)
    (ψ : Fin (2 ^ t) → (Fin (2 ^ m) → ℂ)) :
    sqNorm (branchState α ψ) =
      ∑ r, Complex.normSq (α r) * sqNorm (ψ r) := by
  have perEntry : ∀ s : Fin (2 ^ (m + t)),
      (starRingEnd ℂ (branchState α ψ s) * branchState α ψ s).re =
        Complex.normSq (α (branchPartsEquiv m t s).1) *
          Complex.normSq (ψ (branchPartsEquiv m t s).1 (branchPartsEquiv m t s).2) := by
    intro s
    rw [star_mul_self_re,
      branchState_entry α ψ s (branchPartsEquiv m t s).1 (branchPartsEquiv m t s).2 rfl rfl,
      Complex.normSq_mul]
  have hsq : ∀ r : Fin (2 ^ t), sqNorm (ψ r) = ∑ w, Complex.normSq (ψ r w) := by
    intro r
    simp only [sqNorm]
    exact Finset.sum_congr rfl (fun w _ => star_mul_self_re _)
  calc sqNorm (branchState α ψ)
      = ∑ s, Complex.normSq (α (branchPartsEquiv m t s).1) *
          Complex.normSq (ψ (branchPartsEquiv m t s).1 (branchPartsEquiv m t s).2) := by
        simp only [sqNorm]
        exact Finset.sum_congr rfl (fun s _ => perEntry s)
    _ = ∑ p : Fin (2 ^ t) × Fin (2 ^ m),
          Complex.normSq (α p.1) * Complex.normSq (ψ p.1 p.2) :=
        Fintype.sum_equiv (branchPartsEquiv m t) _ _ (fun s => rfl)
    _ = ∑ r, ∑ w, Complex.normSq (α r) * Complex.normSq (ψ r w) :=
        Fintype.sum_prod_type _
    _ = ∑ r, Complex.normSq (α r) * sqNorm (ψ r) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        simp only [← Finset.mul_sum, hsq r]

/-- **Branch-sum identity:** the acceptance probability of a branch state
is `∑ r, ‖α r‖² • acceptProb (ψ r)`. In particular only the branch weights
`‖α r‖²` matter, not the branch phases. -/
theorem acceptProb_branchState {m t : ℕ} (hm : 1 ≤ m) (α : Fin (2 ^ t) → ℂ)
    (ψ : Fin (2 ^ t) → (Fin (2 ^ m) → ℂ)) :
    acceptProb (branchState α ψ) =
      ∑ r, Complex.normSq (α r) * acceptProb (ψ r) := by
  revert ψ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  intro ψ
  have hq0_val : ∀ x : ℕ, (qBit 0 x).val = x % 2 := fun x => by simp [qBit]
  have hadd : ∀ r w : ℕ, (r * 2 ^ (k + 1) + w) % 2 = w % 2 := by
    intro r w
    have h : r * 2 ^ (k + 1) = 2 * (r * 2 ^ k) := by
      rw [pow_succ]; ring
    rw [h]
    exact Nat.mul_add_mod 2 (r * 2 ^ k) w
  have hmod : ∀ s : ℕ, s % 2 = (s % 2 ^ (k + 1)) % 2 := by
    intro s
    have hdecomp : s = (s / 2 ^ (k + 1)) * 2 ^ (k + 1) + s % 2 ^ (k + 1) := by
      have h := Nat.div_add_mod s (2 ^ (k + 1))
      rw [Nat.mul_comm (2 ^ (k + 1)) (s / 2 ^ (k + 1))] at h
      exact h.symm
    conv_lhs => rw [hdecomp]
    exact hadd _ _
  have hq : ∀ s : Fin (2 ^ (k + 1 + t)),
      qBit 0 s.val = qBit 0 (branchPartsEquiv (k + 1) t s).2.val := by
    intro s
    apply Fin.ext
    rw [hq0_val, hq0_val]
    show s.val % 2 = (s.val % 2 ^ (k + 1)) % 2
    exact hmod s.val
  have perEntry : ∀ s : Fin (2 ^ (k + 1 + t)),
      (if qBit 0 s.val = 1 then (starRingEnd ℂ (branchState α ψ s) * branchState α ψ s).re else 0) =
      (if qBit 0 (branchPartsEquiv (k + 1) t s).2.val = 1 then
        Complex.normSq (α (branchPartsEquiv (k + 1) t s).1) *
          Complex.normSq (ψ (branchPartsEquiv (k + 1) t s).1 (branchPartsEquiv (k + 1) t s).2)
      else 0) := by
    intro s
    rw [hq s]
    by_cases h : qBit 0 (branchPartsEquiv (k + 1) t s).2.val = 1
    · rw [ite_eq_left h, ite_eq_left h, star_mul_self_re,
        branchState_entry α ψ s (branchPartsEquiv (k + 1) t s).1
          (branchPartsEquiv (k + 1) t s).2 rfl rfl, Complex.normSq_mul]
    · rw [ite_eq_right h, ite_eq_right h]
  have hacc : ∀ r : Fin (2 ^ t),
      acceptProb (ψ r) =
        ∑ w, (if qBit 0 w.val = 1 then Complex.normSq (ψ r w) else 0) := by
    intro r
    simp only [acceptProb]
    exact Finset.sum_congr rfl (fun w _ => by
      by_cases h : qBit 0 w.val = 1
      · rw [ite_eq_left h, ite_eq_left h, star_mul_self_re]
      · rw [ite_eq_right h, ite_eq_right h])
  calc acceptProb (branchState α ψ)
      = ∑ s, (if qBit 0 (branchPartsEquiv (k + 1) t s).2.val = 1 then
          Complex.normSq (α (branchPartsEquiv (k + 1) t s).1) *
            Complex.normSq (ψ (branchPartsEquiv (k + 1) t s).1 (branchPartsEquiv (k + 1) t s).2)
        else 0) := by
        simp only [acceptProb]
        exact Finset.sum_congr rfl (fun s _ => perEntry s)
    _ = ∑ p : Fin (2 ^ t) × Fin (2 ^ (k + 1)),
          (if qBit 0 p.2.val = 1 then
            Complex.normSq (α p.1) * Complex.normSq (ψ p.1 p.2)
          else 0) :=
        Fintype.sum_equiv (branchPartsEquiv (k + 1) t) _ _ (fun s => rfl)
    _ = ∑ r, ∑ w, (if qBit 0 w.val = 1 then
          Complex.normSq (α r) * Complex.normSq (ψ r w)
        else 0) :=
        Fintype.sum_prod_type _
    _ = ∑ r, Complex.normSq (α r) * acceptProb (ψ r) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [hacc r, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by rw [mul_ite, mul_zero])

/-- **Phase irrelevance:** replacing each branch amplitude by one of the
same squared norm does not change the acceptance probability. -/
theorem acceptProb_branchState_congr_normSq {m t : ℕ} {α α' : Fin (2 ^ t) → ℂ}
    (hα : ∀ r, Complex.normSq (α' r) = Complex.normSq (α r))
    (ψ : Fin (2 ^ t) → (Fin (2 ^ m) → ℂ)) :
    acceptProb (branchState α' ψ) = acceptProb (branchState α ψ) := by
  have perS : ∀ s : Fin (2 ^ (m + t)),
      (if qBit 0 s.val = 1 then (starRingEnd ℂ (branchState α' ψ s) * branchState α' ψ s).re
        else 0) =
      (if qBit 0 s.val = 1 then (starRingEnd ℂ (branchState α ψ s) * branchState α ψ s).re
        else 0) := by
    intro s
    by_cases h : qBit 0 s.val = 1
    · rw [ite_eq_left h, ite_eq_left h, star_mul_self_re, star_mul_self_re,
        branchState_entry α' ψ s (branchPartsEquiv m t s).1 (branchPartsEquiv m t s).2 rfl rfl,
        branchState_entry α ψ s (branchPartsEquiv m t s).1 (branchPartsEquiv m t s).2 rfl rfl,
        Complex.normSq_mul, Complex.normSq_mul, hα]
    · rw [ite_eq_right h, ite_eq_right h]
  simp only [acceptProb]
  exact Finset.sum_congr rfl (fun s _ => perS s)

/-- **Branch-sum identity grouped by label.** If the branch states factor
through a label map`λ` into finitely many labels with branch states `φ`,
acceptance is `∑ l, q l • acceptProb (φ l)` with branch weights
`q l = ∑ r with λ r = l, ‖α r‖²`. A label with `acceptProb (φ l) = 0` (a
reject branch) contributes `0`. -/
theorem acceptProb_branchState_grouped {m t : ℕ} (hm : 1 ≤ m) {Label : Type*}
    [Fintype Label] [DecidableEq Label] (α : Fin (2 ^ t) → ℂ)
    (lab : Fin (2 ^ t) → Label) (φ : Label → (Fin (2 ^ m) → ℂ)) :
    acceptProb (branchState α (fun r => φ (lab r))) =
      ∑ l, (∑ r ∈ Finset.univ.filter (fun r => lab r = l), Complex.normSq (α r)) *
        acceptProb (φ l) := by
  revert φ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  intro φ
  have hbase : acceptProb (branchState α (fun r => φ (lab r))) =
      ∑ r, Complex.normSq (α r) * acceptProb (φ (lab r)) :=
    acceptProb_branchState hm α (fun r => φ (lab r))
  calc acceptProb (branchState α (fun r => φ (lab r)))
      = ∑ r, Complex.normSq (α r) * acceptProb (φ (lab r)) := hbase
    _ = ∑ l, ∑ r ∈ Finset.univ.filter (fun r => lab r = l),
          Complex.normSq (α r) * acceptProb (φ (lab r)) := by
        rw [← Finset.sum_fiberwise Finset.univ lab
          (fun r => Complex.normSq (α r) * acceptProb (φ (lab r)))]
    _ = ∑ l, (∑ r ∈ Finset.univ.filter (fun r => lab r = l), Complex.normSq (α r)) *
          acceptProb (φ l) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        have hmem : ∀ r ∈ Finset.univ.filter (fun r => lab r = l),
            Complex.normSq (α r) * acceptProb (φ (lab r)) =
            Complex.normSq (α r) * acceptProb (φ l) := by
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          rw [hr]
        rw [Finset.sum_congr rfl hmem]
        exact (Finset.sum_mul _ _ _).symm

end Cslib.Complexity.Classes
