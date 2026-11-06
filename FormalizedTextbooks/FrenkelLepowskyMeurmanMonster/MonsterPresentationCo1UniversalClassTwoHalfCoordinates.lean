/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact coordinate formulas for the source group's actual hyperbolic block images. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoHalfLift

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each actual hyperbolic block uses distinct full binary coordinate indices. -/
theorem co1UniversalHalfIndex_injective (b : Fin 2) :
    Function.Injective (co1UniversalHalfIndex b) := by
  intro i j h
  apply Fin.ext
  have he := congrArg Fin.val h
  by_cases hb : b = 0 <;> simp only [co1UniversalHalfIndex, hb, ite_true, ite_false,
    Fin.val_castAdd, Fin.val_natAdd] at he <;> omega

/-- A block vector retains every coordinate in its actual block. -/
theorem co1UniversalHalfVector_at (b : Fin 2) (v : Fin 12 → ZMod 2) (i : Fin 12) :
    co1UniversalHalfVector b v (co1UniversalHalfIndex b i) = v i := by
  simp only [co1UniversalHalfVector, Finset.sum_apply, Pi.single_apply,
    (co1UniversalHalfIndex_injective b).eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- A first-block vector vanishes at every actual second-block coordinate. -/
theorem co1UniversalHalfVector_first_other (v : Fin 12 → ZMod 2) (j : Fin 12) :
    co1UniversalHalfVector 0 v (Fin.natAdd 12 j) = 0 := by
  change (∑ i : Fin 12, (Pi.single (Fin.castAdd 12 i) (v i) : Fin 24 → ZMod 2))
    (Fin.natAdd 12 j) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : Fin.castAdd 12 i ≠ Fin.natAdd 12 j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp only [Pi.single_apply, h.symm, ite_false]

/-- A second-block vector vanishes at every actual first-block coordinate. -/
theorem co1UniversalHalfVector_second_other (v : Fin 12 → ZMod 2) (j : Fin 12) :
    co1UniversalHalfVector 1 v (Fin.castAdd 12 j) = 0 := by
  change (∑ i : Fin 12, (Pi.single (Fin.natAdd 12 i) (v i) : Fin 24 → ZMod 2))
    (Fin.castAdd 12 j) = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : Fin.natAdd 12 i ≠ Fin.castAdd 12 j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp only [Pi.single_apply, h.symm, ite_false]

/-- The two block images reconstruct every original full binary vector exactly. -/
theorem co1UniversalHalfVector_reconstruct (v : Fin 24 → ZMod 2) :
    co1UniversalHalfVector 0 (fun i => v (Fin.castAdd 12 i)) +
      co1UniversalHalfVector 1 (fun i => v (Fin.natAdd 12 i)) = v := by
  funext k
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective k
  cases j with
  | inl j =>
    rw [finSumFinEquiv_apply_left, Pi.add_apply, co1UniversalHalfVector_second_other, add_zero]
    exact co1UniversalHalfVector_at 0 _ j
  | inr j =>
    rw [finSumFinEquiv_apply_right, Pi.add_apply, co1UniversalHalfVector_first_other, zero_add]
    exact co1UniversalHalfVector_at 1 _ j

/-- The actual polar coefficient between opposite block images is the original cocycle pairing. -/
theorem co1UniversalHalfVector_polar (v w : Fin 24 → ZMod 2) :
    co1BinaryPolar (co1UniversalHalfVector 0 (fun i => v (Fin.castAdd 12 i)))
      (co1UniversalHalfVector 1 (fun i => w (Fin.natAdd 12 i))) = qBeta v w := by
  change qBeta _ _ + qBeta _ _ = _
  simp only [qBeta, co1UniversalHalfVector_first_other, co1UniversalHalfVector_second_other,
    zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  funext i
  rw [show Fin.castAdd 12 i = co1UniversalHalfIndex 0 i from rfl,
    show Fin.natAdd 12 i = co1UniversalHalfIndex 1 i from rfl,
    co1UniversalHalfVector_at, co1UniversalHalfVector_at]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
