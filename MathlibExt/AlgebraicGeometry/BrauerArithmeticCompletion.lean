/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# The completion in the zero-cycle Brauer--Manin complex

The notation `M^` of Harpaz--Wittenberg, arXiv:1409.0993v4, p. 1,
means `lim_n M/nM`. This file gives that exact coherent-family inverse limit
and its native unit and induced maps. The quotients need not be finite, so it
does not substitute a completion over all finite-index subgroups.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerArithmeticCompletion

variable (A : Type*) [AddCommGroup A]

/-- Positive moduli in the arithmetic inverse limit. -/
abbrev Modulus := {n : ℕ // 0 < n}

/-- The actual multiplication map defining `nM`. -/
def multiplication (n : ℕ) : A →+ A := n • AddMonoidHom.id A

/-- Actual multiples in the additive group. -/
def multiples (n : ℕ) : AddSubgroup A := (multiplication A n).range

/-- The actual quotient `M/nM`. -/
abbrev Mod (n : ℕ) := A ⧸ multiples A n

theorem multiples_le {n m : ℕ} (h : n ∣ m) : multiples A m ≤ multiples A n := by
  obtain ⟨k, rfl⟩ := h
  rintro _ ⟨a, rfl⟩
  refine ⟨k • a, ?_⟩
  change n • (k • a) = (n * k) • a
  simpa only [Nat.mul_comm] using (mul_nsmul a k n).symm

/-- The actual reduction `M/mM → M/nM` for `n | m`. -/
def transition {n m : ℕ} (h : n ∣ m) : Mod A m →+ Mod A n :=
  QuotientAddGroup.map _ _ (AddMonoidHom.id A) (multiples_le A h)

/-- Coherent families of actual residue classes form the arithmetic inverse limit. -/
def Completion : AddSubgroup (∀ n : Modulus, Mod A n.val) where
  carrier := {a | ∀ n m : Modulus, ∀ h : n.val ∣ m.val, transition A h (a m) = a n}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb n m h
    simp only [Pi.add_apply, map_add, ha n m h, hb n m h]
  neg_mem' := by
    intro a ha n m h
    simp only [Pi.neg_apply, map_neg, ha n m h]

/-- The actual map of a group to its arithmetic inverse limit. -/
def unit : A →+ Completion A where
  toFun a := ⟨fun _ => QuotientAddGroup.mk a, by intro n m h; rfl⟩
  map_zero' := by ext n; rfl
  map_add' a b := by ext n; rfl

/-- The actual projection of the inverse limit to one modulus quotient. -/
def projection (n : Modulus) : Completion A →+ Mod A n.val where
  toFun a := a.val n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- An additive map killed by `n` descends through the actual `M/nM`. -/
def liftKilled {B : Type*} [AddCommGroup B] (f : A →+ B)
    (n : Modulus) (h : ∀ a, n.val • f a = 0) : Mod A n.val →+ B :=
  QuotientAddGroup.lift _ f (by
    rintro _ ⟨a, rfl⟩
    change f (n.val • a) = 0
    rw [map_nsmul, h a])

/-- Completed evaluation is fixed by the `n`th inverse-limit coordinate. -/
def completedEvaluation {B : Type*} [AddCommGroup B] (f : A →+ B)
    (n : Modulus) (h : ∀ a, n.val • f a = 0) : Completion A →+ B :=
  (liftKilled A f n h).comp (projection A n)

@[simp] theorem completedEvaluation_unit {B : Type*} [AddCommGroup B]
    (f : A →+ B) (n : Modulus) (h : ∀ a, n.val • f a = 0) (a : A) :
    completedEvaluation A f n h (unit A a) = f a := rfl

section Maps

variable {A} {B : Type*} [AddCommGroup B] (f : A →+ B)

/-- The quotient map induced by the same additive map, at one modulus. -/
def modMap (n : ℕ) : Mod A n →+ Mod B n :=
  QuotientAddGroup.map _ _ f (by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, by simp [multiplication, map_nsmul]⟩)

theorem modMap_transition {n m : ℕ} (h : n ∣ m) (a : Mod A m) :
    modMap f n (transition A h a) = transition B h (modMap f m a) := by
  induction a using QuotientAddGroup.induction_on with
  | H a => rfl

/-- The native induced map on coherent inverse-limit families. -/
def map : Completion A →+ Completion B where
  toFun a := ⟨fun n => modMap f n.val (a.val n), by
    intro n m h
    rw [← modMap_transition f h, a.property n m h]⟩
  map_zero' := by ext n; exact map_zero _
  map_add' a b := by ext n; exact map_add _ _ _

/-- Completion is normalized on actual integral classes. -/
@[simp] theorem map_unit (a : A) : map f (unit A a) = unit B (f a) := by
  ext n
  rfl

end Maps

end AlgebraicGeometry.BrauerArithmeticCompletion
