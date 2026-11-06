/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-! Quarter-weight divisibility for three binary patterns supported on two
eight-element sets and their symmetric difference. The intersection has
size four. Only the fixed one-coordinate binary identities are checked
by the kernel; the finite-coordinate conclusion follows by summation and
ordinary divisibility arithmetic. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

lemma binaryTriple_point_zero (o p x y z : ZMod 2)
    (hx : o = 0 → x = 0) (hy : p = 0 → y = 0) (hz : o + p = 0 → z = 0)
    (he : x + y + z + o * p = 0) : x.val + y.val + z.val = (o * p).val + 2 * z.val := by
  revert o p x y z
  decide +kernel

lemma binaryTriple_point_o (o p x y z : ZMod 2)
    (hx : o = 0 → x = 0) (hy : p = 0 → y = 0) (hz : o + p = 0 → z = 0)
    (he : x + y + z + o * p = o) :
    x.val + y.val + z.val = (o * (1 + p)).val + 2 * y.val := by
  revert o p x y z
  decide +kernel

lemma binaryTriple_point_p (o p x y z : ZMod 2)
    (hx : o = 0 → x = 0) (hy : p = 0 → y = 0) (hz : o + p = 0 → z = 0)
    (he : x + y + z + o * p = p) :
    x.val + y.val + z.val = (p * (1 + o)).val + 2 * x.val := by
  revert o p x y z
  decide +kernel

lemma binaryTriple_point_op (o p x y z : ZMod 2)
    (hx : o = 0 → x = 0) (hy : p = 0 → y = 0) (hz : o + p = 0 → z = 0)
    (he : x + y + z + o * p = o + p) :
    x.val + y.val + z.val = (o + p + o * p).val := by
  revert o p x y z
  decide +kernel

lemma binaryIntersectionComplement_point (o p : ZMod 2) :
    (o * (1 + p)).val + (o * p).val = o.val := by
  revert o p
  decide +kernel

lemma binaryUnion_point (o p : ZMod 2) :
    (o + p + o * p).val + (o * p).val = o.val + p.val := by
  revert o p
  decide +kernel

/-- The total integer weight of three even supported patterns is divisible
by four whenever their shifted sum is one of the four generated codewords. -/
theorem binaryTripleQuarterWeight
    {ι : Type*} [Fintype ι] (o p x y z : ι → ZMod 2)
    (hx : ∀ i, o i = 0 → x i = 0)
    (hy : ∀ i, p i = 0 → y i = 0)
    (hz : ∀ i, o i + p i = 0 → z i = 0)
    (hxEven : 2 ∣ ∑ i, (x i).val)
    (hyEven : 2 ∣ ∑ i, (y i).val)
    (hzEven : 2 ∣ ∑ i, (z i).val)
    (ho : ∑ i, (o i).val = 8) (hp : ∑ i, (p i).val = 8)
    (hop : ∑ i, (o i * p i).val = 4)
    (he : x + y + z + o * p = 0 ∨ x + y + z + o * p = o ∨
      x + y + z + o * p = p ∨ x + y + z + o * p = o + p) :
    4 ∣ (∑ i, (x i).val) + (∑ i, (y i).val) + (∑ i, (z i).val) := by
  have hsum : (∑ i, (x i).val) + (∑ i, (y i).val) + (∑ i, (z i).val) =
      ∑ i, ((x i).val + (y i).val + (z i).val) := by
    simp only [Finset.sum_add_distrib]
  have hco : (∑ i, (o i * (1 + p i)).val) = 4 := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun i _ => binaryIntersectionComplement_point (o i) (p i))
    rw [Finset.sum_add_distrib, hop, ho] at h
    omega
  have hcp : (∑ i, (p i * (1 + o i)).val) = 4 := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun i _ => binaryIntersectionComplement_point (p i) (o i))
    have hpo : (∑ i, (p i * o i).val) = 4 := by
      calc
        (∑ i, (p i * o i).val) = ∑ i, (o i * p i).val :=
          Finset.sum_congr rfl (fun i _ => congrArg ZMod.val (mul_comm (p i) (o i)))
        _ = 4 := hop
    rw [Finset.sum_add_distrib, hpo, hp] at h
    omega
  have hunion : (∑ i, (o i + p i + o i * p i).val) = 12 := by
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl
      (fun i _ => binaryUnion_point (o i) (p i))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hop, ho, hp] at h
    omega
  rcases he with he | he | he | he
  · have hi (i : ι) := binaryTriple_point_zero (o i) (p i) (x i) (y i) (z i)
      (hx i) (hy i) (hz i) (congrFun he i)
    rw [hsum, Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib,
      ← Finset.mul_sum, hop]
    omega
  · have hi (i : ι) := binaryTriple_point_o (o i) (p i) (x i) (y i) (z i)
      (hx i) (hy i) (hz i) (congrFun he i)
    rw [hsum, Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib,
      ← Finset.mul_sum, hco]
    omega
  · have hi (i : ι) := binaryTriple_point_p (o i) (p i) (x i) (y i) (z i)
      (hx i) (hy i) (hz i) (congrFun he i)
    rw [hsum, Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib,
      ← Finset.mul_sum, hcp]
    omega
  · have hi (i : ι) := binaryTriple_point_op (o i) (p i) (x i) (y i) (z i)
      (hx i) (hy i) (hz i) (congrFun he i)
    rw [hsum, Finset.sum_congr rfl (fun i _ => hi i), hunion]
    decide

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
