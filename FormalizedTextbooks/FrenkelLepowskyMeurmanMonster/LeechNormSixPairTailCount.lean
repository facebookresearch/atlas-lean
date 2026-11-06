/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountConvolution
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Generating series for the actual remaining 22 bounded source coordinates.
The two exponents record the coordinate square sum and the coordinate sum
modulo eight. Every coefficient counts vectors, with their source residue
conditions imposed coordinate by coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The actual remaining source coordinates with specified integer square sum and height residue. -/
def LeechNormSixTailSolution (m : Bool) (c : Fin 22 → ZMod 2) (q : ℕ) (h : ZMod 8) :=
  {a : Fin 22 → Fin 17 //
    (∀ i, (leechNormEightCoordinate (a i) : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * ((c i).val : ZMod 4)) ∧
    (∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2) = q ∧
    ((∑ i, leechNormEightCoordinate (a i) : ℤ) : ZMod 8) = h}

instance (m : Bool) (c : Fin 22 → ZMod 2) (q : ℕ) (h : ZMod 8) :
    Fintype (LeechNormSixTailSolution m c q h) := by
  unfold LeechNormSixTailSolution
  infer_instance

/-- Abstract finite enumeration for bounded assignments; no enumeration is expanded. -/
@[instance_reducible] def leechNormSixTailAssignmentFintype : Fintype (Fin 22 → Fin 17) :=
  Fintype.ofFinite _

attribute [local instance] leechNormSixTailAssignmentFintype

/-- Independent coordinates multiply their genuine counting series. -/
def leechNormSixTailSeries (m : Bool) (c : Fin 22 → ZMod 2) : LeechNormEightSeries :=
  ∏ i, leechNormEightCoordinateSeries m (c i)

private theorem leechNormSixTailSeries_expand_generic {ι κ : Type*}
    [Fintype ι] [Fintype κ] [Fintype (ι → κ)]
    (p : ι → κ → Prop) [∀ i, DecidablePred (p i)]
    (x : ι → κ → ℤ) :
    (∏ i, ∑ a : κ, if p i a then (AddMonoidAlgebra.single ((x i a).natAbs ^ 2, (x i a : ZMod 8)) 1 :
      LeechNormEightSeries) else 0) =
    ∑ a : ι → κ, if (∀ i, p i (a i)) then
      AddMonoidAlgebra.single ((∑ i, (x i (a i)).natAbs ^ 2),
        ((∑ i, x i (a i) : ℤ) : ZMod 8)) 1 else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  by_cases ha : ∀ i, p i (a i)
  · rw [ite_eq_left ha]
    simp only [ha, ite_true]
    rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]
    congr 1
    apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Int.cast_sum]
  · rw [ite_eq_right ha]
    obtain ⟨i, hi⟩ := not_forall.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

/-- Expansion over all bounded coordinate assignments. -/
theorem leechNormSixTailSeries_expand (m : Bool) (c : Fin 22 → ZMod 2) :
    leechNormSixTailSeries m c =
      ∑ a : Fin 22 → Fin 17,
        if (∀ i, (leechNormEightCoordinate (a i) : ZMod 4) =
            (m.toNat : ZMod 4) + 2 * ((c i).val : ZMod 4)) then
          AddMonoidAlgebra.single
            ((∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2),
              ((∑ i, leechNormEightCoordinate (a i) : ℤ) : ZMod 8)) 1
        else 0 := by
  unfold leechNormSixTailSeries leechNormEightCoordinateSeries
  have h := leechNormSixTailSeries_expand_generic
    (fun i a => (leechNormEightCoordinate a : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * ((c i).val : ZMod 4))
    (fun _ a => leechNormEightCoordinate a)
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> rfl

private theorem leechNormSixTailSeries_count_generic {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (e : α → ℕ × ZMod 8) (t : ℕ × ZMod 8)
    :
    (∑ a : α, if p a then (AddMonoidAlgebra.single (e a) 1 : LeechNormEightSeries)
      else 0).coeff t = Nat.card {a : α // p a ∧ e a = t} := by
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : p a
  · simp only [ha, ite_true, true_and, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  · simp only [ha, ite_false, false_and, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- The desired coefficient is exactly the number of bounded source solutions. -/
theorem leechNormSixTailSeries_count (m : Bool) (c : Fin 22 → ZMod 2) (q : ℕ) (h : ZMod 8) :
    (leechNormSixTailSeries m c).coeff (q, h) =
      Nat.card (LeechNormSixTailSolution m c q h) := by
  rw [leechNormSixTailSeries_expand]
  let p : (Fin 22 → Fin 17) → Prop := fun a =>
    ∀ i, (leechNormEightCoordinate (a i) : ZMod 4) =
      (m.toNat : ZMod 4) + 2 * ((c i).val : ZMod 4)
  let e : (Fin 22 → Fin 17) → ℕ × ZMod 8 := fun a =>
    ((∑ i, (leechNormEightCoordinate (a i)).natAbs ^ 2),
      ((∑ i, leechNormEightCoordinate (a i) : ℤ) : ZMod 8))
  let t : ℕ × ZMod 8 := (q, h)
  have h : {a : Fin 22 → Fin 17 // p a ∧ e a = t} ≃
      LeechNormSixTailSolution m c q h :=
    Equiv.subtypeEquivRight (fun a => by
      simp only [p, e, t, Prod.mk.injEq])
  rw [leechNormSixTailSeries_count_generic p e t, Nat.card_congr h]

/-- The product depends only on the numbers of zero and one code bits. -/
theorem leechNormSixTailSeries_weight (m : Bool) (c : Fin 22 → ZMod 2) :
    leechNormSixTailSeries m c =
      leechNormEightCoordinateSeries m 0 ^ (22 - ∑ i, (c i).val) *
        leechNormEightCoordinateSeries m 1 ^ (∑ i, (c i).val) := by
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have hc (i : Fin 22) : leechNormEightCoordinateSeries m (c i) =
      if c i = 0 then leechNormEightCoordinateSeries m 0
        else leechNormEightCoordinateSeries m 1 := by
    rcases hb (c i) with h | h <;> simp [h]
  unfold leechNormSixTailSeries
  simp_rw [hc]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have h1 : (Finset.univ.filter fun i => ¬c i = 0).card = ∑ i, (c i).val := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases hb (c i) with h | h <;> simp [h, ZMod.val_one]
  have h0 : (Finset.univ.filter fun i => c i = 0).card = 22 - ∑ i, (c i).val := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 22))) (fun i : Fin 22 => c i = 0)
    rw [h1] at h
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [h0, h1]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
