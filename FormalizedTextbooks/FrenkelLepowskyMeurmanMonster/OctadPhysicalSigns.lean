/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Linear physical-coordinate embedding of the eight octad sign coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadProductPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Place the eight local coordinates on the actual physical octad support. -/
def octadPhysicalEmbedding (o : Fin 759) :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) where
  toFun x := ∑ k, Pi.single (golayOctadCoordinate o k) (x k)
  map_add' x y := by
    simp only [Pi.add_apply, Pi.single_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, Pi.single_smul, Finset.smul_sum, RingHom.id_apply]

/-- The physical embedding retains every local coordinate. -/
theorem octadPhysicalEmbedding_local (o : Fin 759) (x : Fin 8 → ZMod 2) (k : Fin 8) :
    octadPhysicalEmbedding o x (golayOctadCoordinate o k) = x k := by
  change (∑ l, (Pi.single (golayOctadCoordinate o l) (x l) : Fin 24 → ZMod 2))
    (golayOctadCoordinate o k) = x k
  simp only [Finset.sum_apply, Pi.single_apply,
    (golayOctadCoordinate_injective o).eq_iff, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The physical embedding is zero outside its actual octad. -/
theorem octadPhysicalEmbedding_supported (o : Fin 759) (x : Fin 8 → ZMod 2) (i : Fin 24)
    (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val ≠ true) :
    octadPhysicalEmbedding o x i = 0 := by
  change (∑ k, (Pi.single (golayOctadCoordinate o k) (x k) : Fin 24 → ZMod 2)) i = 0
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hk : i ≠ golayOctadCoordinate o k := by
    intro h
    apply hi
    rw [h]
    exact golayOctadCoordinate_mem o k
  simp [hk]

/-- Local and physical binary coordinate sums coincide. -/
theorem octadPhysicalEmbedding_sum (o : Fin 759) (x : Fin 8 → ZMod 2) :
    (∑ i, octadPhysicalEmbedding o x i) = ∑ k, x k := by
  change (∑ i, (∑ k, Pi.single (golayOctadCoordinate o k) (x k)) i) = ∑ k, x k
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  simp

/-- The preferred-Q negative pattern is the actual physical embedding of its local bits. -/
theorem griessOctadNegative_embedding (o : Fin 759) (e : Fin 64) :
    integerParity (griessOctadNegativeInteger o e) =
      octadPhysicalEmbedding o (trialityBinaryBit e) := by
  ext i
  by_cases hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
  · obtain ⟨k, rfl⟩ := golayOctadCoordinate_surjective o i hi
    rw [octadPhysicalEmbedding_local]
    simp only [integerParity, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      griessOctadNegativeInteger, griessOctadSignMask_local, trialityBinaryBit]
    cases (trialityEvenMask e).testBit k.val <;> simp [golayBooleanCast]
  · rw [octadPhysicalEmbedding_supported o _ i hi]
    have hn : (griessOctadSignMask o e).testBit i.val = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hi (griessOctadSignMask_subset o e i ht)
    simp [integerParity, griessOctadNegativeInteger, hn]

/-- The physical embedding preserves the binary intersection pairing. -/
theorem octadPhysicalEmbedding_pairing (o : Fin 759) (x y : Fin 8 → ZMod 2) :
    (∑ i, octadPhysicalEmbedding o x i * octadPhysicalEmbedding o y i) =
      ∑ k, x k * y k := by
  change (∑ i, (∑ k, (Pi.single (golayOctadCoordinate o k) (x k) : Fin 24 → ZMod 2)) i *
    octadPhysicalEmbedding o y i) = _
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, octadPhysicalEmbedding_local]

theorem trialityBinaryBit_even : ∀ e : Fin 64, (∑ k : Fin 8, trialityBinaryBit e k) = 0 := by
  unfold trialityBinaryBit trialityEvenMask
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
