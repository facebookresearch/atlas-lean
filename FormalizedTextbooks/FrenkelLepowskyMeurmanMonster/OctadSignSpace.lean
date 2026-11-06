/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! The actual six-dimensional binary octad sign space. Chosen representatives
are even eight-bit patterns with last bit zero. Their intersection pairing
is alternating and nondegenerate. The label equivalence identifies this
linear algebra with the 64 labels used in the actual triality matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

abbrev OctadSignSpace := Fin 6 → ZMod 2

/-- The six free bits of the actual octad sign label. -/
def octadSignLabelBits (e : Fin 64) : OctadSignSpace :=
  fun k => trialityBinaryBit e (Fin.castLE (by decide) k)

set_option maxHeartbeats 0 in
-- Kernel checks on the fixed 64 sign labels exceed the default heartbeat budget.
set_option maxRecDepth 10000 in
lemma octadSignLabelBits_injective : Function.Injective octadSignLabelBits := by
  decide +kernel

/-- The actual sign labels, identified with their six free binary coordinates. -/
noncomputable def octadSignLabelEquiv : Fin 64 ≃ OctadSignSpace :=
  Equiv.ofBijective octadSignLabelBits
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨octadSignLabelBits_injective, by simp [OctadSignSpace, ZMod.card]⟩)

/-- Add a parity bit and a zero anchor to the six free coordinates. -/
def octadSignRepresentative : OctadSignSpace →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun a := Fin.append a (fun k : Fin 2 => if k = 0 then ∑ i, a i else 0)
  map_add' a b := by
    ext k
    refine Fin.addCases (m := 6) (n := 2) (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply, Finset.sum_add_distrib]
      split_ifs <;> simp
  map_smul' c a := by
    ext k
    refine Fin.addCases (m := 6) (n := 2) (fun i => ?_) (fun i => ?_) k
    · simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]
      split_ifs <;> simp [Finset.mul_sum]

@[simp] lemma octadSignRepresentative_free (a : OctadSignSpace) (i : Fin 6) :
    octadSignRepresentative a (Fin.castAdd 2 i) = a i := by
  exact Fin.append_left a (fun k : Fin 2 => if k = 0 then ∑ j, a j else 0) i

@[simp] lemma octadSignRepresentative_parity (a : OctadSignSpace) :
    octadSignRepresentative a 6 = ∑ i, a i := by
  change Fin.append a (fun k : Fin 2 => if k = 0 then ∑ i, a i else 0)
    (Fin.natAdd 6 (0 : Fin 2)) = _
  simp only [Fin.append_right, ite_true]

@[simp] lemma octadSignRepresentative_anchor (a : OctadSignSpace) :
    octadSignRepresentative a 7 = 0 := by
  change Fin.append a (fun k : Fin 2 => if k = 0 then ∑ i, a i else 0)
    (Fin.natAdd 6 (1 : Fin 2)) = _
  simp only [Fin.append_right, show (1 : Fin 2) ≠ 0 by decide, ite_false]

lemma octadSignRepresentative_injective : Function.Injective octadSignRepresentative := by
  intro a b h
  ext i
  simpa only [octadSignRepresentative_free] using
    congrArg (fun v => v (Fin.castAdd 2 i)) h

set_option maxHeartbeats 0 in
-- Kernel checks on the fixed 64 sign labels exceed the default heartbeat budget.
set_option maxRecDepth 10000 in
lemma octadSignRepresentative_label_bits : ∀ (e : Fin 64) (i : Fin 8),
    octadSignRepresentative (octadSignLabelBits e) i = trialityBinaryBit e i := by
  decide +kernel

lemma octadSignRepresentative_label (e : Fin 64) :
    octadSignRepresentative (octadSignLabelEquiv e) = trialityBinaryBit e := by
  ext i
  exact octadSignRepresentative_label_bits e i

lemma octadSignRepresentative_even (a : OctadSignSpace) :
    ∑ i, octadSignRepresentative a i = 0 := by
  rw [Fin.sum_univ_add (a := 6) (b := 2), Fin.sum_univ_two]
  change (∑ i, a i) + (octadSignRepresentative a 6 + octadSignRepresentative a 7) = 0
  rw [octadSignRepresentative_parity, octadSignRepresentative_anchor, add_zero]
  exact CharTwo.add_self_eq_zero (∑ i, a i)


/-- The intersection form on the actual even representatives. -/
def octadSignForm : OctadSignSpace →ₗ[ZMod 2] OctadSignSpace →ₗ[ZMod 2] ZMod 2 :=
  (dotProductBilin (ZMod 2) (ZMod 2)).compl₁₂
    octadSignRepresentative octadSignRepresentative

lemma octadSignForm_apply (a b : OctadSignSpace) :
    octadSignForm a b = ∑ i, a i * b i + (∑ i, a i) * (∑ i, b i) := by
  change (∑ i : Fin 8, octadSignRepresentative a i * octadSignRepresentative b i) = _
  rw [Fin.sum_univ_add (a := 6) (b := 2), Fin.sum_univ_two]
  change (∑ i, a i * b i) +
    (octadSignRepresentative a 6 * octadSignRepresentative b 6 +
      octadSignRepresentative a 7 * octadSignRepresentative b 7) = _
  rw [octadSignRepresentative_parity, octadSignRepresentative_parity,
    octadSignRepresentative_anchor, octadSignRepresentative_anchor, mul_zero, add_zero]


lemma octadSignForm_label (e f : Fin 64) :
    octadSignForm (octadSignLabelEquiv e) (octadSignLabelEquiv f) =
      trialityBinaryPair e f := by
  change (∑ i, octadSignRepresentative (octadSignLabelEquiv e) i *
    octadSignRepresentative (octadSignLabelEquiv f) i) = _
  rw [octadSignRepresentative_label, octadSignRepresentative_label]
  rfl

lemma octadSignForm_symmetric (a b : OctadSignSpace) :
    octadSignForm a b = octadSignForm b a := by
  rw [octadSignForm_apply, octadSignForm_apply, mul_comm (∑ i, a i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

lemma octadSignForm_alternating (a : OctadSignSpace) : octadSignForm a a = 0 := by
  change (∑ i, octadSignRepresentative a i * octadSignRepresentative a i) = 0
  have hf (x : ZMod 2) : x * x = x := by revert x; decide +kernel
  simpa only [hf] using octadSignRepresentative_even a

lemma octadSignForm_single (a : OctadSignSpace) (i : Fin 6) :
    octadSignForm a (Pi.single i 1) = a i + ∑ j, a j := by
  rw [octadSignForm_apply]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- The actual octad intersection form has trivial radical. -/
lemma octadSignForm_nondegenerate (a : OctadSignSpace)
    (ha : ∀ b, octadSignForm a b = 0) : a = 0 := by
  have hi (i : Fin 6) : a i = ∑ j, a j := by
    have h := ha (Pi.single i 1)
    rw [octadSignForm_single] at h
    have hh : a i + (∑ j, a j) = (∑ j, a j) + (∑ j, a j) :=
      h.trans (CharTwo.add_self_eq_zero _).symm
    exact add_right_cancel hh
  have hs : (∑ j, a j) = 0 := by
    calc
      (∑ j, a j) = ∑ _ : Fin 6, (∑ j, a j) := Finset.sum_congr rfl (fun i _ => hi i)
      _ = 0 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul]
        change (6 : ZMod 2) * (∑ j, a j) = 0
        rw [show (6 : ZMod 2) = 0 by decide +kernel, zero_mul]
  ext i
  simpa only [Pi.zero_apply, hs] using hi i

/-- Normalize an eight-bit pattern modulo the full complement, retaining
its six free coordinates. Even patterns are recovered with zero anchor. -/
def octadSignNormalize : (Fin 8 → ZMod 2) →ₗ[ZMod 2] OctadSignSpace where
  toFun v i := v (Fin.castAdd 2 i) + v 7
  map_add' v w := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    ext i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_add]

@[simp] lemma octadSignNormalize_apply (v : Fin 8 → ZMod 2) (i : Fin 6) :
    octadSignNormalize v i = v (Fin.castAdd 2 i) + v 7 := rfl

@[simp] lemma octadSignNormalize_representative (a : OctadSignSpace) :
    octadSignNormalize (octadSignRepresentative a) = a := by
  ext i
  simp only [octadSignNormalize_apply, octadSignRepresentative_free,
    octadSignRepresentative_anchor, add_zero]

lemma octadSignNormalize_complement (v : Fin 8 → ZMod 2) (c : ZMod 2) :
    octadSignNormalize (fun i => v i + c) = octadSignNormalize v := by
  ext i
  simp only [octadSignNormalize_apply]
  calc
    v (Fin.castAdd 2 i) + c + (v 7 + c) =
      (v (Fin.castAdd 2 i) + v 7) + (c + c) := by ring
    _ = v (Fin.castAdd 2 i) + v 7 := by rw [CharTwo.add_self_eq_zero, add_zero]

lemma octadSignNormalize_sum (v : Fin 8 → ZMod 2) :
    ∑ i, octadSignNormalize v i = ∑ i : Fin 6, v (Fin.castAdd 2 i) := by
  simp only [octadSignNormalize_apply, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((6 : ℕ) : ZMod 2) = 0 by decide +kernel, zero_mul, add_zero]

/-- Every even eight-bit pattern differs from its chosen representative
by precisely its anchor times the full eight-bit complement. -/
lemma octadSignRepresentative_normalize (v : Fin 8 → ZMod 2)
    (hv : ∑ i, v i = 0) :
    octadSignRepresentative (octadSignNormalize v) = fun i => v i + v 7 := by
  have he : (∑ i : Fin 6, v (Fin.castAdd 2 i)) + (v 6 + v 7) = 0 := by
    rw [Fin.sum_univ_add (a := 6) (b := 2), Fin.sum_univ_two] at hv
    exact hv
  have hs : (∑ i : Fin 6, v (Fin.castAdd 2 i)) = v 6 + v 7 := by
    apply add_right_cancel (b := v 6 + v 7)
    exact he.trans (CharTwo.add_self_eq_zero (v 6 + v 7)).symm
  ext i
  refine Fin.addCases (m := 6) (n := 2) (fun j => ?_) (fun j => ?_) i
  · simp only [octadSignRepresentative_free, octadSignNormalize_apply]
  · fin_cases j
    · change octadSignRepresentative (octadSignNormalize v) 6 = v 6 + v 7
      rw [octadSignRepresentative_parity, octadSignNormalize_sum, hs]
    · change octadSignRepresentative (octadSignNormalize v) 7 = v 7 + v 7
      rw [octadSignRepresentative_anchor, CharTwo.add_self_eq_zero]

lemma octadSignForm_normalize (v w : Fin 8 → ZMod 2)
    (hv : ∑ i, v i = 0) (hw : ∑ i, w i = 0) :
    octadSignForm (octadSignNormalize v) (octadSignNormalize w) = ∑ i, v i * w i := by
  change (∑ i, octadSignRepresentative (octadSignNormalize v) i *
    octadSignRepresentative (octadSignNormalize w) i) = _
  rw [octadSignRepresentative_normalize v hv, octadSignRepresentative_normalize w hw]
  simp only [add_mul, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hv, hw, mul_zero, zero_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show ((8 : ℕ) : ZMod 2) = 0 by decide +kernel, zero_mul]
  simp

lemma octadSignLabelEquiv_xor (e f : Fin 64) :
    octadSignLabelEquiv (trialityXor e f) = octadSignLabelEquiv e + octadSignLabelEquiv f := by
  apply octadSignRepresentative_injective
  rw [map_add, octadSignRepresentative_label, octadSignRepresentative_label,
    octadSignRepresentative_label]
  ext i
  exact trialityBinaryBit_xor e f i

/-- Reindex the eight physical coordinates before passing to complement classes. -/
def octadSignReindex (p : Equiv.Perm (Fin 8)) :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v i := v (p i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A physical coordinate permutation induces a linear map of actual sign classes. -/
def octadSignPermutationMap (p : Equiv.Perm (Fin 8)) :
    OctadSignSpace →ₗ[ZMod 2] OctadSignSpace :=
  octadSignNormalize.comp ((octadSignReindex p).comp octadSignRepresentative)

lemma octadSignPermutationMap_form (p : Equiv.Perm (Fin 8)) (a b : OctadSignSpace) :
    octadSignForm (octadSignPermutationMap p a) (octadSignPermutationMap p b) =
      octadSignForm a b := by
  have he (x : OctadSignSpace) : (∑ i, octadSignRepresentative x (p i)) = 0 :=
    (Equiv.sum_comp p (octadSignRepresentative x)).trans (octadSignRepresentative_even x)
  change octadSignForm (octadSignNormalize (fun i => octadSignRepresentative a (p i)))
    (octadSignNormalize (fun i => octadSignRepresentative b (p i))) = _
  rw [octadSignForm_normalize _ _ (he a) (he b)]
  exact Equiv.sum_comp p (fun i => octadSignRepresentative a i * octadSignRepresentative b i)

lemma octadSignPermutationMap_injective (p : Equiv.Perm (Fin 8)) :
    Function.Injective (octadSignPermutationMap p) := by
  intro a b h
  apply sub_eq_zero.mp
  apply octadSignForm_nondegenerate
  intro c
  rw [← octadSignPermutationMap_form p, map_sub, h, sub_self, map_zero]
  rfl

/-- Every physical permutation of the eight coordinates acts by an isometry
of the six-dimensional alternating intersection form modulo full complement. -/
noncomputable def octadSignPermutation (p : Equiv.Perm (Fin 8)) :
    OctadSignSpace ≃ₗ[ZMod 2] OctadSignSpace :=
  LinearEquiv.ofBijective (octadSignPermutationMap p)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨octadSignPermutationMap_injective p, rfl⟩)

lemma octadSignPermutation_form (p : Equiv.Perm (Fin 8)) (a b : OctadSignSpace) :
    octadSignForm (octadSignPermutation p a) (octadSignPermutation p b) =
      octadSignForm a b := octadSignPermutationMap_form p a b

lemma octadSignPermutation_representative (p : Equiv.Perm (Fin 8)) (a : OctadSignSpace) :
    octadSignRepresentative (octadSignPermutation p a) =
      fun i => octadSignRepresentative a (p i) + octadSignRepresentative a (p 7) := by
  apply octadSignRepresentative_normalize
  exact (Equiv.sum_comp p (octadSignRepresentative a)).trans (octadSignRepresentative_even a)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
