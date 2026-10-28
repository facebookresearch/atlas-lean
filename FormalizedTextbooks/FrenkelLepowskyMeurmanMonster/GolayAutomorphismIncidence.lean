/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismBase
public import Mathlib.Data.Finset.Card

/-! Octad incidence counts invariant under actual code automorphisms.
These counts provide a finite completeness certificate for a concrete
seven-point stabilizer, independently of the Mathieu group order. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Actual codewords identified with their twelve-bit coefficient labels. -/
noncomputable def golayCodeLabelEquiv : Fin 4096 ≃ golayCode :=
  (Equiv.ofBijective golayLabelCoefficients golayLabelCoefficients_bijective).trans golayCodeEquiv

@[simp] theorem golayCodeLabelEquiv_val (d : Fin 4096) :
    (golayCodeLabelEquiv d).val = golayEncoder (golayLabelCoefficients d) := rfl

/-- The permutation action restricted to the actual code range. -/
def golayCodePermutation (p : golayAutomorphismSubgroup) : golayCode ≃ golayCode where
  toFun c := ⟨golayPermute p.val c.val, (p.property c.val).mp c.property⟩
  invFun c := ⟨golayPermute p.val⁻¹ c.val, ((p⁻¹).property c.val).mp c.property⟩
  left_inv c := Subtype.ext (golayPermute_inv p.val c.val)
  right_inv c := by
    apply Subtype.ext
    change golayPermute p.val (golayPermute p.val⁻¹ c.val) = c.val
    rw [← golayPermute_mul, mul_inv_cancel, golayPermute_one]

/-- The induced permutation of all 4096 coefficient labels. -/
noncomputable def golayLabelPermutation (p : golayAutomorphismSubgroup) : Equiv.Perm (Fin 4096) :=
  golayCodeLabelEquiv.trans ((golayCodePermutation p).trans golayCodeLabelEquiv.symm)

theorem golayLabelPermutation_word (p : golayAutomorphismSubgroup) (d : Fin 4096) :
    golayEncoder (golayLabelCoefficients (golayLabelPermutation p d)) =
      golayPermute p.val (golayEncoder (golayLabelCoefficients d)) := by
  have h : golayCodeLabelEquiv (golayLabelPermutation p d) =
      golayCodePermutation p (golayCodeLabelEquiv d) := by
    simp only [golayLabelPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact congrArg Subtype.val h

/-- The physical forward coordinate action on each coefficient label. -/
theorem golayLabelPermutation_coordinate (p : golayAutomorphismSubgroup) (d : Fin 4096)
    (i : Fin 24) :
    golayEncoder (golayLabelCoefficients (golayLabelPermutation p d)) (p.val i) =
      golayEncoder (golayLabelCoefficients d) i := by
  rw [golayLabelPermutation_word]
  change golayEncoder (golayLabelCoefficients d) (p.val.symm (p.val i)) = _
  rw [p.val.symm_apply_apply]

/-- Bit-mask weight agrees with the weight of the actual encoded word. -/
theorem golayLabel_weight (d : Fin 4096) :
    golayMaskWeight (golayEncodedMask d.val) =
      ∑ i : Fin 24, (golayEncoder (golayLabelCoefficients d) i).val := by
  symm
  apply Finset.sum_congr rfl
  intro i _
  exact golayLabelEncoder_match d i

/-- Automorphisms preserve actual octad labels. -/
theorem golayLabelPermutation_octad (p : golayAutomorphismSubgroup) (d : Fin 4096) :
    golayLabelPermutation p d ∈ golayOctads ↔ d ∈ golayOctads := by
  simp only [golayOctads, Finset.mem_filter, Finset.mem_univ, true_and,
    golayLabel_weight, golayLabelPermutation_word]
  have h : (∑ i, (golayPermute p.val (golayEncoder (golayLabelCoefficients d)) i).val) =
      ∑ i, (golayEncoder (golayLabelCoefficients d) i).val :=
    Equiv.sum_comp p.val.symm (fun i => (golayEncoder (golayLabelCoefficients d) i).val)
  rw [h]

/-- Seven fixed coordinates used by the prospective stabilizer certificate. -/
def golayBasePoints : Fin 7 → Fin 24 := ![0, 1, 2, 3, 4, 8, 5]

/-- The bit pattern on those seven points, encoded as an integer from 0 to 127. -/
def golayBasePattern (d : Fin 4096) : ℕ :=
  ∑ j : Fin 7, (golayEncoder (golayLabelCoefficients d) (golayBasePoints j)).val * 2 ^ j.val

/-- Count octads with a prescribed pattern on the seven points and containing `i`. -/
def golayBaseIncidence (pattern : ℕ) (i : Fin 24) : ℕ :=
  (golayOctads.filter (fun d => golayBasePattern d = pattern ∧
    golayEncoder (golayLabelCoefficients d) i = 1)).card

/-- Every true code automorphism fixing the seven points preserves these incidence counts. -/
theorem golayBaseIncidence_invariant (p : golayAutomorphismSubgroup)
    (hp : ∀ j : Fin 7, p.val (golayBasePoints j) = golayBasePoints j)
    (pattern : ℕ) (i : Fin 24) :
    golayBaseIncidence pattern i = golayBaseIncidence pattern (p.val i) := by
  apply Finset.card_equiv (golayLabelPermutation p)
  intro d
  have hpat : golayBasePattern (golayLabelPermutation p d) = golayBasePattern d := by
    apply Finset.sum_congr rfl
    intro j _
    have h := golayLabelPermutation_coordinate p d (golayBasePoints j)
    rw [hp j] at h
    rw [h]
  simp only [Finset.mem_filter, golayLabelPermutation_octad, hpat,
    golayLabelPermutation_coordinate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
