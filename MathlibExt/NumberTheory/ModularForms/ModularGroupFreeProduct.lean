/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.lean`
and
`P2M/Sol/S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.LinearCombination

/-!
# The modular group modulo its center is a free product

The quotient of `SL(2, ℤ)` by its center is the free product of `ℤ/2` and `ℤ/3`, with the
generators sent to the classes of `S` and `S * T`. The proof is a ping-pong argument for the
Möbius action on the irrational reals.
-/

open Matrix MatrixGroups ModularGroup
open scoped Pointwise

namespace ModularCurve

namespace ModularGroupPingPong

private theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.2
  rw [Matrix.det_fin_two] at h
  exact h

private def IrrationalPt : Type := {x : ℝ // Irrational x}

namespace IrrationalPt

private scoped instance : CoeOut IrrationalPt ℝ := ⟨Subtype.val⟩

@[scoped ext] private theorem ext {x y : IrrationalPt} (h : (x : ℝ) = y) : x = y := Subtype.ext h

private theorem irrational (x : IrrationalPt) : Irrational (x : ℝ) := x.2

private noncomputable def sqrtTwo : IrrationalPt := ⟨Real.sqrt 2, irrational_sqrt_two⟩

private theorem sqrtTwo_pos : (0 : ℝ) < (sqrtTwo : ℝ) := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact this

private noncomputable def negSqrtTwo : IrrationalPt := ⟨-Real.sqrt 2, irrational_sqrt_two.neg⟩

private theorem negSqrtTwo_neg : ((negSqrtTwo : ℝ)) < 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  change -Real.sqrt 2 < 0
  linarith

end IrrationalPt
open scoped ModularCurve.ModularGroupPingPong.IrrationalPt

private noncomputable def moebius (γ : SL(2, ℤ)) (x : ℝ) : ℝ :=
  ((γ 0 0 : ℝ) * x + (γ 0 1 : ℝ)) / ((γ 1 0 : ℝ) * x + (γ 1 1 : ℝ))

private theorem det_entries_real (γ : SL(2, ℤ)) :
    (γ 0 0 : ℝ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) = 1 := by
  exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) (det_entries γ)

private theorem mul_entry (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  show ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem den_ne_zero (γ : SL(2, ℤ)) {x : ℝ} (hx : Irrational x) :
    (γ 1 0 : ℝ) * x + (γ 1 1 : ℝ) ≠ 0 := by
  rcases eq_or_ne (γ 1 0) 0 with h | h
  · have hdet := det_entries γ
    rw [h, mul_zero, sub_zero] at hdet
    rw [h]
    push_cast
    rw [zero_mul, zero_add]
    intro hzero
    rw [show (γ 1 1 : ℤ) = 0 from by exact_mod_cast hzero, mul_zero] at hdet
    exact zero_ne_one hdet
  · intro heq
    refine hx ⟨-(γ 1 1 : ℚ) / (γ 1 0 : ℚ), ?_⟩
    have hc : (γ 1 0 : ℝ) ≠ 0 := by exact_mod_cast h
    push_cast
    rw [div_eq_iff hc]
    linarith

private theorem irrational_moebius (γ : SL(2, ℤ)) {x : ℝ} (hx : Irrational x) :
    Irrational (moebius γ x) := by
  rintro ⟨q, hq⟩
  have hden := den_ne_zero γ hx
  rw [moebius, eq_comm, div_eq_iff hden] at hq
  rcases eq_or_ne ((γ 0 0 : ℚ) - q * (γ 1 0 : ℚ)) 0 with h | h
  · have hR : (γ 0 0 : ℝ) - (q : ℝ) * (γ 1 0 : ℝ) = 0 := by exact_mod_cast h
    have hb : (γ 0 1 : ℝ) = (q : ℝ) * (γ 1 1 : ℝ) := by
      linear_combination hq - x * hR
    have hdet := det_entries_real γ
    rw [show (γ 0 0 : ℝ) = (q : ℝ) * (γ 1 0 : ℝ) from by linarith, hb] at hdet
    have h01 : (0 : ℝ) = 1 := by linear_combination hdet
    exact zero_ne_one h01
  · refine hx ⟨((q : ℚ) * (γ 1 1 : ℚ) - (γ 0 1 : ℚ)) / ((γ 0 0 : ℚ) - q * (γ 1 0 : ℚ)), ?_⟩
    have hR : (γ 0 0 : ℝ) - (q : ℝ) * (γ 1 0 : ℝ) ≠ 0 := by
      intro hc
      exact h (by exact_mod_cast hc)
    push_cast
    rw [div_eq_iff hR]
    linear_combination -hq

private theorem div_div_div_same {P Q D : ℝ} (hD : D ≠ 0) : P / D / (Q / D) = P / Q := by
  obtain rfl | hQ := eq_or_ne Q 0
  · simp
  · field_simp

private theorem moebius_mul (A B : SL(2, ℤ)) {x : ℝ} (hx : Irrational x) :
    moebius (A * B) x = moebius A (moebius B x) := by
  have hB : ((B 1 0 : ℝ) * x + (B 1 1 : ℝ)) ≠ 0 := den_ne_zero B hx
  have key : ∀ a b : ℤ, (a : ℝ) * moebius B x + (b : ℝ)
      = ((a : ℝ) * ((B 0 0 : ℝ) * x + (B 0 1 : ℝ))
          + (b : ℝ) * ((B 1 0 : ℝ) * x + (B 1 1 : ℝ)))
        / ((B 1 0 : ℝ) * x + (B 1 1 : ℝ)) := by
    intro a b
    rw [moebius, eq_div_iff hB, add_mul, mul_assoc, div_mul_cancel₀ _ hB]
  rw [moebius, moebius, key (A 0 0) (A 0 1), key (A 1 0) (A 1 1), div_div_div_same hB]
  have e00 := mul_entry A B 0 0
  have e01 := mul_entry A B 0 1
  have e10 := mul_entry A B 1 0
  have e11 := mul_entry A B 1 1
  congr 1
  · rw [show ((A * B) 0 0 : ℝ) = ((A 0 0 * B 0 0 + A 0 1 * B 1 0 : ℤ) : ℝ) from by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) e00,
      show ((A * B) 0 1 : ℝ) = ((A 0 0 * B 0 1 + A 0 1 * B 1 1 : ℤ) : ℝ) from by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) e01]
    push_cast
    ring
  · rw [show ((A * B) 1 0 : ℝ) = ((A 1 0 * B 0 0 + A 1 1 * B 1 0 : ℤ) : ℝ) from by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) e10,
      show ((A * B) 1 1 : ℝ) = ((A 1 0 * B 0 1 + A 1 1 * B 1 1 : ℤ) : ℝ) from by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) e11]
    push_cast
    ring

private theorem moebius_one (x : ℝ) : moebius 1 x = x := by
  have h00 : ((1 : SL(2, ℤ)) 0 0 : ℤ) = 1 := rfl
  have h01 : ((1 : SL(2, ℤ)) 0 1 : ℤ) = 0 := rfl
  have h10 : ((1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := rfl
  have h11 : ((1 : SL(2, ℤ)) 1 1 : ℤ) = 1 := rfl
  rw [moebius, h00, h01, h10, h11]
  push_cast
  rw [one_mul, add_zero, zero_mul, zero_add, div_one]

private noncomputable scoped instance : MulAction SL(2, ℤ) IrrationalPt where
  smul γ x := ⟨moebius γ (x : ℝ), irrational_moebius γ x.2⟩
  one_smul x := IrrationalPt.ext (moebius_one (x : ℝ))
  mul_smul A B x := IrrationalPt.ext (moebius_mul A B x.2)

private theorem smul_coe (γ : SL(2, ℤ)) (x : IrrationalPt) :
    ((γ • x : IrrationalPt) : ℝ) = moebius γ (x : ℝ) := rfl

private def Pos : Set IrrationalPt := {x | 0 < (x : ℝ)}

private def Neg : Set IrrationalPt := {x | (x : ℝ) < 0}

private theorem pos_nonempty : Pos.Nonempty := ⟨IrrationalPt.sqrtTwo, IrrationalPt.sqrtTwo_pos⟩

private theorem neg_nonempty : Neg.Nonempty := ⟨IrrationalPt.negSqrtTwo,
    IrrationalPt.negSqrtTwo_neg⟩

private theorem disjoint_pos_neg : Disjoint Pos Neg := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : (0 : ℝ) < (x : ℝ) := hx
  have h2 : (x : ℝ) < 0 := hx'
  linarith

private theorem S_smul_coe (x : IrrationalPt) : ((S • x : IrrationalPt) : ℝ) = -1 / (x : ℝ) := by
  rw [smul_coe, moebius]
  norm_num [show (S 0 0 : ℤ) = 0 from rfl, show (S 0 1 : ℤ) = -1 from rfl,
    show (S 1 0 : ℤ) = 1 from rfl, show (S 1 1 : ℤ) = 0 from rfl]

private theorem ST_smul_coe (x : IrrationalPt) :
    (((S * T) • x : IrrationalPt) : ℝ) = -1 / ((x : ℝ) + 1) := by
  rw [smul_coe, moebius]
  norm_num [show ((S * T) 0 0 : ℤ) = 0 from rfl, show ((S * T) 0 1 : ℤ) = -1 from rfl,
    show ((S * T) 1 0 : ℤ) = 1 from rfl, show ((S * T) 1 1 : ℤ) = 1 from rfl]

private theorem ST_sq_smul_coe (x : IrrationalPt) :
    ((((S * T) * (S * T)) • x : IrrationalPt) : ℝ) = (-(x : ℝ) - 1) / (x : ℝ) := by
  rw [smul_coe, moebius]
  norm_num [show (((S * T) * (S * T)) 0 0 : ℤ) = -1 from rfl,
    show (((S * T) * (S * T)) 0 1 : ℤ) = -1 from rfl,
    show (((S * T) * (S * T)) 1 0 : ℤ) = 1 from rfl,
    show (((S * T) * (S * T)) 1 1 : ℤ) = 0 from rfl]
  ring

private theorem neg_one_smul_eq (x : IrrationalPt) : ((-1 : SL(2, ℤ)) • x) = x := by
  apply IrrationalPt.ext
  rw [smul_coe, moebius]
  norm_num [show ((-1 : SL(2, ℤ)) 0 0 : ℤ) = -1 from rfl,
    show ((-1 : SL(2, ℤ)) 0 1 : ℤ) = 0 from rfl,
    show ((-1 : SL(2, ℤ)) 1 0 : ℤ) = 0 from rfl,
    show ((-1 : SL(2, ℤ)) 1 1 : ℤ) = -1 from rfl]

private theorem S_smul_neg_mem_pos {x : IrrationalPt} (hx : x ∈ Neg) : S • x ∈ Pos := by
  change (0 : ℝ) < ((S • x : IrrationalPt) : ℝ)
  rw [S_smul_coe]
  exact div_pos_of_neg_of_neg (by norm_num) hx

private theorem ST_smul_pos_mem_neg {x : IrrationalPt} (hx : x ∈ Pos) : (S * T) • x ∈ Neg := by
  change (((S * T) • x : IrrationalPt) : ℝ) < 0
  rw [ST_smul_coe]
  apply div_neg_of_neg_of_pos (by norm_num)
  have : (0 : ℝ) < (x : ℝ) := hx
  linarith

private theorem ST_sq_smul_pos_mem_neg {x : IrrationalPt} (hx : x ∈ Pos) :
    ((S * T) * (S * T)) • x ∈ Neg := by
  change ((((S * T) * (S * T)) • x : IrrationalPt) : ℝ) < 0
  rw [ST_sq_smul_coe]
  have : (0 : ℝ) < (x : ℝ) := hx
  apply div_neg_of_neg_of_pos (by linarith) this

private noncomputable def toPerm : SL(2, ℤ) →* Equiv.Perm IrrationalPt :=
  MulAction.toPermHom SL(2, ℤ) IrrationalPt

private theorem toPerm_apply (γ : SL(2, ℤ)) (x : IrrationalPt) : toPerm γ x = γ • x := rfl

private noncomputable def permS : Equiv.Perm IrrationalPt := toPerm S

private noncomputable def permU : Equiv.Perm IrrationalPt := toPerm (S * T)

private theorem toPerm_neg_one : toPerm (-1) = 1 := by
  apply Equiv.ext
  intro x
  exact neg_one_smul_eq x

private theorem permS_sq : permS ^ 2 = 1 := by
  rw [permS, ← map_pow, show S ^ 2 = -1 from by decide, toPerm_neg_one]

private theorem permU_pow_three : permU ^ 3 = 1 := by
  rw [permU, ← map_pow, show (S * T) ^ 3 = -1 from by decide, toPerm_neg_one]

private theorem permS_ne_one : permS ≠ 1 := by
  intro h
  have h2 : permS IrrationalPt.sqrtTwo = IrrationalPt.sqrtTwo := by rw [h]; rfl
  have h3 : ((S • IrrationalPt.sqrtTwo : IrrationalPt) : ℝ) = (IrrationalPt.sqrtTwo : ℝ) :=
    congrArg _ h2
  rw [S_smul_coe] at h3
  have hpos := IrrationalPt.sqrtTwo_pos
  have : -1 / (IrrationalPt.sqrtTwo : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) hpos
  linarith

private theorem permU_ne_one : permU ≠ 1 := by
  intro h
  have h2 : permU IrrationalPt.sqrtTwo = IrrationalPt.sqrtTwo := by rw [h]; rfl
  have h3 : (((S * T) • IrrationalPt.sqrtTwo : IrrationalPt) : ℝ)
      = (IrrationalPt.sqrtTwo : ℝ) := congrArg _ h2
  rw [ST_smul_coe] at h3
  have hpos := IrrationalPt.sqrtTwo_pos
  have : -1 / ((IrrationalPt.sqrtTwo : ℝ) + 1) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (by linarith)
  linarith

private theorem permU_sq_ne_one : permU ^ 2 ≠ 1 := by
  intro h
  have h2 : (permU ^ 2) IrrationalPt.sqrtTwo = IrrationalPt.sqrtTwo := by rw [h]; rfl
  have hcoe : (permU ^ 2) IrrationalPt.sqrtTwo
      = (((S * T) * (S * T)) • IrrationalPt.sqrtTwo : IrrationalPt) := by
    rw [pow_two, permU, ← map_mul]
    rfl
  rw [hcoe] at h2
  have h3 : ((((S * T) * (S * T)) • IrrationalPt.sqrtTwo : IrrationalPt) : ℝ)
      = (IrrationalPt.sqrtTwo : ℝ) := congrArg _ h2
  rw [ST_sq_smul_coe] at h3
  have hpos := IrrationalPt.sqrtTwo_pos
  have : (-(IrrationalPt.sqrtTwo : ℝ) - 1) / (IrrationalPt.sqrtTwo : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by linarith) hpos
  linarith

private scoped instance fact_prime_two_freeProduct : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private scoped instance fact_prime_three_freeProduct : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem orderOf_permS : orderOf permS = 2 :=
  orderOf_eq_prime permS_sq permS_ne_one

private theorem orderOf_permU : orderOf permU = 3 :=
  orderOf_eq_prime permU_pow_three permU_ne_one

open Subgroup

private abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))

private scoped instance factOneLt (i : Fin 2) : Fact (1 < i.val + 2) := ⟨by omega⟩

private noncomputable def gen : Fin 2 → Equiv.Perm IrrationalPt := ![permS, permU]

@[scoped simp] private theorem gen_zero : gen 0 = permS := rfl
@[scoped simp] private theorem gen_one : gen 1 = permU := rfl

private theorem gen_pow_eq_one (i : Fin 2) : gen i ^ (i.val + 2) = 1 := by
  fin_cases i
  · exact permS_sq
  · exact permU_pow_three

private noncomputable def incl (i : Fin 2) : G23 i →* Equiv.Perm IrrationalPt where
  toFun x := gen i ^ (Multiplicative.toAdd x).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (gen_pow_eq_one i), pow_add]

private theorem incl_ofAdd_one (i : Fin 2) : incl i (Multiplicative.ofAdd 1) = gen i := by
  change gen i ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod (i.val + 2)))).val = gen i
  rw [toAdd_ofAdd, ZMod.val_one, pow_one]

private theorem incl_zero_eq (h : G23 0) (hne : h ≠ 1) : incl 0 h = permS := by
  have hh : h = Multiplicative.ofAdd 1 := by
    revert hne; revert h; decide
  subst hh
  rw [incl_ofAdd_one, gen_zero]

private theorem incl_one_eq (h : G23 1) (hne : h ≠ 1) :
    incl 1 h = permU ∨ incl 1 h = permU * permU := by
  have hh : h = Multiplicative.ofAdd 1 ∨
      h = Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 := by
    revert hne; revert h; decide
  rcases hh with rfl | rfl
  · left; rw [incl_ofAdd_one, gen_one]
  · right; rw [map_mul, incl_ofAdd_one, gen_one]

private def pingPongSet : Fin 2 → Set IrrationalPt := ![Pos, Neg]

@[scoped simp] private theorem pingPongSet_zero : pingPongSet 0 = Pos := rfl
@[scoped simp] private theorem pingPongSet_one : pingPongSet 1 = Neg := rfl

private theorem pingPong : Pairwise fun i j => ∀ h : G23 i, h ≠ 1 →
    incl i h • pingPongSet j ⊆ pingPongSet i := by
  intro i j hij h hne
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rintro _ ⟨y, hy, rfl⟩
    change incl 0 h • y ∈ Pos
    rw [incl_zero_eq h hne]
    exact S_smul_neg_mem_pos hy
  · rintro _ ⟨y, hy, rfl⟩
    change incl 1 h • y ∈ Neg
    rcases incl_one_eq h hne with h1 | h2
    · rw [h1]
      exact ST_smul_pos_mem_neg hy
    · rw [h2, permU, ← map_mul]
      exact ST_sq_smul_pos_mem_neg hy
  · exact absurd rfl hij

private theorem three_le_card_factor_one : 3 ≤ Cardinal.mk (G23 1) := by
  have hc : Fintype.card (G23 1) = 3 := by decide
  rw [Cardinal.mk_fintype, hc]
  norm_num

private theorem lift_injective : Function.Injective (Monoid.CoprodI.lift incl) := by
  apply Monoid.CoprodI.lift_injective_of_ping_pong incl
    (Or.inr ⟨1, three_le_card_factor_one⟩) pingPongSet
  · intro i
    fin_cases i
    · exact pos_nonempty
    · exact neg_nonempty
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_pos_neg
    · exact disjoint_pos_neg.symm
    · exact absurd rfl hij
  · exact pingPong

private theorem range_lift_eq : (Monoid.CoprodI.lift incl).range = toPerm.range := by
  apply le_antisymm
  · rw [Monoid.CoprodI.range_eq_iSup]
    apply iSup_le
    intro i
    rintro _ ⟨x, rfl⟩
    change gen i ^ (Multiplicative.toAdd x).val ∈ toPerm.range
    refine Subgroup.pow_mem _ ?_ _
    fin_cases i
    · exact ⟨S, rfl⟩
    · exact ⟨S * T, rfl⟩
  · rw [MonoidHom.range_eq_map, ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hS : toPerm S ∈ (Monoid.CoprodI.lift incl).range := by
      refine ⟨Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd 1), ?_⟩
      rw [Monoid.CoprodI.lift_of, incl_ofAdd_one, gen_zero, permS]
    have hST : toPerm (S * T) ∈ (Monoid.CoprodI.lift incl).range := by
      refine ⟨Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd 1), ?_⟩
      rw [Monoid.CoprodI.lift_of, incl_ofAdd_one, gen_one, permU]
    rcases hx with rfl | rfl
    · exact hS
    · have : toPerm T = (toPerm S)⁻¹ * toPerm (S * T) := by
        rw [← map_inv, ← map_mul, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem hS) hST

private theorem irrational_sqrt_three : Irrational (Real.sqrt 3) := by
  have h : Irrational (Real.sqrt ((3 : ℕ) : ℝ)) := Nat.prime_three.irrational_sqrt
  rwa [Nat.cast_ofNat] at h

private theorem eq_zero_of_irrational_relation {x : ℝ} (hx : Irrational x) {p q : ℤ}
    (h : (p : ℝ) + (q : ℝ) * x = 0) : p = 0 ∧ q = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine ⟨?_, rfl⟩
    have hp : (p : ℝ) = 0 := by push_cast at h; linarith
    exact_mod_cast hp
  · exfalso
    refine hx ⟨-(p : ℚ) / (q : ℚ), ?_⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    rw [div_eq_iff hq']
    have hcomm : x * (q : ℝ) = (q : ℝ) * x := mul_comm _ _
    linarith

private theorem moebius_eq_self_relation (γ : SL(2, ℤ)) {x : ℝ} (hx : Irrational x)
    (h : moebius γ x = x) :
    (γ 1 0 : ℝ) * (x * x) + ((γ 1 1 : ℝ) - (γ 0 0 : ℝ)) * x - (γ 0 1 : ℝ) = 0 := by
  rw [moebius, div_eq_iff (den_ne_zero γ hx)] at h
  linear_combination -h

private theorem eq_one_or_neg_one_of_toPerm_eq_one {γ : SL(2, ℤ)} (h : toPerm γ = 1) :
    γ = 1 ∨ γ = -1 := by
  have key : ∀ x : IrrationalPt, moebius γ (x : ℝ) = (x : ℝ) := by
    intro x
    have hx : toPerm γ x = x := by simp [h]
    have hval : ((γ • x : IrrationalPt) : ℝ) = (x : ℝ) := congrArg Subtype.val hx
    rwa [smul_coe] at hval
  have r2 := moebius_eq_self_relation γ irrational_sqrt_two
    (key ⟨Real.sqrt 2, irrational_sqrt_two⟩)
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at r2
  obtain ⟨h2a, hdiag⟩ := eq_zero_of_irrational_relation irrational_sqrt_two
    (p := 2 * γ 1 0 - γ 0 1) (q := γ 1 1 - γ 0 0) (by push_cast; linear_combination r2)
  have r3 := moebius_eq_self_relation γ irrational_sqrt_three
    (key ⟨Real.sqrt 3, irrational_sqrt_three⟩)
  rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at r3
  obtain ⟨h3a, -⟩ := eq_zero_of_irrational_relation irrational_sqrt_three
    (p := 3 * γ 1 0 - γ 0 1) (q := γ 1 1 - γ 0 0) (by push_cast; linear_combination r3)
  have hc : γ 1 0 = 0 := by omega
  have hb : γ 0 1 = 0 := by omega
  have hd : γ 1 1 = γ 0 0 := by omega
  have hdet : γ 0 0 * γ 0 0 = 1 := by
    have h0 := det_entries γ
    rw [hb, hc, hd] at h0
    linear_combination h0
  rcases mul_self_eq_one_iff.mp hdet with h00 | h00
  · left
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hc, hd, h00]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hb, hc, hd, h00, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

private theorem mem_center_iff_eq (A : SL(2, ℤ)) : A ∈ Subgroup.center SL(2, ℤ) ↔ A = 1 ∨ A = -1 :=
    by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hA⟩
    have hr' : r * r = 1 := by rw [← pow_two]; simpa using hr
    rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
    · left
      apply Subtype.ext
      rw [← hA, map_one]
      rfl
    · right
      apply Subtype.ext
      rw [← hA, map_neg, map_one]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩

private theorem ker_toPerm_eq_center : toPerm.ker = Subgroup.center SL(2, ℤ) := by
  ext γ
  rw [MonoidHom.mem_ker, mem_center_iff_eq]
  constructor
  · exact eq_one_or_neg_one_of_toPerm_eq_one
  · rintro (rfl | rfl)
    · exact map_one _
    · exact toPerm_neg_one

private noncomputable def equivRange : Monoid.CoprodI G23 ≃* toPerm.range :=
  (MonoidHom.ofInjective lift_injective).trans (MulEquiv.subgroupCongr range_lift_eq)

private theorem equivRange_apply_coe (w : Monoid.CoprodI G23) :
    (equivRange w : Equiv.Perm IrrationalPt) = Monoid.CoprodI.lift incl w := rfl

private noncomputable def mulEquiv : Monoid.CoprodI G23 ≃* SL(2, ℤ) ⧸ Subgroup.center SL(2, ℤ) :=
  equivRange.trans
    ((QuotientGroup.quotientKerEquivRange toPerm).symm.trans
      (QuotientGroup.quotientMulEquivOfEq ker_toPerm_eq_center))

private theorem mulEquiv_apply_of_eq (i : Fin 2) (x : G23 i) (g : SL(2, ℤ)) (hg : toPerm g = incl i
    x) :
    mulEquiv (Monoid.CoprodI.of x) = QuotientGroup.mk g := by
  unfold mulEquiv
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have h1 : equivRange (Monoid.CoprodI.of x) = ⟨toPerm g, g, rfl⟩ := by
    apply Subtype.ext
    rw [equivRange_apply_coe, Monoid.CoprodI.lift_of]
    exact hg.symm
  have h2 : (QuotientGroup.quotientKerEquivRange toPerm) (QuotientGroup.mk g) = ⟨toPerm g, g, rfl⟩
      := rfl
  rw [h1, ← h2, MulEquiv.symm_apply_apply]
  rfl

private theorem mulEquiv_of_zero :
    mulEquiv (Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd 1)) = QuotientGroup.mk S :=
  mulEquiv_apply_of_eq 0 _ S (by rw [incl_ofAdd_one, gen_zero, permS])

private theorem mulEquiv_of_one :
    mulEquiv (Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd 1)) = QuotientGroup.mk (S * T) :=
  mulEquiv_apply_of_eq 1 _ (S * T) (by rw [incl_ofAdd_one, gen_one, permU])

end ModularGroupPingPong
open scoped ModularCurve.ModularGroupPingPong.IrrationalPt ModularCurve.ModularGroupPingPong

end ModularCurve

/-- `SL(2, ℤ)` modulo its center is the free product `ℤ/2 ∗ ℤ/3`, with the generators sent to the
classes of `S` and `S * T`. -/
public theorem ModularGroup.exists_mulEquiv_freeProduct_quotient_center :
    ∃ e : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))
        ≃* Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            ℤ),
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk ModularGroup.S ∧
      e (Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
          (Multiplicative.ofAdd 1)) = QuotientGroup.mk (ModularGroup.S * ModularGroup.T) :=
  ⟨ModularCurve.ModularGroupPingPong.mulEquiv, ModularCurve.ModularGroupPingPong.mulEquiv_of_zero,
    ModularCurve.ModularGroupPingPong.mulEquiv_of_one⟩
