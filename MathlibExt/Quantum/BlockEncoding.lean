/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.FinCases

/-!
# Block encodings and their products

Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1: Definition 43 (block-encoding),
Definition 44 (trivial block-encoding), Lemma 53 (product of block-encoded matrices).
Lemma 53 as stated omits the cross term `δ * ε`; `IsBlockEncoding.mul` carries it and
`IsBlockEncoding.mul_of_norm_le` recovers the stated bound under `‖B‖ ≤ β`.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

@[expose] public section

namespace MathlibExt.Quantum.BlockEncoding

set_option autoImplicit false

variable {ι κ μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- The ancilla block `(⟨o| ⊗ I) U (|o⟩ ⊗ I)` of a matrix on `κ × ι`. -/
def ancillaBlock (o : κ) (U : Matrix (κ × ι) (κ × ι) ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => U (o, i) (o, j)

/-- Definition 43 for an ancilla register `κ` with reference basis vector `o`: the
normalization `α` and error `ε` are nonnegative reals. -/
def IsBlockEncoding (A : Matrix ι ι ℂ) (α ε : ℝ) (o : κ)
    (U : Matrix (κ × ι) (κ × ι) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (κ × ι) ℂ ∧ ‖A - (α : ℂ) • ancillaBlock o U‖ ≤ ε ∧ 0 ≤ α ∧ 0 ≤ ε

/-- Qubit form of Definition 43: `A` on `s` qubits, `U` on `a + s` qubits with the ancilla
register first and reference vector `|0^a⟩`. -/
abbrev IsQubitBlockEncoding {s a : ℕ} (A : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ) (α ε : ℝ)
    (U : Matrix (Fin (2 ^ a) × Fin (2 ^ s)) (Fin (2 ^ a) × Fin (2 ^ s)) ℂ) : Prop :=
  IsBlockEncoding A α ε (0 : Fin (2 ^ a)) U

private def embMat (o : κ) : Matrix (κ × ι) ι ℂ :=
  Matrix.of fun p j => if p = (o, j) then 1 else 0

private theorem embMat_conjTranspose_mul_self (o : κ) :
    (embMat o)ᴴ * embMat o = (1 : Matrix ι ι ℂ) := by
  ext i j
  show (∑ p : κ × ι, star (if p = (o, i) then (1 : ℂ) else 0) *
      (if p = (o, j) then (1 : ℂ) else 0)) = (1 : Matrix ι ι ℂ) i j
  by_cases h : i = j
  · rw [h]
    have hterm : ∀ p : κ × ι, star (if p = (o, j) then (1 : ℂ) else 0) *
        (if p = (o, j) then (1 : ℂ) else 0) = if p = (o, j) then (1 : ℂ) else 0 := by
      intro p
      by_cases hp : p = (o, j) <;> simp [hp]
    simp only [hterm]
    rw [Fintype.sum_ite_eq']
    simp
  · have hterm : ∀ p : κ × ι, star (if p = (o, i) then (1 : ℂ) else 0) *
        (if p = (o, j) then (1 : ℂ) else 0) = 0 := by
      intro p
      by_cases hp : p = (o, i) <;> simp [hp, h]
    simp only [hterm]
    simp [h]

private theorem embMat_norm (o : κ) [Nonempty ι] :
    ‖(embMat o : Matrix (κ × ι) ι ℂ)‖ = (1 : ℝ) := by
  set E : Matrix (κ × ι) ι ℂ := embMat o
  have hEE : Eᴴ * E = (1 : Matrix ι ι ℂ) :=
    embMat_conjTranspose_mul_self o
  have hC := Matrix.l2_opNorm_conjTranspose_mul_self E
  have h1norm : ‖(1 : Matrix ι ι ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (Matrix.mem_unitaryGroup_iff.mpr (by simp))
  simp only [hEE, h1norm, pow_two] at hC
  have hEsq : ‖E‖ * ‖E‖ = 1 := by rw [← hC]
  have hfactor : (‖E‖ - 1) * (‖E‖ + 1) = 0 := by
    have hring : (‖E‖ - 1) * (‖E‖ + 1) = ‖E‖ * ‖E‖ - 1 := by
      ring
    rw [hring, hEsq, sub_self]
  rcases mul_eq_zero.mp hfactor with h | h
  · rw [sub_eq_zero] at h
    exact h
  · have hnn : (0 : ℝ) ≤ ‖E‖ := by positivity
    linarith

theorem norm_ancillaBlock_le_one {o : κ} {U : Matrix (κ × ι) (κ × ι) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (κ × ι) ℂ) : ‖ancillaBlock o U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    have h0 : ancillaBlock o U = 0 := Matrix.ext fun i j => (IsEmpty.false i).elim
    rw [h0, norm_zero]
    exact zero_le_one
  · haveI := hι
    haveI : Nonempty κ := ⟨o⟩
    have hfactor : ancillaBlock o U = (embMat o)ᴴ * U * embMat o := by
      ext i j
      show U (o, i) (o, j) = ∑ p : κ × ι,
        (∑ q : κ × ι, star (if q = (o, i) then (1 : ℂ) else 0) * U q p) *
        (if p = (o, j) then (1 : ℂ) else 0)
      simp only [apply_ite, star_one, star_zero]
      have hinner : ∀ p : κ × ι, (∑ q : κ × ι,
          (if q = (o, i) then (1 : ℂ) else 0) * U q p) = U (o, i) p := by
        intro p
        refine (Fintype.sum_eq_single (o, i) ?_).trans ?_
        · intro q hq
          simp [hq]
        · simp only [eq_self_iff_true, if_true, one_mul]
      simp only [hinner]
      have houter : (∑ p : κ × ι, if p = (o, j) then U (o, i) p * 1 else U (o, i) p * 0)
          = U (o, i) (o, j) := by
        simp only [mul_one, mul_zero, Fintype.sum_ite_eq']
      exact houter.symm
    have hE : ‖(embMat o : Matrix (κ × ι) ι ℂ)‖ = 1 := embMat_norm o
    have hEH : ‖(embMat o : Matrix (κ × ι) ι ℂ)ᴴ‖ = 1 := by
      rw [Matrix.l2_opNorm_conjTranspose, hE]
    have hU1 : ‖U‖ = 1 := CStarRing.norm_of_mem_unitary hU
    have hle1 : ‖((embMat o)ᴴ * U) * embMat o‖
        ≤ ‖(embMat o)ᴴ * U‖ * ‖(embMat o : Matrix (κ × ι) ι ℂ)‖ := by
      apply Matrix.l2_opNorm_mul
    have hle2 : ‖(embMat o)ᴴ * U‖ ≤ ‖(embMat o : Matrix (κ × ι) ι ℂ)ᴴ‖ * ‖U‖ := by
      apply Matrix.l2_opNorm_mul
    have hle2' : ‖(embMat o)ᴴ * U‖ ≤ 1 := by
      have h := hle2
      rw [hEH, hU1, mul_one] at h
      exact h
    have hle1' : ‖((embMat o)ᴴ * U) * embMat o‖ ≤ 1 := by
      have h := hle1
      rw [hE, mul_one] at h
      exact le_trans h hle2'
    rw [hfactor]
    exact hle1'

private theorem norm_smul_ancillaBlock (o : κ) (U : Matrix (κ × ι) (κ × ι) ℂ) (α : ℝ)
    (hU : U ∈ Matrix.unitaryGroup (κ × ι) ℂ) (hα : 0 ≤ α) :
    ‖(α : ℂ) • ancillaBlock o U‖ ≤ α := by
  have hB : ‖ancillaBlock o U‖ ≤ 1 := norm_ancillaBlock_le_one hU
  have hαc : ‖((α : ℝ) : ℂ)‖ = α :=
    (RCLike.norm_ofReal α).trans (abs_of_nonneg hα)
  calc ‖(α : ℂ) • ancillaBlock o U‖ = ‖(α : ℂ)‖ * ‖ancillaBlock o U‖ := by rw [norm_smul]
    _ ≤ α * 1 := by
        rw [hαc]
        exact mul_le_mul_of_nonneg_left hB hα
    _ = α := mul_one α

/-- The note after Definition 43: `‖A‖ ≤ α + ε`. -/
theorem IsBlockEncoding.norm_le {A : Matrix ι ι ℂ} {α ε : ℝ} {o : κ}
    {U : Matrix (κ × ι) (κ × ι) ℂ} (h : IsBlockEncoding A α ε o U) :
    ‖A‖ ≤ α + ε := by
  obtain ⟨hU, herr, hα, _⟩ := h
  have hαB := norm_smul_ancillaBlock o U α hU hα
  calc ‖A‖ = ‖(A - (α : ℂ) • ancillaBlock o U) + (α : ℂ) • ancillaBlock o U‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖A - (α : ℂ) • ancillaBlock o U‖ + ‖(α : ℂ) • ancillaBlock o U‖ := by
        apply norm_add_le
    _ ≤ ε + α := add_le_add herr hαB
    _ = α + ε := add_comm _ _

/-- The encoding of `U` by itself, with a one-point ancilla register (`a = 0`). -/
def trivialEncoding (U : Matrix ι ι ℂ) : Matrix (Fin 1 × ι) (Fin 1 × ι) ℂ :=
  Matrix.of fun p q => U p.2 q.2

private def trivialEquiv (ι : Type*) : Fin 1 × ι ≃ ι where
  toFun := Prod.snd
  invFun i := (0, i)
  left_inv := fun ⟨a, k⟩ => by
    fin_cases a
    rfl
  right_inv := fun i => rfl

private theorem trivialEncoding_mem_unitaryGroup (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    trivialEncoding U ∈ Matrix.unitaryGroup (Fin 1 × ι) ℂ := by
  have hEq : trivialEncoding U = U.submatrix (trivialEquiv ι) (trivialEquiv ι) := rfl
  rw [hEq]
  show U.submatrix ⇑(trivialEquiv ι) ⇑(trivialEquiv ι) ∈
    unitary (Matrix (Fin 1 × ι) (Fin 1 × ι) ℂ)
  exact (Matrix.submatrix_equiv_mem_unitary (e₁ := trivialEquiv ι)
    (e₂ := trivialEquiv ι)).mpr hU

theorem ancillaBlock_trivialEncoding (U : Matrix ι ι ℂ) :
    ancillaBlock (0 : Fin 1) (trivialEncoding U) = U := by
  ext i j
  rfl

/-- Definition 44: a unitary is a `(1, 0, 0)`-block-encoding of itself. -/
theorem isBlockEncoding_self {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    IsBlockEncoding U 1 0 (0 : Fin 1) (trivialEncoding U) := by
  refine ⟨trivialEncoding_mem_unitaryGroup U hU, ?_, zero_le_one, le_refl 0⟩
  rw [ancillaBlock_trivialEncoding]
  simp

/-- The one-ancilla unitary `X ⊗ (1 - P) + 1 ⊗ P`, whose ancilla block is `P`. -/
def projEncoding (P : Matrix ι ι ℂ) : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then P p.2 q.2 else (1 - P) p.2 q.2

private theorem star_projEncoding {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    star (projEncoding P) = projEncoding P := by
  have hPsa : star P = P := hP.isSelfAdjoint
  have hQsa : star (1 - P) = 1 - P := by rw [star_sub, star_one, hPsa]
  have hPentry : ∀ x y, star (P y x) = P x y := fun x y => congrFun (congrFun hPsa x) y
  have hQentry : ∀ x y, star ((1 - P) y x) = (1 - P) x y :=
    fun x y => congrFun (congrFun hQsa x) y
  ext p q
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  show star (if b = a then P j i else (1 - P) j i) =
    (if a = b then P i j else (1 - P) i j)
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl]
    exact hPentry i j
  · rw [if_neg (fun h => hab h.symm), if_neg hab]
    exact hQentry i j

theorem projEncoding_mem_unitaryGroup {P : Matrix ι ι ℂ} (hP : IsStarProjection P) :
    projEncoding P ∈ Matrix.unitaryGroup (Fin 2 × ι) ℂ := by
  have hPP : P * P = P := hP.1
  have hPQ : P * (1 - P) = 0 := by simp only [mul_sub, mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by simp only [sub_mul, one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero]
  have hstar := star_projEncoding hP
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  refine Matrix.mem_unitaryGroup_iff.mpr ?_
  rw [hstar]
  ext p q
  obtain ⟨a, i⟩ := p
  obtain ⟨b, j⟩ := q
  show (∑ x : Fin 2 × ι, (projEncoding P) (a, i) x * (projEncoding P) x (b, j)) =
    (1 : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ) (a, i) (b, j)
  rw [Fintype.sum_prod_type]
  fin_cases a <;> fin_cases b
  · show (∑ c : Fin 2, ∑ k : ι,
        (if (0 : Fin 2) = c then P i k else (1 - P) i k) *
        (if c = (0 : Fin 2) then P k j else (1 - P) k j)) =
        (if ((0 : Fin 2), i) = ((0 : Fin 2), j) then (1 : ℂ) else 0)
    rw [Fin.sum_univ_two]
    simp only [eq_self_iff_true, if_true, h01, h10, if_false]
    simp only [← Matrix.mul_apply, hPP, hQQ]
    by_cases h : i = j
    · rw [h]
      show P j j + (1 - P) j j = (if ((0 : Fin 2), j) = ((0 : Fin 2), j) then (1 : ℂ) else 0)
      rw [if_pos rfl]
      show P j j + ((if j = j then (1 : ℂ) else 0) - P j j) = 1
      rw [if_pos rfl]
      ring
    · show P i j + (1 - P) i j = (if ((0 : Fin 2), i) = ((0 : Fin 2), j) then (1 : ℂ) else 0)
      have hne : ((0 : Fin 2), i) ≠ ((0 : Fin 2), j) := fun he => h (congrArg Prod.snd he)
      rw [if_neg hne]
      show P i j + ((if i = j then (1 : ℂ) else 0) - P i j) = 0
      rw [if_neg h]
      ring
  · show (∑ c : Fin 2, ∑ k : ι,
        (if (0 : Fin 2) = c then P i k else (1 - P) i k) *
        (if c = (1 : Fin 2) then P k j else (1 - P) k j)) =
        (if ((0 : Fin 2), i) = ((1 : Fin 2), j) then (1 : ℂ) else 0)
    have hne : ((0 : Fin 2), i) ≠ ((1 : Fin 2), j) := fun he => h01 (congrArg Prod.fst he)
    rw [if_neg hne]
    rw [Fin.sum_univ_two]
    simp only [eq_self_iff_true, if_true, h01, h10, if_false]
    simp only [← Matrix.mul_apply, hPQ, hQP]
    show (0 : Matrix ι ι ℂ) i j + (0 : Matrix ι ι ℂ) i j = (0 : ℂ)
    show (0 : ℂ) + (0 : ℂ) = (0 : ℂ)
    exact add_zero _
  · show (∑ c : Fin 2, ∑ k : ι,
        (if (1 : Fin 2) = c then P i k else (1 - P) i k) *
        (if c = (0 : Fin 2) then P k j else (1 - P) k j)) =
        (if ((1 : Fin 2), i) = ((0 : Fin 2), j) then (1 : ℂ) else 0)
    have hne : ((1 : Fin 2), i) ≠ ((0 : Fin 2), j) := fun he => h10 (congrArg Prod.fst he)
    rw [if_neg hne]
    rw [Fin.sum_univ_two]
    simp only [eq_self_iff_true, if_true, h01, h10, if_false]
    simp only [← Matrix.mul_apply, hPQ, hQP]
    show (0 : Matrix ι ι ℂ) i j + (0 : Matrix ι ι ℂ) i j = (0 : ℂ)
    show (0 : ℂ) + (0 : ℂ) = (0 : ℂ)
    exact add_zero _
  · show (∑ c : Fin 2, ∑ k : ι,
        (if (1 : Fin 2) = c then P i k else (1 - P) i k) *
        (if c = (1 : Fin 2) then P k j else (1 - P) k j)) =
        (if ((1 : Fin 2), i) = ((1 : Fin 2), j) then (1 : ℂ) else 0)
    rw [Fin.sum_univ_two]
    simp only [eq_self_iff_true, if_true, h01, h10, if_false]
    simp only [← Matrix.mul_apply, hPP, hQQ]
    by_cases h : i = j
    · rw [h]
      show (1 - P) j j + P j j = (if ((1 : Fin 2), j) = ((1 : Fin 2), j) then (1 : ℂ) else 0)
      rw [if_pos rfl]
      show ((if j = j then (1 : ℂ) else 0) - P j j) + P j j = 1
      rw [if_pos rfl]
      ring
    · show (1 - P) i j + P i j = (if ((1 : Fin 2), i) = ((1 : Fin 2), j) then (1 : ℂ) else 0)
      have hne : ((1 : Fin 2), i) ≠ ((1 : Fin 2), j) := fun he => h (congrArg Prod.snd he)
      rw [if_neg hne]
      show ((if i = j then (1 : ℂ) else 0) - P i j) + P i j = 0
      rw [if_neg h]
      ring

/-- Scaled projections: `α • P` has the `(α, 1, 0)` encoding `projEncoding P`. -/
theorem isBlockEncoding_smul_projection {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (α : ℝ) (hα : 0 ≤ α) : IsBlockEncoding ((α : ℂ) • P) α 0 (0 : Fin 2) (projEncoding P) := by
  have hblock : ancillaBlock (0 : Fin 2) (projEncoding P) = P := by
    ext i j
    show (if (0 : Fin 2) = 0 then P i j else (1 - P) i j) = P i j
    rw [if_pos rfl]
  refine ⟨projEncoding_mem_unitaryGroup hP, ?_, hα, le_refl 0⟩
  rw [hblock]
  simp

/-- Reindexing `κ × (μ × ι) ≃ (μ × κ) × ι`. -/
def swapAncillaEquiv (κ μ ι : Type*) : κ × (μ × ι) ≃ (μ × κ) × ι :=
  (Equiv.prodAssoc κ μ ι).symm.trans ((Equiv.prodComm κ μ).prodCongr (Equiv.refl ι))

/-- The product unitary `(I_μ ⊗ U)(I_κ ⊗ V)` on `(μ × κ) × ι`: `V` acts on `μ × ι` first, then
`U` on `κ × ι`, each as the identity on the other ancilla (Lemma 53 and its footnote 25). -/
def ancillaMul (U : Matrix (κ × ι) (κ × ι) ℂ) (V : Matrix (μ × ι) (μ × ι) ℂ) :
    Matrix ((μ × κ) × ι) ((μ × κ) × ι) ℂ :=
  Matrix.reindex (Equiv.prodAssoc μ κ ι).symm (Equiv.prodAssoc μ κ ι).symm
      ((1 : Matrix μ μ ℂ) ⊗ₖ U) *
    Matrix.reindex (swapAncillaEquiv κ μ ι) (swapAncillaEquiv κ μ ι) ((1 : Matrix κ κ ℂ) ⊗ₖ V)

theorem ancillaBlock_ancillaMul (oκ : κ) (oμ : μ) (U : Matrix (κ × ι) (κ × ι) ℂ)
    (V : Matrix (μ × ι) (μ × ι) ℂ) :
    ancillaBlock (oμ, oκ) (ancillaMul U V) = ancillaBlock oκ U * ancillaBlock oμ V := by
  ext i j
  show (∑ p : (μ × κ) × ι,
      (Matrix.reindex (Equiv.prodAssoc μ κ ι).symm (Equiv.prodAssoc μ κ ι).symm
        ((1 : Matrix μ μ ℂ) ⊗ₖ U)) ((oμ, oκ), i) p *
      (Matrix.reindex (swapAncillaEquiv κ μ ι) (swapAncillaEquiv κ μ ι)
        ((1 : Matrix κ κ ℂ) ⊗ₖ V)) p ((oμ, oκ), j)) =
    (ancillaBlock oκ U * ancillaBlock oμ V) i j
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  show (∑ m : μ, ∑ k : κ, ∑ i'' : ι,
      (((if oμ = m then (1 : ℂ) else 0) * U (oκ, i) (k, i'')) *
        ((if k = oκ then (1 : ℂ) else 0) * V (m, i'') (oμ, j)))) =
    ∑ k : ι, U (oκ, i) (oκ, k) * V (oμ, k) (oμ, j)
  have hcollapse_m : ∀ m : μ, (∑ k : κ, ∑ i'' : ι,
      (((if oμ = m then (1 : ℂ) else 0) * U (oκ, i) (k, i'')) *
        ((if k = oκ then (1 : ℂ) else 0) * V (m, i'') (oμ, j)))) =
      (if oμ = m then (∑ k : κ, ∑ i'' : ι, U (oκ, i) (k, i'') *
        ((if k = oκ then (1 : ℂ) else 0) * V (m, i'') (oμ, j))) else 0) := by
    intro m
    by_cases hm : oμ = m
    · rw [if_pos hm]
      simp only [hm, eq_self_iff_true, if_true, one_mul]
    · simp [hm]
  simp only [hcollapse_m]
  have hcollapse_k : ∀ k : κ, (∑ i'' : ι, U (oκ, i) (k, i'') *
      ((if k = oκ then (1 : ℂ) else 0) * V (oμ, i'') (oμ, j))) =
      (if k = oκ then (∑ i'' : ι, U (oκ, i) (k, i'') * V (oμ, i'') (oμ, j)) else 0) := by
    intro k
    by_cases hk : k = oκ
    · rw [if_pos hk]
      simp only [hk, eq_self_iff_true, if_true, one_mul]
    · simp [hk]
  refine (Fintype.sum_eq_single oμ ?_).trans ?_
  · intro m hm
    rw [if_neg (fun h => hm h.symm)]
  · rw [if_pos rfl]
    simp only [hcollapse_k]
    refine (Fintype.sum_eq_single oκ ?_).trans ?_
    · intro k hk
      rw [if_neg hk]
    · rw [if_pos rfl]

theorem ancillaMul_mem_unitaryGroup {U : Matrix (κ × ι) (κ × ι) ℂ}
    {V : Matrix (μ × ι) (μ × ι) ℂ} (hU : U ∈ Matrix.unitaryGroup (κ × ι) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (μ × ι) ℂ) :
    ancillaMul U V ∈ Matrix.unitaryGroup ((μ × κ) × ι) ℂ := by
  have h1μ : (1 : Matrix μ μ ℂ) ∈ unitary (Matrix μ μ ℂ) :=
    Matrix.mem_unitaryGroup_iff.mpr (by simp)
  have h1κ : (1 : Matrix κ κ ℂ) ∈ unitary (Matrix κ κ ℂ) :=
    Matrix.mem_unitaryGroup_iff.mpr (by simp)
  have hKU : (1 : Matrix μ μ ℂ) ⊗ₖ U ∈ unitary (Matrix (μ × (κ × ι)) (μ × (κ × ι)) ℂ) :=
    Matrix.kronecker_mem_unitary h1μ hU
  have hKV : (1 : Matrix κ κ ℂ) ⊗ₖ V ∈ unitary (Matrix (κ × (μ × ι)) (κ × (μ × ι)) ℂ) :=
    Matrix.kronecker_mem_unitary h1κ hV
  have hX : Matrix.reindex (Equiv.prodAssoc μ κ ι).symm (Equiv.prodAssoc μ κ ι).symm
      ((1 : Matrix μ μ ℂ) ⊗ₖ U) ∈ Matrix.unitaryGroup ((μ × κ) × ι) ℂ := by
    show ((1 : Matrix μ μ ℂ) ⊗ₖ U).submatrix ⇑((Equiv.prodAssoc μ κ ι).symm).symm
      ⇑((Equiv.prodAssoc μ κ ι).symm).symm ∈ unitary (Matrix ((μ × κ) × ι) ((μ × κ) × ι) ℂ)
    exact (Matrix.submatrix_equiv_mem_unitary
      (e₁ := (Equiv.prodAssoc μ κ ι).symm.symm)
      (e₂ := (Equiv.prodAssoc μ κ ι).symm.symm)).mpr hKU
  have hY : Matrix.reindex (swapAncillaEquiv κ μ ι) (swapAncillaEquiv κ μ ι)
      ((1 : Matrix κ κ ℂ) ⊗ₖ V) ∈ Matrix.unitaryGroup ((μ × κ) × ι) ℂ := by
    show ((1 : Matrix κ κ ℂ) ⊗ₖ V).submatrix ⇑(swapAncillaEquiv κ μ ι).symm
      ⇑(swapAncillaEquiv κ μ ι).symm ∈ unitary (Matrix ((μ × κ) × ι) ((μ × κ) × ι) ℂ)
    exact (Matrix.submatrix_equiv_mem_unitary (e₁ := (swapAncillaEquiv κ μ ι).symm)
      (e₂ := (swapAncillaEquiv κ μ ι).symm)).mpr hKV
  show _ * _ ∈ Matrix.unitaryGroup _ ℂ
  exact mul_mem hX hY

/-- Lemma 53 with the cross term `δ * ε` that the source proof omits. -/
theorem IsBlockEncoding.mul {A B : Matrix ι ι ℂ} {α β δ ε : ℝ} {oκ : κ} {oμ : μ}
    {U : Matrix (κ × ι) (κ × ι) ℂ} {V : Matrix (μ × ι) (μ × ι) ℂ}
    (hU : IsBlockEncoding A α δ oκ U) (hV : IsBlockEncoding B β ε oμ V)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    IsBlockEncoding (A * B) (α * β) (α * ε + β * δ + δ * ε) (oμ, oκ) (ancillaMul U V) := by
  obtain ⟨hUmem, hUerr, hα0, hδ⟩ := hU
  obtain ⟨hVmem, hVerr, hβ0, hε0⟩ := hV
  have hαB := norm_smul_ancillaBlock oκ U α hUmem hα
  have hβB := norm_smul_ancillaBlock oμ V β hVmem hβ
  have hBnorm : ‖B‖ ≤ β + ε := by
    have hdecompB : B = (B - (β : ℂ) • ancillaBlock oμ V) + (β : ℂ) • ancillaBlock oμ V := by
      rw [sub_add_cancel]
    calc ‖B‖ = ‖(B - (β : ℂ) • ancillaBlock oμ V) + (β : ℂ) • ancillaBlock oμ V‖ :=
          congrArg _ hdecompB
      _ ≤ ‖B - (β : ℂ) • ancillaBlock oμ V‖ + ‖(β : ℂ) • ancillaBlock oμ V‖ := by
          apply norm_add_le
      _ ≤ ε + β := add_le_add hVerr hβB
      _ = β + ε := add_comm _ _
  have hsmul : ((α * β : ℝ) : ℂ) • (ancillaBlock oκ U * ancillaBlock oμ V) =
      ((α : ℂ) • ancillaBlock oκ U) * ((β : ℂ) • ancillaBlock oμ V) := by
    have hcast : ((α * β : ℝ) : ℂ) = (α : ℂ) * (β : ℂ) := by simp
    rw [hcast, smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]
  have hdecomp : A * B - ((α * β : ℝ) : ℂ) • (ancillaBlock oκ U * ancillaBlock oμ V) =
      (A - (α : ℂ) • ancillaBlock oκ U) * B +
      ((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V) := by
    rw [hsmul]
    simp only [sub_mul, mul_sub]
    abel
  refine ⟨ancillaMul_mem_unitaryGroup hUmem hVmem, ?_, mul_nonneg hα0 hβ0,
    add_nonneg (add_nonneg (mul_nonneg hα0 hε0) (mul_nonneg hβ0 hδ)) (mul_nonneg hδ hε0)⟩
  rw [ancillaBlock_ancillaMul, hdecomp]
  have h1 : ‖(A - (α : ℂ) • ancillaBlock oκ U) * B‖ ≤ δ * ‖B‖ :=
    le_trans (by apply norm_mul_le) (mul_le_mul hUerr le_rfl (by positivity) hδ)
  have h2 : ‖((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V)‖ ≤ α * ε :=
    le_trans (by apply norm_mul_le) (mul_le_mul hαB hVerr (by positivity) hα)
  calc ‖(A - (α : ℂ) • ancillaBlock oκ U) * B +
        ((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V)‖
        ≤ ‖(A - (α : ℂ) • ancillaBlock oκ U) * B‖ +
          ‖((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V)‖ := by
          apply norm_add_le
    _ ≤ δ * ‖B‖ + α * ε := add_le_add h1 h2
    _ ≤ δ * (β + ε) + α * ε :=
        add_le_add (mul_le_mul_of_nonneg_left hBnorm hδ) le_rfl
    _ = α * ε + β * δ + δ * ε := by ring

/-- Lemma 53 as stated, under the bound `‖B‖ ≤ β` that its proof uses. -/
theorem IsBlockEncoding.mul_of_norm_le {A B : Matrix ι ι ℂ} {α β δ ε : ℝ} {oκ : κ} {oμ : μ}
    {U : Matrix (κ × ι) (κ × ι) ℂ} {V : Matrix (μ × ι) (μ × ι) ℂ}
    (hU : IsBlockEncoding A α δ oκ U) (hV : IsBlockEncoding B β ε oμ V)
    (hα : 0 ≤ α) (hB : ‖B‖ ≤ β) :
    IsBlockEncoding (A * B) (α * β) (α * ε + β * δ) (oμ, oκ) (ancillaMul U V) := by
  obtain ⟨hUmem, hUerr, hα0, hδ⟩ := hU
  obtain ⟨hVmem, hVerr, hβ0, hε0⟩ := hV
  have hαB := norm_smul_ancillaBlock oκ U α hUmem hα
  have hsmul : ((α * β : ℝ) : ℂ) • (ancillaBlock oκ U * ancillaBlock oμ V) =
      ((α : ℂ) • ancillaBlock oκ U) * ((β : ℂ) • ancillaBlock oμ V) := by
    have hcast : ((α * β : ℝ) : ℂ) = (α : ℂ) * (β : ℂ) := by simp
    rw [hcast, smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]
  have hdecomp : A * B - ((α * β : ℝ) : ℂ) • (ancillaBlock oκ U * ancillaBlock oμ V) =
      (A - (α : ℂ) • ancillaBlock oκ U) * B +
      ((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V) := by
    rw [hsmul]
    simp only [sub_mul, mul_sub]
    abel
  refine ⟨ancillaMul_mem_unitaryGroup hUmem hVmem, ?_, mul_nonneg hα0 hβ0,
    add_nonneg (mul_nonneg hα0 hε0) (mul_nonneg hβ0 hδ)⟩
  rw [ancillaBlock_ancillaMul, hdecomp]
  have h1 : ‖(A - (α : ℂ) • ancillaBlock oκ U) * B‖ ≤ δ * β :=
    le_trans (by apply norm_mul_le) (mul_le_mul hUerr hB (by positivity) hδ)
  have h2 : ‖((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V)‖ ≤ α * ε :=
    le_trans (by apply norm_mul_le) (mul_le_mul hαB hVerr (by positivity) hα)
  calc ‖(A - (α : ℂ) • ancillaBlock oκ U) * B +
        ((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V)‖
        ≤ ‖(A - (α : ℂ) • ancillaBlock oκ U) * B‖ +
          ‖((α : ℂ) • ancillaBlock oκ U) * (B - (β : ℂ) • ancillaBlock oμ V)‖ := by
          apply norm_add_le
    _ ≤ δ * β + α * ε := add_le_add h1 h2
    _ = α * ε + β * δ := by ring

/-- `Fin (2 ^ b) × Fin (2 ^ a) ≃ Fin (2 ^ (a + b))`, sending `(0, 0)` to `0`. -/
def qubitAncillaEquiv (a b : ℕ) : Fin (2 ^ b) × Fin (2 ^ a) ≃ Fin (2 ^ (a + b)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm]))

private theorem fin_zero_val (k : ℕ) [NeZero k] : (0 : Fin k).val = 0 := by
  simp

theorem qubitAncillaEquiv_zero (a b : ℕ) : qubitAncillaEquiv a b (0, 0) = 0 := by
  have hfin : finProdFinEquiv (0, 0) = (0 : Fin (2 ^ b * 2 ^ a)) := by
    apply Fin.ext
    show (0 : Fin (2 ^ a)).val + 2 ^ a * (0 : Fin (2 ^ b)).val =
      (0 : Fin (2 ^ b * 2 ^ a)).val
    simp only [fin_zero_val, mul_zero, add_zero]
  unfold qubitAncillaEquiv
  rw [Equiv.trans_apply, hfin]
  apply Fin.ext
  show (0 : Fin (2 ^ b * 2 ^ a)).val = (0 : Fin (2 ^ (a + b))).val
  simp only [fin_zero_val]

/-- Lemma 53 in qubit form with the corrected error term: an `(αβ, a + b, ·)` encoding. -/
theorem IsQubitBlockEncoding.mul {s a b : ℕ} {A B : Matrix (Fin (2 ^ s)) (Fin (2 ^ s)) ℂ}
    {α β δ ε : ℝ}
    {U : Matrix (Fin (2 ^ a) × Fin (2 ^ s)) (Fin (2 ^ a) × Fin (2 ^ s)) ℂ}
    {V : Matrix (Fin (2 ^ b) × Fin (2 ^ s)) (Fin (2 ^ b) × Fin (2 ^ s)) ℂ}
    (hU : IsQubitBlockEncoding A α δ U) (hV : IsQubitBlockEncoding B β ε V)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    IsQubitBlockEncoding (a := a + b) (A * B) (α * β) (α * ε + β * δ + δ * ε)
      (Matrix.reindex ((qubitAncillaEquiv a b).prodCongr (Equiv.refl _))
        ((qubitAncillaEquiv a b).prodCongr (Equiv.refl _)) (ancillaMul U V)) := by
  have hU' : IsBlockEncoding A α δ (0 : Fin (2 ^ a)) U := hU
  have hV' : IsBlockEncoding B β ε (0 : Fin (2 ^ b)) V := hV
  have hMul := IsBlockEncoding.mul hU' hV' hα hβ
  obtain ⟨hWmem, hWerr, hαβ, hε⟩ := hMul
  have hsymm : (qubitAncillaEquiv a b).symm 0 = (0, 0) := by
    refine Equiv.injective (qubitAncillaEquiv a b) ?_
    rw [Equiv.apply_symm_apply, qubitAncillaEquiv_zero]
  have hblock : ancillaBlock (0 : Fin (2 ^ (a + b))) (Matrix.reindex
        ((qubitAncillaEquiv a b).prodCongr (Equiv.refl _))
        ((qubitAncillaEquiv a b).prodCongr (Equiv.refl _)) (ancillaMul U V)) =
      ancillaBlock ((0 : Fin (2 ^ b)), (0 : Fin (2 ^ a))) (ancillaMul U V) := by
    ext i j
    show (ancillaMul U V)
        (((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm (0, i))
        (((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm (0, j)) =
      (ancillaMul U V) ((0, 0), i) ((0, 0), j)
    have hEi : ((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm
        (0, i) = ((0, 0), i) := by
      show ((qubitAncillaEquiv a b).symm 0, (Equiv.refl (Fin (2 ^ s))).symm i) = ((0, 0), i)
      rw [hsymm]
      rfl
    have hEj : ((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm
        (0, j) = ((0, 0), j) := by
      show ((qubitAncillaEquiv a b).symm 0, (Equiv.refl (Fin (2 ^ s))).symm j) = ((0, 0), j)
      rw [hsymm]
      rfl
    rw [hEi, hEj]
  show IsBlockEncoding (A * B) (α * β) (α * ε + β * δ + δ * ε) (0 : Fin (2 ^ (a + b))) _
  refine ⟨?_, ?_, hαβ, hε⟩
  · show (ancillaMul U V).submatrix
        ⇑(((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm)
        ⇑(((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm) ∈ unitary _
    exact (Matrix.submatrix_equiv_mem_unitary
      (e₁ := ((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm)
      (e₂ := ((qubitAncillaEquiv a b).prodCongr (Equiv.refl (Fin (2 ^ s)))).symm)).mpr hWmem
  · rw [hblock]
    exact hWerr

end MathlibExt.Quantum.BlockEncoding
