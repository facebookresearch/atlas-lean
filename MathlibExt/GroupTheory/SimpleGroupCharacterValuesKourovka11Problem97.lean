/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Character

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import MathlibExt.GroupTheory.BurnsidePaqb.CharacterOrthogonality

/-!
# Simple groups with a given set of character values at an element (Kourovka Notebook Problem 11.97)

Kourovka Notebook, Archive of Solved Problems, Problem 11.97 (S. P. Strunkov): are there only
finitely many finite simple groups with a given set of all different values of irreducible
characters on a single element?

This module refutes Kourovka Problem 11.97 using involutions in
`PSL(2, F)` over finite fields of characteristic two.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.97 (S. P.
Strunkov). UnsolvedMath record UM-00700789 (`KOU-11.97`), dataset ulamai/UnsolvedMath v1.8.0.

The groups are finite non-abelian simple groups: the cyclic groups of prime order all have the
single value 1 at the identity, which would refute the statement for a trivial reason, and the
Archive's answer concerns `L_2(2^m)`. The set of values at `g` is `{χ(g) : χ irreducible}`, with
irreducible characters those of the simple objects of `FDRep ℂ G`. "Finitely many" up to isomorphism
is a bound on the order.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97Wanted

/-- **Values of the irreducible characters at an element.** For an element $g$ of a group $G$, the
set of complex numbers $\chi(g)$, where $\chi$ ranges over the characters of the irreducible
finite-dimensional complex representations of $G$. -/
def irrCharValues {G : Type} [Group G] (g : G) : Set ℂ :=
  {z | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character g = z}

/-- **Kourovka Problem 11.97 (simple groups with a given set of character values).** The
statement that for every finite set $S$ of complex numbers there is a bound $N$ such that every
finite non-abelian simple group $G$ having an element $g$ at which the set of values of the
irreducible complex characters of $G$ is exactly $S$ has order at most $N$. The problem is due to
S. P. Strunkov.

"Only finitely many such groups" up to isomorphism is stated as this bound on the order. -/
def finitelyManySimpleGivenCharacterValues : Prop :=
  ∀ S : Set ℂ, S.Finite → ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → (∃ g : G, irrCharValues g = S) → Nat.card G ≤ N

open Matrix CategoryTheory
open Matrix.SpecialLinearGroup
open scoped MatrixGroups MonoidAlgebra

variable {F : Type} [Field F]

section
variable [CharP F 2]

private lemma add_self_eq_zero (x : F) : x + x = 0 := by
  rw [← two_mul, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_mul]

private lemma neg_eq_self (x : F) : -x = x :=
  neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero x)

private def reflection : SL(2, F) :=
  .mk !![0, 1; 1, 0] (by simp [det_fin_two_of, neg_eq_self])

end

private def unipotent (x : F) : SL(2, F) :=
  Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one x

private noncomputable def diagonal (a : Fˣ) : SL(2, F) :=
  diag2 (a : F) a.ne_zero

private lemma coe_unipotent (x : F) :
    (unipotent x : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := by
  rw [unipotent, transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma coe_diagonal (a : Fˣ) :
    (diagonal a : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] :=
  by simpa [diagonal] using diag2_coe' a.ne_zero

private lemma sl_ext {g h : SL(2, F)}
    (h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = (h : Matrix (Fin 2) (Fin 2) F) 0 1)
    (h10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (h : Matrix (Fin 2) (Fin 2) F) 1 1) : g = h := by
  apply Subtype.ext
  exact Matrix.ext fun i j ↦ by fin_cases i <;> fin_cases j <;> assumption

private lemma unipotent_add (x y : F) :
    unipotent (x + y) = unipotent x * unipotent y :=
  transvection_add zero_ne_one x y

private lemma unipotent_injective : Function.Injective (unipotent (F := F)) :=
  fun _ _ h ↦ by
    simpa [coe_unipotent] using
      congrArg (fun g : SL(2, F) ↦ (g : Matrix (Fin 2) (Fin 2) F) 0 1) h

private lemma diagonal_one : diagonal (1 : Fˣ) = 1 := by
  apply sl_ext <;> simp [coe_diagonal]

private lemma diagonal_mul (a b : Fˣ) : diagonal (a * b) = diagonal a * diagonal b := by
  apply sl_ext <;> simp [coe_diagonal, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private noncomputable def diagonalHom : Fˣ →* SL(2, F) where
  toFun := diagonal
  map_one' := diagonal_one
  map_mul' := diagonal_mul

variable [CharP F 2]

private lemma reflection_sq : (reflection : SL(2, F)) * reflection = 1 := by
  apply sl_ext <;> simp [reflection, Matrix.mul_apply, Fin.sum_univ_two]

omit [CharP F 2] in
private lemma diagonal_unipotent (a : Fˣ) (x : F) :
    diagonal a * unipotent x = unipotent ((a : F)^2 * x) * diagonal a := by
  apply sl_ext <;> simp [coe_diagonal, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

private lemma diagonal_reflection (a : Fˣ) :
    diagonal a * reflection = reflection * diagonal a⁻¹ := by
  apply sl_ext <;> simp [coe_diagonal, reflection, Matrix.mul_apply, Fin.sum_univ_two]

-- The lower-left entry determines which of the two Bruhat cells contains the matrix.
private lemma bruhat (g : SL(2, F)) :
    (∃ (x : F) (a : Fˣ), g = unipotent x * diagonal a) ∨
    (∃ (x y : F) (a : Fˣ), g = unipotent x * (diagonal a * reflection) * unipotent y) := by
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
    by_cases hc : c = 0
    · subst c
      simp only [mul_zero, sub_zero] at hdet
      have ha : a ≠ 0 := by aesop
      have had : a⁻¹ = d := (inv_eq_of_mul_eq_one_right hdet)
      refine Or.inl ⟨b * a, Units.mk0 a ha, ?_⟩
      apply sl_ext <;>
        simp [coe_unipotent, coe_diagonal, Matrix.mul_apply, Fin.sum_univ_two, had, mul_assoc, hdet]
    · have hb : b = a * (d / c) + c⁻¹ := by
        field_simp [hc]
        linear_combination -hdet - (add_self_eq_zero (1 : F))
      have hd : c * (d / c) = d := by rw [mul_comm c, div_mul_cancel₀ _ hc]
      refine Or.inr ⟨a / c, d / c, (Units.mk0 c hc)⁻¹, ?_⟩
      apply sl_ext <;>
        simp [coe_unipotent, coe_diagonal, reflection, Matrix.mul_apply, Fin.sum_univ_two,
          div_mul_cancel₀ _ hc, hb, hd]

private def reverseTranspose : SL(2, F) →* (SL(2, F))ᵐᵒᵖ where
  toFun g := MulOpposite.op (reflection * g.transpose * reflection)
  map_one' := by
    apply MulOpposite.unop_injective
    rw [show (1 : SL(2, F)).transpose = 1 by
      apply Subtype.ext
      simp, mul_one, reflection_sq]
    rfl
  map_mul' g h := by
    have htranspose : (g * h).transpose = h.transpose * g.transpose :=
      Subtype.ext (by simp [coe_transpose, Matrix.transpose_mul])
    apply MulOpposite.unop_injective
    change reflection * (g * h).transpose * reflection =
      (reflection * h.transpose * reflection) * (reflection * g.transpose * reflection)
    rw [htranspose]
    simp only [mul_assoc, ← mul_assoc reflection reflection, reflection_sq, one_mul]

private lemma reverseTranspose_unipotent (x : F) :
    (reverseTranspose (unipotent x)).unop = unipotent x := by
  change reflection * (unipotent x).transpose * reflection = _
  apply sl_ext <;>
    simp [coe_unipotent, reflection, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

private lemma reverseTranspose_diagonal (a : Fˣ) :
    (reverseTranspose (diagonal a)).unop = diagonal a⁻¹ := by
  change reflection * (diagonal a).transpose * reflection = _
  apply sl_ext <;>
    simp [coe_diagonal, reflection, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

private lemma reverseTranspose_reflection :
    (reverseTranspose (reflection : SL(2, F))).unop = reflection := by
  change reflection * (reflection : SL(2, F)).transpose * reflection = _
  rw [show (reflection : SL(2, F)).transpose = reflection by
    apply sl_ext <;> rfl, reflection_sq, one_mul]

private lemma center_eq_bot : Subgroup.center SL(2, F) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨a, ha, hscalar⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha' : a ^ 2 = 1 := by simpa using ha
  have hone : a = 1 := by
    rcases sq_eq_one_iff.mp ha' with h | h
    · exact h
    · exact h.trans (neg_eq_self 1)
  subst a
  exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using hscalar.symm))

private noncomputable def toSL : PSL(2, F) ≃* SL(2, F) :=
  (QuotientGroup.quotientMulEquivOfEq center_eq_bot).trans QuotientGroup.quotientBot

private lemma not_commutative : ∃ a b : SL(2, F), a * b ≠ b * a := by
  refine ⟨reflection, unipotent 1, fun h ↦ (zero_ne_one : (0 : F) ≠ 1) ?_⟩
  simpa [reflection, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two] using
    congrArg (fun g : SL(2, F) ↦ (g : Matrix (Fin 2) (Fin 2) F) 0 0) h

section Projectors

open MulOpposite MonoidAlgebra

variable [Fintype F]

private noncomputable abbrev groupBasis : SL(2, F) →* ℂ[SL(2, F)] := MonoidAlgebra.of ℂ _

private noncomputable def projector (χ : AddChar F ℂ) : ℂ[SL(2, F)] :=
  (Fintype.card F : ℂ)⁻¹ • ∑ x : F, χ x • groupBasis (unipotent x)

omit [Fintype F] in
private lemma character_sq (χ : AddChar F ℂ) (x : F) : χ x * χ x = 1 := by
  rw [← χ.map_add_eq_mul, add_self_eq_zero, χ.map_zero_eq_one]

private lemma basis_mul_projector (χ : AddChar F ℂ) (t : F) :
    groupBasis (unipotent t) * projector χ = χ t • projector χ := by
  have h (x : F) : χ x = χ t * χ (t + x) := by
    rw [χ.map_add_eq_mul, ← mul_assoc, character_sq, one_mul]
  unfold projector
  simp only [Algebra.mul_smul_comm, Finset.mul_sum, ← map_mul, ← unipotent_add]
  rw [smul_comm (χ t)]
  exact congrArg ((Fintype.card F : ℂ)⁻¹ • ·) (by
    rw [Finset.smul_sum]
    apply Fintype.sum_bijective (fun x : F ↦ t + x) (AddGroup.addLeft_bijective t)
    intro x
    rw [smul_smul, ← h])

private lemma projector_mul_basis (χ : AddChar F ℂ) (t : F) :
    projector χ * groupBasis (unipotent t) = χ t • projector χ := by
  rw [← basis_mul_projector]
  simp only [projector, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Finset.sum_mul,
    Finset.mul_sum, ← map_mul, ← unipotent_add]
  congr 1
  exact Finset.sum_congr rfl fun x _ ↦ by rw [add_comm x t]

private lemma projector_idempotent (χ : AddChar F ℂ) : IsIdempotentElem (projector χ) := by
  unfold IsIdempotentElem
  conv_lhs => arg 1; unfold projector
  simp only [Algebra.smul_mul_assoc, Finset.sum_mul, basis_mul_projector, smul_smul, character_sq,
    one_smul, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hq, one_smul]

private noncomputable def antiAlgebra : ℂ[SL(2, F)] →ₐ[ℂ] (ℂ[SL(2, F)])ᵐᵒᵖ :=
  MonoidAlgebra.lift ℂ _ _
    { toFun := fun g ↦ op (groupBasis (reverseTranspose g).unop)
      map_one' := by rw [map_one, unop_one, map_one, op_one]
      map_mul' := fun g h ↦ by rw [map_mul, unop_mul, map_mul, op_mul] }

omit [Fintype F] in
private lemma antiAlgebra_basis (g : SL(2, F)) :
    antiAlgebra (groupBasis g) = op (groupBasis (reverseTranspose g).unop) :=
  MonoidAlgebra.lift_of ..

private lemma antiAlgebra_projector (χ : AddChar F ℂ) :
    antiAlgebra (projector χ) = op (projector χ) := by
  simp only [projector, map_smul, map_sum, antiAlgebra_basis, reverseTranspose_unipotent, op_smul]
  congr 1
  exact (map_sum (MulOpposite.opAddEquiv : ℂ[SL(2, F)] ≃+ _) _ _).symm

private lemma diagonal_sandwich_vanishes {χ : AddChar F ℂ} (hχ : χ ≠ 1)
    {a : Fˣ} (ha : a ≠ 1) :
    projector χ * groupBasis (diagonal a) * projector χ = 0 := by
  have ha2 : (a : F)^2 ≠ 1 := by
    intro h
    apply ha
    apply Units.ext
    rcases sq_eq_one_iff.mp h with he | he
    · exact he
    · exact he.trans (neg_eq_self 1)
  have hχ' := (AddChar.IsPrimitive.of_ne_one hχ) (sub_ne_zero.mpr ha2)
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hχ'
  have hdiff : χ x - χ ((a : F)^2 * x) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hx
    change χ (((a : F)^2 - 1) * x) = 1
    rw [sub_mul, one_mul, sub_eq_add_neg, neg_eq_self, χ.map_add_eq_mul, ← h, character_sq]
  set e := projector χ
  set d := groupBasis (diagonal a)
  have hdu : d * groupBasis (unipotent x) = groupBasis (unipotent ((a : F)^2 * x)) * d := by
    rw [← map_mul, ← map_mul, diagonal_unipotent]
  have he : χ x • (e * d * e) = χ ((a : F)^2 * x) • (e * d * e) := calc
    _ = e * (d * groupBasis (unipotent x)) * e := by
      rw [mul_assoc e, mul_assoc e, mul_assoc d, show e = projector χ from rfl,
        basis_mul_projector, Algebra.mul_smul_comm, Algebra.mul_smul_comm]
    _ = e * (groupBasis (unipotent ((a : F)^2 * x)) * d) * e := by rw [hdu]
    _ = _ := by
      rw [← mul_assoc e, show e = projector χ from rfl, projector_mul_basis,
        Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
  have hz : (χ x - χ ((a : F)^2 * x)) • (e * d * e) = 0 := by
    rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left hdiff

-- Reversing products fixes the compressed basis elements. In the upper triangular
-- cell only the unipotent subgroup contributes, and in the other cell the diagonal
-- times the reflection is fixed by reverse transposition.
private lemma antiAlgebra_sandwich_basis {χ : AddChar F ℂ} (hχ : χ ≠ 1) (g : SL(2, F)) :
    antiAlgebra (projector χ * groupBasis g * projector χ) =
      op (projector χ * groupBasis g * projector χ) := by
  let e := projector χ
  have strip (p : SL(2, F)) (x : F) :
      e * groupBasis (unipotent x * p) * e = χ x • (e * groupBasis p * e) := by
    rw [map_mul, ← mul_assoc e, show e = projector χ from rfl, projector_mul_basis,
      Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
  have strip' (p : SL(2, F)) (y : F) :
      e * groupBasis (p * unipotent y) * e = χ y • (e * groupBasis p * e) := by
    rw [map_mul, mul_assoc e, mul_assoc (groupBasis p), show e = projector χ from rfl,
      basis_mul_projector, Algebra.mul_smul_comm, Algebra.mul_smul_comm, mul_assoc]
  rcases bruhat g with ⟨x, a, rfl⟩ | ⟨x, y, a, rfl⟩
  · change antiAlgebra (e * groupBasis _ * e) = _
    rw [strip, map_smul, op_smul]
    by_cases ha : a = 1
    · subst a
      rw [diagonal_one, map_one, mul_one, projector_idempotent χ, antiAlgebra_projector]
    · rw [diagonal_sandwich_vanishes hχ ha, map_zero, op_zero]
  · change antiAlgebra (e * groupBasis _ * e) = _
    rw [strip', strip, map_smul, map_smul, op_smul, op_smul]
    have hfix : (reverseTranspose (diagonal a * reflection)).unop = diagonal a * reflection := by
      rw [map_mul, unop_mul, reverseTranspose_reflection, reverseTranspose_diagonal,
        diagonal_reflection]
    rw [map_mul, map_mul, antiAlgebra_projector, antiAlgebra_basis, hfix, ← op_mul, ← op_mul,
      mul_assoc]

private lemma antiAlgebra_sandwich {χ : AddChar F ℂ} (hχ : χ ≠ 1) (r : ℂ[SL(2, F)]) :
    antiAlgebra (projector χ * r * projector χ) = op (projector χ * r * projector χ) := by
  induction r using MonoidAlgebra.induction_on with
  | of g => exact antiAlgebra_sandwich_basis hχ g
  | add a b ha hb =>
    simp only [mul_add, add_mul, map_add, ha, hb]
    rfl
  | smul c a ha => simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, map_smul, op_smul, ha]

private lemma sandwich_commute {χ : AddChar F ℂ} (hχ : χ ≠ 1) (a b : ℂ[SL(2, F)]) :
    Commute (projector χ * a * projector χ) (projector χ * b * projector χ) := by
  let e := projector χ
  have he : e * e = e := projector_idempotent χ
  have hmul : (e * a * e) * (e * b * e) = e * (a * e * b) * e := by
    simp only [mul_assoc, ← mul_assoc e e, he]
  change (e * a * e) * (e * b * e) = _
  apply MulOpposite.op_injective
  calc
    op ((e * a * e) * (e * b * e)) = antiAlgebra ((e * a * e) * (e * b * e)) := by
      rw [hmul]
      exact (antiAlgebra_sandwich hχ _).symm
    _ = op ((e * b * e) * (e * a * e)) := by
      rw [map_mul]
      exact congrArg₂ (· * ·) (antiAlgebra_sandwich hχ a) (antiAlgebra_sandwich hχ b)

end Projectors

section Ranks

open LinearMap Module MonoidAlgebra

variable [Fintype F] (V : FDRep ℂ SL(2, F))

private noncomputable abbrev rep : Representation ℂ SL(2, F) V := V.ρ

private noncomputable abbrev action := (rep V).asAlgebraHom

private noncomputable abbrev projection (χ : AddChar F ℂ) := action V (projector χ)

private lemma projection_idempotent (χ : AddChar F ℂ) :
    IsIdempotentElem (projection V χ) := by
  rw [IsIdempotentElem, ← map_mul, projector_idempotent χ]

private lemma projection_fixes {χ : AddChar F ℂ} {v : V}
    (hv : v ∈ LinearMap.range (projection V χ)) : projection V χ v = v :=
  (projection_idempotent V χ).isProj_range.map_id v hv

omit [CharP F 2] [Fintype F] in
private lemma exists_action_eq [Finite F] [Simple V] {v : V} (hv : v ≠ 0) (w : V) :
    ∃ a : ℂ[SL(2, F)], action V a v = w := by
  have : (rep V).IsIrreducible := BurnsidePaqb.irreducible_of_simple_fdrep _ V
  have : IsSimpleModule (ℂ[SL(2, F)]) (rep V).asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule (rep V)).mp inferInstance
  let e := (rep V).asModuleEquiv
  have hv' : e.symm v ≠ 0 := by simpa using hv
  obtain ⟨a, ha⟩ :=
    IsSimpleModule.toSpanSingleton_surjective (R := ℂ[SL(2, F)]) hv' (e.symm w)
  exact ⟨a, by simpa [e] using congrArg e ha⟩

private noncomputable def compressed (χ : AddChar F ℂ) (a : ℂ[SL(2, F)]) :
    Module.End ℂ (LinearMap.range (projection V χ)) :=
  ((projection V χ * action V a).domRestrict _).codRestrict _
    fun v ↦ ⟨action V a v, rfl⟩

private lemma compressed_commute {χ : AddChar F ℂ} (hχ : χ ≠ 1) (a b : ℂ[SL(2, F)]) :
    Commute (compressed V χ a) (compressed V χ b) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change projection V χ (action V a (projection V χ (action V b v))) =
    projection V χ (action V b (projection V χ (action V a v)))
  have h := congrArg (fun r ↦ action V r (v : V)) (sandwich_commute hχ a b).eq
  simpa only [map_mul, mul_apply_eq_comp, projection_fixes V v.property,
    projection_fixes V
      (show projection V χ (action V b (v : V)) ∈ LinearMap.range (projection V χ) from ⟨_, rfl⟩),
    projection_fixes V
      (show projection V χ (action V a (v : V)) ∈ LinearMap.range (projection V χ) from ⟨_, rfl⟩)]
    using h

private lemma exists_compressed_eq [Simple V] (χ : AddChar F ℂ)
    {v : LinearMap.range (projection V χ)} (hv : v ≠ 0)
    (w : LinearMap.range (projection V χ)) :
    ∃ a, compressed V χ a v = w := by
  obtain ⟨a, ha⟩ := exists_action_eq V (v := (v : V)) (by simpa using hv) w
  exact ⟨a, Subtype.ext (show projection V χ (action V a v) = w by
    rw [ha, projection_fixes V w.property])⟩

-- Every nonzero vector in the projection range is cyclic for the compressed operators.
private lemma nontrivial_projection_rank [Simple V] {χ : AddChar F ℂ} (hχ : χ ≠ 1) :
    finrank ℂ (LinearMap.range (projection V χ)) ≤ 1 := by
  let W := LinearMap.range (projection V χ)
  cases subsingleton_or_nontrivial W with
  | inl h =>
    have : Subsingleton W := h
    change finrank ℂ W ≤ _
    rw [finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | inr h =>
    have : Nontrivial W := h
    obtain ⟨v, hv⟩ := exists_ne (0 : W)
    apply finrank_le_one v
    intro w
    obtain ⟨a, ha⟩ := exists_compressed_eq V χ hv w
    obtain ⟨c, hc⟩ := (compressed V χ a).exists_eigenvalue
    obtain ⟨u, hu⟩ := hc.exists_hasEigenvector
    obtain ⟨b, hb⟩ := exists_compressed_eq V χ hu.2 v
    refine ⟨c, ?_⟩
    have hcomm := DFunLike.congr_fun (compressed_commute V hχ a b).eq u
    simpa only [mul_apply_eq_comp, hb, hu.apply_eq_smul, map_smul, ha] using hcomm.symm

omit [CharP F 2] in
private lemma trivial_projection_commute_diagonal (a : Fˣ) :
    Commute (groupBasis (diagonal a)) (projector (1 : AddChar F ℂ)) := by
  have ha : (a : F)^2 ≠ 0 := pow_ne_zero _ a.ne_zero
  change groupBasis (diagonal a) * projector (1 : AddChar F ℂ) =
    projector (1 : AddChar F ℂ) * groupBasis (diagonal a)
  simp only [projector, one_apply, one_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Finset.mul_sum, Finset.sum_mul, ← map_mul, diagonal_unipotent]
  exact congrArg ((Fintype.card F : ℂ)⁻¹ • ·) (by
    apply Fintype.sum_bijective _ (mulLeft_bijective₀ _ ha)
    intro x
    rfl)

-- Choose a diagonal eigenvector in the fixed space. The two Bruhat cells give
-- two vectors whose span contains its entire projected group orbit.
private lemma trivial_projection_rank [Simple V] :
    finrank ℂ (LinearMap.range (projection V (1 : AddChar F ℂ))) ≤ 2 := by
  classical
  let χ : AddChar F ℂ := 1
  let P := projection V χ
  let W := LinearMap.range P
  cases subsingleton_or_nontrivial W with
  | inl h =>
    have : Subsingleton W := h
    change finrank ℂ W ≤ _
    rw [finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  | inr h =>
    have : Nontrivial W := h
    obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
    let d := V.ρ.comp (diagonalHom : Fˣ →* SL(2, F))
    have hdcomm (b : Fˣ) : Commute (d b) P := by
      simpa [P, χ, d, diagonalHom] using
        (trivial_projection_commute_diagonal b).map (action V)
    obtain ⟨c, hc⟩ := (compressed V χ (groupBasis (diagonal a))).exists_eigenvalue
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hv' : (v : V) ≠ 0 := by simpa using hv.2
    have hpv : P v = v := projection_fixes V v.property
    have hda : d a (v : V) = c • (v : V) := by
      have hc' := congrArg (fun w : W ↦ (w : V)) hv.apply_eq_smul
      change P (action V (groupBasis (diagonal a)) v) = c • (v : V) at hc'
      have hc'' : P (d a v) = c • (v : V) := by simpa [d, diagonalHom] using hc'
      have hcom := DFunLike.congr_fun (hdcomm a).eq (v : V)
      simpa only [mul_apply_eq_comp, hpv, hc''] using hcom
    have hdb (b : Fˣ) : ∃ k : ℂ, d b (v : V) = k • (v : V) := by
      obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers).mpr (ha b)
      have heig : Module.End.HasEigenvector (d a) c (v : V) :=
        ⟨Module.End.mem_eigenspace_iff.mpr hda, hv'⟩
      exact ⟨c ^ n, by simpa only [map_pow] using heig.pow_apply n⟩
    have hu (x : F) : V.ρ (unipotent x) * P = P := by
      simpa [P, χ] using congrArg (action V) (basis_mul_projector χ x)
    have hup (x : F) : P * V.ρ (unipotent x) = P := by
      simpa [P, χ] using congrArg (action V) (projector_mul_basis χ x)
    have huv (x : F) : V.ρ (unipotent x) (v : V) = v := by
      simpa only [mul_apply_eq_comp, hpv] using DFunLike.congr_fun (hu x) (v : V)
    let z := P (V.ρ reflection (v : V))
    let S := Submodule.span ℂ ({(v : V), z} : Set V)
    have hvS : (v : V) ∈ S := Submodule.subset_span (Set.mem_insert _ _)
    have hzS : z ∈ S := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    have hs (g : SL(2, F)) : P (V.ρ g (v : V)) ∈ S := by
      rcases bruhat g with ⟨x, b, rfl⟩ | ⟨x, y, b, rfl⟩
      · obtain ⟨k, hk⟩ := hdb b
        simp only [map_mul, ← mul_apply_eq_comp, ← mul_assoc, hup]
        change P (d b v) ∈ S
        rw [hk, map_smul, hpv]
        exact S.smul_mem k hvS
      · obtain ⟨k, hk⟩ := hdb b⁻¹
        rw [diagonal_reflection]
        simp only [map_mul, mul_apply_eq_comp, huv]
        change P (V.ρ (unipotent x) (V.ρ reflection (d b⁻¹ v))) ∈ S
        rw [← mul_apply_eq_comp, hup, hk, map_smul, map_smul]
        exact S.smul_mem k hzS
    have hw : W ≤ S := by
      intro w hmem
      obtain ⟨r, hr⟩ := exists_action_eq V hv' w
      have hpw := projection_fixes V hmem
      rw [← hpw, ← hr]
      clear hr
      induction r using MonoidAlgebra.induction_on with
      | of g => simpa using hs g
      | add a b ha hb => simpa only [map_add, LinearMap.add_apply] using S.add_mem ha hb
      | smul k a ha => simpa only [map_smul, LinearMap.smul_apply] using S.smul_mem k ha
    calc
      finrank ℂ W ≤ finrank ℂ S := Submodule.finrank_mono hw
      _ ≤ 2 := (finrank_span_le_card _).trans (by
        simpa [Set.toFinset_insert] using Finset.card_insert_le (v : V) {z})

end Ranks

open LinearMap Module MonoidAlgebra

variable [Fintype F]

omit [Fintype F] in
private lemma char_unipotent [Finite F] (V : FDRep ℂ SL(2, F)) {x : F} (hx : x ≠ 0) :
    V.character (unipotent x) = V.character (unipotent (1 : F)) := by
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' x
  have ha' : a ≠ 0 := fun h ↦ hx (by simp [ha, h])
  let b := Units.mk0 a ha'
  have he : diagonal b * unipotent 1 * (diagonal b)⁻¹ = unipotent x := by
    rw [diagonal_unipotent, mul_inv_cancel_right, mul_one, sq]
    exact congrArg unipotent ha.symm
  rw [← he, V.char_conj]

omit [CharP F 2] in
private lemma trace_projection (V : FDRep ℂ SL(2, F)) (χ : AddChar F ℂ) :
    trace ℂ V (projection V χ) =
      (Fintype.card F : ℂ)⁻¹ * ∑ x : F, χ x * V.character (unipotent x) := by
  change trace ℂ V (action V (projector χ)) = _
  rw [projector]
  simp only [map_smul, map_sum, Representation.asAlgebraHom_of, smul_eq_mul]
  rfl

-- The contribution at zero cancels, and all nonzero unipotent elements are conjugate.
private lemma char_sub_projection_traces (V : FDRep ℂ SL(2, F))
    {χ : AddChar F ℂ} (hχ : χ ≠ 1) :
    V.character (unipotent (1 : F)) =
      trace ℂ V (projection V 1) - trace ℂ V (projection V χ) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [trace_projection, trace_projection, ← mul_sub, ← Finset.sum_sub_distrib]
  symm
  calc
    _ = (Fintype.card F : ℂ)⁻¹ *
        ∑ x : F, (1 - χ x) * V.character (unipotent (1 : F)) := by
      apply congrArg ((Fintype.card F : ℂ)⁻¹ * ·)
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hx : x = 0
      · simp [hx]
      · simp [char_unipotent V hx, sub_mul]
    _ = V.character (unipotent (1 : F)) := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, AddChar.sum_eq_zero_of_ne_one hχ]
      simp [hq]

omit [CharP F 2] [Fintype F] in
private noncomputable def possibleValues : Finset ℂ :=
  Finset.univ.image (fun p : Fin 3 × Fin 2 ↦ (p.1.val : ℂ) - p.2.val)

omit [Fintype F] in
private lemma char_mem_possibleValues [Finite F] (V : FDRep ℂ SL(2, F)) [Simple V] :
    V.character (unipotent (1 : F)) ∈ possibleValues := by
  let _ := Fintype.ofFinite F
  obtain ⟨χ, hχ₁⟩ := AddChar.exists_apply_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)
  have hχ : χ ≠ 1 := AddChar.ne_one_iff.mpr ⟨1, hχ₁⟩
  have h0 := trivial_projection_rank V
  have h1 := nontrivial_projection_rank V (χ := χ) hχ
  refine Finset.mem_image.mpr ⟨(⟨_, Nat.lt_succ_of_le h0⟩, ⟨_, Nat.lt_succ_of_le h1⟩),
    Finset.mem_univ _, ?_⟩
  rw [char_sub_projection_traces V (χ := χ) hχ, (projection_idempotent V 1).isProj_range.trace,
    (projection_idempotent V χ).isProj_range.trace]

/--
**Kourovka Problem 11.97 has a negative answer.** There is a finite set $S$ of complex numbers
such that for every natural number $N$ there is a finite non-abelian simple group $G$ with more
than $N$ elements and an element $g \in G$ at which the set of values of the irreducible complex
characters of $G$ is exactly $S$.

The Kourovka Archive records (V. D. Mazurov) that every complex irreducible character of
$L_2(2^m)$, $m \ge 2$, takes a value in $\{0, 1, -1\}$ at an involution, so some subset of
$\{0, 1, -1\}$ is the set of values at an involution for infinitely many of these non-abelian
simple groups.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.97
(S. P. Strunkov); resolution: V. D. Mazurov, Kourovka Archive, Problem 11.97: "No; all complex
irreducible characters of the groups `L_2(2^m)`, `m ≥ 2`, take the values `0, ±1` on involutions",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem finitelyManySimpleGivenCharacterValues_refuted :
    ¬ finitelyManySimpleGivenCharacterValues := by
  classical
  intro h
  -- Take one maximum over the finitely many possible sets of character values.
  let N (s : Finset ℂ) : ℕ := (h (s : Set ℂ) s.finite_toSet).choose
  let M := possibleValues.powerset.sup N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (M + 2)
  have hK : Nat.card K = 2 ^ (M + 2) := GaloisField.card _ _ (by omega)
  have hK₄ : 4 ≤ Nat.card K := by
    rw [hK]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left 2 M)
  have hsimple : IsSimpleGroup SL(2, K) :=
    toSL.isSimpleGroup_congr.mp (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hK₄)
  let S := irrCharValues (unipotent (1 : K))
  have hsubset : S ⊆ (possibleValues : Set ℂ) := by
    rintro _ ⟨V, hV, rfl⟩
    exact char_mem_possibleValues V
  let fS := possibleValues.finite_toSet.subset hsubset
  let s := fS.toFinset
  have hS : (s : Set ℂ) = S := fS.coe_toFinset
  have hs : s ∈ possibleValues.powerset := by
    rw [Finset.mem_powerset, ← Finset.coe_subset, hS]
    exact hsubset
  have hbound : Nat.card SL(2, K) ≤ N s :=
    (h (s : Set ℂ) s.finite_toSet).choose_spec SL(2, K) hsimple not_commutative
      ⟨unipotent 1, hS.symm⟩
  have hle : Nat.card K ≤ M :=
    (Nat.card_le_card_of_injective _ unipotent_injective).trans
      (hbound.trans (Finset.le_sup hs))
  have hlt : M < Nat.card K := by
    rw [hK]
    exact (show M < 2 ^ M from Nat.lt_two_pow_self).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right M 2))
  exact (not_lt_of_ge hle) hlt

end MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97Wanted
