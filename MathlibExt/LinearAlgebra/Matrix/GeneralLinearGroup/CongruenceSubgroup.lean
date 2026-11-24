/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import MathlibExt.RingTheory.TwoSidedIdeal.Quasiregular
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Congruence subgroups of finite general linear groups

For a two-sided ideal `I` of a ring `R`, the finite-rank congruence subgroup
is the kernel of the coefficient map

`GL n R → GL n (R ⨸ I.ringCon)`.

Membership is equivalently entrywise congruence to the identity matrix.  If
`I` is quasiregular, the quotient map on `GL` is surjective.  The lifting proof
uses both products of chosen lifts of a quotient unit and its inverse; it does
not assume commutativity or stable finiteness.

No stable relative general linear group or relative `K₁` is defined here.
-/

@[expose] public section

open Function

universe u v w

namespace Matrix.GeneralLinearGroup

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {R : Type v} [Ring R]

/-- The finite-rank congruence subgroup modulo a two-sided ideal. -/
def congruenceSubgroup (I : TwoSidedIdeal R) : Subgroup (GL n R) :=
  (mapRingHom (n := n) I.ringCon.mk').ker

/-- Membership in the congruence subgroup means that reduction modulo the
ideal is the identity. -/
@[simp]
theorem mem_congruenceSubgroup_iff (I : TwoSidedIdeal R) (g : GL n R) :
    g ∈ congruenceSubgroup (n := n) I ↔
      mapRingHom I.ringCon.mk' g = 1 :=
  MonoidHom.mem_ker

/-- Entrywise characterization of congruence-subgroup membership. -/
theorem mem_congruenceSubgroup_iff_entries (I : TwoSidedIdeal R) (g : GL n R) :
    g ∈ congruenceSubgroup (n := n) I ↔
      ∀ i j, (g : Matrix n n R) i j - (1 : Matrix n n R) i j ∈ I := by
  constructor
  · intro hg i j
    have hg' := (mem_congruenceSubgroup_iff I g).mp hg
    have hmat :
        (g : Matrix n n R).map I.ringCon.mk' =
          (1 : Matrix n n R).map I.ringCon.mk' := by
      calc
        (g : Matrix n n R).map I.ringCon.mk' =
            (↑(mapRingHom I.ringCon.mk' g) : Matrix n n I.ringCon.Quotient) :=
          (coe_mapRingHom I.ringCon.mk' g).symm
        _ = ↑(1 : GL n I.ringCon.Quotient) := congrArg Units.val hg'
        _ = 1 := rfl
        _ = (1 : Matrix n n R).map I.ringCon.mk' :=
          I.ringCon.mk'.mapMatrix.map_one.symm
    have hij := congr_fun (congr_fun hmat i) j
    exact (I.rel_iff _ _).mp (Quotient.eq'.mp hij)
  · intro hg
    have hmat :
        (g : Matrix n n R).map I.ringCon.mk' =
          (1 : Matrix n n R).map I.ringCon.mk' := by
      ext i j
      exact Quotient.sound' ((I.rel_iff _ _).mpr (hg i j))
    apply (mem_congruenceSubgroup_iff I g).mpr
    apply Units.ext
    calc
      (↑(mapRingHom I.ringCon.mk' g) : Matrix n n I.ringCon.Quotient) =
          (g : Matrix n n R).map I.ringCon.mk' :=
        coe_mapRingHom I.ringCon.mk' g
      _ = (1 : Matrix n n R).map I.ringCon.mk' := hmat
      _ = 1 := I.ringCon.mk'.mapMatrix.map_one
      _ = ↑(1 : GL n I.ringCon.Quotient) := rfl

/-- Congruence subgroups are monotone in the two-sided ideal. -/
theorem congruenceSubgroup_mono {I J : TwoSidedIdeal R} (hIJ : I ≤ J) :
    congruenceSubgroup (n := n) I ≤ congruenceSubgroup (n := n) J := by
  intro g hg
  apply (mem_congruenceSubgroup_iff_entries J g).mpr
  intro i j
  exact hIJ ((mem_congruenceSubgroup_iff_entries I g).mp hg i j)

/-- The congruence subgroup modulo the zero ideal is trivial. -/
@[simp]
theorem congruenceSubgroup_bot :
    congruenceSubgroup (n := n) (⊥ : TwoSidedIdeal R) = ⊥ := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_bot]
    apply Units.ext
    ext i j
    exact sub_eq_zero.mp
      ((TwoSidedIdeal.mem_bot R).mp
        ((mem_congruenceSubgroup_iff_entries (⊥ : TwoSidedIdeal R) g).mp hg i j))
  · exact bot_le

/-- The congruence subgroup modulo the unit ideal is the whole general linear
group. -/
@[simp]
theorem congruenceSubgroup_top :
    congruenceSubgroup (n := n) (⊤ : TwoSidedIdeal R) = ⊤ := by
  apply top_unique
  intro g _
  apply (mem_congruenceSubgroup_iff_entries (⊤ : TwoSidedIdeal R) g).mpr
  intro i j
  exact TwoSidedIdeal.mem_top _

/-- A coefficient map carries the congruence subgroup modulo `I` into that
modulo `J` whenever it carries `I` into `J`. -/
theorem mapRingHom_mem_congruenceSubgroup
    {S : Type w} [Ring S] (f : R →+* S)
    {I : TwoSidedIdeal R} {J : TwoSidedIdeal S}
    (hIJ : I ≤ J.comap f) {g : GL n R}
    (hg : g ∈ congruenceSubgroup (n := n) I) :
    mapRingHom f g ∈ congruenceSubgroup (n := n) J := by
  apply (mem_congruenceSubgroup_iff_entries J (mapRingHom f g)).mpr
  intro i j
  have hmem := hIJ ((mem_congruenceSubgroup_iff_entries I g).mp hg i j)
  rw [TwoSidedIdeal.mem_comap] at hmem
  have hone : f ((1 : Matrix n n R) i j) = (1 : Matrix n n S) i j :=
    congr_fun (congr_fun f.mapMatrix.map_one i) j
  simpa only [coe_mapRingHom, Matrix.map_apply, map_sub, hone] using hmem

private theorem mapMatrix_surjective {S : Type w} [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Function.Surjective (f.mapMatrix : Matrix n n R → Matrix n n S) := by
  classical
  intro A
  choose a ha using fun i j ↦ hf (A i j)
  refine ⟨fun i j ↦ a i j, ?_⟩
  ext i j
  exact ha i j

private theorem isUnit_of_mul_and_reverse_isUnit {M : Type*} [Monoid M]
    {a b : M} (hab : IsUnit (a * b)) (hba : IsUnit (b * a)) : IsUnit a := by
  let r : M := b * ↑hab.unit⁻¹
  let l : M := ↑hba.unit⁻¹ * b
  have har : a * r = 1 := by
    dsimp [r]
    rw [← mul_assoc, hab.mul_val_inv]
  have hla : l * a = 1 := by
    dsimp [l]
    rw [mul_assoc, hba.val_inv_mul]
  have hlr : l = r := by
    calc
      l = l * 1 := (mul_one l).symm
      _ = l * (a * r) := by rw [har]
      _ = (l * a) * r := (mul_assoc l a r).symm
      _ = r := by rw [hla, one_mul]
  exact ⟨⟨a, r, har, by rw [← hlr]; exact hla⟩, rfl⟩

private theorem sub_one_mem_matrix_of_map_eq_one
    (I : TwoSidedIdeal R) (A : Matrix n n R)
    (hA : I.ringCon.mk'.mapMatrix A = 1) :
    A - 1 ∈ I.matrix n := by
  change ∀ i j, A i j - (1 : Matrix n n R) i j ∈ I
  have hA' :
      I.ringCon.mk'.mapMatrix A =
        I.ringCon.mk'.mapMatrix (1 : Matrix n n R) := by
    exact hA.trans I.ringCon.mk'.mapMatrix.map_one.symm
  intro i j
  apply (I.rel_iff _ _).mp
  apply Quotient.eq'.mp
  exact congr_fun (congr_fun hA' i) j

/-- If `I` is quasiregular, every invertible matrix over `R/I` lifts to an
invertible matrix over `R`. -/
theorem mapRingHom_quotient_surjective (I : TwoSidedIdeal R)
    (hI : I.IsQuasiregular) :
    Function.Surjective (mapRingHom (n := n) I.ringCon.mk') := by
  classical
  intro g
  obtain ⟨A, hA⟩ := mapMatrix_surjective (n := n) I.ringCon.mk'
    I.ringCon.mk'_surjective (g : Matrix n n I.ringCon.Quotient)
  obtain ⟨B, hB⟩ := mapMatrix_surjective (n := n) I.ringCon.mk'
    I.ringCon.mk'_surjective (↑(g⁻¹) : Matrix n n I.ringCon.Quotient)
  have hABmap : I.ringCon.mk'.mapMatrix (A * B) = 1 := by
    rw [map_mul, hA, hB]
    exact congrArg Units.val (mul_inv_cancel g)
  have hBAmap : I.ringCon.mk'.mapMatrix (B * A) = 1 := by
    rw [map_mul, hA, hB]
    exact congrArg Units.val (inv_mul_cancel g)
  have hABerr : A * B - 1 ∈ I.matrix n :=
    sub_one_mem_matrix_of_map_eq_one I (A * B) hABmap
  have hBAerr : B * A - 1 ∈ I.matrix n :=
    sub_one_mem_matrix_of_map_eq_one I (B * A) hBAmap
  have hABunit₀ : IsUnit (1 + (A * B - 1)) :=
    (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add.mp
      (hI.matrix n)) _ hABerr
  have hBAunit₀ : IsUnit (1 + (B * A - 1)) :=
    (TwoSidedIdeal.isQuasiregular_iff_forall_isUnit_one_add.mp
      (hI.matrix n)) _ hBAerr
  have hABeq : 1 + (A * B - 1) = A * B := by abel
  have hBAeq : 1 + (B * A - 1) = B * A := by abel
  have hABunit : IsUnit (A * B) := hABeq ▸ hABunit₀
  have hBAunit : IsUnit (B * A) := hBAeq ▸ hBAunit₀
  have hAunit : IsUnit A := isUnit_of_mul_and_reverse_isUnit hABunit hBAunit
  refine ⟨hAunit.unit, ?_⟩
  apply Units.ext
  change I.ringCon.mk'.mapMatrix
      (↑hAunit.unit : Matrix n n R) = (g : Matrix n n I.ringCon.Quotient)
  rw [hAunit.unit_spec]
  exact hA

end Matrix.GeneralLinearGroup

end
