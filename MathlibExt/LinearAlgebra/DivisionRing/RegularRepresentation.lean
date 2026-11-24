/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.DivisionRing.RankDivisibility
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Regular matrices from actual right subfield actions

The subfield acts on a division algebra by right multiplication. Left matrices
preserve both this action and the native right opposite-algebra action. Actual
subfield coordinates give matrices over the subfield, with the opposite action
transported through the common base field rather than assumed subfield-linear.

Reference: Ivanyos, Qiao and Subrahmanyam, *Constructive noncommutative rank
computation in deterministic polynomial time over fields of arbitrary
characteristics*, 20 January 2016 addendum, Claim 11. Cyclic division algebra
construction, source splitting/density, regularity and computational bounds
remain separate.
-/

@[expose] public section

noncomputable section

universe uF uL uD uN uK

open scoped BigOperators
open Module

section RightAction

variable {L : Type uL} [CommSemiring L] {D : Type uD} [Semiring D]

namespace RingHom

private theorem commute_range (ι : L →+* D) (x y : L) : Commute (ι x) (ι y) := by
  change ι x * ι y = ι y * ι x
  rw [← map_mul, ← map_mul, mul_comm]

/-- The named right subfield module, using the native opposite-module action. -/
@[instance_reducible] def rightModule (ι : L →+* D) : Module L D :=
  Module.compHom D (ι.toOpposite (by exact commute_range ι))

/-- The chosen subfield action is actual multiplication on the right. -/
@[simp] theorem rightModule_smul (ι : L →+* D) (a : L) (x : D) :
    letI := ι.rightModule
    a • x = x * ι a := rfl

end RingHom

namespace Matrix

variable {n : Type uN} [Fintype n] [DecidableEq n]

/-- Actual left matrices act linearly on the chosen right subfield module. -/
def leftRegular (ι : L →+* D) :
    letI := ι.rightModule
    Matrix n n D →+* Module.End L (n → D) := by
  let φ : L →+* Dᵐᵒᵖ := ι.toOpposite (by exact RingHom.commute_range ι)
  letI : Module L Dᵐᵒᵖ := Module.compHom Dᵐᵒᵖ φ
  letI := ι.rightModule
  letI : IsScalarTower L Dᵐᵒᵖ D := ⟨fun l a x => by
    change x * (MulOpposite.unop a * ι l) = (x * MulOpposite.unop a) * ι l
    exact (mul_assoc _ _ _).symm⟩
  let e : Matrix n n D ≃+* Module.End Dᵐᵒᵖ (n → D) :=
    (RingEquiv.moduleEndSelfOp D).mapMatrix.trans
      (endVecRingEquivMatrixEnd n Dᵐᵒᵖ D).symm
  exact
    { toFun := fun A => (e A).restrictScalars L
      map_one' := by
        apply LinearMap.ext
        intro x
        change (e 1) x = x
        rw [map_one]
        rfl
      map_mul' := fun A B => by
        apply LinearMap.ext
        intro x
        change (e (A * B)) x = (e A) ((e B) x)
        rw [map_mul]
        rfl
      map_zero' := by
        apply LinearMap.ext
        intro x
        change (e 0) x = 0
        rw [map_zero]
        rfl
      map_add' := fun A B => by
        apply LinearMap.ext
        intro x
        change (e (A + B)) x = (e A) x + (e B) x
        rw [map_add]
        rfl }

/-- The regular action is the literal left matrix-vector product over the original algebra. -/
@[simp] theorem leftRegular_apply (ι : L →+* D) (A : Matrix n n D) (x : n → D) :
    letI := ι.rightModule
    leftRegular ι A x = A *ᵥ x := rfl

/-- Actual left matrices also preserve the native right opposite-algebra action. -/
theorem leftRegular_smul_op (ι : L →+* D) (A : Matrix n n D) (a : Dᵐᵒᵖ) (x : n → D) :
    letI := ι.rightModule
    leftRegular ι A (a • x) = a • leftRegular ι A x := by
  simp only [leftRegular_apply]
  exact A.mulVec_smul a x

/-- The actual regular action is faithful, including an empty matrix index type. -/
theorem leftRegular_injective (ι : L →+* D) :
    letI := ι.rightModule
    Function.Injective (leftRegular (n := n) ι) := by
  intro A B h
  apply Matrix.mulVec_injective
  funext x
  simpa only [leftRegular_apply] using congrArg (fun f => f x) h

end Matrix

end RightAction

section Coordinates

variable {L : Type uL} [CommSemiring L] {D : Type uD} [Semiring D]
variable {κ : Type uK} [Fintype κ]

namespace RingHom

/-- Actual finite right-subfield basis coordinates on tuples of algebra elements. -/
def rightCoordinates (ι : L →+* D) (b : letI := ι.rightModule; Basis κ L D)
    (n : Type uN) :
    letI := ι.rightModule
    (n → D) ≃ₗ[L] (n × κ → L) := by
  letI := ι.rightModule
  exact (LinearEquiv.piCongrRight fun _ : n => b.equivFun).trans
    (LinearEquiv.curry L L n κ).symm

/-- Every coordinate is the genuine coordinate of the corresponding tuple entry. -/
@[simp] theorem rightCoordinates_apply (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (n : Type uN) (x : n → D) (p : n × κ) :
    letI := ι.rightModule
    ι.rightCoordinates b n x p = b.equivFun (x p.1) p.2 := rfl

/-- Transport the native opposite action across the actual basis-coordinate equivalence. -/
@[instance_reducible] def rightCoordinateModule (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (n : Type uN) : Module Dᵐᵒᵖ (n × κ → L) := by
  letI := ι.rightModule
  exact (ι.rightCoordinates b n).symm.toAddEquiv.module Dᵐᵒᵖ

/-- The coordinate opposite action is the actual transported right multiplication. -/
theorem rightCoordinateModule_smul (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (n : Type uN) (a : Dᵐᵒᵖ) (x : n × κ → L) :
    letI := ι.rightModule
    letI := ι.rightCoordinateModule b n
    a • x = ι.rightCoordinates b n (a • (ι.rightCoordinates b n).symm x) := rfl

end RingHom

namespace Matrix

variable {n : Type uN} [Fintype n] [DecidableEq n] [DecidableEq κ]

/-- The actual coordinate matrix ring representation with a specified genuine right-subfield basis. -/
def regularRepresentationWithBasis (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) :
    Matrix n n D →+* Matrix (n × κ) (n × κ) L := by
  letI := ι.rightModule
  exact (LinearMap.toMatrixAlgEquiv' (R := L) (n := n × κ)).toRingHom.comp
    ((ι.rightCoordinates b n).conjRingEquiv.toRingHom.comp (leftRegular ι))

/-- The coordinate matrix acts by taking an actual preimage, applying the left matrix, and reading
the actual basis coordinates back. -/
theorem regularRepresentationWithBasis_mulVec (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (A : Matrix n n D) (x : n × κ → L) :
    letI := ι.rightModule
    regularRepresentationWithBasis ι b A *ᵥ x =
      ι.rightCoordinates b n (A *ᵥ (ι.rightCoordinates b n).symm x) := by
  let := ι.rightModule
  change LinearMap.toMatrixAlgEquiv'
    ((ι.rightCoordinates b n).conjRingEquiv (leftRegular ι A)) *ᵥ x = _
  rw [← Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  rfl

/-- Each actual matrix entry is the actual basis coordinate of left multiplication. -/
theorem regularRepresentationWithBasis_apply (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (A : Matrix n n D) (p q : n × κ) :
    letI := ι.rightModule
    regularRepresentationWithBasis ι b A p q = b.equivFun (A p.1 q.1 * b q.2) p.2 := by
  let := ι.rightModule
  let e := ι.rightCoordinates b n
  have hsingle (j : n) (l : κ) : e.symm (Pi.single (j, l) 1) = Pi.single j (b l) := by
    apply e.injective
    funext r
    rw [LinearEquiv.apply_symm_apply]
    rcases r with ⟨i, k⟩
    by_cases h : i = j
    · subst i
      simp [e, RingHom.rightCoordinates_apply, Pi.single_apply, Basis.equivFun_self, eq_comm]
    · simp [e, RingHom.rightCoordinates_apply, h]
  change LinearMap.toMatrixAlgEquiv' (e.conjRingEquiv (leftRegular ι A)) p q = _
  rw [LinearMap.toMatrixAlgEquiv'_apply]
  change e (A *ᵥ e.symm (Pi.single q 1)) p = _
  rw [hsingle q.1 q.2, RingHom.rightCoordinates_apply, Matrix.mulVec_single]
  rfl

/-- This matrix representation is faithful, including empty matrix indices. -/
theorem regularRepresentationWithBasis_injective (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) :
    Function.Injective (regularRepresentationWithBasis (n := n) ι b) := by
  let := ι.rightModule
  exact (LinearMap.toMatrixAlgEquiv' (R := L) (n := n × κ)).injective.comp
    ((ι.rightCoordinates b n).conjRingEquiv.injective.comp (leftRegular_injective ι))

/-- The actual coordinate matrices preserve the transported opposite action. -/
theorem regularRepresentationWithBasis_smul_op (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (A : Matrix n n D) (a : Dᵐᵒᵖ)
    (x : n × κ → L) :
    letI := ι.rightModule
    letI := ι.rightCoordinateModule b n
    regularRepresentationWithBasis ι b A *ᵥ (a • x) =
      a • (regularRepresentationWithBasis ι b A *ᵥ x) := by
  let := ι.rightModule
  let := ι.rightCoordinateModule b n
  rw [RingHom.rightCoordinateModule_smul, RingHom.rightCoordinateModule_smul,
    regularRepresentationWithBasis_mulVec, regularRepresentationWithBasis_mulVec]
  simp only [LinearEquiv.symm_apply_apply]
  exact congrArg (ι.rightCoordinates b n)
    (A.mulVec_smul a ((ι.rightCoordinates b n).symm x))

end Matrix

end Coordinates

section CommonBase

variable {F : Type uF} [CommSemiring F] {L : Type uL} [CommSemiring L]
  {D : Type uD} [Semiring D] [Algebra F L] [Algebra F D]

namespace AlgHom

/-- A base-compatible embedding makes the right subfield action extend the same base action. -/
theorem rightModule_isScalarTower (ι : L →ₐ[F] D) :
    letI := ι.toRingHom.rightModule
    IsScalarTower F L D := by
  let := ι.toRingHom.rightModule
  constructor
  intro r l x
  change x * ι (r • l) = r • (x * ι l)
  rw [map_smul, mul_smul_comm]

/-- The transported opposite action on coordinates extends the common base field action.
It is not assumed linear over the embedded subfield. -/
theorem rightCoordinateModule_isScalarTower (ι : L →ₐ[F] D)
    {κ : Type uK} [Fintype κ]
    (b : letI := ι.toRingHom.rightModule; Basis κ L D) (n : Type uN) :
    letI := ι.toRingHom.rightCoordinateModule b n
    IsScalarTower F Dᵐᵒᵖ (n × κ → L) := by
  let := ι.toRingHom.rightModule
  let : IsScalarTower F L D := ι.rightModule_isScalarTower
  exact ((ι.toRingHom.rightCoordinates b n).symm.restrictScalars F).isScalarTower Dᵐᵒᵖ

end AlgHom

end CommonBase

section Rank

variable {F : Type uF} [Field F] {L : Type uL} [Field L]
  {D : Type uD} [DivisionRing D] [Algebra F L] [Algebra F D]
variable {n : Type uN} [Fintype n] [DecidableEq n]
variable {κ : Type uK} [Fintype κ] [DecidableEq κ]

namespace Matrix

/-- Actual coordinates of left matrices over the division algebra have subfield rank divisible by
`d`, when the two scalar dimensions over the common base field are `d` and `d²`. -/
theorem dvd_rank_regularRepresentationWithBasis (ι : L →ₐ[F] D)
    (b : letI := ι.toRingHom.rightModule; Basis κ L D) (A : Matrix n n D)
    {d : ℕ} (hd : 0 < d) (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2) :
    d ∣ (regularRepresentationWithBasis ι.toRingHom b A).rank := by
  let := ι.toRingHom.rightModule
  let : FiniteDimensional F L := FiniteDimensional.of_finrank_pos (by rw [hL]; exact hd)
  let := ι.toRingHom.rightCoordinateModule b n
  let : IsScalarTower F Dᵐᵒᵖ (n × κ → L) := ι.rightCoordinateModule_isScalarTower b n
  have hop : Module.finrank F Dᵐᵒᵖ = d ^ 2 := by
    rw [← (MulOpposite.opLinearEquiv F : D ≃ₗ[F] Dᵐᵒᵖ).finrank_eq]
    exact hD
  exact Matrix.dvd_rank_of_divisionRing_action F Dᵐᵒᵖ
    (regularRepresentationWithBasis ι.toRingHom b A)
    (regularRepresentationWithBasis_smul_op ι.toRingHom b A) hd hL hop

end Matrix

end Rank

section ConstructedBasis

variable {F : Type uF} [Field F] {L : Type uL} [Field L]
  {D : Type uD} [DivisionRing D] [Algebra F L] [Algebra F D]

namespace AlgHom

/-- Construct the actual degree-`d` right-subfield basis from the two base-field dimensions. -/
def rightSubfieldBasis (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2) :
    letI := ι.toRingHom.rightModule
    Basis (Fin d) L D := by
  letI := ι.toRingHom.rightModule
  letI : IsScalarTower F L D := ι.rightModule_isScalarTower
  letI : FiniteDimensional F L := FiniteDimensional.of_finrank_pos (by rw [hL]; exact hd)
  letI : FiniteDimensional F D := FiniteDimensional.of_finrank_pos (by
    rw [hD]
    exact pow_pos hd 2)
  letI : FiniteDimensional L D := Module.Finite.of_restrictScalars_finite F L D
  have hdim := Module.finrank_mul_finrank F L D
  rw [hL, hD, pow_two] at hdim
  have hright : Module.finrank L D = d := Nat.eq_of_mul_eq_mul_left hd hdim
  exact (Module.finBasis L D).reindex (finCongr hright)

end AlgHom

namespace Matrix

variable {n : Type uN} [Fintype n] [DecidableEq n]

/-- The actual regular matrix representation with its right-subfield basis constructed from the
given scalar dimensions, rather than supplied as an additional input. -/
def regularRepresentation (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2) :
    Matrix n n D →+* Matrix (n × Fin d) (n × Fin d) L :=
  regularRepresentationWithBasis ι.toRingHom (ι.rightSubfieldBasis hd hL hD)

/-- The actual dimension-based regular representation is faithful. -/
theorem regularRepresentation_injective (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2) :
    Function.Injective (regularRepresentation (n := n) ι hd hL hD) :=
  regularRepresentationWithBasis_injective ι.toRingHom (ι.rightSubfieldBasis hd hL hD)

/-- The constructed regular representation has genuine subfield rank divisible by its degree. -/
theorem dvd_rank_regularRepresentation (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2)
    (A : Matrix n n D) : d ∣ (regularRepresentation ι hd hL hD A).rank :=
  dvd_rank_regularRepresentationWithBasis ι (ι.rightSubfieldBasis hd hL hD) A hd hL hD

end Matrix

end ConstructedBasis
