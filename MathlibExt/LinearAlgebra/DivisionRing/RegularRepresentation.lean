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
# Regular matrices from right coefficient actions

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
With a finite right-L basis b of D, coordinates turn left matrix action into a faithful
representation M_n(D)→M_(n×κ)(L). The opposite D-action transports to the coordinate module. Compatible actions over a common
central base support the dimension and rank comparisons. If F,L are fields, D a division
F-algebra, ι is F-linear, d>0, [L:F]=d and [D:F]=d², these matrices have rank divisible by d.

Reference: Ivanyos, Qiao and Subrahmanyam, Constructive noncommutative rank computation in
deterministic polynomial time over fields of arbitrary characteristics, 20 January 2016
addendum, Claim 11.
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

/-- **Right coefficient scalar module.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
The L-module rightModule ι on D is a•x=xι(a).
-/
@[instance_reducible] def rightModule (ι : L →+* D) : Module L D :=
  Module.compHom D (ι.toOpposite (by exact commute_range ι))

/-- **Value of the right coefficient scalar action.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
For a∈L,x∈D, the action of rightModule ι is a•x=x*ι(a).
-/
@[simp] theorem rightModule_smul (ι : L →+* D) (a : L) (x : D) :
    letI := ι.rightModule
    a • x = x * ι a := rfl

end RingHom

namespace Matrix

variable {n : Type uN} [Fintype n] [DecidableEq n]

/-- **Left matrix regular representation over right scalars.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
The ring homomorphism leftRegular ι:M_n(D)→End_L(D^n) sends A to x↦A*x.
-/
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

/-- **Value of left regular matrix multiplication.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
For A∈M_n(D),x∈D^n, leftRegular ι A x=A.mulVec x.
-/
@[simp] theorem leftRegular_apply (ι : L →+* D) (A : Matrix n n D) (x : n → D) :
    letI := ι.rightModule
    leftRegular ι A x = A *ᵥ x := rfl

/-- **Left matrix action preserves right multiplication by D.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
For t∈Dᵒᵖ and x∈D^n, leftRegular(A)(x*unop(t))=leftRegular(A)(x)*unop(t), coordinatewise.
-/
theorem leftRegular_smul_op (ι : L →+* D) (A : Matrix n n D) (a : Dᵐᵒᵖ) (x : n → D) :
    letI := ι.rightModule
    leftRegular ι A (a • x) = a • leftRegular ι A x := by
  simp only [leftRegular_apply]
  exact A.mulVec_smul a x

/-- **Faithfulness of the left regular matrix action.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
The map leftRegular ι is injective, including an empty finite matrix index.
-/
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

/-- **Right-basis coordinates of tuples.**

Let L be a commutative semiring,D a semiring,ι:L→D, with right action xι(a), and b:κ→D a
finite L-basis. Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. The equivalence rightCoordinates ι b n is C_b.
-/
def rightCoordinates (ι : L →+* D) (b : letI := ι.rightModule; Basis κ L D)
    (n : Type uN) :
    letI := ι.rightModule
    (n → D) ≃ₗ[L] (n × κ → L) := by
  letI := ι.rightModule
  exact (LinearEquiv.piCongrRight fun _ : n => b.equivFun).trans
    (LinearEquiv.curry L L n κ).symm

/-- **Coordinate value of a right-basis tuple.**

Let L be a commutative semiring,D a semiring,ι:L→D a coefficient homomorphism and b a finite
basis of the right L-action xι(a); let n be any tuple index. Then rightCoordinates ι b n x
(i,a)=b.repr(x_i)_a.
-/
@[simp] theorem rightCoordinates_apply (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (n : Type uN) (x : n → D) (p : n × κ) :
    letI := ι.rightModule
    ι.rightCoordinates b n x p = b.equivFun (x p.1) p.2 := rfl

/-- **Right opposite action transported into basis coordinates.**

Let L be a commutative semiring,D a semiring and b a finite basis of D under right L-action
through ι:L→D. Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. This action is rightCoordinateModule ι b n.
-/
@[instance_reducible] def rightCoordinateModule (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (n : Type uN) : Module Dᵐᵒᵖ (n × κ → L) := by
  letI := ι.rightModule
  exact (ι.rightCoordinates b n).symm.toAddEquiv.module Dᵐᵒᵖ

/-- **Value of the coordinate right opposite action.**

Let L be a commutative semiring,D a semiring,ι:L→D and b a finite right-L basis. Let b:κ→D be
a finite basis for this right L-module. For any tuple index n, C_b:D^n≃ₗ[L]L^(n×κ) has
C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is t•z=C_b(C_b⁻¹(z)*unop(t)) for
t∈Dᵒᵖ. For t∈Dᵒᵖ,z∈L^(n×κ), t•z=C_b(t•C_b⁻¹(z)).
-/
theorem rightCoordinateModule_smul (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) (n : Type uN) (a : Dᵐᵒᵖ) (x : n × κ → L) :
    letI := ι.rightModule
    letI := ι.rightCoordinateModule b n
    a • x = ι.rightCoordinates b n (a • (ι.rightCoordinates b n).symm x) := rfl

end RingHom

namespace Matrix

variable {n : Type uN} [Fintype n] [DecidableEq n] [DecidableEq κ]

/-- **Faithful matrix representation in right-basis coordinates.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. The ring homomorphism regularRepresentationWithBasis ι b
sends A to the matrix of C_b∘leftRegular(A)∘C_b⁻¹.
-/
def regularRepresentationWithBasis (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) :
    Matrix n n D →+* Matrix (n × κ) (n × κ) L := by
  letI := ι.rightModule
  exact (LinearMap.toMatrixAlgEquiv' (R := L) (n := n × κ)).toRingHom.comp
    ((ι.rightCoordinates b n).conjRingEquiv.toRingHom.comp (leftRegular ι))

/-- **Action of the regular coordinate matrix.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. For z∈L^(n×κ),
regularRepresentationWithBasis(A)*z=C_b(A*C_b⁻¹(z)).
-/
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

/-- **Entry of a right-basis regular matrix.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. For p=(i,a),q=(j,b), the entry of
regularRepresentationWithBasis(A) is the a-coordinate of A_ij*b_b in the right-L basis.
-/
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

/-- **Injectivity of the regular coordinate matrix representation.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. The representation regularRepresentationWithBasis ι b is
injective.
-/
theorem regularRepresentationWithBasis_injective (ι : L →+* D)
    (b : letI := ι.rightModule; Basis κ L D) :
    Function.Injective (regularRepresentationWithBasis (n := n) ι b) := by
  let := ι.rightModule
  exact (LinearMap.toMatrixAlgEquiv' (R := L) (n := n × κ)).injective.comp
    ((ι.rightCoordinates b n).conjRingEquiv.injective.comp (leftRegular_injective ι))

/-- **Regular coordinate matrices preserve the right opposite action.**

Let L be a commutative semiring, D a semiring and ι:L→D a coefficient homomorphism. Give D the
right L-action a•x=x*ι(a). For finite n, a matrix A∈M_n(D) acts by left multiplication on D^n.
Let b:κ→D be a finite basis for this right L-module. For any tuple index n,
C_b:D^n≃ₗ[L]L^(n×κ) has C_b(x)_(i,a)=b.repr(x_i)_a. The transported right D-action is
t•z=C_b(C_b⁻¹(z)*unop(t)) for t∈Dᵒᵖ. For t∈Dᵒᵖ,z∈L^(n×κ), ρ_b(A)(t•z)=t•ρ_b(A)(z), where
ρ_b=regularRepresentationWithBasis.
-/
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

/-- **Right subfield scalar action agrees with the common base.**

Let F,L be commutative semirings,D an F-algebra and ι:L→ₐ[F]D. On D with right L-action xι(a),
the F-action agrees with restriction through F→L, giving the scalar tower F→L→D.
-/
theorem rightModule_isScalarTower (ι : L →ₐ[F] D) :
    letI := ι.toRingHom.rightModule
    IsScalarTower F L D := by
  let := ι.toRingHom.rightModule
  constructor
  intro r l x
  change x * ι (r • l) = r • (x * ι l)
  rw [map_smul, mul_smul_comm]

/-- **Coordinate opposite action agrees over the common base.**

Let F,L be commutative semirings,D an F-algebra,ι:L→ₐ[F]D and b a finite right-L basis. The
transported right D-action on L^(n×κ) extends the same F-action, giving a scalar tower
F→Dᵒᵖ→L^(n×κ).
-/
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

/-- **Rank divisibility of a basis-coordinate regular representation.**

Let F,L be fields, D a division F-algebra and ι:L→ₐ[F]D. For d>0 assume dim_F L=d and dim_F
D=d². Then D with right L-action has L-dimension d. For a finite right-L basis b and A∈M_n(D),
d divides rank_L(regularRepresentationWithBasis ι b A).
-/
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

/-- **Right subfield basis from the two base dimensions.**

Let F,L be fields, D a division F-algebra and ι:L→ₐ[F]D. For d>0 assume dim_F L=d and dim_F
D=d². Then D with right L-action has L-dimension d. The constructor rightSubfieldBasis ι hd hL
hD gives a basis Fin d→D for the right L-action.
-/
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

/-- **Regular representation from a degree-d subfield.**

Let F,L be fields, D a division F-algebra and ι:L→ₐ[F]D. For d>0 assume dim_F L=d and dim_F
D=d². Then D with right L-action has L-dimension d. For finite n, regularRepresentation ι hd
hL hD:M_n(D)→M_(n×Fin d)(L) uses this right subfield basis to represent left matrix
multiplication.
-/
def regularRepresentation (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2) :
    Matrix n n D →+* Matrix (n × Fin d) (n × Fin d) L :=
  regularRepresentationWithBasis ι.toRingHom (ι.rightSubfieldBasis hd hL hD)

/-- **Faithfulness of the dimension-based regular representation.**

Let F,L be fields, D a division F-algebra and ι:L→ₐ[F]D. For d>0 assume dim_F L=d and dim_F
D=d². Then D with right L-action has L-dimension d. The representation regularRepresentation ι
hd hL hD is injective for every finite matrix index.
-/
theorem regularRepresentation_injective (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2) :
    Function.Injective (regularRepresentation (n := n) ι hd hL hD) :=
  regularRepresentationWithBasis_injective ι.toRingHom (ι.rightSubfieldBasis hd hL hD)

/-- **Rank divisibility of the dimension-based regular matrices.**

Let F,L be fields, D a division F-algebra and ι:L→ₐ[F]D. For d>0 assume dim_F L=d and dim_F
D=d². Then D with right L-action has L-dimension d. For A∈M_n(D), d divides
rank_L(regularRepresentation ι hd hL hD A).
-/
theorem dvd_rank_regularRepresentation (ι : L →ₐ[F] D) {d : ℕ} (hd : 0 < d)
    (hL : Module.finrank F L = d) (hD : Module.finrank F D = d ^ 2)
    (A : Matrix n n D) : d ∣ (regularRepresentation ι hd hL hD A).rank :=
  dvd_rank_regularRepresentationWithBasis ι (ι.rightSubfieldBasis hd hL hD) A hd hL hD

end Matrix

end ConstructedBasis
