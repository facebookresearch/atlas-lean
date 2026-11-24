/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The associated graded ring of an ideal-adic filtration

For an ideal `I` in a commutative ring, this file defines the graded pieces
`I ^ n / I ^ (n + 1)` and equips their direct sum with its natural commutative
ring structure.  It also constructs the induced equivalence of associated
graded rings under an equivalence of the ambient rings.
-/

@[expose] public section

open DirectSum

namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

/-- The `n`-th graded piece `I ^ n / I ^ (n + 1)` of the `I`-adic filtration.

The denominator is written as `I • ⊤` inside the subtype `I ^ n`; membership in
it is equivalent to membership in `I ^ (n + 1)` in the ambient ring. -/
abbrev adicGradedPiece (I : Ideal R) (n : ℕ) : Type u :=
  (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))

/-- The class of an element of `I ^ n` in `I ^ n / I ^ (n + 1)`. -/
def adicSymbol (I : Ideal R) (n : ℕ) :
    (I ^ n : Ideal R) →ₗ[R] I.adicGradedPiece n :=
  (I • ⊤ : Submodule R (I ^ n : Ideal R)).mkQ

@[simp]
theorem adicSymbol_apply (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    I.adicSymbol n x = Submodule.Quotient.mk x :=
  rfl

/-- Multiplication of representatives of two ideal-adic graded pieces. -/
def adicGradedMulRepresentative (I : Ideal R) (m n : ℕ)
    (x : (I ^ m : Ideal R)) (y : (I ^ n : Ideal R)) :
    I.adicGradedPiece (m + n) :=
  I.adicSymbol (m + n) ⟨(x : R) * y, by
    rw [pow_add]
    exact Ideal.mul_mem_mul x.2 y.2⟩

/-- The bilinear representative multiplication before descending through the
two quotient modules. -/
def adicGradedMulRaw (I : Ideal R) (m n : ℕ) :
    (I ^ m : Ideal R) →ₗ[R] (I ^ n : Ideal R) →ₗ[R] I.adicGradedPiece (m + n) :=
  LinearMap.mk₂ R (adicGradedMulRepresentative I m n)
    (fun x y z ↦ by
      simp only [adicGradedMulRepresentative, Submodule.coe_add, add_mul,
        adicSymbol_apply]
      rw [← Submodule.Quotient.mk_add
        (I • ⊤ : Submodule R (I ^ (m + n) : Ideal R))]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp)
    (fun r x y ↦ by
      simp only [adicGradedMulRepresentative, Submodule.coe_smul_of_tower,
        smul_eq_mul, adicSymbol_apply]
      rw [← Submodule.Quotient.mk_smul
        (I • ⊤ : Submodule R (I ^ (m + n) : Ideal R))]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp [mul_assoc])
    (fun x y z ↦ by
      simp only [adicGradedMulRepresentative, Submodule.coe_add, mul_add,
        adicSymbol_apply]
      rw [← Submodule.Quotient.mk_add
        (I • ⊤ : Submodule R (I ^ (m + n) : Ideal R))]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp)
    (fun r x y ↦ by
      simp only [adicGradedMulRepresentative, Submodule.coe_smul_of_tower,
        smul_eq_mul, adicSymbol_apply]
      rw [← Submodule.Quotient.mk_smul
        (I • ⊤ : Submodule R (I ^ (m + n) : Ideal R))]
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp [mul_left_comm])

/-- Representative multiplication vanishes when its left input lies in the
denominator `I ^ (m + 1)`. -/
theorem adicGradedMulRaw_left (I : Ideal R) (m n : ℕ) :
    (I • ⊤ : Submodule R (I ^ m : Ideal R)) ≤
      (adicGradedMulRaw I m n).ker := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  intro y
  simp only [LinearMap.zero_apply]
  change adicGradedMulRepresentative I m n x y = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  apply (Submodule.mem_smul_top_iff (I := I) _ _).2
  have hx' : (x : R) ∈ I ^ (m + 1) := by
    simpa only [Ideal.smul_eq_mul, pow_succ'] using
      (Submodule.mem_smul_top_iff (I := I) (I ^ m : Ideal R) x).1 hx
  have hxy : (x : R) * y ∈ I ^ ((m + n) + 1) := by
    rw [show (m + n) + 1 = (m + 1) + n by omega, pow_add]
    exact Ideal.mul_mem_mul hx' y.2
  simpa only [Ideal.smul_eq_mul, pow_succ'] using hxy

/-- Representative multiplication vanishes when its right input lies in the
denominator `I ^ (n + 1)`. -/
theorem adicGradedMulRaw_right (I : Ideal R) (m n : ℕ) :
    (I • ⊤ : Submodule R (I ^ n : Ideal R)) ≤
      (adicGradedMulRaw I m n).flip.ker := by
  intro y hy
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  intro x
  simp only [LinearMap.zero_apply]
  change adicGradedMulRepresentative I m n x y = 0
  apply (Submodule.Quotient.mk_eq_zero _).2
  apply (Submodule.mem_smul_top_iff (I := I) _ _).2
  have hy' : (y : R) ∈ I ^ (n + 1) := by
    simpa only [Ideal.smul_eq_mul, pow_succ'] using
      (Submodule.mem_smul_top_iff (I := I) (I ^ n : Ideal R) y).1 hy
  have hxy : (x : R) * y ∈ I ^ ((m + n) + 1) := by
    rw [show (m + n) + 1 = m + (n + 1) by omega, pow_add]
    exact Ideal.mul_mem_mul x.2 hy'
  simpa only [Ideal.smul_eq_mul, pow_succ'] using hxy

/-- Multiplication of ideal-adic graded pieces, obtained by multiplying
representatives and descending through both quotients. -/
noncomputable def adicGradedMul (I : Ideal R) (m n : ℕ) :
    I.adicGradedPiece m →ₗ[R] I.adicGradedPiece n →ₗ[R]
      I.adicGradedPiece (m + n) :=
  (adicGradedMulRaw I m n).liftQ₂
    (I • ⊤ : Submodule R (I ^ m : Ideal R))
    (I • ⊤ : Submodule R (I ^ n : Ideal R))
    (adicGradedMulRaw_left I m n) (adicGradedMulRaw_right I m n)

@[simp, nolint simpNF]
theorem adicGradedMul_symbol (I : Ideal R) (m n : ℕ)
    (x : (I ^ m : Ideal R)) (y : (I ^ n : Ideal R)) :
    I.adicGradedMul m n (I.adicSymbol m x) (I.adicSymbol n y) =
      I.adicSymbol (m + n) ⟨(x : R) * y, by
        rw [pow_add]
        exact Ideal.mul_mem_mul x.2 y.2⟩ :=
  LinearMap.liftQ₂_mk (adicGradedMulRaw_left I m n)
    (adicGradedMulRaw_right I m n) x y

private theorem gradedMonoid_eq_of_cast {A : ℕ → Type*}
    {i j : ℕ} {x : A i} {y : A j} (h : i = j)
    (hxy : cast (congrArg A h) x = y) :
    GradedMonoid.mk i x = GradedMonoid.mk j y := by
  subst j
  exact congrArg (GradedMonoid.mk i) (by simpa using hxy)

private theorem adicGradedPiece_cast_symbol (I : Ideal R) {m n : ℕ}
    (h : m = n) (x : (I ^ m : Ideal R)) (y : (I ^ n : Ideal R))
    (hxy : (x : R) = y) :
    cast (congrArg I.adicGradedPiece h) (I.adicSymbol m x) =
      I.adicSymbol n y := by
  subst n
  rw [cast_eq]
  apply congrArg (I.adicSymbol m)
  exact Subtype.ext hxy

private theorem adicGradedMul_one_left (I : Ideal R) (n : ℕ)
    (x : I.adicGradedPiece n) :
    cast (congrArg I.adicGradedPiece (zero_add n))
        (I.adicGradedMul 0 n
          (I.adicSymbol 0 ⟨1, by simp⟩) x) = x := by
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ n : Ideal R)) x ?_
  intro x
  let y : (I ^ (0 + n) : Ideal R) := ⟨(1 : R) * x, by
    rw [pow_add]
    exact Ideal.mul_mem_mul (by simp) x.2⟩
  calc
    cast (congrArg I.adicGradedPiece (zero_add n))
        (I.adicGradedMul 0 n (I.adicSymbol 0 ⟨1, by simp⟩)
          (I.adicSymbol n x)) =
      cast (congrArg I.adicGradedPiece (zero_add n))
        (I.adicSymbol (0 + n) y) := congrArg _
          (I.adicGradedMul_symbol 0 n ⟨1, by simp⟩ x)
    _ = I.adicSymbol n x :=
      adicGradedPiece_cast_symbol I (zero_add n) y x (by simp [y])

private theorem adicGradedMul_one_right (I : Ideal R) (n : ℕ)
    (x : I.adicGradedPiece n) :
    cast (congrArg I.adicGradedPiece (add_zero n))
        (I.adicGradedMul n 0 x
          (I.adicSymbol 0 ⟨1, by simp⟩)) = x := by
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ n : Ideal R)) x ?_
  intro x
  let y : (I ^ (n + 0) : Ideal R) := ⟨(x : R) * 1, by
    rw [pow_add]
    exact Ideal.mul_mem_mul x.2 (by simp)⟩
  calc
    cast (congrArg I.adicGradedPiece (add_zero n))
        (I.adicGradedMul n 0 (I.adicSymbol n x)
          (I.adicSymbol 0 ⟨1, by simp⟩)) =
      cast (congrArg I.adicGradedPiece (add_zero n))
        (I.adicSymbol (n + 0) y) := congrArg _
          (I.adicGradedMul_symbol n 0 x ⟨1, by simp⟩)
    _ = I.adicSymbol n x :=
      adicGradedPiece_cast_symbol I (add_zero n) y x (by simp [y])

private theorem adicGradedMul_assoc (I : Ideal R) (i j k : ℕ)
    (x : I.adicGradedPiece i) (y : I.adicGradedPiece j)
    (z : I.adicGradedPiece k) :
    cast (congrArg I.adicGradedPiece (add_assoc i j k))
        (I.adicGradedMul (i + j) k (I.adicGradedMul i j x y) z) =
      I.adicGradedMul i (j + k) x (I.adicGradedMul j k y z) := by
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ i : Ideal R)) x ?_
  intro x
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ j : Ideal R)) y ?_
  intro y
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ k : Ideal R)) z ?_
  intro z
  let xy : (I ^ (i + j) : Ideal R) := ⟨(x : R) * y, by
    rw [pow_add]
    exact Ideal.mul_mem_mul x.2 y.2⟩
  let yz : (I ^ (j + k) : Ideal R) := ⟨(y : R) * z, by
    rw [pow_add]
    exact Ideal.mul_mem_mul y.2 z.2⟩
  let lhs : (I ^ ((i + j) + k) : Ideal R) := ⟨(xy : R) * z, by
    rw [pow_add]
    exact Ideal.mul_mem_mul xy.2 z.2⟩
  let rhs : (I ^ (i + (j + k)) : Ideal R) := ⟨(x : R) * yz, by
    rw [pow_add]
    exact Ideal.mul_mem_mul x.2 yz.2⟩
  calc
    cast (congrArg I.adicGradedPiece (add_assoc i j k))
        (I.adicGradedMul (i + j) k
          (I.adicGradedMul i j (I.adicSymbol i x) (I.adicSymbol j y))
          (I.adicSymbol k z)) =
      cast (congrArg I.adicGradedPiece (add_assoc i j k))
        (I.adicSymbol ((i + j) + k) lhs) := by
          apply congrArg
          rw [I.adicGradedMul_symbol i j x y]
          exact I.adicGradedMul_symbol (i + j) k xy z
    _ = I.adicSymbol (i + (j + k)) rhs :=
      adicGradedPiece_cast_symbol I (add_assoc i j k) lhs rhs (by
        simp [lhs, rhs, xy, yz, mul_assoc])
    _ = I.adicGradedMul i (j + k) (I.adicSymbol i x)
        (I.adicGradedMul j k (I.adicSymbol j y) (I.adicSymbol k z)) := by
          rw [I.adicGradedMul_symbol j k y z]
          exact (I.adicGradedMul_symbol i (j + k) x yz).symm

private theorem adicGradedMul_comm (I : Ideal R) (i j : ℕ)
    (x : I.adicGradedPiece i) (y : I.adicGradedPiece j) :
    cast (congrArg I.adicGradedPiece (add_comm i j))
        (I.adicGradedMul i j x y) = I.adicGradedMul j i y x := by
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ i : Ideal R)) x ?_
  intro x
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ j : Ideal R)) y ?_
  intro y
  let lhs : (I ^ (i + j) : Ideal R) := ⟨(x : R) * y, by
    rw [pow_add]
    exact Ideal.mul_mem_mul x.2 y.2⟩
  let rhs : (I ^ (j + i) : Ideal R) := ⟨(y : R) * x, by
    rw [pow_add]
    exact Ideal.mul_mem_mul y.2 x.2⟩
  calc
    cast (congrArg I.adicGradedPiece (add_comm i j))
        (I.adicGradedMul i j (I.adicSymbol i x) (I.adicSymbol j y)) =
      cast (congrArg I.adicGradedPiece (add_comm i j))
        (I.adicSymbol (i + j) lhs) := congrArg _
          (I.adicGradedMul_symbol i j x y)
    _ = I.adicSymbol (j + i) rhs :=
      adicGradedPiece_cast_symbol I (add_comm i j) lhs rhs (by
        simp [lhs, rhs, mul_comm])
    _ = I.adicGradedMul j i (I.adicSymbol j y) (I.adicSymbol i x) :=
      (I.adicGradedMul_symbol j i y x).symm

noncomputable instance instGOneAdicGradedPiece (I : Ideal R) :
    GradedMonoid.GOne I.adicGradedPiece where
  one := I.adicSymbol 0 ⟨1, by simp⟩

noncomputable instance instGMulAdicGradedPiece (I : Ideal R) :
    GradedMonoid.GMul I.adicGradedPiece where
  mul {m n} x y := I.adicGradedMul m n x y

/-- The graded commutative-ring structure on the pieces of an ideal-adic
filtration. -/
noncomputable instance instGCommRingAdicGradedPiece (I : Ideal R) :
    DirectSum.GCommRing I.adicGradedPiece where
  one_mul := by
    rintro ⟨n, x⟩
    exact gradedMonoid_eq_of_cast (zero_add n) (adicGradedMul_one_left I n x)
  mul_one := by
    rintro ⟨n, x⟩
    exact gradedMonoid_eq_of_cast (add_zero n) (adicGradedMul_one_right I n x)
  mul_assoc := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    exact gradedMonoid_eq_of_cast (add_assoc i j k)
      (adicGradedMul_assoc I i j k x y z)
  mul_zero := fun x ↦ map_zero (I.adicGradedMul _ _ x)
  zero_mul := fun y ↦ by
    change I.adicGradedMul _ _ 0 y = 0
    simp
  mul_add := fun x y z ↦ map_add (I.adicGradedMul _ _ x) y z
  add_mul := fun x y z ↦ by
    change I.adicGradedMul _ _ (x + y) z =
      I.adicGradedMul _ _ x z + I.adicGradedMul _ _ y z
    simp
  gnpow := GradedMonoid.GMonoid.gnpowRec
  gnpow_zero' := fun a ↦
    GradedMonoid.GMonoid.gnpowRec_zero (A := I.adicGradedPiece) a
  gnpow_succ' := fun n a ↦
    GradedMonoid.GMonoid.gnpowRec_succ (A := I.adicGradedPiece) n a
  mul_comm := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    exact gradedMonoid_eq_of_cast (add_comm i j) (adicGradedMul_comm I i j x y)
  natCast n := n • (GradedMonoid.GOne.one : I.adicGradedPiece 0)
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    simpa using add_nsmul (GradedMonoid.GOne.one : I.adicGradedPiece 0) n 1
  intCast z := z • (GradedMonoid.GOne.one : I.adicGradedPiece 0)
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := by
    rw [show Int.negSucc n = -(n + 1 : ℕ) by rfl, neg_zsmul]
    apply congrArg Neg.neg
    exact ofNat_zsmul (GradedMonoid.GOne.one : I.adicGradedPiece 0) (n + 1)

/-- The associated graded ring `⊕ n, I ^ n / I ^ (n + 1)` of the `I`-adic
filtration. -/
noncomputable abbrev adicAssociatedGraded (I : Ideal R) : Type u :=
  ⨁ n : ℕ, I.adicGradedPiece n

section Transport

variable {S : Type v} [CommRing S]

/-- A ring equivalence restricts to a semilinear equivalence between
corresponding powers of an ideal and its image. -/
noncomputable def adicPowMapEquiv (e : R ≃+* S) (I : Ideal R) (n : ℕ) :
    letI := RingHomInvPair.of_ringEquiv e
    letI := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
    (I ^ n : Ideal R) ≃ₛₗ[(e : R →+* S)]
      ((I.map (e : R →+* S)) ^ n : Ideal S) := by
  let _ := RingHomInvPair.of_ringEquiv e
  let _ := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  exact
    { toFun := fun x ↦ ⟨e x, by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem e x.2⟩
      invFun := fun y ↦ ⟨e.symm y, by
        rw [Ideal.symm_apply_mem_of_equiv_iff, Ideal.map_pow]
        exact y.2⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y)
      map_smul' := fun r x ↦ Subtype.ext (e.map_mul r x) }

@[simp]
theorem adicPowMapEquiv_apply (e : R ≃+* S) (I : Ideal R) (n : ℕ)
    (x : (I ^ n : Ideal R)) :
    ((I.adicPowMapEquiv e n x :
      ((I.map (e : R →+* S)) ^ n : Ideal S)) : S) = e x :=
  rfl

/-- A ring equivalence carries the denominator `I • ⊤` of an adic graded
piece to the corresponding denominator for the image ideal. -/
theorem adicPowMapEquiv_denominator (e : R ≃+* S)
    (I : Ideal R) (n : ℕ) :
    (I • ⊤ : Submodule R (I ^ n : Ideal R)).map
        (I.adicPowMapEquiv e n :
          (I ^ n : Ideal R) →ₛₗ[(e : R →+* S)]
            ((I.map (e : R →+* S)) ^ n : Ideal S)) =
      (I.map (e : R →+* S) • ⊤ :
        Submodule S ((I.map (e : R →+* S)) ^ n : Ideal S)) := by
  let _ := RingHomInvPair.of_ringEquiv e
  let _ := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  ext y
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hy
    have hraw :=
      (Submodule.mem_smul_top_iff (I := I) (I ^ n : Ideal R)
        ((I.adicPowMapEquiv e n).symm y)).1 hy
    change (e.symm (y : S) : R) ∈
      (I • (I ^ n : Ideal R) : Submodule R R) at hraw
    have hy' : (e.symm (y : S) : R) ∈ I ^ (n + 1) := by
      rw [pow_succ']
      exact hraw
    apply (Submodule.mem_smul_top_iff
      (I := I.map (e : R →+* S)) _ _).2
    change (y : S) ∈
      (I.map (e : R →+* S) •
        (I.map (e : R →+* S)) ^ n : Submodule S S)
    rw [Ideal.smul_eq_mul, ← pow_succ', ← Ideal.map_pow]
    rw [← e.apply_symm_apply (y : S)]
    exact Ideal.mem_map_of_mem (e : R →+* S) hy'
  · intro hy
    have hraw :=
      (Submodule.mem_smul_top_iff
        (I := I.map (e : R →+* S)) _ y).1 hy
    change (y : S) ∈
      (I.map (e : R →+* S) •
        (I.map (e : R →+* S)) ^ n : Submodule S S) at hraw
    have hy' : (y : S) ∈ (I.map (e : R →+* S)) ^ (n + 1) := by
      rw [pow_succ']
      exact hraw
    apply (Submodule.mem_smul_top_iff (I := I) _ _).2
    change (e.symm (y : S) : R) ∈
      (I • (I ^ n : Ideal R) : Submodule R R)
    rw [Ideal.smul_eq_mul, ← pow_succ']
    apply Ideal.symm_apply_mem_of_equiv_iff.mpr
    rw [Ideal.map_pow]
    change (y : S) ∈ (I.map (e : R →+* S)) ^ (n + 1)
    exact hy'

/-- Transport of one ideal-adic graded piece under an equivalence of the
ambient rings. -/
noncomputable def adicGradedPieceMapEquiv (e : R ≃+* S)
    (I : Ideal R) (n : ℕ) :
    I.adicGradedPiece n ≃+
      (I.map (e : R →+* S)).adicGradedPiece n := by
  letI := RingHomInvPair.of_ringEquiv e
  letI := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  exact (Submodule.Quotient.equiv
    (I • ⊤ : Submodule R (I ^ n : Ideal R))
    (I.map (e : R →+* S) • ⊤ :
      Submodule S ((I.map (e : R →+* S)) ^ n : Ideal S))
    (I.adicPowMapEquiv e n) (adicPowMapEquiv_denominator e I n)).toAddEquiv

@[simp, nolint simpNF]
theorem adicGradedPieceMapEquiv_symbol (e : R ≃+* S)
    (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    I.adicGradedPieceMapEquiv e n (I.adicSymbol n x) =
      (I.map (e : R →+* S)).adicSymbol n
        ⟨e x, by
          rw [← Ideal.map_pow]
          exact Ideal.mem_map_of_mem e x.2⟩ :=
  rfl

private theorem adicGradedPieceMapEquiv_one (e : R ≃+* S)
    (I : Ideal R) :
    I.adicGradedPieceMapEquiv e 0
        (GradedMonoid.GOne.one : I.adicGradedPiece 0) =
      (GradedMonoid.GOne.one :
        (I.map (e : R →+* S)).adicGradedPiece 0) := by
  change I.adicGradedPieceMapEquiv e 0
      (I.adicSymbol 0 ⟨1, by simp⟩) =
    (I.map (e : R →+* S)).adicSymbol 0 ⟨1, by simp⟩
  rw [adicGradedPieceMapEquiv_symbol]
  apply congrArg ((I.map (e : R →+* S)).adicSymbol 0)
  apply Subtype.ext
  exact e.map_one

private theorem adicGradedPieceMapEquiv_mul (e : R ≃+* S)
    (I : Ideal R) (m n : ℕ) (x : I.adicGradedPiece m)
    (y : I.adicGradedPiece n) :
    I.adicGradedPieceMapEquiv e (m + n) (I.adicGradedMul m n x y) =
      (I.map (e : R →+* S)).adicGradedMul m n
        (I.adicGradedPieceMapEquiv e m x)
        (I.adicGradedPieceMapEquiv e n y) := by
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ m : Ideal R)) x ?_
  intro x
  refine Submodule.Quotient.induction_on
    (I • ⊤ : Submodule R (I ^ n : Ideal R)) y ?_
  intro y
  change I.adicGradedPieceMapEquiv e (m + n)
      (I.adicGradedMul m n (I.adicSymbol m x) (I.adicSymbol n y)) =
    (I.map (e : R →+* S)).adicGradedMul m n
      (I.adicGradedPieceMapEquiv e m (I.adicSymbol m x))
      (I.adicGradedPieceMapEquiv e n (I.adicSymbol n y))
  rw [I.adicGradedMul_symbol m n x y,
    adicGradedPieceMapEquiv_symbol,
    adicGradedPieceMapEquiv_symbol,
    adicGradedPieceMapEquiv_symbol,
    (I.map (e : R →+* S)).adicGradedMul_symbol]
  apply congrArg ((I.map (e : R →+* S)).adicSymbol (m + n))
  apply Subtype.ext
  exact e.map_mul x y

/-- The equivalence of ideal-adic associated graded rings induced by an
equivalence of the ambient commutative rings. -/
noncomputable def adicAssociatedGradedMapEquiv (e : R ≃+* S)
    (I : Ideal R) :
    I.adicAssociatedGraded ≃+*
      (I.map (e : R →+* S)).adicAssociatedGraded := by
  let pieceEquiv := fun n ↦ I.adicGradedPieceMapEquiv e n
  let f : I.adicAssociatedGraded →+*
      (I.map (e : R →+* S)).adicAssociatedGraded :=
    DirectSum.toSemiring
      (fun n ↦ (DirectSum.of
        (fun n ↦ (I.map (e : R →+* S)).adicGradedPiece n) n).comp
          (pieceEquiv n).toAddMonoidHom)
      (by
        change DirectSum.of _ 0
            (I.adicGradedPieceMapEquiv e 0 GradedMonoid.GOne.one) = 1
        rw [adicGradedPieceMapEquiv_one]
        rfl)
      (by
        intro m n x y
        simp only [AddMonoidHom.comp_apply]
        change DirectSum.of _ (m + n)
            (I.adicGradedPieceMapEquiv e (m + n)
              (I.adicGradedMul m n x y)) =
          DirectSum.of _ m (I.adicGradedPieceMapEquiv e m x) *
            DirectSum.of _ n (I.adicGradedPieceMapEquiv e n y)
        rw [DirectSum.of_mul_of]
        apply congrArg (DirectSum.of
          (fun n ↦ (I.map (e : R →+* S)).adicGradedPiece n) (m + n))
        exact adicGradedPieceMapEquiv_mul e I m n x y)
  let g := DirectSum.congrAddEquiv pieceEquiv
  refine AddEquiv.toRingEquiv g ?_
  intro x y
  have hgf : g.toAddMonoidHom = f.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro n x
    have hg : g.toAddMonoidHom (DirectSum.of I.adicGradedPiece n x) =
        DirectSum.of
          (fun n ↦ (I.map (e : R →+* S)).adicGradedPiece n) n
          (pieceEquiv n x) := by
      calc
        g.toAddMonoidHom (DirectSum.of I.adicGradedPiece n x) =
            DirectSum.map (fun n ↦ (pieceEquiv n).toAddMonoidHom)
              (DirectSum.of I.adicGradedPiece n x) := by
                exact congrFun (DirectSum.coe_congrAddEquiv pieceEquiv)
                  (DirectSum.of I.adicGradedPiece n x)
        _ = _ := DirectSum.map_of _ n x
    have hf : f (DirectSum.of I.adicGradedPiece n x) =
        DirectSum.of
          (fun n ↦ (I.map (e : R →+* S)).adicGradedPiece n) n
          (pieceEquiv n x) := by
      exact DirectSum.toSemiring_of _ _ _ n x
    exact hg.trans hf.symm
  change g.toAddMonoidHom (x * y) =
    g.toAddMonoidHom x * g.toAddMonoidHom y
  rw [hgf]
  exact f.map_mul x y

@[simp, nolint simpNF]
theorem adicAssociatedGradedMapEquiv_of_symbol (e : R ≃+* S)
    (I : Ideal R) (n : ℕ) (x : (I ^ n : Ideal R)) :
    I.adicAssociatedGradedMapEquiv e
        (DirectSum.of I.adicGradedPiece n (I.adicSymbol n x)) =
      DirectSum.of
        (fun n ↦ (I.map (e : R →+* S)).adicGradedPiece n) n
        ((I.map (e : R →+* S)).adicSymbol n
          ⟨e x, by
            rw [← Ideal.map_pow]
            exact Ideal.mem_map_of_mem e x.2⟩) := by
  change (DirectSum.congrAddEquiv
      (fun n ↦ I.adicGradedPieceMapEquiv e n))
      (DirectSum.of I.adicGradedPiece n (I.adicSymbol n x)) = _
  change DirectSum.map
      (fun n ↦ (I.adicGradedPieceMapEquiv e n).toAddMonoidHom)
      (DirectSum.of I.adicGradedPiece n (I.adicSymbol n x)) = _
  rw [DirectSum.map_of]
  change DirectSum.of _ n
      (I.adicGradedPieceMapEquiv e n (I.adicSymbol n x)) = _
  exact congrArg (DirectSum.of
    (fun n ↦ (I.map (e : R →+* S)).adicGradedPiece n) n)
      (I.adicGradedPieceMapEquiv_symbol e n x)

end Transport

end Ideal
