/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/RingTheory/DeltaRing/Basic.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: the namespace `TauCeti` is renamed `MathlibExt.RingTheory` (two documentation
bullets are rewrapped to the line limit). Definitions, hypotheses and proofs are retained verbatim.
-/

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.FieldTheory.Finite.Basic

/-!
# δ-rings

Fix a prime `p`. A `δ`-ring is a commutative ring `A` with a map `δ : A → A` such that
`δ 0 = δ 1 = 0`, `δ (x * y) = x ^ p * δ y + y ^ p * δ x + p * δ x * δ y` and
`δ (x + y) = δ x + δ y + (x ^ p + y ^ p - (x + y) ^ p) / p`. The last quotient is the integral
polynomial `DeltaRing.addCorrection p x y`, a sum over the binomial coefficients `p.choose i`
with `0 < i < p`, each divided by `p`.

The map `φ x = x ^ p + p * δ x` is a ring endomorphism lifting Frobenius modulo `p`
(`DeltaRing.frobenius`). Conversely, on a ring in which `p` is a nonzerodivisor, a ring
endomorphism lifting Frobenius modulo `p` determines a unique `δ`-structure with that Frobenius
(`DeltaRing.ofFrobeniusLift` and `DeltaRing.ext_of_frobenius`). In particular `ℤ` has a unique
`δ`-structure (`DeltaRing.instInt` and `DeltaRing.instSubsingletonInt`), with
`δ n = (n - n ^ p) / p`.

## Main definitions

* `MathlibExt.RingTheory.DeltaRing.addCorrection`: the polynomial
  `(x ^ p + y ^ p - (x + y) ^ p) / p`.
* `MathlibExt.RingTheory.DeltaRing`: a `δ`-structure on a commutative ring.
* `MathlibExt.RingTheory.DeltaRing.frobenius`: the Frobenius lift `x ↦ x ^ p + p * δ x`.
* `MathlibExt.RingTheory.DeltaRing.ofFrobeniusLift`: the `δ`-structure of a Frobenius lift on a
  ring in which `p` is a nonzerodivisor.

## References

* B. Bhatt and P. Scholze, *Prisms and prismatic cohomology*, Ann. of Math. 196 (2022),
  §2.1, Definition 2.1, Remarks 2.2 and 2.4.
-/

public section

namespace MathlibExt.RingTheory

namespace DeltaRing

variable (p : ℕ) {A : Type*} [CommRing A]

/-- The integral polynomial `(x ^ p + y ^ p - (x + y) ^ p) / p`, written as
`-∑_{0 < i < p} x ^ i y ^ (p - i) (p.choose i / p)`. For prime `p` it satisfies
`p * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p` (`natCast_mul_addCorrection`). -/
def addCorrection (x y : A) : A :=
  -∑ i ∈ Finset.Ioo 0 p, x ^ i * y ^ (p - i) * ((p.choose i / p : ℕ) : A)

/-- The explicit binomial sum defining `addCorrection p x y`. -/
theorem addCorrection_def (x y : A) :
    addCorrection p x y = -∑ i ∈ Finset.Ioo 0 p, x ^ i * y ^ (p - i) * ((p.choose i / p : ℕ) : A) :=
  (rfl)

variable {p}

/-- For prime `p`, `p * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p`, so `addCorrection`
is the integral quotient `(x ^ p + y ^ p - (x + y) ^ p) / p` appearing in the sum rule of a
`δ`-ring. -/
theorem natCast_mul_addCorrection [hp : Fact p.Prime] (x y : A) :
    (p : A) * addCorrection p x y = x ^ p + y ^ p - (x + y) ^ p := by
  rw [addCorrection_def, add_pow_prime_eq' hp.out x y]
  ring

/-- Ring homomorphisms commute with `addCorrection`. -/
@[simp]
theorem map_addCorrection {B F : Type*} [CommRing B] [FunLike F A B] [RingHomClass F A B]
    (f : F) (x y : A) : f (addCorrection p x y) = addCorrection p (f x) (f y) := by
  simp [addCorrection_def]

/-- `addCorrection p 0 y = 0`. -/
@[simp]
theorem addCorrection_zero_left (y : A) : addCorrection p 0 y = 0 := by
  rw [addCorrection_def, neg_eq_zero]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [zero_pow (Finset.mem_Ioo.mp hi).1.ne', zero_mul, zero_mul]

/-- `addCorrection p x 0 = 0`. -/
@[simp]
theorem addCorrection_zero_right (x : A) : addCorrection p x 0 = 0 := by
  rw [addCorrection_def, neg_eq_zero]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_Ioo.mp hi).2), mul_zero, zero_mul]

/-- `addCorrection` is symmetric in its two arguments. -/
theorem addCorrection_comm (x y : A) : addCorrection p x y = addCorrection p y x := by
  rw [addCorrection_def, addCorrection_def, neg_inj]
  refine Finset.sum_nbij' (p - ·) (p - ·) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) fun i hi => ?_ <;> simp only [Finset.mem_Ioo] at hi ⊢ <;> try omega
  rw [Nat.sub_sub_self hi.2.le, Nat.choose_symm hi.2.le]
  ring

end DeltaRing

/-- A `δ`-structure on a commutative ring `A` for the prime `p` (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Definition 2.1): a map
`delta` with `delta 0 = delta 1 = 0`, the product rule
`delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y` and the sum rule
`delta (x + y) = delta x + delta y + (x ^ p + y ^ p - (x + y) ^ p) / p`, where the last quotient
is the polynomial `DeltaRing.addCorrection p x y`.

The prime `p` is a parameter rather than a hypothesis of the class; the results that need its
primality assume `Fact p.Prime`. -/
@[ext]
class DeltaRing (p : ℕ) (A : Type*) [CommRing A] where
  /-- The `δ`-operation. -/
  delta : A → A
  delta_zero : delta 0 = 0
  delta_one : delta 1 = 0
  delta_add (x y : A) : delta (x + y) = delta x + delta y + DeltaRing.addCorrection p x y
  delta_mul (x y : A) :
    delta (x * y) = x ^ p * delta y + y ^ p * delta x + p * delta x * delta y

namespace DeltaRing

variable {p : ℕ} {A : Type*} [CommRing A]

attribute [simp] delta_zero delta_one

section Frobenius

variable [Fact p.Prime] [DeltaRing p A]

variable (p A) in
/-- The Frobenius lift `φ x = x ^ p + p * δ x` of a `δ`-ring, a ring endomorphism
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.2). -/
def frobenius : A →+* A where
  toFun x := x ^ p + p * delta p x
  map_one' := by simp
  map_mul' x y := by
    simp only [delta_mul, mul_pow]
    ring
  map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
  map_add' x y := by
    simp only [delta_add, mul_add, natCast_mul_addCorrection]
    ring

theorem frobenius_apply (x : A) : frobenius p A x = x ^ p + p * delta p x := (rfl)

theorem frobenius_sub_pow (x : A) : frobenius p A x - x ^ p = p * delta p x := by
  rw [frobenius_apply]
  ring

/-- The Frobenius of a `δ`-ring lifts the `p`-th power map modulo `p`. -/
theorem natCast_dvd_frobenius_sub_pow (x : A) : (p : A) ∣ frobenius p A x - x ^ p :=
  ⟨delta p x, frobenius_sub_pow x⟩

omit [DeltaRing p A] in
/-- On a ring in which `p` is a nonzerodivisor, a `δ`-structure is determined by its Frobenius
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4). -/
theorem ext_of_frobenius (hA : IsRegular (p : A)) {δ₁ δ₂ : DeltaRing p A}
    (h : ∀ x, @frobenius p A _ _ δ₁ x = @frobenius p A _ _ δ₂ x) : δ₁ = δ₂ := by
  ext x
  apply hA.left
  dsimp only
  have h₁ := @frobenius_sub_pow p A _ _ δ₁ x
  have h₂ := @frobenius_sub_pow p A _ _ δ₂ x
  rw [← h₁, ← h₂, h x]

end Frobenius

section OfFrobeniusLift

variable [hp : Fact p.Prime]

/-- The `δ`-structure of a Frobenius lift `φ` on a ring in which `p` is a nonzerodivisor
(Bhatt and Scholze, *Prisms and prismatic cohomology*, Remark 2.4): `δ x` is the unique element
with `p * δ x = φ x - x ^ p`. -/
@[instance_reducible]
noncomputable def ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) : DeltaRing p A where
  delta x := (hφ x).choose
  delta_zero := by
    rw [← hA.left.mul_left_eq_zero_iff, ← (hφ 0).choose_spec]
    simp [hp.out.ne_zero]
  delta_one := by
    rw [← hA.left.mul_left_eq_zero_iff, ← (hφ 1).choose_spec]
    simp
  delta_add x y := by
    apply hA.left
    have hx := (hφ x).choose_spec
    have hy := (hφ y).choose_spec
    have hxy : φ x + φ y - (x + y) ^ p = p * (hφ (x + y)).choose := by
      rw [← map_add]
      exact (hφ (x + y)).choose_spec
    have hc := natCast_mul_addCorrection (p := p) x y
    dsimp only
    linear_combination -hxy + hx + hy - hc
  delta_mul x y := by
    apply hA.left
    have hx := (hφ x).choose_spec
    have hy := (hφ y).choose_spec
    have hxy : φ x * φ y - (x * y) ^ p = p * (hφ (x * y)).choose := by
      rw [← map_mul]
      exact (hφ (x * y)).choose_spec
    dsimp only
    linear_combination -hxy + φ x * hy + (y ^ p + p * (hφ y).choose) * hx

/-- Under `ofFrobeniusLift hA φ hφ`, `δ x` is characterised by `p * δ x = φ x - x ^ p`. -/
theorem natCast_mul_delta_ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) (x : A) :
    (p : A) * @delta p A _ (ofFrobeniusLift hA φ hφ) x = φ x - x ^ p :=
  ((hφ x).choose_spec).symm

/-- The Frobenius of `ofFrobeniusLift hA φ hφ` is `φ`. -/
@[simp]
theorem frobenius_ofFrobeniusLift (hA : IsRegular (p : A)) (φ : A →+* A)
    (hφ : ∀ x, (p : A) ∣ φ x - x ^ p) :
    @frobenius p A _ _ (ofFrobeniusLift hA φ hφ) = φ := by
  ext x
  rw [@frobenius_apply, natCast_mul_delta_ofFrobeniusLift]
  ring

end OfFrobeniusLift

section Int

variable [hp : Fact p.Prime]

/-- The `δ`-structure on `ℤ` whose Frobenius is the identity (Bhatt and Scholze, *Prisms and
prismatic cohomology*, Remark 2.4); it is the only one (`instSubsingletonInt`). -/
noncomputable instance instInt : DeltaRing p ℤ :=
  ofFrobeniusLift (A := ℤ)
    (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)) (RingHom.id ℤ) fun n =>
      (Int.ModEq.pow_prime_eq_self hp.out n).dvd

/-- `ℤ` has at most one `δ`-structure, since its Frobenius, a ring endomorphism of `ℤ`, must be
the identity. -/
instance instSubsingletonInt : Subsingleton (DeltaRing p ℤ) :=
  ⟨fun _ _ => ext_of_frobenius (isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    fun x => DFunLike.congr_fun (Subsingleton.elim _ _) x⟩

/-- The Frobenius of the `δ`-structure on `ℤ` is the identity. This is not `@[simp]`, since
`simp` already proves it by `frobenius_ofFrobeniusLift`. -/
theorem frobenius_int : frobenius p ℤ = RingHom.id ℤ :=
  frobenius_ofFrobeniusLift _ _ _

/-- The `δ`-operation on `ℤ` is `n ↦ (n - n ^ p) / p`; the division is exact since `p` divides
`n - n ^ p`. -/
theorem delta_int (n : ℤ) : delta p n = (n - n ^ p) / p := by
  have h := frobenius_sub_pow (p := p) n
  rw [frobenius_int, RingHom.id_apply] at h
  rw [h, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]

end Int

end DeltaRing

end MathlibExt.RingTheory
