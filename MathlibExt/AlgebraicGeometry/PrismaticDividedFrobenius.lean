/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticNygaardTowers
public import Mathlib.RingTheory.Ideal.Span

/-!
# Actual oriented divided Frobenius and its fiber sign

For an actual delta ring and regular generator d, divided Frobenius
on the native ideal preimage is the unique y with d^n y = phi(x).
The cochain map is integer-linear; no A-linearity of phi is asserted.
The coordinate syntomic complex is the actual fiber of phi/d^n minus
the literal inclusion, hence has cohomological degrees zero and one
for a discrete input.

This is the oriented-coordinate operator used after a normalized
Breuil--Kisin lattice frame. Gluing that frame and identifying a
completed filtered model are separate construction/comparison requests.

References: Bhatt--Scholze, arXiv:1905.08229v4, Theorem 1.14(2)
and Section 15; BMS arXiv:1802.03261v2, Section 7.4 and the explicit
xi-tilde^(-i) Frobenius formula after Theorem 10.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticDividedFrobenius

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory
open PrismaticNygaardTowers
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [DeltaRing p A]
  (d : A)

/-- The actual source ideal of oriented divided Frobenius. -/
abbrev Domain (n : ℕ) := ↥(nygaardIdeal p A (Ideal.span {d}) n)

/-- A regular generator makes multiplication by every power injective. -/
theorem power_mul_injective (regular : Function.Injective (fun x : A ↦ d * x))
    (n : ℕ) : Function.Injective (fun x : A ↦ d ^ n * x) := by
  induction n with
  | zero =>
      intro x y h
      simpa only [pow_zero, one_mul] using h
  | succ n ih =>
      intro x y h
      apply ih
      apply regular
      simpa only [pow_succ', mul_assoc] using h

/-- The defining ideal membership supplies an actual divisibility witness. -/
theorem phi_divisible (n : ℕ) (x : Domain p A d n) :
    ∃ y : A, d ^ n * y = DeltaRing.frobenius p A x.val := by
  have hx := x.property
  change DeltaRing.frobenius p A x.val ∈ (Ideal.span {d}) ^ n at hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy.symm⟩

/-- Division is selected from that real ideal-membership witness. -/
def dividedValue (n : ℕ) (x : Domain p A d n) : A :=
  Classical.choose (phi_divisible p A d n x)

/-- Its defining equation keeps the actual delta Frobenius and divisor. -/
theorem divisor_mul_value (n : ℕ) (x : Domain p A d n) :
    d ^ n * dividedValue p A d n x = DeltaRing.frobenius p A x.val :=
  Classical.choose_spec (phi_divisible p A d n x)

/-- The actual normalized divided Frobenius is integer-linear. -/
def dividedLinear (regular : Function.Injective (fun x : A ↦ d * x)) (n : ℕ) :
    Domain p A d n →ₗ[ℤ] A where
  toFun := dividedValue p A d n
  map_add' x y := by
    apply power_mul_injective A d regular n
    change d ^ n * dividedValue p A d n (x + y) =
      d ^ n * (dividedValue p A d n x + dividedValue p A d n y)
    rw [mul_add, divisor_mul_value, divisor_mul_value, divisor_mul_value]
    exact map_add _ _ _
  map_smul' a x := by
    apply power_mul_injective A d regular n
    change d ^ n * dividedValue p A d n (a • x) =
      d ^ n * (a • dividedValue p A d n x)
    rw [divisor_mul_value, mul_smul_comm, divisor_mul_value]
    exact map_zsmul _ _ _

/-- The canonical map is literal ideal inclusion, with the same integer scalars. -/
def inclusion (n : ℕ) : Domain p A d n →ₗ[ℤ] A :=
  (nygaardIdeal p A (Ideal.span {d}) n).subtype.restrictScalars ℤ

/-- The actual discrete source complex, in the site module universe. -/
def sourceComplex (n : ℕ) : CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).obj
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ (Domain p A d n)))

/-- The actual delta ring as the same integer-coefficient cochain object. -/
def targetComplex : CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).obj
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ A))

/-- Divided Frobenius as a real map of the prescribed cochain complexes. -/
def phi (regular : Function.Injective (fun x : A ↦ d * x)) (n : ℕ) :
    sourceComplex p A d n ⟶ targetComplex A :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).map
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).map (ModuleCat.ofHom (dividedLinear p A d regular n)))

/-- The canonical map has the same source and target and keeps actual inclusion. -/
def can (n : ℕ) : sourceComplex p A d n ⟶ targetComplex A :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).map
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).map (ModuleCat.ofHom (inclusion p A d n)))

/-- Actual oriented-coordinate syntomic cochains, with phi minus can and the fiber shift. -/
def localSyntomic (regular : Function.Injective (fun x : A ↦ d * x)) (n : ℕ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  CochainComplex.mappingCocone (phi p A d regular n - can p A d n)

/-- Actual ring multiplication remains integer-linear after fixed scalar restriction. -/
def targetMultiply (a : A) : targetComplex A ⟶ targetComplex A :=
  (HomologicalComplex.single (ModuleCat.{1} ℤ) (ComplexShape.up ℤ) 0).map
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).map (ModuleCat.ofHom
      { toFun x := a * x
        map_add' x y := mul_add a x y
        map_smul' n x := mul_smul_comm n a x }))

/-- Signed divided Frobenius multiplies by d^(-i) at a negative weight. -/
def phiSigned (regular : Function.Injective (fun x : A ↦ d * x)) (i : ℤ) :
    sourceComplex p A d i.toNat ⟶ targetComplex A :=
  match i with
  | Int.ofNat n => phi p A d regular n
  | Int.negSucc n => phi p A d regular 0 ≫ targetMultiply A (d ^ (n + 1))

/-- The signed canonical map always retains the actual ideal inclusion. -/
def canSigned (i : ℤ) : sourceComplex p A d i.toNat ⟶ targetComplex A :=
  can p A d i.toNat

/-- Every signed coordinate complex is the actual fiber of phi minus can. -/
def localSyntomicSigned (regular : Function.Injective (fun x : A ↦ d * x)) (i : ℤ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  CochainComplex.mappingCocone (phiSigned p A d regular i - canSigned p A d i)

/-- A native source generator for the coordinate normalization equations. -/
def sourceGenerator (n : ℕ) (x : Domain p A d n) : (sourceComplex p A d n).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ (Domain p A d n)))).inv
      (ULift.up x)

/-- A native target generator, with the same prescribed integer coefficient object. -/
def targetGenerator (x : A) : (targetComplex A).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    ((ModuleCat.uliftFunctor.{1, 0} ℤ).obj (ModuleCat.of ℤ A))).inv (ULift.up x)

end MathlibExt.AlgebraicGeometry.PrismaticDividedFrobenius
