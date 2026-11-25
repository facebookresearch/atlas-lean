/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.CompleteGradedCoordinates
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Polynomial coordinates on the associated graded enveloping algebra

For a chosen ordered basis of a Lie algebra over a commutative ring, PBW coordinates identify
a basis-indexed model of the associated graded enveloping algebra with the polynomial algebra
on the basis variables.

Symbols multiply as the classes of enveloping products. The polynomial coordinate algebra
equivalence preserves the homogeneous components, including degree zero.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped DirectSum

namespace UniversalEnvelopingAlgebra.PBW

variable {R : Type u} [CommRing R]
  {L : Type v} [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "P" => MvPolynomial I R

/-- The carrier is the direct sum with finite support of the enveloping algebra quotient layers.
The basis parameter records the constructed coordinates. -/
structure AssociatedGraded (b : Module.Basis I R L) where
  /-- The finite-support sum of homogeneous quotient coordinates. -/
  toGradedModule : GradedModule R L

/-- Forgetting the wrapper retains the exact quotient direct sum. -/
def associatedGradedRawEquiv (b : Module.Basis I R L) :
    AssociatedGraded b ≃ GradedModule R L where
  toFun := AssociatedGraded.toGradedModule
  invFun := AssociatedGraded.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The computed coordinate bijection, before installing a ring structure. -/
def associatedGradedCoordinateEquiv (b : Module.Basis I R L) : AssociatedGraded b ≃ P :=
  (associatedGradedRawEquiv b).trans (completeGradedModuleEquiv b).toEquiv

instance associatedGradedCommRing (b : Module.Basis I R L) : CommRing (AssociatedGraded b) :=
  (associatedGradedCoordinateEquiv b).commRing

instance associatedGradedAlgebra (b : Module.Basis I R L) : Algebra R (AssociatedGraded b) :=
  (associatedGradedCoordinateEquiv b).algebra R

/-- The full algebra coordinate equivalence of the quotient carrier. -/
def associatedGradedAlgEquiv (b : Module.Basis I R L) : AssociatedGraded b ≃ₐ[R] P :=
  (associatedGradedCoordinateEquiv b).algEquiv R

@[simp]
theorem associatedGradedAlgEquiv_apply (b : Module.Basis I R L) (x : AssociatedGraded b) :
    associatedGradedAlgEquiv b x = completeGradedModuleEquiv b x.toGradedModule := rfl

/-- Addition agrees with the addition of the quotient direct sum. -/
@[simp]
theorem associatedGraded_toGradedModule_add (b : Module.Basis I R L)
    (x y : AssociatedGraded b) : (x + y).toGradedModule = x.toGradedModule + y.toGradedModule := by
  apply (completeGradedModuleEquiv b).injective
  change associatedGradedAlgEquiv b (x + y) = _
  rw [map_add, map_add]
  rfl

/-- Scalar multiplication agrees with the scalar action of the quotient direct sum. -/
@[simp]
theorem associatedGraded_toGradedModule_smul (b : Module.Basis I R L)
    (r : R) (x : AssociatedGraded b) : (r • x).toGradedModule = r • x.toGradedModule := by
  apply (completeGradedModuleEquiv b).injective
  change associatedGradedAlgEquiv b (r • x) = _
  rw [map_smul, map_smul]
  rfl

/-- Embed a quotient layer into the associated graded carrier. -/
def ofGradedLayer (b : Module.Basis I R L) (n : ℕ) : GradedLayer R L n →ₗ[R] AssociatedGraded b :=
  (associatedGradedAlgEquiv b).symm.toLinearMap.comp
    ((MvPolynomial.homogeneousSubmodule I R n).subtype.comp
      (completeGradedEquiv b n).toLinearMap)

theorem associatedGradedAlgEquiv_ofGradedLayer (b : Module.Basis I R L) (n : ℕ)
    (x : GradedLayer R L n) :
    associatedGradedAlgEquiv b (ofGradedLayer b n x) = (completeGradedEquiv b n x).val := by
  change associatedGradedAlgEquiv b
    ((associatedGradedAlgEquiv b).symm (completeGradedEquiv b n x).val) = _
  exact (associatedGradedAlgEquiv b).apply_symm_apply _

/-- The layer embedding is the singleton of the quotient direct sum. -/
@[simp]
theorem ofGradedLayer_toGradedModule (b : Module.Basis I R L) (n : ℕ)
    (x : GradedLayer R L n) :
    (ofGradedLayer b n x).toGradedModule = DirectSum.lof R ℕ (GradedLayer R L) n x := by
  apply (completeGradedModuleEquiv b).injective
  change associatedGradedAlgEquiv b (ofGradedLayer b n x) = _
  rw [associatedGradedAlgEquiv_ofGradedLayer, completeGradedModuleEquiv_lof]

/-- The symbol of a filtered enveloping algebra element. -/
def symbol (b : Module.Basis I R L) (n : ℕ) :
    UniversalEnvelopingAlgebra.degreeFiltration R L n →ₗ[R] AssociatedGraded b :=
  (ofGradedLayer b n).comp (gradedLowerStage R L n).mkQ

theorem associatedGradedAlgEquiv_symbol (b : Module.Basis I R L) (n : ℕ)
    (u : UniversalEnvelopingAlgebra.degreeFiltration R L n) :
    associatedGradedAlgEquiv b (symbol b n u) =
      MvPolynomial.homogeneousComponent n (polynomialCoordinates b u.val) := by
  rw [symbol, LinearMap.comp_apply, associatedGradedAlgEquiv_ofGradedLayer,
    completeGradedEquiv_mk]
  rfl

/-- The associated graded multiplication is the class of the enveloping algebra product, proved
for all degrees and all filtered representatives. -/
theorem symbol_mul (b : Module.Basis I R L) (n m : ℕ)
    (u : UniversalEnvelopingAlgebra.degreeFiltration R L n)
    (v : UniversalEnvelopingAlgebra.degreeFiltration R L m) :
    symbol b n u * symbol b m v =
      symbol b (n + m) ⟨u.val * v.val,
        UniversalEnvelopingAlgebra.mul_mem_degreeFiltration R L u.property v.property⟩ := by
  apply (associatedGradedAlgEquiv b).injective
  rw [map_mul, associatedGradedAlgEquiv_symbol, associatedGradedAlgEquiv_symbol,
    associatedGradedAlgEquiv_symbol]
  exact (homogeneous_polynomialCoordinates_mul b n m u.property v.property).symm

private theorem polynomialCoordinates_one (b : Module.Basis I R L) :
    polynomialCoordinates b (1 : U) = (1 : P) := by
  let xs : OrderedWord I := ⟨[], List.Pairwise.nil⟩
  have h := polynomialCoordinates_orderedWord b xs
  change polynomialCoordinates b (1 : U) = MvPolynomial.monomial (wordExponent []) 1 at h
  simpa only [wordExponent_nil, MvPolynomial.monomial_zero', MvPolynomial.C_1] using h

/-- The scalar map in degree zero is the class of the enveloping algebra scalar map. -/
theorem symbol_algebraMap (b : Module.Basis I R L) (r : R) :
    symbol b 0 ⟨algebraMap R U r,
      UniversalEnvelopingAlgebra.algebraMap_mem_degreeFiltration R L 0 r⟩ =
        algebraMap R (AssociatedGraded b) r := by
  apply (associatedGradedAlgEquiv b).injective
  rw [associatedGradedAlgEquiv_symbol, AlgEquiv.commutes]
  change MvPolynomial.homogeneousComponent 0
    (polynomialCoordinates b (algebraMap R U r)) = algebraMap R P r
  rw [
    Algebra.algebraMap_eq_smul_one, map_smul, polynomialCoordinates_one, map_smul]
  simp only [MvPolynomial.homogeneousComponent_zero, MvPolynomial.coeff_one,
    ite_true, MvPolynomial.C_1, Algebra.algebraMap_eq_smul_one]

/-- The unit is the degree-zero symbol of the enveloping algebra unit. -/
theorem symbol_one (b : Module.Basis I R L) :
    symbol b 0 ⟨(1 : U), UniversalEnvelopingAlgebra.one_mem_degreeFiltration R L 0⟩ = 1 := by
  simpa only [map_one] using symbol_algebraMap b (1 : R)

/-- The quotient layer component, expressed through the computed polynomial coordinates. -/
def associatedGradedComponent (b : Module.Basis I R L) (n : ℕ) : Submodule R (AssociatedGraded b) :=
  (MvPolynomial.homogeneousSubmodule I R n).comap (associatedGradedAlgEquiv b).toLinearMap

/-- Every component is exactly the image of its quotient layer. -/
theorem associatedGradedComponent_eq_range (b : Module.Basis I R L) (n : ℕ) :
    associatedGradedComponent b n = LinearMap.range (ofGradedLayer b n) := by
  ext x
  constructor
  · intro hx
    let p : MvPolynomial.homogeneousSubmodule I R n := ⟨associatedGradedAlgEquiv b x, hx⟩
    refine ⟨(completeGradedEquiv b n).symm p, ?_⟩
    apply (associatedGradedAlgEquiv b).injective
    rw [associatedGradedAlgEquiv_ofGradedLayer, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, rfl⟩
    change associatedGradedAlgEquiv b (ofGradedLayer b n y) ∈
      MvPolynomial.homogeneousSubmodule I R n
    rw [associatedGradedAlgEquiv_ofGradedLayer]
    exact (completeGradedEquiv b n y).property

attribute [local instance] MvPolynomial.gradedAlgebra

instance associatedGradedComponent_gradedMonoid (b : Module.Basis I R L) :
    SetLike.GradedMonoid (associatedGradedComponent b) where
  one_mem := by
    change associatedGradedAlgEquiv b 1 ∈ MvPolynomial.homogeneousSubmodule I R 0
    rw [map_one]
    exact SetLike.one_mem_graded (MvPolynomial.homogeneousSubmodule I R)
  mul_mem := by
    intro n m x y hx hy
    change associatedGradedAlgEquiv b (x * y) ∈ MvPolynomial.homogeneousSubmodule I R (n + m)
    rw [map_mul]
    exact SetLike.mul_mem_graded hx hy

/-- The graded component is linearly equivalent to its homogeneous polynomial coordinates. -/
def associatedGradedComponentEquiv (b : Module.Basis I R L) (n : ℕ) :
    associatedGradedComponent b n ≃ₗ[R] MvPolynomial.homogeneousSubmodule I R n where
  toFun x := ⟨associatedGradedAlgEquiv b x.val, x.property⟩
  invFun p := ⟨(associatedGradedAlgEquiv b).symm p.val, by
    change associatedGradedAlgEquiv b ((associatedGradedAlgEquiv b).symm p.val) ∈
      MvPolynomial.homogeneousSubmodule I R n
    rw [AlgEquiv.apply_symm_apply]
    exact p.property⟩
  left_inv x := by apply Subtype.ext; exact (associatedGradedAlgEquiv b).symm_apply_apply x.val
  right_inv p := by apply Subtype.ext; exact (associatedGradedAlgEquiv b).apply_symm_apply p.val
  map_add' x y := by apply Subtype.ext; exact map_add (associatedGradedAlgEquiv b) x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul (associatedGradedAlgEquiv b) r x.val

/-- The finite-support decomposition into the graded components. -/
def associatedGradedDecomposeEquiv (b : Module.Basis I R L) :
    AssociatedGraded b ≃ₗ[R] ⨁ n, associatedGradedComponent b n :=
  (associatedGradedAlgEquiv b).toLinearEquiv.trans
    ((DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule I R)).trans
      (DirectSum.congrLinearEquiv (associatedGradedComponentEquiv b)).symm)

/-- Reassembly of the decomposition is the sum of component inclusions. -/
theorem associatedGradedDecomposeEquiv_symm_eq_coe (b : Module.Basis I R L) :
    (associatedGradedDecomposeEquiv b).symm.toLinearMap =
      DirectSum.coeLinearMap (associatedGradedComponent b) := by
  apply LinearMap.ext
  intro z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
      rw [DirectSum.coeLinearMap_of]
      change (associatedGradedAlgEquiv b).symm
        ((DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule I R)).symm
          (DirectSum.lmap (fun n => (associatedGradedComponentEquiv b n).toLinearMap)
             (DirectSum.lof R ℕ (fun n => associatedGradedComponent b n) n x))) = x.val
      rw [DirectSum.lmap_lof, DirectSum.decomposeLinearEquiv_symm_lof]
      exact (associatedGradedAlgEquiv b).symm_apply_apply x.val
  | add x y hx hy => simp only [map_add, hx, hy]

instance associatedGradedComponentDecomposition (b : Module.Basis I R L) :
    DirectSum.Decomposition (associatedGradedComponent b) :=
  (DirectSum.Decomposition.ofLinearMap (associatedGradedComponent b)
    (associatedGradedDecomposeEquiv b).toLinearMap
    (by
      rw [← associatedGradedDecomposeEquiv_symm_eq_coe]
      apply LinearMap.ext
      intro x
      exact (associatedGradedDecomposeEquiv b).symm_apply_apply x)
    (by
      rw [← associatedGradedDecomposeEquiv_symm_eq_coe]
      apply LinearMap.ext
      intro x
      exact (associatedGradedDecomposeEquiv b).apply_symm_apply x))

/-- The quotient components form a graded algebra. -/
instance associatedGradedGradedAlgebra (b : Module.Basis I R L) :
    GradedAlgebra (associatedGradedComponent b) :=
  { (inferInstance : SetLike.GradedMonoid (associatedGradedComponent b)),
    (inferInstance : DirectSum.Decomposition (associatedGradedComponent b)) with }

/-- The full algebra coordinate equivalence preserves each degree. -/
theorem associatedGradedAlgEquiv_mem_component_iff (b : Module.Basis I R L) (n : ℕ)
    (x : AssociatedGraded b) :
    associatedGradedAlgEquiv b x ∈ MvPolynomial.homogeneousSubmodule I R n ↔
      x ∈ associatedGradedComponent b n := Iff.rfl

end UniversalEnvelopingAlgebra.PBW
