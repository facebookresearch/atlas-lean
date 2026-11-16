/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Projective
/-!
# Finite-free obstruction complexes and real affine presentation maps

A differential between actual finite-free B-modules is placed in degrees
−1 and 0 using Mathlib's mapping cone. Finite projectivity and the degree
bounds are proved. The presentation comparison is a genuine cochain map to
Mathlib's I/I² → Ω_P⊗B differential; its kernel/cokernel maps are the H⁻¹/H⁰
maps of that displayed two-term presentation model.

The actual full cotangent complex is constructed separately from polynomial
resolution data. No presentation cone is silently identified with the full
cotangent complex on a singular scheme. The coefficient obstruction module
is the literal dual-differential cokernel, with an error map from actual
morphisms of extensions, useful for local models.

Sources: Mathlib RingTheory/Extension/Cotangent/Basic.lean, revision
56a005855ea17e0b0958f73ec801ae140b0a1679 (Andrew Yang, Apache 2.0);
Behrend--Fantechi, *The intrinsic normal cone*, §4,
https://arxiv.org/abs/alg-geom/9601010. Generic cotangent/deformation
constructions already occur in AxiomMath/Stacks and are not reasserted here.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard

variable (B : Type) [CommRing B]

structure FreeTwoTerm where
  negativeRank : ℕ
  zeroRank : ℕ
  differential : (Fin negativeRank → B) →ₗ[B] (Fin zeroRank → B)

abbrev negative (E : FreeTwoTerm B) := Fin E.negativeRank → B
abbrev degreeZero (E : FreeTwoTerm B) := Fin E.zeroRank → B

def complex (E : FreeTwoTerm B) : CochainComplex (ModuleCat.{0} B) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom E.differential))

def derived (E : FreeTwoTerm B) : DerivedCategory (ModuleCat.{0} B) :=
  DerivedCategory.Q.obj (complex B E)

variable {B}
variable {k : Type} [Field k] [Algebra k B] {n : ℕ} (G : _root_.Algebra.Generators k B (Fin n))

def naiveComplex : CochainComplex (ModuleCat.{0} B) ℤ :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map
    (ModuleCat.ofHom G.toExtension.cotangentComplex))

structure Comparison (E : FreeTwoTerm B) where
  negative : (Fin E.negativeRank → B) →ₗ[B] G.toExtension.Cotangent
  degreeZero : (Fin E.zeroRank → B) →ₗ[B] G.toExtension.CotangentSpace
  comm : G.toExtension.cotangentComplex ∘ₗ negative = degreeZero ∘ₗ E.differential

variable {G} {E : FreeTwoTerm B}

def negativeHomology (F : Comparison G E) :
    LinearMap.ker E.differential →ₗ[B] LinearMap.ker G.toExtension.cotangentComplex where
  toFun x := ⟨F.negative x.1, by
    change G.toExtension.cotangentComplex (F.negative x.1) = 0
    rw [← LinearMap.comp_apply, F.comm, LinearMap.comp_apply, x.2, map_zero]⟩
  map_add' x y := by ext; exact F.negative.map_add x.1 y.1
  map_smul' r x := by ext; exact F.negative.map_smul r x.1

def zeroHomology (F : Comparison G E) :
    ((Fin E.zeroRank → B) ⧸ LinearMap.range E.differential) →ₗ[B]
      G.toExtension.CotangentSpace ⧸ LinearMap.range G.toExtension.cotangentComplex :=
  Submodule.mapQ _ _ F.degreeZero (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨F.negative y, (LinearMap.congr_fun F.comm y)⟩)

def cochainMap (F : Comparison G E) : complex B E ⟶ naiveComplex G :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom F.negative))
    ((CochainComplex.singleFunctor (ModuleCat.{0} B) 0).map (ModuleCat.ofHom F.degreeZero)) (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact ModuleCat.hom_ext F.comm.symm)

variable (E) (M : Type) [AddCommGroup M] [Module B M]

def dualDifferential : ((Fin E.zeroRank → B) →ₗ[B] M) →ₗ[B]
    ((Fin E.negativeRank → B) →ₗ[B] M) where
  toFun f := f ∘ₗ E.differential
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev ObstructionModule := ((Fin E.negativeRank → B) →ₗ[B] M) ⧸
  LinearMap.range (dualDifferential E M)

variable {M}
variable {A : Type} [CommRing A] [Algebra k A] [Algebra B A] [IsScalarTower k B A]
  (Q : _root_.Algebra.Extension.{0} k A) (h : _root_.Algebra.Extension.Hom G.toExtension Q)

def obstruction (F : Comparison G E) : ObstructionModule E Q.Cotangent :=
  (LinearMap.range (dualDifferential E Q.Cotangent)).mkQ
    (_root_.Algebra.Extension.Cotangent.map h ∘ₗ F.negative)

def HasLift : Prop :=
  ∃ f : B →ₐ[k] Q.Ring, (IsScalarTower.toAlgHom k Q.Ring A).comp f = IsScalarTower.toAlgHom k B A

variable {E}

def presentedDerived (G : _root_.Algebra.Generators k B (Fin n)) :
    DerivedCategory (ModuleCat.{0} B) :=
  DerivedCategory.Q.obj (naiveComplex G)

def derivedMap (F : Comparison G E) : derived B E ⟶ presentedDerived G :=
  DerivedCategory.Q.map (cochainMap F)

structure PresentationTheory (G : _root_.Algebra.Generators k B (Fin n)) where
  model : FreeTwoTerm B
  comparison : Comparison G model
  surjectiveNegative : Function.Surjective (negativeHomology comparison)
  bijectiveZero : Function.Bijective (zeroHomology comparison)

theorem supportedDegrees (E : FreeTwoTerm B) (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((complex B E).X i) := by
  rw [complex, CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of B (negative B E)) (i + 1) (by omega)
  · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (ModuleCat.of B (degreeZero B E)) i hzero

variable (E)

instance finiteNegative : Module.Finite B (negative B E) := inferInstance
instance finiteZero : Module.Finite B (degreeZero B E) := inferInstance
instance projectiveNegative : Module.Projective B (negative B E) := inferInstance
instance projectiveZero : Module.Projective B (degreeZero B E) := inferInstance

end MathlibExt.AlgebraicGeometry.AffineObstructionComplexes
