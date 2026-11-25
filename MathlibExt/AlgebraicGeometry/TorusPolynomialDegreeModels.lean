/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusDifferentialGeometryModels
public import MathlibExt.Algebra.Module.EndScalarRestriction
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Topology.Algebra.MulAction

/-!
# Actual character polynomials, polarization and intrinsic A-degree

Polynomial variables represent the actual character coordinates.
Every matrix is pinned by the original scheme map on Laurent units.
The relative filtration is generated over the quotient coefficients by
polynomials of bounded total degree; it therefore uses no chosen splitting.
The generic tensor construction is applied to native quotient-torus
Borel cohomology in the stable-envelope interface.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.TorusPolynomialDegreeModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonObj
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusDifferentialGeometryModels
open scoped TensorProduct

abbrev CharacterPolynomials (r : ℕ) := MvPolynomial (Fin r) ℂ

def linearCharacter {r : ℕ} (a : Lattice r) : CharacterPolynomials r :=
  ∑ j, MvPolynomial.C (a j : ℂ) * MvPolynomial.X j

def coordinateUnit {T : Over base} [GrpObj T] (M : TorusModel T) (j : Fin M.rank) :
    Γ(T.left, ⊤)ˣ :=
  Units.map M.iso.hom.left.appTop.hom.toMonoidHom
    (Units.map (Scheme.ΓSpecIso (.of (CoordinateRing M.rank))).inv.hom.toMonoidHom
      (characterUnit M.rank (Pi.single j 1)))

/-- The coefficient matrix belongs to the actual group-scheme morphism. -/
structure TorusMorphismCoordinates {S T : Over base} [GrpObj S] [GrpObj T]
    (MS : TorusModel S) (MT : TorusModel T) (f : S ⟶ T) [IsMonHom f] where
  exponent : Fin MT.rank → Lattice MS.rank
  normalized : ∀ j : Fin MT.rank,
    f.left.appTop (coordinateUnit MT j : Γ(T.left, ⊤)) =
      MS.iso.hom.left.appTop
        ((Scheme.ΓSpecIso (.of (CoordinateRing MS.rank))).inv.hom
          (characterUnit MS.rank (exponent j) : CoordinateRing MS.rank))

def TorusMorphismCoordinates.polynomialMap {S T : Over base} [GrpObj S] [GrpObj T]
    {MS : TorusModel S} {MT : TorusModel T} {f : S ⟶ T} [IsMonHom f]
    (P : TorusMorphismCoordinates MS MT f) :
    CharacterPolynomials MT.rank →ₐ[ℂ] CharacterPolynomials MS.rank :=
  MvPolynomial.aeval (fun j => linearCharacter (P.exponent j))

/-- The continuous group map is computed from that actual integer character matrix. -/
def TorusMorphismCoordinates.groupMap {S T : Over base} [GrpObj S] [GrpObj T]
    {MS : TorusModel S} {MT : TorusModel T} {f : S ⟶ T} [IsMonHom f]
    (P : TorusMorphismCoordinates MS MT f) : (Fin MS.rank → ℂˣ) →* (Fin MT.rank → ℂˣ) where
  toFun g j := ∏ k, g k ^ P.exponent j k
  map_one' := by ext j; simp
  map_mul' g h := by ext j; simp [mul_zpow, Finset.prod_mul_distrib]

theorem TorusMorphismCoordinates.groupMap_continuous {S T : Over base} [GrpObj S] [GrpObj T]
    {MS : TorusModel S} {MT : TorusModel T} {f : S ⟶ T} [IsMonHom f]
    (P : TorusMorphismCoordinates MS MT f) : Continuous P.groupMap := by
  apply continuous_pi
  intro j
  change Continuous (fun g : Fin MS.rank → ℂˣ => ∏ k, g k ^ P.exponent j k)
  exact continuous_finsetProd (f := fun k (g : Fin MS.rank → ℂˣ) => g k ^ P.exponent j k)
    Finset.univ (fun k _ =>
    (show Continuous (fun g : Fin MS.rank → ℂˣ => g k) from continuous_apply k).zpow
      (P.exponent j k))

def normalEuler {A X F : Over base} [GrpObj A] [ModObj A X] {M : TorusModel A}
    {i : F ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint A X i} {N : NormalGeometry M i hi}
    (R : NormalRoots N) : CharacterPolynomials M.rank :=
  ∏ j : Fin R.roots.count, linearCharacter (R.roots.coordinates j).exponent ^ N.weights.rank
    (R.index j).1

def negativeEuler {A X F : Over base} [GrpObj A] [ModObj A X] {M : TorusModel A}
    {i : F ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint A X i} {N : NormalGeometry M i hi}
    (R : NormalRoots N) (C : Chamber R.roots) (L : ChamberCocharacter C) : CharacterPolynomials
      M.rank :=
  ∏ j : Fin R.roots.count, if (L.paired j).weight < 0 then
    linearCharacter (R.roots.coordinates j).exponent ^ N.weights.rank (R.index j).1 else 1

/-- The sign is the source square-root normalization of the actual A-normal Euler. -/
structure Polarization {A X F : Over base} [GrpObj A] [ModObj A X] {M : TorusModel A}
    {i : F ⟶ X} {hi : TorusFixedSchemeModels.FixedPoint A X i} {N : NormalGeometry M i hi}
    (R : NormalRoots N) (C : Chamber R.roots) (L : ChamberCocharacter C) where
  epsilon : CharacterPolynomials M.rank
  square : epsilon^2 = (-1)^(normalRank R / 2) * normalEuler R
  sign : ℤˣ
  normalization : epsilon = (sign : ℤ) • negativeEuler R C L

variable {r s : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
  (q : CharacterPolynomials s →ₐ[ℂ] CharacterPolynomials r)
  (ρ : CharacterPolynomials s →ₐ[ℂ] Module.End ℂ V)

/-- This is extension of the prescribed quotient-character action along the actual quotient map. -/
abbrev RelativeTensor :=
  letI := MathlibExt.EndScalarRestriction.module ρ
  letI : Algebra (CharacterPolynomials s) (CharacterPolynomials r) := q.toRingHom.toAlgebra
  TensorProduct (CharacterPolynomials s) (CharacterPolynomials r) V

/-- Intrinsic partial degree: arbitrary quotient classes and bounded character polynomials. -/
def relativeFiltration (d : ℕ) : Submodule ℂ (RelativeTensor q ρ) := by
  letI := MathlibExt.EndScalarRestriction.module ρ
  letI : Algebra (CharacterPolynomials s) (CharacterPolynomials r) := q.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (CharacterPolynomials s) (CharacterPolynomials r) :=
    IsScalarTower.of_algebraMap_eq (fun c => (q.commutes c).symm)
  exact Submodule.span ℂ {x | ∃ (p : CharacterPolynomials r) (v : V),
    p.totalDegree ≤ d ∧ x = p ⊗ₜ[CharacterPolynomials s] v}

/-- Zero has degree minus infinity, including the half-codimension-zero case. -/
def strictHalfDegree (codimension : ℕ) (a : RelativeTensor q ρ) : Prop :=
  a=0 ∨ ∃ d : ℕ, 2*d<codimension ∧ a ∈ relativeFiltration q ρ d

end MathlibExt.AlgebraicGeometry.TorusPolynomialDegreeModels
