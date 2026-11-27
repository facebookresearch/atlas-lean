/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalDeRhamCupModels

/-!
# Phi-normalized prismatic/formal de Rham algebra maps

The coefficient map is literally phi_A followed by A → A/I. A cochain
comparison preserves the prescribed products and scalar units on every
homogeneous tensor generator. Scalar linearization uses the native
extension/restriction adjunction, derived scalar extension uses its Kan
counit, and p-completion uses the existing universal completion unit.

Construction and invertibility of the geometric comparison remain explicit
joint Wanted outputs. A module isomorphism alone is not an algebra comparison.

Reference: Bhatt–Scholze, arXiv:1905.08229v4, Theorem 1.8(3) and
Corollary 15.4. This is the ordinary derived-algebra/cochain component;
it does not assert a completed E-infinity realization.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticFormalDeRhamAlgebraMaps

open CategoryTheory
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.RingTheory.DerivedAdicCompleteness
open PrismaticCosimplicialAlgebras PrismaticAlgebraHypermodels
open RelativePrismaticCohomology FormalDeRhamModels FormalDeRhamCupModels

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (X : PadicFormalSchemes.FormalScheme p P.ring P.ideal)
  [RelativePrismaticCohomology.HasDerivedSections p P X]
  {O : StructuralAlgebra p P X} (H : Hypermodel p P X O)
  (M : AlgebraAssembly H.globalDiagram)
  (S : System p P X) {Q : HypermodelAlgebra p P X S} (F : FormalAlgebra p P X S Q)

def restrictedFormal : Cochains P.ring :=
  ((ModuleCat.restrictScalars.{1, 0, 0} (deRhamScalars p P)).mapHomologicalComplex
    (.up ℤ)).obj S.complex

/-- A genuine algebra map on the specified cochains, with the actual
phi_A scalar convention and every cup/unit equation explicit. -/
structure Map where
  cochain : PrismaticCosimplicialAlgebras.complex H.globalDiagram ⟶ restrictedFormal p P X S
  product : ∀ (i j k : ℤ) (h : i + j = k)
    (x : (PrismaticCosimplicialAlgebras.complex H.globalDiagram).X i)
    (y : (PrismaticCosimplicialAlgebras.complex H.globalDiagram).X j),
    cochain.f k (multiply M.multiplication i j k h x y) =
      multiply F.algebra.multiplication i j k h (cochain.f i x) (cochain.f j y)
  unit : ∀ a : P.ring,
    cochain.f 0 (M.unit.f 0 (scalarGenerator a)) =
      F.algebra.unit.f 0 (scalarGenerator (deRhamScalars p P a))

namespace Map

variable {p P X H M S F} (a : Map p P X H M S F)

def linearized :
    ((ModuleCat.extendScalars.{0, 0, 1} (deRhamScalars p P)).mapHomologicalComplex
      (.up ℤ)).obj (PrismaticCosimplicialAlgebras.complex H.globalDiagram) ⟶ S.complex where
  f i := ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 0}
    (deRhamScalars p P)).homEquiv _ _).symm (a.cochain.f i)
  comm' i j _ :=
    ((ModuleCat.extendRestrictScalarsAdj.{1, 0, 0}
      (deRhamScalars p P)).homEquiv_naturality_right_square
        ((PrismaticCosimplicialAlgebras.complex H.globalDiagram).d i j)
        (a.cochain.f j) (a.cochain.f i) (S.complex.d i j) (a.cochain.comm i j).symm).symm

def derived [HasExtension (deRhamScalars p P)] :
    (extension (deRhamScalars p P)).obj (prismatic p P X) ⟶ S.derived :=
  (extension (deRhamScalars p P)).map H.prismaticIso.inv ≫
    (extensionCounit (deRhamScalars p P)).app
      (PrismaticCosimplicialAlgebras.complex H.globalDiagram) ≫ DerivedCategory.Q.map a.linearized

def completed [HasExtension (deRhamScalars p P)]
    (C : Completion P.Residue (Ideal.span {(p : P.Residue)}))
    (h : IsComplete P.Residue (Ideal.span {(p : P.Residue)}) S.derived) :
    deRhamSpecialization p P X C ⟶ S.derived :=
  (Equiv.ofBijective _ (C.universal _ _ h)).symm a.derived

theorem completed_unit [HasExtension (deRhamScalars p P)]
    (C : Completion P.Residue (Ideal.span {(p : P.Residue)}))
    (h : IsComplete P.Residue (Ideal.span {(p : P.Residue)}) S.derived) :
    C.unit.app ((extension (deRhamScalars p P)).obj (prismatic p P X)) ≫
      a.completed C h = a.derived :=
  (Equiv.ofBijective _ (C.universal _ _ h)).apply_symm_apply _

end Map

end MathlibExt.AlgebraicGeometry.PrismaticFormalDeRhamAlgebraMaps
