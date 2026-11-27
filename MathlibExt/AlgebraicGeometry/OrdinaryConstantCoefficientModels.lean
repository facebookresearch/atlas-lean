/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
public import MathlibExt.CategoryTheory.DGSource.DGCochainCategory
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# All ordinary coefficient modules in the native constant-algebra DG source

The ring is any actual commutative ring, including the zero ring. Its
simplicial algebra is literally constant. Ordinary module complexes use
the complete native cochain Hom, differential and Koszul composition.
The comparison to modules over its shuffle normalization fixes every
coefficient action and every homogeneous module map.

Tor amplitude tests every ordinary module placed in degree zero. The
tensor is the actual balanced coequalizer of the native DG actions;
perfect inputs use their original cofibrant finite-cell/retract models.

Sources: Bhatt--Mathew, arXiv:1807.04725v4, Section5.4/Theorem5.16;
Keller, Deriving DG categories, Section2. Native Moore, DG, tensor and
Hom operations retain the source revisions and Apache notices in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
open CochainComplex.HomComplex

attribute [local instance 2000] ModuleCat.instLinear

variable (A : OrdinaryAlgebras)

/-- The complete native ordinary module cochain category over the original ring. -/
abbrev ModuleComplexes := CochainComplex (ModuleCat.{0} A) ℤ

/-- Forget only to the canonical integer action, termwise on the original complex. -/
def integerComplex : ModuleComplexes A ⥤ Cochains ℤ :=
  (ModuleCat.restrictScalars (algebraMap ℤ A)).mapHomologicalComplex (.up ℤ)

/-- The native full cochain DG enrichment uses every shifted R-linear module map. -/
@[instance_reducible]
def moduleDG : DGCategory ℤ (ModuleComplexes A) := by
  letI : Linear ℤ (ModuleCat.{0} A) := inferInstance
  infer_instance

/-- Every native Hom degree is the actual group of shifted ordinary module cochains. -/
theorem module_hom_degree (F G : ModuleComplexes A) (n : ℤ) :
    letI := moduleDG A
    (dgHomComplex ℤ F G).X n = ModuleCat.of ℤ (Cochain F G n) := rfl

variable (N : ShuffleAlgebraFunctor ℤ)

/-- The coefficient DG category is the actual normalization of the constant original ring. -/
abbrev ringCategory := coefficientCategory N (constantCoefficients.obj A)

/-- The actual original one-object coefficient module value. -/
abbrev ringValue (P : RightModule ℤ (ringCategory A N)) : Cochains ℤ :=
  letI := (ringCategory A N).dg
  P.toEnrichedFunctor.obj (op PUnit.unit)

/-- Constant normalization fixes the original ring in degree zero and has no other coefficient degrees. -/
structure ConstantRingSource where
  degree_zero : (N.functor.obj (constantCoefficients.obj A)).X.X 0 ≅ ModuleCat.of ℤ A
  coefficient_zero : ∀ a : (N.functor.obj (constantCoefficients.obj A)).X.X 0,
    coefficient (constantCoefficients.obj A) 0
      (((N.model (constantCoefficients.obj A)).complexIso.hom.f 0).hom a) =
        degree_zero.hom a
  off_zero : ∀ n : ℤ, n ≠ 0 → IsZero ((N.functor.obj (constantCoefficients.obj A)).X.X n)

variable (C : ConstantRingSource A N)

/-- An original scalar is its actual degree-zero normalized coefficient. -/
def scalar (r : A) :
    letI := (ringCategory A N).dg
    DGHom (C := (ringCategory A N)ᵒᵖ) ℤ 0 (op (PUnit.unit : ringCategory A N)) (op PUnit.unit) := by
  letI := (ringCategory A N).dg
  exact C.degree_zero.inv.hom r

/-- The comparison fixes all original complexes, scalar actions and homogeneous maps. -/
structure OrdinaryModuleSource where
  functor : letI := moduleDG A
    letI := (ringCategory A N).dg
    EnrichedFunctor (Cochains ℤ) (ModuleComplexes A) (RightModule ℤ (ringCategory A N))
  object : ∀ F : ModuleComplexes A, ringValue A N (functor.obj F) ≅ (integerComplex A).obj F
  action : letI := moduleDG A
    letI := (ringCategory A N).dg
    ∀ (F : ModuleComplexes A) (r : A) (i : ℤ)
      (m : (ringValue A N (functor.obj F)).X i),
    ((object F).hom.f i).hom
      (((functor.obj F).toEnrichedFunctor.dgMap 0 (scalar A N C r) :
        Cochain _ _ 0).v i i (by omega) m) =
      r • (show F.X i from (((object F).hom.f i).hom m))
  homogeneous : letI := moduleDG A
    letI := (ringCategory A N).dg
    ∀ (F G : ModuleComplexes A) (n p q : ℤ) (h : p + n = q)
      (f : DGHom ℤ n F G) (m : F.X p),
    ((object G).hom.f q).hom
      ((DGFunctor.dgApp (C := (ringCategory A N)ᵒᵖ) ℤ n (op PUnit.unit)
        (functor.dgMap n f) : Cochain _ _ n).v p q h
        (((object F).inv.f p).hom m)) =
      (f : Cochain F G n).v p q h m

variable (J : OrdinaryModuleSource A N C)

/-- Every ordinary module, with no finite-generation hypothesis, is tested in degree zero. -/
def discreteModule (V : ModuleCat.{0} A) : ModuleComplexes A :=
  (HomologicalComplex.single (ModuleCat.{0} A) (.up ℤ) 0).obj V

/-- Its actual native constant-coefficient DG module retains the original R action. -/
def discreteDGModule (V : ModuleCat.{0} A) : RightModule ℤ (ringCategory A N) :=
  J.functor.obj (discreteModule A V)

/-- The literal Tor-amplitude condition on a cofibrant native coefficient module. -/
def InTorAmplitude (P : DGDerivedModules ℤ (ringCategory A N))
    (T : ∀ Q : RightModule ℤ (ringCategory A N), ActionModel (ringCategory A N) PUnit.unit Q)
    (a b : ℤ) : Prop :=
  ∀ (V : ModuleCat.{0} A) (i : ℤ), i < a ∨ b < i →
    IsZero ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (.up ℤ) i).obj
      (balancedTensor (ringCategory A N) PUnit.unit (T P.obj) (T (discreteDGModule A N C J V))))

/-- One all-ring source retains every ordinary module and its actual native coefficient action. -/
structure OrdinaryTorSystem (N : ShuffleAlgebraFunctor ℤ) where
  ring : ∀ A : OrdinaryAlgebras, ConstantRingSource A N
  modules : ∀ A : OrdinaryAlgebras, OrdinaryModuleSource A N (ring A)
  action : ∀ (A : OrdinaryAlgebras) (P : RightModule ℤ (ringCategory A N)),
    ActionModel (ringCategory A N) PUnit.unit P

end MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
