/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Condensed.FrobeniusCoefficientUnit
public import MathlibExt.Condensed.SolidFpScalarModels

/-!
# The source-normalized local overconvergent Frobenius comparison

On a strictly totally disconnected chart, the source is the actual
one-object ring of locally constant Fp-valued functions. Its integer
enrichment retains that entire ring and every module-action map.
The coefficient-unit functor fixes the actual scalar map into A^+/pi
and has zero homotopy component on those scalars. Its right adjoint is
the literal module Hom from that unit, with its original Fp action.

The comparison is specified by the DG Hom adjunction with this fixed
right adjoint, given by its closed unit with homogeneous naturality and
holding up to quasi-isomorphism of Hom complexes. Full faithfulness and
the perfect-object equivalence are separate proof requests. They are not
fields of its construction model.

Scope: this is a local comparison between the DG source and the DG
enhancement of φ-modules. Identifying these endpoints with Mann's
geometric source and target, and this functor with Mann's
Riemann--Hilbert functor and the overconvergence condition, is a
separate prerequisite that is not asserted here.

Source: Mann, arXiv:2206.02022v1, Theorem 1.2.7,
Definitions 3.9.17 and 3.9.21; Lemma 3.9.18(iii).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.SolidOverconvergentRHModels

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.IntegerDGRestriction
open MathlibExt.CategoryTheory.DGScalarNerveMaps
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open LocalSolidCoefficientModels SolidTorsionFrobeniusModels SolidWeakPerfectModels
open FrobeniusModuleHomModels FrobeniusCoefficientUnit SolidFpScalarModels
open CochainComplex.HomComplex

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)
  (π : Pseudouniformizer p P) (h : π.element ∣ (p : P.pair.plus))
  (M : TorsionModel p P π) (F : FrobeniusModel p P π h M)

/-- The actual local Fp coefficient ring retains all scalars under integer enrichment. -/
def SourceCoefficient : DGCat Integers.{1} := by
  letI : DGCategory (FpFunctions p P) (fpCoefficientCategory p P) :=
    inferInstanceAs (DGCategory (FpFunctions p P)
      (discreteCoefficientCategory (FpFunctions p P)))
  exact DGCat.of Integers.{1}
    (IntegerDG (FpFunctions p P) (fpCoefficientCategory p P))

/-- Actual derived modules of the one-object local Fp ring, with their full action. -/
abbrev Source := DGDerivedModules Integers.{1} (SourceCoefficient p P)

/-- The actual phi enhancement is used, with no unrelated target carrier. -/
abbrev PhiFunctor (E : Enhancement p P π h M F)
    (C : Type*) [DGCategory Integers.{1} C] :=
  letI := E.category
  EnrichedFunctor (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
    C (PhiObject p P π h M F)

set_option maxHeartbeats 1200000 in
/-- The unit functor fixes the actual coefficient unit and every Fp scalar. -/
structure UnitFunctor (E : Enhancement p P π h M F)
    (U : UnitInductionModel p P π M) (A : CompactUnit p P π h M F U)
    (V : AlmostUnit p P π h M F U A) (S : FpScalarModel p P π) where
  functor : PhiFunctor p P π h M F E (SourceCoefficient p P)
  object_eq : letI := E.category; ∀ x, functor.obj x = V.object
  scalar_first : ∀ a : FpFunctions p P,
    letI := E.category
    let x := functor.obj PUnit.unit
    let f := functor.dgMap 0
      (show DGHom (C := SourceCoefficient p P) Integers.{1} 0
        PUnit.unit PUnit.unit from scalarEnd (FpFunctions p P) a)
    (first p P π h M F x x 0).hom (((eqToHom (E.hom_fixed x x)).f 0) f) =
      S.map a • dgId (C := TorsionCategory p P π M) (TorsionRing p P π) x.module
  scalar_second : ∀ a : FpFunctions p P,
    letI := E.category
    let x := functor.obj PUnit.unit
    let f := functor.dgMap 0
      (show DGHom (C := SourceCoefficient p P) Integers.{1} 0
        PUnit.unit PUnit.unit from scalarEnd (FpFunctions p P) a)
    (second p P π h M F x x 0).hom (((eqToHom (E.hom_fixed x x)).f 0) f) = 0

/-- The right adjoint is literal precomposition of the actual unit Hom module. -/
def unitHomModule {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    (B : UnitFunctor p P π h M F E U A V S) (X : PhiObject p P π h M F) :
    RightModule Integers.{1} (SourceCoefficient p P) :=
  letI := E.category
  ⟨(EnrichedFunctor.op B.functor).comp
    (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ) (dgRepresentable Integers.{1} X)⟩

set_option maxHeartbeats 1200000 in
/-- Hom-module functoriality retains every homogeneous postcomposition. -/
structure UnitHomFunctor {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    (B : UnitFunctor p P π h M F E U A V S) where
  functor : letI := E.category
    EnrichedFunctor (CochainComplex (ModuleCat.{1} Integers.{1}) ℤ)
      (PhiObject p P π h M F) (RightModule Integers.{1} (SourceCoefficient p P))
  object_eq : letI := E.category
    ∀ X, functor.obj X = unitHomModule p P π h M F B X
  components : ∀ (X Y : PhiObject p P π h M F) (n : ℤ)
    (a : letI := E.category; DGHom Integers.{1} n X Y) (x : (SourceCoefficient p P)ᵒᵖ),
    letI := E.category
    HEq (DGFunctor.dgApp Integers.{1} n x (functor.dgMap n a))
      (dgPostcomp Integers.{1} (op (B.functor.obj x.unop)) n a)

set_option maxHeartbeats 1200000 in
/-- The local RH construction: an adjunction with the prescribed Hom module, given by the unit and
holding up to quasi-isomorphism of Hom complexes. Its endpoints are the DG source `Source` and the
DG enhancement of φ-modules; their identification with Mann's geometric source and target, and the
relation of this functor to Mann's Riemann--Hilbert functor and to `IsOverconvergent`, is a separate
prerequisite that is not asserted here (Mann, Prop. 3.9.8, Lemma 3.9.18(iii), Def. 3.9.21). -/
structure RHPModel {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    (B : UnitFunctor p P π h M F E U A V S)
    (R : UnitHomFunctor p P π h M F B) where
  functor : PhiFunctor p P π h M F E (Source p P)
  unit : letI := E.category
    ∀ X : Source p P, DGHom Integers.{1} 0 X.obj (R.functor.obj (functor.obj X))
  closed : letI := E.category; ∀ X, dgDifferential Integers.{1} 0 (unit X) = 0
  /-- The adjunction map of Hom complexes, `a ↦ unit X ≫ R a` (see `hom_formula`). It is required
  to be a quasi-isomorphism, i.e. an equivalence of derived mapping complexes as in Mann's
  ∞-adjunction, not an isomorphism of the literal complexes. -/
  homMap : ∀ (X : Source p P) (Y : PhiObject p P π h M F),
    letI := E.category
    dgHomComplex Integers.{1} (functor.obj X) Y ⟶
      dgHomComplex Integers.{1} X.obj (R.functor.obj Y)
  quasiIso : ∀ (X : Source p P) (Y : PhiObject p P π h M F),
    letI := E.category
    QuasiIso (homMap X Y)
  hom_formula : ∀ (X : Source p P) (Y : PhiObject p P π h M F) (n : ℤ)
    (a : letI := E.category; DGHom Integers.{1} n (functor.obj X) Y),
    letI := E.category
    ((homMap X Y).f n) a =
      dgComp Integers.{1} (unit X) (R.functor.dgMap n a) (by omega)
  target_naturality : ∀ (X : Source p P) (Y Z : PhiObject p P π h M F)
    (i j n : ℤ)
    (a : letI := E.category; DGHom Integers.{1} i (functor.obj X) Y)
    (b : letI := E.category; DGHom Integers.{1} j Y Z) (e : i + j = n),
    letI := E.category
    ((homMap X Z).f n) (dgComp Integers.{1} a b e) =
      dgComp Integers.{1} (((homMap X Y).f i) a) (R.functor.dgMap j b) e
  source_naturality : ∀ (X Y : Source p P) (Z : PhiObject p P π h M F)
    (i j n : ℤ) (a : DGHom Integers.{1} i X Y)
    (b : letI := E.category; DGHom Integers.{1} j (functor.obj Y) Z) (e : i + j = n),
    letI := E.category
    ((homMap X Z).f n) (dgComp Integers.{1} (functor.dgMap i a) b e) =
      dgComp Integers.{1} (X := X.obj) (Y := Y.obj) (Z := R.functor.obj Z)
        a (((homMap Y Z).f j) b) e

/-- The source nerve retains the entire one-object Fp algebra and its native modules. -/
def sourceNerve : SSet.{2} := coherentNerve (R := Integers.{1}) (Source p P)

/-- The phi enhancement nerve retains its actual complete mapping fibres. -/
def phiNerve (E : Enhancement p P π h M F) : SSet.{2} :=
  letI := E.category
  coherentNerve (R := Integers.{1}) (PhiObject p P π h M F)

/-- The actual local comparison map on every coherent nerve simplex. -/
def RHPModel.nerveMap {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    {B : UnitFunctor p P π h M F E U A V S}
    {R : UnitHomFunctor p P π h M F B} (L : RHPModel p P π h M F B R) :
    sourceNerve p P ⟶ phiNerve p P π h M F E :=
  letI := E.category
  dgNerveMap L.functor

/-- Full faithfulness is the actual all-degree Hom quasi-isomorphism conclusion. -/
def IsFullyFaithful {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    {B : UnitFunctor p P π h M F E U A V S}
    {R : UnitHomFunctor p P π h M F B} (L : RHPModel p P π h M F B R) : Prop :=
  letI := E.category
  ∀ X Y : Source p P, QuasiIso (L.functor.map X Y)

/-- Perfect preservation uses only the one-object discrete Fp source. -/
def PreservesPerfect {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    {B : UnitFunctor p P π h M F E U A V S}
    {R : UnitHomFunctor p P π h M F B} (L : RHPModel p P π h M F B R) : Prop :=
  letI := E.category
  ∀ X : Source p P,
    IsPerfectModule (SourceCoefficient p P) X.obj →
      IsPerfectPhi p P π h M F U (L.functor.obj X)

/-- Closed cycles and native boundaries express essential surjectivity on perfect objects. -/
def IsEssentiallyPerfect {E : Enhancement p P π h M F}
    {U : UnitInductionModel p P π M} {A : CompactUnit p P π h M F U}
    {V : AlmostUnit p P π h M F U A} {S : FpScalarModel p P π}
    {B : UnitFunctor p P π h M F E U A V S}
    {R : UnitHomFunctor p P π h M F B} (L : RHPModel p P π h M F B R) : Prop :=
  letI := E.category
  ∀ Y : PhiObject p P π h M F, IsPerfectPhi p P π h M F U Y →
    ∃ X : Source p P, IsPerfectModule (SourceCoefficient p P) X.obj ∧
      ∃ (a : DGHom Integers.{1} 0 (L.functor.obj X) Y)
        (b : DGHom Integers.{1} 0 Y (L.functor.obj X)),
        dgDifferential Integers.{1} 0 a = 0 ∧ dgDifferential Integers.{1} 0 b = 0 ∧
        dgComp Integers.{1} a b (by omega) - dgId Integers.{1} (L.functor.obj X) ∈
          dgBoundaries Integers.{1} (L.functor.obj X) (L.functor.obj X) ∧
        dgComp Integers.{1} b a (by omega) - dgId Integers.{1} Y ∈
          dgBoundaries Integers.{1} Y Y

end MathlibExt.Condensed.SolidOverconvergentRHModels
