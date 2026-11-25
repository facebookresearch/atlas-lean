/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import MathlibExt.AlgebraicGeometry.RelativePrismaticSite
public import MathlibExt.RingTheory.DerivedModuleScalarOperations

/-!
# Structural prismatic algebras and fixed Alexander--Whitney cups

The structural presheaf takes an actual prism to its actual commutative
base algebra. The cosimplicial complex uses the native alternating
coface differential. Its cup on homogeneous generators is the actual
front-coface image times the back-coface image, with the scalar unit.

An algebra assembly is an output constrained on every tensor summand,
including the Koszul permutation and a genuine commutativity homotopy.
It supplies the ordinary associative algebra in the derived category.
It does not construct an E-infinity algebra from a module comparison.

References: Bhatt--Scholze, arXiv:1905.08229v4, Definition 4.1,
Theorem 1.8(3),(5); Stacks Project, Tags 01FM and 0FKM.
All ring, differential, tensor, cochain and derived operations below are
native Mathlib. Algebra/hyperresolution assembly is requested separately.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open MathlibExt.RingTheory.DerivedModuleScalarOperations
open MathlibExt.AlgebraicGeometry.RelativePrismaticSite
open MathlibExt.RingTheory.BoundedPrisms
open scoped TensorProduct
open scoped Simplicial

attribute [local instance] HasDerivedCategory.standard

variable (p : ℕ) [Fact p.Prime] (P : Prism.{0} p)
  (X : PadicFormalSchemes.FormalScheme p P.ring P.ideal)

/-- The actual structural base algebra, before the harmless universe lift. -/
def smallAlgebraPresheaf : (Obj p P X)ᵒᵖ ⥤ CommAlgCat.{0} P.ring where
  obj U := CommAlgCat.of P.ring U.unop.prism.ring
  map {U V} f := CommAlgCat.ofHom
    { toRingHom := f.unop.map.hom
      commutes' a := by
        exact congrArg (fun h : P ⟶ V.unop.prism ↦ h.hom a) f.unop.base }
  map_id _ := by apply CommAlgCat.hom_ext; ext a; rfl
  map_comp _ _ := by apply CommAlgCat.hom_ext; ext a; rfl

/-- The actual structural commutative-algebra presheaf in the site universe. -/
def algebraPresheaf : (Obj p P X)ᵒᵖ ⥤ CommAlgCat.{1} P.ring :=
  smallAlgebraPresheaf p P X ⋙ CommAlgCat.uliftFunctor.{1, 0} P.ring

variable (A : Type) [CommRing A]

/-- The fixed forgetful functor retains the actual scalar action. -/
def algebraModules : CommAlgCat.{1} A ⥤ ModuleCat.{1} A :=
  forget₂ (CommAlgCat.{1} A) (AlgCat.{1} A) ⋙
    forget₂ (AlgCat.{1} A) (ModuleCat.{1} A)

/-- Forgetting the structural algebra recovers the existing structural module diagram. -/
def underlyingPresheafIso :
    algebraPresheaf p P X ⋙ algebraModules P.ring ≅ structurePresheaf p P X :=
  NatIso.ofComponents (fun U ↦ Iso.refl ((structurePresheaf p P X).obj U))
    (by intro U V f; rfl)

/-- An actual cosimplicial diagram of commutative coefficient algebras. -/
abbrev AlgebraDiagram := CosimplicialObject (CommAlgCat.{1} A)

variable {A} (F : AlgebraDiagram A)

/-- Its actual module-valued cosimplicial diagram. -/
abbrev moduleDiagram : CosimplicialObject (ModuleCat.{1} A) :=
  F ⋙ algebraModules A

/-- Native alternating-coface cochains, extended by zero in negative degrees. -/
def complex : Cochains A :=
  ((alternatingCofaceMapComplex (ModuleCat.{1} A)).obj (moduleDiagram F)).extend
    ComplexShape.embeddingUpNat

/-- The canonical identification with the actual nth ring module. -/
def degreeIso (n : ℕ) :
    (complex F).X (n : ℤ) ≅ ModuleCat.of A (F.obj ⦋n⦌) :=
  ((alternatingCofaceMapComplex (ModuleCat.{1} A)).obj
    (moduleDiagram F)).extendXIso ComplexShape.embeddingUpNat (by simp)

/-- The first p+1 vertices in the actual total simplex. -/
def front (i j : ℕ) : ⦋i⦌ ⟶ ⦋i + j⦌ :=
  SimplexCategory.mkHom
    { toFun a := ⟨a.val, by omega⟩
      monotone' := by intro a b h; exact h }

/-- The last q+1 vertices, with the common vertex at p. -/
def back (i j : ℕ) : ⦋j⦌ ⟶ ⦋i + j⦌ :=
  SimplexCategory.mkHom
    { toFun a := ⟨i + a.val, by omega⟩
      monotone' := by intro a b h; exact Nat.add_le_add_left h i }

/-- The literal Alexander--Whitney product, not an independently chosen cup. -/
def cupRing (i j : ℕ) (x : F.obj ⦋i⦌) (y : F.obj ⦋j⦌) : F.obj ⦋i + j⦌ :=
  (F.map (front i j)).hom x * (F.map (back i j)).hom y

/-- Its actual A-bilinear tensor map. -/
def cupTensor (i j : ℕ) :
    (F.obj ⦋i⦌) ⊗[A] (F.obj ⦋j⦌) →ₗ[A] F.obj ⦋i + j⦌ :=
  (LinearMap.mul' A (F.obj ⦋i + j⦌)).comp
    (TensorProduct.map (F.map (front i j)).hom.toLinearMap
      (F.map (back i j)).hom.toLinearMap)

@[simp] theorem cupTensor_tmul (i j : ℕ)
    (x : F.obj ⦋i⦌) (y : F.obj ⦋j⦌) :
    cupTensor F i j (x ⊗ₜ[A] y) = cupRing F i j x y := by
  simp [cupTensor, cupRing]

/-- Cosimplicial algebra maps preserve the fixed cups on every generator. -/
theorem cupRing_naturality {G : AlgebraDiagram A} (f : F ⟶ G)
    (i j : ℕ) (x : F.obj ⦋i⦌) (y : F.obj ⦋j⦌) :
    (f.app ⦋i + j⦌).hom (cupRing F i j x y) =
      cupRing G i j ((f.app ⦋i⦌).hom x) ((f.app ⦋j⦌).hom y) := by
  rw [cupRing, map_mul, cupRing]
  congr 1
  · exact congrArg (fun h : F.obj ⦋i⦌ ⟶ G.obj ⦋i + j⦌ ↦ h.hom x)
      (f.naturality (front i j))
  · exact congrArg (fun h : F.obj ⦋j⦌ ⟶ G.obj ⦋i + j⦌ ↦ h.hom y)
      (f.naturality (back i j))

/-- The tensor source used by the existing genuine two-variable derived tensor. -/
abbrev totalTensor (C E : Cochains A) : Cochains A :=
  HomologicalComplex.mapBifunctor C E (tensorBifunctor A) (ComplexShape.up ℤ)

/-- Its actual homogeneous summand map. -/
def tensorGenerator (C E : Cochains A) (i j k : ℤ) (h : i + j = k)
    (x : C.X i) (y : E.X j) : (totalTensor C E).X k :=
  HomologicalComplex.ιMapBifunctor C E (tensorBifunctor A)
    (ComplexShape.up ℤ) i j k h (x ⊗ₜ[A] y)

/-- A fixed multiplication map evaluated on the native tensor summand. -/
def multiply {C : Cochains A} (m : totalTensor C C ⟶ C)
    (i j k : ℤ) (h : i + j = k) (x : C.X i) (y : C.X j) : C.X k :=
  m.f k (tensorGenerator C C i j k h x y)

/-- The actual cochain scalar unit, with the necessary module-universe lift. -/
abbrev scalarComplex : Cochains A :=
  (HomologicalComplex.single (Modules A) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of A (ULift.{1} A))

/-- The scalar-unit generator in the native degree-zero component. -/
def scalarGenerator (a : A) : (scalarComplex (A := A)).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (ModuleCat.of A (ULift.{1} A))).inv (ULift.up a)

/-- A genuine ordinary cochain algebra whose operations have fixed generators.
The Koszul swap is constrained on every totalization summand; its
commutativity is an actual cochain homotopy. -/
structure AlgebraAssembly where
  multiplication : totalTensor (complex F) (complex F) ⟶ complex F
  unit : scalarComplex (A := A) ⟶ complex F
  product : ∀ (i j : ℕ) (x : F.obj ⦋i⦌) (y : F.obj ⦋j⦌),
    (degreeIso F (i + j)).hom
      (multiply multiplication (i : ℤ) (j : ℤ) (i + j : ℕ) (by omega)
        ((degreeIso F i).inv x) ((degreeIso F j).inv y)) = cupRing F i j x y
  scalar : ∀ a : A,
    (degreeIso F 0).hom (unit.f 0 (scalarGenerator a)) = algebraMap A (F.obj ⦋0⦌) a
  associative : ∀ (i j k r s t : ℤ) (hij : i + j = r) (hjk : j + k = s)
    (hrt : r + k = t) (hit : i + s = t)
    (x : (complex F).X i) (y : (complex F).X j) (z : (complex F).X k),
    multiply multiplication r k t hrt (multiply multiplication i j r hij x y) z =
      multiply multiplication i s t hit x (multiply multiplication j k s hjk y z)
  left_unit : ∀ (i : ℤ) (a : A) (x : (complex F).X i),
    multiply multiplication 0 i i (by omega) (unit.f 0 (scalarGenerator a)) x = a • x
  right_unit : ∀ (i : ℤ) (a : A) (x : (complex F).X i),
    multiply multiplication i 0 i (by omega) x (unit.f 0 (scalarGenerator a)) = a • x
  swap : totalTensor (complex F) (complex F) ⟶ totalTensor (complex F) (complex F)
  swap_generator : ∀ (i j k : ℤ) (h : i + j = k)
    (x : (complex F).X i) (y : (complex F).X j),
    swap.f k (tensorGenerator (complex F) (complex F) i j k h x y) =
      (-1 : ℤ) ^ (i * j).natAbs •
        tensorGenerator (complex F) (complex F) j i k (by omega) y x
  commutative : Homotopy (swap ≫ multiplication) multiplication

/-- The actual derived cup is the tensor Kan-counit followed by the fixed cochain cup. -/
def derivedCup [HasTensor A] (M : AlgebraAssembly F) :
    (tensor A).obj (DerivedCategory.Q.obj (complex F),
      DerivedCategory.Q.obj (complex F)) ⟶ DerivedCategory.Q.obj (complex F) :=
  (tensorCounit A).app (complex F, complex F) ≫
    DerivedCategory.Q.map M.multiplication

/-- Derived unit, retaining the actual scalar-complex generator. -/
def derivedUnit (M : AlgebraAssembly F) :
    DerivedCategory.Q.obj (scalarComplex (A := A)) ⟶
      DerivedCategory.Q.obj (complex F) :=
  DerivedCategory.Q.map M.unit

/-- Restrict the actual structural algebras along a simplicial prism diagram. -/
def prismDiagram (T : SimplicialObject (Obj p P X)) : AlgebraDiagram P.ring :=
  T.rightOp ⋙ algebraPresheaf p P X

end MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras
