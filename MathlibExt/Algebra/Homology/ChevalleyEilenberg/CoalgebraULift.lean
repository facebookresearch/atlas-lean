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

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraNaturality
public import MathlibExt.CategoryTheory.Monoidal.ComonObjIsoMap
public import Mathlib.Algebra.Lie.TransferInstance
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.Additive

/-!
# Carrier lifts of exterior Lie coalgebras

For a Lie ring L, lifting its carrier transfers the bracket by
[up(x),up(y)]=up([x,y]). With an R-Lie structure over commutative R,
the down map is an R-Lie equivalence and Lie homomorphisms lift by
up(x)↦up(f(x)).

For R:Type u, L:Type v and any height z, the degree equivalences
Λ_R^n(U^zL)≃U^z(Λ_R^nL) form a chain isomorphism
C(U^zL)≅U^zC(L). Transporting the exterior comonoid through this
isomorphism gives a cocommutative coaugmented coalgebra on the
lifted chain complex in carrier height max{u,v,z}.

For a Lie map between L:Type v and L′:Type w, choose the common
height H=max{u,v,w}. Conjugating the lifted Lie chain map by the
exterior comparison isomorphisms gives U^H C(L)→U^H C(L′),
with value up(a)↦up(Λ^n f(a)) in degree n. It preserves the
coproduct, counit and coaugmentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

universe u v w z

namespace ChevalleyEilenberg.LieLift

/-- For a Lie ring L and any carrier lift height z, ULift.{z}L
has Lie bracket [up(x),up(y)]=up([x,y]) and the lifted additive
Lie ring laws. -/
scoped instance lieRing {L : Type v} [LieRing L] : LieRing (ULift.{z} L) :=
  (AddEquiv.ulift : ULift.{z} L ≃+ L).lieRing

open scoped ChevalleyEilenberg.LieLift

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The scalar action r•up(x)=up(r•x) is compatible with the
lifted bracket, giving U^zL its R-Lie algebra structure. -/
scoped instance lieAlgebra {R : Type u} [CommRing R] {L : Type v}
    [LieRing L] [LieAlgebra R L] : LieAlgebra R (ULift.{z} L) :=
  (ULift.moduleEquiv : ULift.{z} L ≃ₗ[R] L).lieAlgebra

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The down map U^zL→L is an R-Lie equivalence, with inverse
x↦up(x). -/
def downEquiv (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L] :
    ULift.{z} L ≃ₗ⁅R⁆ L := (ULift.moduleEquiv : ULift.{z} L ≃ₗ[R] L).lieEquiv R

@[simp]
theorem downEquiv_apply (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
    (x : ULift.{z} L) : downEquiv R L x = x.down := rfl

@[simp]
theorem downEquiv_symm_apply (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
    (x : L) : (downEquiv R L).symm x = ULift.up x := rfl

/-- Let R be commutative and f:L→L′ an R-Lie homomorphism, with
independent carrier universes v,w and common extra lift height z.
Its lifted Lie map U^zL→U^zL′ sends up(x) to up(f(x)). -/
def map {R : Type u} [CommRing R] {L : Type v} [LieRing L] [LieAlgebra R L]
    {L' : Type w} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') :
    ULift.{z} L →ₗ⁅R⁆ ULift.{z} L' :=
  (downEquiv R L').symm.toLieHom.comp (f.comp (downEquiv R L).toLieHom)

@[simp]
theorem map_up {R : Type u} [CommRing R] {L : Type v} [LieRing L] [LieAlgebra R L]
    {L' : Type w} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') (x : L) :
    map f (ULift.up x : ULift.{z} L) = ULift.up (f x) := rfl

end ChevalleyEilenberg.LieLift

open scoped ChevalleyEilenberg.LieLift

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

local instance coalgebraLiftFiniteBiproducts : HasFiniteBiproducts (ModuleCat.{max u z} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u z} R)

/-- For R:Type u commutative and any height z, tensoring in
ModuleCat.{max u z}R has internal R-linear Hom as right adjoint,
giving the closed tensor structure at that height. -/
local instance coalgebraLiftClosed :
    letI : MonoidalCategoryStruct (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, z} (R := R)
    MonoidalClosed (ModuleCat.{max u z} R) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, z} (R := R)
  exact ModuleCat.UniverseScalarRestriction.monoidalClosed.{u, z} (R := R)

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The carrier-lifted CE complex U^zC(L) has degree-n term
U^z(Λ_R^nL) and lifted differentials, in ModuleCat at
max{u,v,z}. -/
def canonicalComplexULift : ChainComplex (ModuleCat.{max u v z} R) ℕ :=
  ((ModuleCat.uliftFunctor.{z, max u v} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (canonicalChainData R L).complex

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The R-linear exterior lift equivalence is
Λ_R^n(U^zL)≃U^z(Λ_R^nL), sending a lifted decomposable
wedge to the lift of its down-vector wedge. -/
def exteriorULiftEquiv (n : ℕ) :
    (⋀[R]^n (ULift.{z} L)) ≃ₗ[R] ULift.{z} (⋀[R]^n L) where
  toLinearMap := (ULift.moduleEquiv : ULift.{z} (⋀[R]^n L) ≃ₗ[R] (⋀[R]^n L)).symm.toLinearMap.comp
    (exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).toLinearMap)
  invFun a := exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).symm.toLinearMap a.down
  left_inv a := by
    change exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).symm.toLinearMap
      (exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).toLinearMap a) = a
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have h : (LieLift.downEquiv.{u,v,z} R L).symm.toLinearMap.comp
        (LieLift.downEquiv.{u,v,z} R L).toLinearMap =
        (LinearMap.id : ULift.{z} L →ₗ[R] ULift.{z} L) := by
      apply LinearMap.ext
      intro x
      exact (LieLift.downEquiv.{u,v,z} R L).symm_apply_apply x
    rw [h, exteriorPower.map_id, LinearMap.id_apply]
  right_inv a := by
    change ULift.up (exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).toLinearMap
      (exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).symm.toLinearMap a.down)) = a
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    have h : (LieLift.downEquiv.{u,v,z} R L).toLinearMap.comp
        (LieLift.downEquiv.{u,v,z} R L).symm.toLinearMap = (LinearMap.id : L →ₗ[R] L) := by
      apply LinearMap.ext
      intro x
      exact (LieLift.downEquiv.{u,v,z} R L).apply_symm_apply x
    rw [h, exteriorPower.map_id, LinearMap.id_apply]

@[simp]
theorem exteriorULiftEquiv_apply (n : ℕ) (a : ⋀[R]^n (ULift.{z} L)) :
    exteriorULiftEquiv R L n a =
      ULift.up (exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).toLinearMap a) := rfl

@[simp]
theorem exteriorULiftEquiv_symm_apply (n : ℕ) (a : ULift.{z} (⋀[R]^n L)) :
    (exteriorULiftEquiv R L n).symm a =
      exteriorPower.map n (LieLift.downEquiv.{u,v,z} R L).symm.toLinearMap a.down := rfl

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The exterior-degree equivalences give a chain isomorphism
C(U^zL)≅U^zC(L), compatible with the CE boundary in every degree. -/
def complexLiftComparisonIso :
    (canonicalChainData R (ULift.{z} L)).complex ≅ canonicalComplexULift.{u,v,z} R L :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (exteriorULiftEquiv R L n).toModuleIso)
    (fun i j h => by
      change j + 1 = i at h
      subst i
      change (exteriorULiftEquiv R L (j + 1)).toModuleIso.hom ≫
          (ModuleCat.uliftFunctor.{z, max u v} R).map
            ((canonicalChainData R L).complex.d (j + 1) j) =
        (canonicalChainData R (ULift.{z} L)).complex.d (j + 1) j ≫
          (exteriorULiftEquiv R L j).toModuleIso.hom
      rw [ChainData.complex_d_succ, ChainData.complex_d_succ]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      change ULift.up (differential R L j
          (exteriorPower.map (j + 1) (LieLift.downEquiv.{u,v,z} R L).toLinearMap a)) =
        ULift.up (exteriorPower.map j (LieLift.downEquiv.{u,v,z} R L).toLinearMap
          (differential R (ULift.{z} L) j a))
      exact congrArg ULift.up (LinearMap.congr_fun
        (differential_naturality R (ULift.{z} L) (LieLift.downEquiv.{u,v,z} R L).toLieHom j) a))

@[simp]
theorem complexLiftComparisonIso_hom_f (n : ℕ) :
    (complexLiftComparisonIso.{u,v,z} R L).hom.f n =
      (exteriorULiftEquiv R L n).toModuleIso.hom := rfl

@[simp]
theorem complexLiftComparisonIso_inv_f (n : ℕ) :
    (complexLiftComparisonIso.{u,v,z} R L).inv.f n =
      (exteriorULiftEquiv R L n).toModuleIso.inv := rfl

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
Transporting the comonoid of C(U^zL) through the chain
comparison equips U^zC(L) with its coproduct and counit
in the signed tensor category at max{u,v,z}. -/
def liftedComonObj :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
    ComonObj (canonicalComplexULift.{u,v,z} R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
  letI : ComonObj (canonicalChainData R (ULift.{z} L)).complex := nativeComonObj R (ULift.{z} L)
  exact ComonObj.ofIso (complexLiftComparisonIso.{u,v,z} R L)

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The lifted coaugmentation has source the tensor-unit complex
at max{u,v,z} and target U^zC(L). It is the coaugmentation
of C(U^zL) followed by the chain comparison. -/
def liftedComplexCoaug : nativeUnitComplex.{u,max v z} R ⟶ canonicalComplexULift.{u,v,z} R L :=
  nativeComplexCoaug R (ULift.{z} L) ≫ (complexLiftComparisonIso.{u,v,z} R L).hom

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The transported coaugmentation into U^zC(L) is a comonoid
morphism from the tensor-unit coalgebra. -/
def liftedComplexCoaugIsComonHom :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
    letI : ComonObj (nativeUnitComplex.{u,max v z} R) :=
      ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v z} R) ℕ)
    letI : ComonObj (canonicalComplexULift.{u,v,z} R L) := liftedComonObj R L
    IsComonHom (liftedComplexCoaug.{u,v,z} R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
  letI : ComonObj (nativeUnitComplex.{u,max v z} R) :=
    ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v z} R) ℕ)
  letI : ComonObj (canonicalChainData R (ULift.{z} L)).complex := nativeComonObj R (ULift.{z} L)
  letI : ComonObj (canonicalComplexULift.{u,v,z} R L) := liftedComonObj R L
  letI : IsComonHom (nativeComplexCoaug R (ULift.{z} L)) := nativeComplexCoaugIsComonHom _ _
  letI : IsComonHom (complexLiftComparisonIso.{u,v,z} R L).hom := ComonObj.isComonHom_ofIso _
  unfold liftedComplexCoaug
  infer_instance

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The transported coproduct on U^zC(L) is cocommutative
for the signed chain braiding, with degree-(p,q) sign (−1)^{pq}. -/
theorem liftedComul_cocommutative :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
    letI : SymmetricCategory (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.symmetricCategory.{u, max v z} (R := R)
    letI : ComonObj (canonicalComplexULift.{u,v,z} R L) := liftedComonObj R L
    ComonObj.comul (X := canonicalComplexULift.{u,v,z} R L) ≫
        (HomologicalComplex.koszulTensorBraidingIso
          (canonicalComplexULift.{u,v,z} R L) (canonicalComplexULift.{u,v,z} R L)).hom =
      ComonObj.comul (X := canonicalComplexULift.{u,v,z} R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
  letI : SymmetricCategory (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.symmetricCategory.{u, max v z} (R := R)
  letI : ComonObj (canonicalComplexULift.{u,v,z} R L) := liftedComonObj R L
  let e := complexLiftComparisonIso.{u,v,z} R L
  have hn := HomologicalComplex.koszulTensorBraidingIso_hom_naturality e.hom e.hom
  have hc := nativeComplexComul_cocommutative R (ULift.{z} L)
  change e.inv ≫ nativeComplexComul R (ULift.{z} L) ≫
      HomologicalComplex.tensorHom e.hom e.hom ≫
        (HomologicalComplex.koszulTensorBraidingIso
          (canonicalComplexULift.{u,v,z} R L) (canonicalComplexULift.{u,v,z} R L)).hom =
    e.inv ≫ nativeComplexComul R (ULift.{z} L) ≫ HomologicalComplex.tensorHom e.hom e.hom
  have h₁ := congrArg (fun t => e.inv ≫ nativeComplexComul R (ULift.{z} L) ≫ t) hn
  have h₂ := (Category.assoc (nativeComplexComul R (ULift.{z} L))
    (HomologicalComplex.koszulTensorBraidingIso
      ((canonicalChainData R (ULift.{z} L)).complex)
      ((canonicalChainData R (ULift.{z} L)).complex)).hom
    (HomologicalComplex.tensorHom e.hom e.hom)).symm
  have h₃ := congrArg (fun t => t ≫ HomologicalComplex.tensorHom e.hom e.hom) hc
  exact h₁.trans (congrArg (fun t => e.inv ≫ t) (h₂.trans h₃))

/-- Let R:Type u be commutative, L:Type v an R-Lie algebra,
and z an independent lift height. Write C(L) for its canonical
exterior chain complex and U^z for carrier lifting.
The lifted complex U^zC(L), with transported coproduct and
counit, is a bundled coalgebra in the chain category at max{u,v,z}. -/
def liftedCoalgebra :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
    Comon (ChainComplex (ModuleCat.{max u v z} R) ℕ) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v z} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v z} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v z} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v z} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v z} (R := R)
  exact { X := canonicalComplexULift.{u,v,z} R L, comon := liftedComonObj R L }

section IndependentWorlds

variable {L' : Type w} [LieRing L'] [LieAlgebra R L']

/-- Let R:Type u be commutative, L:Type v and L′:Type w R-Lie
algebras, and f:L→L′ a Lie homomorphism. At H=max{u,v,w},
the exterior lift comparisons give the chain map
U^H C(L)→U^H C(L′) induced by the lifted Lie map. -/
def nativeLiftedComplexMap (f : L →ₗ⁅R⁆ L') :
    canonicalComplexULift.{u,v,max u v w} R L ⟶
      canonicalComplexULift.{u,w,max u v w} R L' :=
  (complexLiftComparisonIso.{u,v,max u v w} R L).inv ≫
    nativeComplexMap R (ULift.{max u v w} L) (LieLift.map.{u,v,w,max u v w} f) ≫
      (complexLiftComparisonIso.{u,w,max u v w} R L').hom

/-- For an R-Lie map f:L→L′ with scalar and carrier worlds u,v,w,
the common-height chain map at H=max{u,v,w} sends up(a) to
up(Λ_R^n f(a)) for every a∈Λ_R^nL. -/
theorem nativeLiftedComplexMap_f_apply (f : L →ₗ⁅R⁆ L') (n : ℕ) (a : ⋀[R]^n L) :
    ((nativeLiftedComplexMap R L f).f n).hom (ULift.up a) =
      ULift.up (exteriorPower.map n f.toLinearMap a) := by
  simp only [nativeLiftedComplexMap, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, complexLiftComparisonIso_hom_f, complexLiftComparisonIso_inv_f,
    nativeComplexMap_f, ModuleCat.hom_ofHom, exteriorULiftEquiv_apply,
      exteriorULiftEquiv_symm_apply]
  change ULift.up (exteriorPower.map n (LieLift.downEquiv.{u,w,max u v w} R L').toLinearMap
      (exteriorPower.map n (LieLift.map.{u,v,w,max u v w} f).toLinearMap
        (exteriorPower.map n (LieLift.downEquiv.{u,v,max u v w} R L).symm.toLinearMap a))) = _
  congr 1
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have h : (LieLift.downEquiv.{u,w,max u v w} R L').toLinearMap.comp
      ((LieLift.map.{u,v,w,max u v w} f).toLinearMap.comp
        (LieLift.downEquiv.{u,v,max u v w} R L).symm.toLinearMap) = f.toLinearMap := by
    apply LinearMap.ext
    intro x
    rfl
  have h' : ((LieLift.downEquiv.{u,w,max u v w} R L').toLinearMap.comp
      (LieLift.map.{u,v,w,max u v w} f).toLinearMap).comp
      (LieLift.downEquiv.{u,v,max u v w} R L).symm.toLinearMap = f.toLinearMap := by
    exact h
  exact congrArg (fun t => exteriorPower.map n t a) h'

/-- For an R-Lie homomorphism f:L→L′, lifting to H=max{u,v,w}
gives a comonoid morphism U^H C(L)→U^H C(L′), preserving
the transported coproduct and counit. -/
def nativeLiftedComplexMapIsComonHom (f : L →ₗ⁅R⁆ L') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max u v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max u v w} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v w} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max u v w} (R := R)
    letI : ComonObj (canonicalComplexULift.{u,v,max u v w} R L) :=
      liftedComonObj.{u,v,max u v w} R L
    letI : ComonObj (canonicalComplexULift.{u,w,max u v w} R L') :=
      liftedComonObj.{u,w,max u v w} R L'
    IsComonHom (nativeLiftedComplexMap R L f) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v w} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v w} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v w} (R := R)
  letI : ComonObj (canonicalChainData R (ULift.{max u v w} L)).complex :=
    nativeComonObj R (ULift.{max u v w} L)
  letI : ComonObj (canonicalChainData R (ULift.{max u v w} L')).complex :=
    nativeComonObj R (ULift.{max u v w} L')
  letI : ComonObj (canonicalComplexULift.{u,v,max u v w} R L) := liftedComonObj R L
  letI : ComonObj (canonicalComplexULift.{u,w,max u v w} R L') := liftedComonObj R L'
  letI : IsComonHom (complexLiftComparisonIso.{u,v,max u v w} R L).hom :=
    ComonObj.isComonHom_ofIso _
  letI : IsComonHom (complexLiftComparisonIso.{u,w,max u v w} R L').hom :=
    ComonObj.isComonHom_ofIso _
  letI : IsComonHom (nativeComplexMap R (ULift.{max u v w} L)
      (LieLift.map.{u,v,w,max u v w} f)) := nativeComplexMapIsComonHom _ _ _
  unfold nativeLiftedComplexMap
  infer_instance

/-- For an R-Lie homomorphism f:L→L′ at H=max{u,v,w}, the
common-height chain map F preserves the transported coaugmentations:
Fu_L^H=u_{L′}^H. -/
theorem nativeLiftedComplexMap_coaug (f : L →ₗ⁅R⁆ L') :
    liftedComplexCoaug.{u,v,max u v w} R L ≫ nativeLiftedComplexMap R L f =
      liftedComplexCoaug.{u,w,max u v w} R L' := by
  unfold liftedComplexCoaug nativeLiftedComplexMap
  rw [Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc (nativeComplexCoaug R (ULift.{max u v w} L)),
    nativeComplexMap_coaug]

/-- For an R-Lie map f:L→L′, the common-height chain map at
max{u,v,w} is bundled as a morphism of the transported exterior
coalgebras, without identifying the carrier universes v,w. -/
def nativeLiftedCoalgebraMap (f : L →ₗ⁅R⁆ L') :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u, max u v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u, max u v w} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v w} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalLinear.{u, max u v w} (R := R)
    liftedCoalgebra.{u,v,max u v w} R L ⟶ liftedCoalgebra.{u,w,max u v w} R L' := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max u v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max u v w} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max u v w} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max u v w} (R := R)
  letI : ComonObj (canonicalComplexULift.{u,v,max u v w} R L) :=
    liftedComonObj.{u,v,max u v w} R L
  letI : ComonObj (canonicalComplexULift.{u,w,max u v w} R L') :=
    liftedComonObj.{u,w,max u v w} R L'
  letI : IsComonHom (nativeLiftedComplexMap R L f) := nativeLiftedComplexMapIsComonHom R L f
  refine { hom := nativeLiftedComplexMap R L f, isComonHom_hom := ?_ }
  exact nativeLiftedComplexMapIsComonHom R L f

end IndependentWorlds

end ChevalleyEilenberg
