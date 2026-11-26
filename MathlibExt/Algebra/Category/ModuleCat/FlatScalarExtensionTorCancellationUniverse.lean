/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FlatScalarExtensionResolutionUniverse
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseCompatibility

/-!
# Tensor cancellation and flat scalar extension for Tor

Let R,S be commutative rings in independent universes u,v, with coefficient modules in
W=max(u,v,w). For a ring homomorphism f:R→S, an S-module N and an R-module X, scalar tensor
cancellation gives the R-linear isomorphism U(N⊗_S(S⊗_R X))≅U(N)⊗_R X. It sends n⊗(s⊗x) to
(s•n)⊗x and is natural in X.

If S is flat over R, scalar extension sends a projective resolution of X to a projective
resolution of S⊗_R X. The tensor cancellation isomorphism and exact scalar restriction then give
U(Tor_q^S(N,S⊗_R X))≅Tor_q^R(U(N),X) for every q∈ℕ. The coefficient N is an arbitrary S-module;
the flatness hypothesis is on S over R. The ring universes and lift height w are independent.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v w

open scoped ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/-- Let R,S be commutative rings in independent universes u,v, w an independent common lift height,
and W=max(u,v,w). For a ring homomorphism f:R→S, N an S-module and X an R-module with carriers
in W, this is the R-linear isomorphism U(N⊗_S(S⊗_R X))≅U(N)⊗_R X. Its forward map sends n⊗(s⊗x)
to (s•n)⊗x, and its inverse sends n⊗x to n⊗(1⊗x). The R-actions are induced by f. -/
def scalarTensorCancellationIso (f : R →+* S)
    (N : ModuleCat.{max u v w} S) (X : ModuleCat.{max u v w} R) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,max v w} (R := R)
    letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.tensorStructure.{v,max u w} (R := S)
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
    (restrictScalars.{max u v w,u,v} f).obj (N ⊗ (extendScalars.{u,v,max u v w} f).obj X) ≅
      (restrictScalars.{max u v w,u,v} f).obj N ⊗ X := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,max v w} (R := R)
  letI : MonoidalCategoryStruct (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.tensorStructure.{v,max u w} (R := S)
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
  letI : Algebra R S := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N X).restrictScalars R).toModuleIso

/-- Let R,S be commutative rings in independent universes u,v, w an independent common lift height,
and W=max(u,v,w). For f:R→S and an S-module N in W, the isomorphisms U(N⊗_S(S⊗_R X))≅U(N)⊗_R X
form a natural isomorphism of functors on R-modules in W. For h:X→Y, the cancellation maps
c_X,c_Y satisfy U(id_N⊗(id_S⊗h))≫c_Y.hom=c_X.hom≫(id_{U(N)}⊗h). -/
def scalarTensorCancellationNatIso (f : R →+* S) (N : ModuleCat.{max u v w} S) :
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
    extendScalars.{u,v,max u v w} f ⋙ (tensoringLeft (ModuleCat.{max u v w} S)).obj N ⋙
      restrictScalars.{max u v w,u,v} f ≅
      (tensoringLeft (ModuleCat.{max u v w} R)).obj ((restrictScalars.{max u v w,u,v} f).obj N) := by
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
  exact NatIso.ofComponents (fun X => scalarTensorCancellationIso R S f N X) (by
    intro X Y g
    let : Algebra R S := f.toAlgebra
    let : Module R N := Module.compHom N f
    let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have h := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
      R S S (M := N) g.hom
    exact congrArg (fun k : (N ⊗[S] (S ⊗[R] X)) →ₗ[S] (N ⊗[R] Y) => k z) h.symm)


/-- Let R,S be commutative rings in independent universes u,v, w an independent common lift height,
and W=max(u,v,w). Assume S is an R-algebra and flat as an R-module. Write F(X)=S⊗_R X for scalar
extension and U for restriction to R. For an arbitrary S-module N and R-module X in W and q∈ℕ,
this is the canonical R-module isomorphism c_{N,X,q}:U(Tor_q^S(N,F(X)))≅Tor_q^R(U(N),X). It is
obtained by extending a projective resolution of X, applying scalar tensor cancellation
termwise, and comparing homology through exact restriction of scalars. -/
def flatScalarExtensionTorCancellationIso [Algebra R S] [Module.Flat R S]
    (N : ModuleCat.{max u v w} S) (X : ModuleCat.{max u v w} R) (q : ℕ) :
    letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w} (R := S)
    (restrictScalars.{max u v w,u,v} (algebraMap R S)).obj
      (((Tor (ModuleCat.{max u v w} S) q).obj N).obj
        ((extendScalars.{u,v,max u v w} (algebraMap R S)).obj X)) ≅
      ((Tor (ModuleCat.{max u v w} R) q).obj
        ((restrictScalars.{max u v w,u,v} (algebraMap R S)).obj N)).obj X := by
  letI : MonoidalCategory (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,max v w} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalCategory.{v,max u w} (R := S)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,max v w} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v w} S) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{v,max u w} (R := S)
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u,v,max u v w} (algebraMap R S)
  let G : ModuleCat.{max u v w} S ⥤ ModuleCat.{max u v w} R :=
    restrictScalars.{max u v w,u,v} (algebraMap R S)
  letI : F.PreservesHomology := ModuleCat.preservesHomology_extendScalars_of_flat.{u,v,w} (algebraMap R S) (by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance)
  let P := projectiveResolution X
  let Q := flatScalarExtensionProjectiveResolution R S P
  let L := (tensoringLeft (ModuleCat.{max u v w} R)).obj (G.obj N)
  let L' := (tensoringLeft (ModuleCat.{max u v w} S)).obj N
  let K := (L'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  exact G.mapIso (Q.isoLeftDerivedObj L' q) ≪≫
    ((K.sc q).mapHomologyIso G).symm ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v w} R)
        (ComplexShape.down ℕ) q).mapIso
          ((NatIso.mapHomologicalComplex
            (scalarTensorCancellationNatIso R S (algebraMap R S) N)
              (ComplexShape.down ℕ)).app P.complex) ≪≫
                (P.isoLeftDerivedObj L q).symm

end ModuleCat.UniverseTensor
