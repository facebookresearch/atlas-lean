/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.Algebra.Category.ModuleCat.NativeTorLongExactUniverse
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings
/-!
# Scalar tensor association with a restricted first coefficient

Let R→S→Q be maps of commutative rings in universe u whose composite is the specified map R→Q,
and let module carriers lie in W=max(u,v). For R-modules N,M, with N first, scalar cancellation
and association give the S-linear isomorphism U_g(Q⊗_R N)⊗_S(S⊗_R M)≅U_g(Q⊗_R(N⊗_R M)). It is
natural in M and sends (q⊗n)⊗(s⊗m) to qg(s)⊗(n⊗m).

The inverse comparison applies termwise to nonnegative chain complexes. Tensoring two such
complexes gives the commuting bicomplex with entry A_p⊗B_q, horizontal map d_A⊗id and vertical
map id⊗d_B. Tensoring by a fixed coefficient N on the left commutes with forming this bicomplex
through the module associator (N⊗A_p)⊗B_q≅N⊗(A_p⊗B_q). No flatness or finite-length condition
enters these tensor isomorphisms.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor
universe u v
namespace ModuleCat.UniverseTensor
/-- Let R,S,Q be commutative rings in universe u, with modules in W=max(u,v) for an independent
height v. Let a:R→S, f:R→Q and g:S→Q satisfy g∘a=f, and write H=U_g∘(Q⊗_R-). For R-modules N,M
in W, this is the S-linear isomorphism H(N)⊗_S(S⊗_R M)≅H(N⊗_R M). Its forward map sends
(q⊗n)⊗(s⊗m) to qg(s)⊗(n⊗m), and its inverse sends q⊗(n⊗m) to (q⊗n)⊗(1⊗m). The coefficient order
remains N before M. -/
def extendRestrictTensorComponentIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (a : R →+* S) (f : R →+* Q) (g : S →+* Q) (h : g.comp a = f)
    (N M : ModuleCat.{max u v} R) :
    ((tensoringLeft (ModuleCat.{max u v} S)).obj
        ((ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).obj N)).obj
          ((ModuleCat.extendScalars.{u,u,max u v} a).obj M) ≅
      (ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).obj (N ⊗ M) := by
  letI : Algebra R S := a.toAlgebra
  letI : Algebra S Q := g.toAlgebra
  letI : Algebra R Q := f.toAlgebra
  letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq' h.symm
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Q ⊗[R] N) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.assoc R R S Q N M).toModuleIso

/-- Let R,S,Q be commutative rings in universe u, with modules in W=max(u,v) for an independent
height v. Let a:R→S, f:R→Q and g:S→Q satisfy g∘a=f, and write H=U_g∘(Q⊗_R-). For a fixed
R-module N, the isomorphisms H(N)⊗_S(S⊗_R M)≅H(N⊗_R M) form a natural isomorphism of functors on
R-modules in W. If k:M→M′, then (id_{H(N)}⊗(S⊗k))≫c_{M′}.hom=c_M.hom≫H(id_N⊗k). -/
def extendRestrictTensorNatIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (a : R →+* S) (f : R →+* Q) (g : S →+* Q) (h : g.comp a = f)
    (N : ModuleCat.{max u v} R) :
    ModuleCat.extendScalars.{u,u,max u v} a ⋙
        (tensoringLeft (ModuleCat.{max u v} S)).obj
          ((ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).obj N) ≅
      (tensoringLeft (ModuleCat.{max u v} R)).obj N ⋙
        (ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g) := by
  letI : Algebra R S := a.toAlgebra
  letI : Algebra S Q := g.toAlgebra
  letI : Algebra R Q := f.toAlgebra
  letI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq' h.symm
  exact NatIso.ofComponents (fun M => extendRestrictTensorComponentIso R S Q a f g h N M)
    (fun {X Y} k => by
      apply ModuleCat.hom_ext
      let cX := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Q ⊗[R] N) X ≪≫ₗ
        TensorProduct.AlgebraTensorModule.assoc R R S Q N X
      let cY := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S (Q ⊗[R] N) Y ≪≫ₗ
        TensorProduct.AlgebraTensorModule.assoc R R S Q N Y
      change cY.toLinearMap ∘ₗ TensorProduct.map (LinearMap.id (R := S) (M := Q ⊗[R] N))
          (k.hom.baseChange S) =
        ((k.hom.lTensor N).baseChange Q).restrictScalars S ∘ₗ cX.toLinearMap
      apply TensorProduct.ext
      apply LinearMap.ext
      intro z
      apply LinearMap.ext
      intro sm
      induction z using TensorProduct.inductionOn with
      | tmul q n =>
        induction sm using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add z₁ z₂ h₁ h₂ =>
          simp only [map_add]
          rw [h₁, h₂]
      | add z₁ z₂ h₁ h₂ =>
        simp only [map_add, LinearMap.add_apply]
        rw [h₁, h₂])

/-- Let R,S,Q be commutative rings in universe u, with modules in W=max(u,v) for an independent
height v. Let a:R→S, f:R→Q and g:S→Q satisfy g∘a=f, and write H=U_g∘(Q⊗_R-). For an R-module N
and a chain complex C of shape down ℕ in W, the inverse component comparisons give a chain
isomorphism H(N⊗_R C)≅H(N)⊗_S(S⊗_R C). In degree n it is the inverse of H(N)⊗_S(S⊗_R C_n)≅H(N⊗_R
C_n), and naturality makes it commute with all chain differentials. -/
def extendRestrictTensorComplexIso
    (R S Q : Type u) [CommRing R] [CommRing S] [CommRing Q]
    (a : R →+* S) (f : R →+* Q) (g : S →+* Q) (h : g.comp a = f)
    (N : ModuleCat.{max u v} R) (C : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    ((ModuleCat.extendScalars.{u,u,max u v} f ⋙ ModuleCat.restrictScalars.{max u v,u,u} g).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj
      ((((tensoringLeft (ModuleCat.{max u v} R)).obj N).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C) ≅
      ((((tensoringLeft (ModuleCat.{max u v} S)).obj
        ((ModuleCat.extendScalars.{u,u,max u v} f ⋙
          ModuleCat.restrictScalars.{max u v,u,u} g).obj N)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
            (((ModuleCat.extendScalars.{u,u,max u v} a).mapHomologicalComplex (ComplexShape.down ℕ)).obj C)) := by
  let e := extendRestrictTensorNatIso R S Q a f g h N
  exact ((NatIso.mapHomologicalComplex e (ComplexShape.down ℕ)).app C).symm

/-- Let R be commutative in universe u and A,B chain complexes of shape down ℕ with R-module terms
in W=max(u,v). This bicomplex has entry A_p⊗_R B_q at (p,q), horizontal differential d_A⊗id and
vertical differential id⊗d_B. The two differentials commute, giving shape (down ℕ,down ℕ). -/
def tensorBicomplex (R : Type u) [CommRing R]
    (A B : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) := by
  let F := curriedTensor (ModuleCat.{max u v} R)
  let : F.Additive := by dsimp [F]; infer_instance
  let : ∀ N : ModuleCat.{max u v} R, (F.obj N).Additive := fun N => CategoryTheory.tensorLeft_additive N
  exact ((F.mapBifunctorHomologicalComplex (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj A).obj B

/-- Let R be commutative in universe u, N an R-module and B a bicomplex of shape (down ℕ,down ℕ),
all in W=max(u,v). This bicomplex has entry N⊗_R B_{p,q}; its horizontal and vertical maps are
id_N tensored with the corresponding maps of B. Additivity preserves both chain structures. -/
def tensorLeftBicomplex (R : Type u) [CommRing R] (N : ModuleCat.{max u v} R)
    (B : HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    HomologicalComplex₂ (ModuleCat.{max u v} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ) := by
  let T := (tensoringLeft (ModuleCat.{max u v} R)).obj N
  let : T.Additive := CategoryTheory.tensoringLeft_additive N
  exact ((T.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj B

/-- Let R be commutative in universe u, N an R-module and A,B chain complexes of shape down ℕ, all
in W=max(u,v). The component associators (N⊗_R A_p)⊗_R B_q≅N⊗_R(A_p⊗_R B_q) define an
isomorphism from the tensor bicomplex of N⊗A with B to N tensored on the left of the tensor
bicomplex of A,B. Naturality of the associator preserves both horizontal and vertical
differentials. -/
def tensorLeftBicomplexAssociator (R : Type u) [CommRing R]
    (N : ModuleCat.{max u v} R) (A B : ChainComplex (ModuleCat.{max u v} R) ℕ) :
    tensorBicomplex R ((((tensoringLeft (ModuleCat.{max u v} R)).obj N).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj A) B ≅ tensorLeftBicomplex R N (tensorBicomplex R A B) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p => ?_) ?_
  · exact HomologicalComplex.Hom.isoOfComponents
      (fun q => α_ N (A.X p) (B.X q)) (fun q q' _ => by
        change (α_ N (A.X p) (B.X q)).hom ≫
            (𝟙 N ⊗ₘ (𝟙 (A.X p) ⊗ₘ B.d q q')) =
          (𝟙 (N ⊗ A.X p) ⊗ₘ B.d q q') ≫ (α_ N (A.X p) (B.X q')).hom
        exact (associator_naturality_right N (A.X p) (B.d q q')).symm)
  · intro p p' _
    apply HomologicalComplex.Hom.ext
    funext q
    change (α_ N (A.X p) (B.X q)).hom ≫
        (𝟙 N ⊗ₘ (A.d p p' ⊗ₘ 𝟙 (B.X q))) =
      ((𝟙 N ⊗ₘ A.d p p') ⊗ₘ 𝟙 (B.X q)) ≫ (α_ N (A.X p') (B.X q)).hom
    exact (associator_naturality_middle N (A.d p p') (B.X q)).symm

end ModuleCat.UniverseTensor
