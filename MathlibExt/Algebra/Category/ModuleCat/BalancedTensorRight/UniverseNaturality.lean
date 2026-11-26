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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.Universe
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientMapsAdditive
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.CoefficientIsomorphisms
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ExactPostcomposition
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.PrecompositionNaturality
public import MathlibExt.CategoryTheory.Functor.ComparisonTransport
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.TransportComparison

/-!
# Source-derived Tor with independent module and coefficient worlds

Let R,S be rings and B an (R,S)-bimodule, with commuting left R- and
right S-actions. For a right R-module X in world a and B in world b,
put Γ_z=max(r,a,b,z). The functor T_(n,z)(X,B) is the nth left derived
functor of −⊗_R ULift^Γ_z B in ModuleCat^Γ_z(Rᵒᵖ), evaluated at
ULift^Γ_z X. Derivation is in the right R-module source X.

Thus source resolutions are taken in a world containing R, while the
original source and coefficient worlds remain independent. The target
is ModuleCat^Γ_z(Sᵒᵖ); no bound on the ring world of S is imposed.
Degree zero identifies naturally with the lifted balanced tensor.

Bimodule maps act additively on these tensor and Tor functors and
preserve identities and composition. Their height comparisons commute
with coefficient maps and the degree-zero augmentation.
Two heights are compared after lifting both outputs to a common third
height, with identity, inverse and composition laws. Comparison with
Tor formed in the unlifted common world v separately requires R to be
small in v; this condition is imposed only on that source-world comparison.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped TensorProduct
universe zGlobal tGlobal rGlobal sGlobal aGlobal bGlobal
namespace ModuleCat.BalancedTensorRight
variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]
  (B : Type bGlobal) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

instance largeTensorFunctorAt_additive.{z, r, s, a, b} (R : Type r) (S : Type s)
    [Ring R] [Ring S] (B : Type b) [AddCommGroup B] [Module R B]
    [Module Sᵐᵒᵖ B] [SMulCommClass R Sᵐᵒᵖ B] :
    (largeTensorFunctorAt.{z, r, s, a, b} R S B).Additive :=
  tensorFunctor_additive R S (ULift.{max r a b z} B)

/-- For rings R,S and an (R,S)-bimodule B, the functor
T_(n,z):ModuleCat^a(Rᵒᵖ)→ModuleCat^Γ_z(Sᵒᵖ) is left derivation
of −⊗_R ULift^Γ_z B at the lifted source ULift^Γ_z X,
where Γ_z=max(r,a,b,z). The target ring world s is independent. -/
def torFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ ⋙
    torFunctor R S (ULift.{max r a b z} B) n

/-- For a right R-module X in world a and an (R,S)-bimodule B,
T_(n,z)(X,B) is the nth derived balanced tensor evaluated at
ULift^Γ_z X, with Γ_z=max(r,a,b,z).
It is a right S-module in carrier world Γ_z. -/
abbrev torObjAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ) :
    ModuleCat.{max r a b z} Sᵐᵒᵖ :=
  (torFunctorAt.{z, r, s, a, b} R S B n).obj X

/-- For a right R-linear map f:X→Y and an (R,S)-bimodule B,
lifting f to Γ_z and applying the nth derived tensor functor
gives T_(n,z)(X,B)→T_(n,z)(Y,B).
Derivation takes place in ModuleCat^Γ_z(Rᵒᵖ), Γ_z=max(r,a,b,z). -/
def torMapAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) {X Y : ModuleCat.{a} Rᵐᵒᵖ} (f : X ⟶ Y) :
    torObjAt.{z, r, s, a, b} R S B n X ⟶ torObjAt.{z, r, s, a, b} R S B n Y :=
  (torFunctorAt.{z, r, s, a, b} R S B n).map f

/-- For rings R,S and an (R,S)-bimodule B, right exactness
gives the natural isomorphism
T_(0,z)(X,B)≅ULift^Γ_z X⊗_R ULift^Γ_z B.
The source world a is arbitrary and Γ_z=max(r,a,b,z). -/
def torZeroIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    torFunctorAt.{z, r, s, a, b} R S B 0 ≅
      tensorFunctorAt.{z, r, s, a, b} R S B := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (torZeroIso R S (ULift.{max r a b z} B))

/-- For a right R-module X and an (R,S)-bimodule B,
the forward T_(0,z)(X,B)→ULift^Γ_z X⊗_R ULift^Γ_z B map
is the canonical degree-zero derived-to-self augmentation
evaluated at ULift^Γ_z X in the sufficient source category. -/
theorem torZeroIsoAt_hom_app.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (X : ModuleCat.{a} Rᵐᵒᵖ) :
    letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
    (torZeroIsoAt.{z, r, s, a, b} R S B).hom.app X =
      (tensorFunctor R S (ULift.{max r a b z} B)).fromLeftDerivedZero.app
        ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) := rfl

/-- For an (R,S)-bimodule B, a right R-module X and a
projective resolution P of ULift^Γ_z X in ModuleCat^Γ_z(Rᵒᵖ),
there is an isomorphism
T_(n,z)(X,B)≅H_n(P⊗_R ULift^Γ_z B).
The tensor is applied termwise and Γ_z=max(r,a,b,z). -/
def torResolutionIsoAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ)
    (P : ProjectiveResolution
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)) :
    torObjAt.{z, r, s, a, b} R S B n X ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{max r a b z} Sᵐᵒᵖ)
        (ComplexShape.down ℕ) n).obj
        (((largeTensorFunctorAt.{z, r, s, a, b} R S B).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj P.complex) :=
  P.isoLeftDerivedObj (tensorFunctor R S (ULift.{max r a b z} B)) n

section Coefficients

variable (B' : Type bGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B']
  (f : B →ₗ[R] B')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- For left R-modules B,B′ in world b and an R-linear map
f:B→B′, its height-Γ_z lift sends up(y) to up(f(y)).
It is the R-linear map ULift^Γ_z B→ULift^Γ_z B′,
where Γ_z=max(r,a,b,z). -/
def liftedCoefficientMapAt.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B']
    (f : B →ₗ[R] B') :
    ULift.{max r a b z} B →ₗ[R] ULift.{max r a b z} B' :=
  (ULift.moduleEquiv : ULift.{max r a b z} B' ≃ₗ[R] B').symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv : ULift.{max r a b z} B ≃ₗ[R] B).toLinearMap)

/-- For an R-linear map f:B→B′ satisfying
f(s•y)=s•f(y) for s∈Sᵒᵖ, its height-Γ_z lift satisfies the
same Sᵒᵖ-equivariance equation.
The coefficient carriers are lifted by up and down. -/
theorem liftedCoefficientMapAt_outer.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (s : Sᵐᵒᵖ) (x : ULift.{max r a b z} B) :
    liftedCoefficientMapAt.{z, r, a, b} R B B' f (s • x) =
      s • liftedCoefficientMapAt.{z, r, a, b} R B B' f x :=
  congrArg ULift.up (hf s x.down)

/-- For rings R,S and a bimodule map f:B→B′, applying the
lifted coefficient map gives a natural transformation
−⊗_R ULift^Γ_z B→−⊗_R ULift^Γ_z B′
on right R-modules already in world Γ_z=max(r,a,b,z). -/
def largeTensorCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    largeTensorFunctorAt.{z, r, s, a, b} R S B ⟶
      largeTensorFunctorAt.{z, r, s, a, b} R S B' :=
  tensorCoefficientTransformation R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)

/-- For an (R,S)-bimodule map f:B→B′ and n≥0, deriving the
common-height tensor transformation gives
L_n(−⊗_R ULift^Γ_z B)→L_n(−⊗_R ULift^Γ_z B′)
in the sufficient right R-module source category. -/
def largeTorCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    torFunctor R S (ULift.{max r a b z} B) n ⟶
      torFunctor R S (ULift.{max r a b z} B') n :=
  NatTrans.leftDerived (largeTensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf) n

/-- For rings R,S and a bimodule map f:B→B′, the natural
coefficient transformation on source world a sends
ULift^Γ_z X⊗_R ULift^Γ_z B to ULift^Γ_z X⊗_R ULift^Γ_z B′.
It fixes the source factor and lifts f on the coefficient factor. -/
def tensorCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    tensorFunctorAt.{z, r, s, a, b} R S B ⟶
      tensorFunctorAt.{z, r, s, a, b} R S B' :=
  Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (tensorCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))

/-- For a bimodule map f:B→B′, the chosen-height tensor
transformation has pure value
[up(x)⊗up(y)]↦[up(x)⊗up(f(y))].
The source is a right R-module and the outputs are right S-modules. -/
theorem tensorCoefficientTransformationAt_mk.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf).app X).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B') (ULift.up x) (ULift.up (f y)) := by
  change (tensorCoefficientMap R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)).hom _ = _
  exact tensorCoefficientMap_mk R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
    ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)
    (ULift.up x) (ULift.up y)

/-- For an (R,S)-bimodule map f:B→B′ and n≥0, the derived
coefficient transformation gives
T_(n,z)(X,B)→T_(n,z)(X,B′), naturally in the right R-module X.
It is derived in Γ_z before precomposing with source lifting. -/
def torCoefficientTransformationAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    torFunctorAt.{z, r, s, a, b} R S B n ⟶
      torFunctorAt.{z, r, s, a, b} R S B' n :=
  Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (torCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf) n)

/-- For a bimodule map f:B→B′ and a projective resolution P
of ULift^Γ_z X, the coefficient map on T_(n,z) is conjugate
to H_n(P⊗_R ULift^Γ_z f) through the two resolution comparisons.
It fixes P and applies the lifted coefficient map termwise. -/
theorem torCoefficientTransformationAt_resolution.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (n : ℕ) (X : ModuleCat.{a} Rᵐᵒᵖ)
    (P : ProjectiveResolution
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)) :
    (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n).app X =
      (torResolutionIsoAt R S B n X P).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{max r a b z} Sᵐᵒᵖ)
          (ComplexShape.down ℕ) n).map
          ((NatTrans.mapHomologicalComplex
            (tensorCoefficientTransformation R S
              (ULift.{max r a b z} B) (ULift.{max r a b z} B')
              (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
              (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))
            (ComplexShape.down ℕ)).app P.complex) ≫
          (torResolutionIsoAt R S B' n X P).inv :=
  torCoefficientTransformation_resolution R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf) n P

/-- For a bimodule map f:B→B′, the degree-zero isomorphisms
T_(0,z)(−,B)≅Tensor_z(−,B) commute with the coefficient
transformations. Taking Tor's degree-zero map then the tensor
comparison equals taking that comparison then the tensor
coefficient map. -/
theorem torZeroIsoAt_naturality_coefficient.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf 0 ≫
        (torZeroIsoAt R S B').hom =
      (torZeroIsoAt R S B).hom ≫
        tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf := by
  have h := NatTrans.leftDerivedZeroIsoSelf_hom_naturality_functor
    (tensorCoefficientTransformation R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf))
  exact congrArg (Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)) h

/-- For left R-modules B,B′, the height-Γ_z lift of the
zero R-linear map is zero.
Its value on every lifted coefficient is the lifted zero. -/
theorem liftedCoefficientMapAt_zero.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] :
    liftedCoefficientMapAt.{z, r, a, b} R B B' (0 : B →ₗ[R] B') = 0 := by
  apply LinearMap.ext
  intro x
  rfl

/-- For R-linear maps f,g:B→B′, their lifted maps satisfy
lift(f+g)=lift(f)+lift(g) on ULift^Γ_z B.
This is additivity over arbitrary, possibly noncommutative R. -/
theorem liftedCoefficientMapAt_add.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B']
    (f : B →ₗ[R] B') (g : B →ₗ[R] B') :
    liftedCoefficientMapAt.{z, r, a, b} R B B' (f + g) =
      liftedCoefficientMapAt.{z, r, a, b} R B B' f + liftedCoefficientMapAt.{z, r, a, b} R B B' g := by
  apply LinearMap.ext
  intro x
  rfl

/-- For (R,S)-bimodules B,B′, the coefficient transformation
associated with the zero bimodule map is the zero natural
transformation of the chosen-height tensor functors. -/
theorem tensorCoefficientTransformationAt_zero.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' 0
      (by intro s x; simp only [LinearMap.zero_apply, smul_zero]) = 0 := by
  unfold tensorCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_zero, tensorCoefficientTransformation_zero]
  rfl

/-- For bimodule maps f,g:B→B′, the chosen-height tensor
transformations satisfy Tensor(f+g)=Tensor(f)+Tensor(g).
Their common right R-module source is lifted to Γ_z. -/
theorem tensorCoefficientTransformationAt_add.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (g : B →ₗ[R] B')
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B), g (s • x) = s • g x) :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' (f + g)
        (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add]) =
      tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf +
        tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' g hg := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R
    (ULift.{max r a b z} X) (ULift.{max r a b z} B)
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  have hSum := tensorCoefficientTransformationAt_mk.{z, r, s, a, b} R S B B'
    (f + g) (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add]) X x y
  have hF := tensorCoefficientTransformationAt_mk.{z, r, s, a, b} R S B B' f hf X x y
  have hG := tensorCoefficientTransformationAt_mk.{z, r, s, a, b} R S B B' g hg X x y
  change ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' (f + g)
      (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add])).app X).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) = _
  rw [hSum]
  change TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
      (ULift.{max r a b z} B') (ULift.up x) (ULift.up ((f + g) y)) =
    ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf).app X).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)) +
    ((tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' g hg).app X).hom
      (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
        (ULift.{max r a b z} B) (ULift.up x) (ULift.up y))
  rw [hF, hG, LinearMap.add_apply]
  exact (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
    (ULift.{max r a b z} B') (ULift.up x)).map_add _ _

/-- For (R,S)-bimodules B,B′ and n≥0, the Tor coefficient
transformation of the zero map is zero in every source module.
This is an equality of natural transformations of T_(n,z). -/
theorem torCoefficientTransformationAt_zero.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' 0
      (by intro s x; simp only [LinearMap.zero_apply, smul_zero]) n = 0 := by
  unfold torCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_zero, torCoefficientTransformation_zero]
  rfl

/-- For bimodule maps f,g:B→B′ and n≥0, the derived
coefficient transformations satisfy
Tor_(n,z)(f+g)=Tor_(n,z)(f)+Tor_(n,z)(g).
The assertion is additive and preserves the noncommutative ring scope. -/
theorem torCoefficientTransformationAt_add.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (g : B →ₗ[R] B')
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B), g (s • x) = s • g x) (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' (f + g)
        (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add]) n =
      torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n +
        torCoefficientTransformationAt.{z, r, s, a, b} R S B B' g hg n := by
  apply NatTrans.ext
  funext X
  have h := torCoefficientTransformation_add R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt.{z, r, a, b} R B B' g)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' g hg) n
  have hX := congrArg
    (fun α => α.app ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)) h
  change (torCoefficientTransformation R S (ULift.{max r a b z} B)
      (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' (f + g))
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' (f + g)
        (by intro s x; simp only [LinearMap.add_apply, hf, hg, smul_add])) n).app
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) =
    (torCoefficientTransformation R S (ULift.{max r a b z} B)
      (ULift.{max r a b z} B') (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf) n).app
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) +
    (torCoefficientTransformation R S (ULift.{max r a b z} B)
      (ULift.{max r a b z} B') (liftedCoefficientMapAt.{z, r, a, b} R B B' g)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' g hg) n).app
      ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)
  simpa only [liftedCoefficientMapAt_add, NatTrans.app_add] using hX

/-- For (R,S)-bimodules B,B′ and n≥0, sending a bimodule map
to its Tor coefficient transformation is a homomorphism of
additive groups. It preserves zero, sums and integer multiples
of R-linear right S-equivariant coefficient maps. -/
def torCoefficientAddHomAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B'] (n : ℕ) :
    coefficientMapGroup R S B B' →+
      (torFunctorAt.{z, r, s, a, b} R S B n ⟶
        torFunctorAt.{z, r, s, a, b} R S B' n) where
  toFun f := torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f.val f.property n
  map_zero' := torCoefficientTransformationAt_zero R S B B' n
  map_add' f g := torCoefficientTransformationAt_add R S B B'
    f.val f.property g.val g.property n

end Coefficients

section CoefficientIdentityComposition

/-- For a left R-module B, the lift of id_B to ULift^Γ_z B
is the identity R-linear map.
It sends up(y) to the same up(y). -/
theorem liftedCoefficientMapAt_id.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B] :
    liftedCoefficientMapAt.{z, r, a, b} R B B LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro x
  rfl

/-- For an (R,S)-bimodule B, the tensor coefficient
transformation of id_B is id on Tensor_z(−,B).
It fixes both factors of every lifted balanced class. -/
theorem tensorCoefficientTransformationAt_id.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id
      (fun _ _ => rfl) = 𝟙 (tensorFunctorAt.{z, r, s, a, b} R S B) := by
  unfold tensorCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_id, tensorCoefficientTransformation_id]
  rfl

/-- For an (R,S)-bimodule B and n≥0, the coefficient
transformation of id_B is id on T_(n,z)(−,B).
This holds after derivation in the sufficient source world. -/
theorem torCoefficientTransformationAt_id.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B LinearMap.id
      (fun _ _ => rfl) n = 𝟙 (torFunctorAt.{z, r, s, a, b} R S B n) := by
  unfold torCoefficientTransformationAt
  simp only [liftedCoefficientMapAt_id, torCoefficientTransformation_id]
  rfl

variable (B' B'' : Type bGlobal) [AddCommGroup B'] [AddCommGroup B'']
  [Module R B'] [Module R B''] [Module Sᵐᵒᵖ B'] [Module Sᵐᵒᵖ B'']
  [SMulCommClass R Sᵐᵒᵖ B'] [SMulCommClass R Sᵐᵒᵖ B'']
  (f : B →ₗ[R] B') (g : B' →ₗ[R] B'')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)
  (hg : ∀ (sGlobal : Sᵐᵒᵖ) (x : B'), g (sGlobal • x) = sGlobal • g x)

/-- For R-linear maps f:B→B′ and g:B′→B″, the lifted maps
satisfy lift(g∘f)=lift(g)∘lift(f).
All coefficient carriers use the same chosen height Γ_z. -/
theorem liftedCoefficientMapAt_comp.{z, r, a, b} (R : Type r) [Ring R] (B : Type b) [AddCommGroup B] [Module R B]
    (B' : Type b) [AddCommGroup B'] [Module R B']
    (B'' : Type b) [AddCommGroup B''] [Module R B'']
    (f : B →ₗ[R] B')
    (g : B' →ₗ[R] B'') :
    liftedCoefficientMapAt.{z, r, a, b} R B B'' (g.comp f) =
      (liftedCoefficientMapAt.{z, r, a, b} R B' B'' g).comp (liftedCoefficientMapAt.{z, r, a, b} R B B' f) := by
  apply LinearMap.ext
  intro x
  rfl

/-- For bimodule maps f:B→B′ and g:B′→B″, applying the
tensor transformation for f and then g equals that for g∘f:
Tensor(g)∘Tensor(f)=Tensor(g∘f).
The right R-module source and balanced factor order are fixed. -/
theorem tensorCoefficientTransformationAt_comp.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (B'' : Type b) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
    [SMulCommClass R Sᵐᵒᵖ B'']
    (f : B →ₗ[R] B')
    (g : B' →ₗ[R] B'')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B'), g (s • x) = s • g x) :
    tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf ≫
        tensorCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg =
      tensorCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) := by
  apply NatTrans.ext
  funext X
  have h := congrArg
    (fun α => α.app ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X))
    (tensorCoefficientTransformation_comp R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
      (ULift.{max r a b z} B'') (liftedCoefficientMapAt.{z, r, a, b} R B' B'' g)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B' B'' g hg))
  exact h

/-- For bimodule maps f:B→B′ and g:B′→B″, the derived maps
satisfy Tor_(n,z)(g)∘Tor_(n,z)(f)=Tor_(n,z)(g∘f)
for every n≥0, naturally in the source right R-module. -/
theorem torCoefficientTransformationAt_comp.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (B'' : Type b) [AddCommGroup B''] [Module R B''] [Module Sᵐᵒᵖ B'']
    [SMulCommClass R Sᵐᵒᵖ B'']
    (f : B →ₗ[R] B')
    (g : B' →ₗ[R] B'')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x)
    (hg : ∀ (s : Sᵐᵒᵖ) (x : B'), g (s • x) = s • g x) (n : ℕ) :
    torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n ≫
        torCoefficientTransformationAt.{z, r, s, a, b} R S B' B'' g hg n =
      torCoefficientTransformationAt.{z, r, s, a, b} R S B B'' (g.comp f)
        (fun s x => (congrArg g (hf s x)).trans (hg s (f x))) n := by
  apply NatTrans.ext
  funext X
  have h := congrArg
    (fun α => α.app ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X))
    (torCoefficientTransformation_comp R S
      (ULift.{max r a b z} B) (ULift.{max r a b z} B')
      (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
      (ULift.{max r a b z} B'') (liftedCoefficientMapAt.{z, r, a, b} R B' B'' g)
      (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B' B'' g hg) n)
  exact h

end CoefficientIdentityComposition

section CoefficientHeight

variable (B' : Type bGlobal) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
  [SMulCommClass R Sᵐᵒᵖ B'] (f : B →ₗ[R] B')
  (hf : ∀ (sGlobal : Sᵐᵒᵖ) (x : B), f (sGlobal • x) = sGlobal • f x)

/-- For a bimodule map f:B→B′ and Γ_z≤Γ′=max(r,a,b,z,t),
the square comparing higher-height tensor after input lifting
with lifted lower-height tensor commutes with f.
Both paths lift the source and apply f to the coefficient. -/
theorem tensorHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) :
    Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
        (largeTensorCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf) ≫
      (tensorHeightIsoAt.{t, z, r, s, a, b} R S B').hom =
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom ≫
      Functor.whiskerRight (largeTensorCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply TensorProduct.Balanced.addHom_ext ℤ R
    (ULift.{max r a b z t} X) (ULift.{max r a b z t} B)
  intro x y
  obtain ⟨x⟩ := x
  obtain ⟨y⟩ := y
  change ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B').hom.app X).hom
      ((tensorCoefficientMap R S
        (ULift.{max r a b z t} B) (ULift.{max r a b z t} B')
        (liftedCoefficientMapAt.{max z t, r, a, b} R B B' f)
        (liftedCoefficientMapAt_outer.{max z t, r, s, a, b} R S B B' f hf)
        ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
          (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y))) =
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
      ((largeTensorCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf).app X)).hom
      (((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom.app X).hom
        (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
          (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y)))
  have hHigh := tensorCoefficientMap_mk R S
    (ULift.{max r a b z t} B) (ULift.{max r a b z t} B')
    (liftedCoefficientMapAt.{max z t, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{max z t, r, s, a, b} R S B B' f hf)
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)
    (ULift.up x) (ULift.up y)
  have hHeightB := tensorHeightIsoAt_hom_mk.{t, z, r, s, a, b} R S B X x y
  have hHeightB' := tensorHeightIsoAt_hom_mk.{t, z, r, s, a, b} R S B' X x (f y)
  have hLow := tensorCoefficientMap_mk R S
    (ULift.{max r a b z} B) (ULift.{max r a b z} B')
    (liftedCoefficientMapAt.{z, r, a, b} R B B' f)
    (liftedCoefficientMapAt_outer.{z, r, s, a, b} R S B B' f hf)
    X x (ULift.up y)
  have hHigh' := congrArg ((tensorHeightIsoAt.{t, z, r, s, a, b} R S B').hom.app X).hom hHigh
  have hHeight' := congrArg
    ((ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ).map
      ((largeTensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf).app X)).hom hHeightB
  exact hHigh'.trans (hHeightB'.trans
    ((congrArg ULift.up hLow).symm.trans hHeight'.symm))

end CoefficientHeight

section ParameterFunctors

/-- For rings R,S, the category of (R,S)-bimodules in world b
maps to functors ModuleCat^a(Rᵒᵖ)→ModuleCat^Γ_z(Sᵒᵖ)
by B↦Tensor_z(−,B). Its morphisms are the lifted coefficient
tensor transformations. -/
def tensorCoefficientFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] :
    coefficientCategory.{r, s, b} R S ⥤
      (ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ) ⋙
    coefficientTensorFunctor R S ⋙
    AdditiveFunctor.forget (ModuleCat.{max r a b z} Rᵐᵒᵖ)
      (ModuleCat.{max r a b z} Sᵐᵒᵖ) ⋙
    (Functor.whiskeringLeft (ModuleCat.{a} Rᵐᵒᵖ)
      (ModuleCat.{max r a b z} Rᵐᵒᵖ) (ModuleCat.{max r a b z} Sᵐᵒᵖ)).obj
        (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)

/-- For rings R,S and n≥0, the category of (R,S)-bimodules
in world b maps to functors from right R-modules in world a
to right S-modules in world Γ_z by B↦T_(n,z)(−,B).
Coefficient morphisms act by the derived transformations. -/
def torCoefficientFunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] (n : ℕ) :
    coefficientCategory.{r, s, b} R S ⥤
      (ModuleCat.{a} Rᵐᵒᵖ ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ) ⋙
    coefficientTorFunctor.{r, s, max r a b z} R S n ⋙
    (Functor.whiskeringLeft (ModuleCat.{a} Rᵐᵒᵖ)
      (ModuleCat.{max r a b z} Rᵐᵒᵖ) (ModuleCat.{max r a b z} Sᵐᵒᵖ)).obj
        (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)

/-- For rings R,S, the chosen-height tensor is a bifunctor
in right R-modules in world a and (R,S)-bimodules in world b,
with values in ModuleCat^Γ_z(Sᵒᵖ).
Its two morphism actions are input maps and coefficient maps. -/
def tensorBifunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] :
    ModuleCat.{a} Rᵐᵒᵖ ⥤
      (coefficientCategory.{r, s, b} R S ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  (tensorCoefficientFunctorAt.{z, r, s, a, b} R S).flip

/-- For rings R,S and n≥0, T_(n,z) is a bifunctor in the
right R-module source and the (R,S)-bimodule coefficient.
The independent source and coefficient worlds are a,b, and
the output carrier world is Γ_z=max(r,a,b,z). -/
def torBifunctorAt.{z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S] (n : ℕ) :
    ModuleCat.{a} Rᵐᵒᵖ ⥤
      (coefficientCategory.{r, s, b} R S ⥤ ModuleCat.{max r a b z} Sᵐᵒᵖ) :=
  (torCoefficientFunctorAt.{z, r, s, a, b} R S n).flip

end ParameterFunctors

section Heights

/-- For rings R,S and an (R,S)-bimodule B, put
Γ_z=max(r,a,b,z), Γ′=max(r,a,b,z,t).
There is a natural isomorphism from the lift to Γ′ of
L_n(−⊗_R ULift^Γ_z B) to
L_n(−⊗_R ULift^Γ′ B) after source lifting Γ_z→Γ′.
Source lifting preserves projectives because Γ_z contains R. -/
def largeTorHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torFunctor R S (ULift.{max r a b z} B) n ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ ⋙
        torFunctor R S (ULift.{max r a b z t} B) n := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : U.PreservesProjectiveObjects := inferInstance
  exact Functor.leftDerivedTransportIso U V F G
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B) n


/-- For rings R,S and an (R,S)-bimodule B, the output lift
of T_(n,z):ModuleCat^a(Rᵒᵖ)→ModuleCat^Γ_z(Sᵒᵖ)
is naturally isomorphic to T_(n,max(z,t)) at Γ′.
The source remains the original carrier category in world a. -/
def torHeightIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torFunctorAt.{z, r, s, a, b} R S B n ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      torFunctorAt.{max z t, r, s, a, b} R S B n := Functor.precompositionComparisonIso
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (torFunctor R S (ULift.{max r a b z} B) n)
    (torFunctor R S (ULift.{max r a b z t} B) n)
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n)
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)


/-- For rings R,S and an (R,S)-bimodule B, lifting the
output of Tensor_z to Γ′=max(r,a,b,z,t) gives the natural
isomorphism with Tensor_(max(z,t)) on the same source world a. -/
def tensorHeightFacadeIsoAt.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctorAt.{z, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ ≅
      tensorFunctorAt.{max z t, r, s, a, b} R S B := Functor.precompositionComparisonIso
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (largeTensorFunctorAt.{z, r, s, a, b} R S B)
    (largeTensorFunctorAt.{max z t, r, s, a, b} R S B)
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).symm
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)


/-- For a right R-module X and an (R,S)-bimodule B, the
forward Tor height component is the sufficient-world derived
comparison at ULift^Γ_z X followed by the higher derived
functor applied to ULift^Γ′(ULift^Γ_z X)→ULift^Γ′X.
This flattening retains the underlying source coefficient. -/
theorem torHeightIsoAt_hom_app.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ)
    (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (torHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app X =
      (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app
          ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) ≫
        (torFunctor R S (ULift.{max r a b z t} B) n).map
          ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a}
            Rᵐᵒᵖ).hom.app X) := by
  exact Functor.precompositionComparisonIso_hom_app
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (torFunctor R S (ULift.{max r a b z} B) n)
    (torFunctor R S (ULift.{max r a b z t} B) n)
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n)
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)
    X


/-- For a right R-module X and an (R,S)-bimodule B, the
forward independent-source tensor height map first uses the
inverse common-height tensor comparison, then flattens
ULift^Γ′(ULift^Γ_z X) to ULift^Γ′X.
The output is the higher lifted-factor balanced tensor. -/
theorem tensorHeightFacadeIsoAt_hom_app.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) :
    (tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom.app X =
      (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).inv.app
          ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) ≫
        (largeTensorFunctorAt.{max z t, r, s, a, b} R S B).map
          ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a}
            Rᵐᵒᵖ).hom.app X) := by
  exact Functor.precompositionComparisonIso_hom_app
    (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
    (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ)
    (largeTensorFunctorAt.{z, r, s, a, b} R S B)
    (largeTensorFunctorAt.{max z t, r, s, a, b} R S B)
    (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).symm
    (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ)
    X


/-- For a right R-module X and an (R,S)-bimodule B, the
height map Γ_z→Γ′ sends
up([up_Γ_z(x)⊗up_Γ_z(y)]) to
[up_Γ′(x)⊗up_Γ′(y)].
The left side is the lift of the lower-height whole output. -/
theorem tensorHeightFacadeIsoAt_hom_mk.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (X : ModuleCat.{a} Rᵐᵒᵖ) (x : X) (y : B) :
    ((tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom.app X).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y))) =
      TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z t} X)
        (ULift.{max r a b z t} B) (ULift.up x) (ULift.up y) := by
  rw [tensorHeightFacadeIsoAt_hom_app]
  change (tensorMap R S (ULift.{max r a b z t} B)
      ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app X)).hom
      (((tensorHeightIsoAt.{t, z, r, s, a, b} R S B).inv.app
        ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X)).hom
        (ULift.up (TensorProduct.Balanced.mk ℤ R (ULift.{max r a b z} X)
          (ULift.{max r a b z} B) (ULift.up x) (ULift.up y)))) = _
  have hInv := tensorHeightIsoAt_inv_mk.{t, z, r, s, a, b} R S B
    ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X) (ULift.up x) y
  have hInv' := congrArg
    (tensorMap R S (ULift.{max r a b z t} B)
      ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app X)).hom hInv
  have hMap := tensorMap_mk R S (ULift.{max r a b z t} B)
    (A := ((ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ) ⋙
      ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ).obj X)
    (A' := (ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X)
    ((ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ).hom.app X)
    (ULift.up (ULift.up x)) (ULift.up y)
  exact hInv'.trans hMap

/-- For an (R,S)-bimodule B, the common-height derived
comparison in degree zero, followed by the higher tensor
augmentation and the forward tensor height comparison, equals
the lift of the lower tensor augmentation.
The source is the sufficient category at Γ_z and Γ′=max(r,a,b,z,t). -/
theorem largeTorHeightIsoAt_hom_augmentation.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
    let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B 0).hom ≫
        Functor.whiskerLeft U G.fromLeftDerivedZero ≫
          (tensorHeightIsoAt.{t, z, r, s, a, b} R S B).hom =
      Functor.whiskerRight (largeTensorFunctorAt.{z, r, s, a, b} R S B).fromLeftDerivedZero
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let e := tensorHeightIsoAt.{t, z, r, s, a, b} R S B
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : U.PreservesProjectiveObjects := inferInstance
  change (Functor.leftDerivedTransportIso U V F G e 0).hom ≫
    Functor.whiskerLeft U G.fromLeftDerivedZero ≫ e.hom = Functor.whiskerRight F.fromLeftDerivedZero V
  rw [← Category.assoc, Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


/-- For rings R,S and an (R,S)-bimodule B, let h_Tor and
h_Tensor be the independent-source height comparisons.
The degree-zero maps satisfy
θ_Γ′∘h_Tor=h_Tensor∘ULift(θ_Γ_z),
where θ identifies Tor_0 with the chosen-height balanced tensor. -/
theorem torHeightIsoAt_hom_zero.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    (torHeightIsoAt.{t, z, r, s, a, b} R S B 0).hom ≫
        (torZeroIsoAt.{max z t, r, s, a, b} R S B).hom =
      Functor.whiskerRight (torZeroIsoAt.{z, r, s, a, b} R S B).hom
          (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
        (tensorHeightFacadeIsoAt.{t, z, r, s, a, b} R S B).hom := by
  let W := ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ
  let W' := ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let e := tensorHeightIsoAt.{t, z, r, s, a, b} R S B
  let s := ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a} Rᵐᵒᵖ
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : U.PreservesProjectiveObjects := inferInstance
  have h := Functor.precompositionComparisonIso_naturality
    W W' U V (F.leftDerived 0) (G.leftDerived 0)
    (Functor.leftDerivedTransportIso U V F G e 0) s
    F.fromLeftDerivedZero G.fromLeftDerivedZero e.symm
    (Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero U V F G e).symm
  change (Functor.precompositionComparisonIso W W' U V (F.leftDerived 0)
    (G.leftDerived 0) (Functor.leftDerivedTransportIso U V F G e 0) s).hom ≫
      Functor.whiskerLeft W' G.fromLeftDerivedZero =
    Functor.whiskerRight (Functor.whiskerLeft W F.fromLeftDerivedZero) V ≫
      (Functor.precompositionComparisonIso W W' U V F G e.symm s).hom
  exact h.symm


/-- For a bimodule map f:B→B′, the natural isomorphism
between lifted lower-height derived tensor and higher-height
derived tensor after source lifting commutes with the
coefficient Tor maps in every degree n≥0. -/
theorem largeTorHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    Functor.whiskerRight (largeTorCoefficientTransformationAt.{z, r, s, a, b}
        R S B B' f hf n)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
      (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B' n).hom =
    (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom ≫
      Functor.whiskerLeft (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ)
        (largeTorCoefficientTransformationAt.{max z t, r, s, a, b}
          R S B B' f hf n) := by
  let F := largeTensorFunctorAt.{z, r, s, a, b} R S B
  let F' := largeTensorFunctorAt.{z, r, s, a, b} R S B'
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let G' := largeTensorFunctorAt.{max z t, r, s, a, b} R S B'
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : U.PreservesProjectiveObjects := inferInstance
  let α := largeTensorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf
  let β := largeTensorCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf
  let e := tensorHeightIsoAt.{t, z, r, s, a, b} R S B
  let e' := tensorHeightIsoAt.{t, z, r, s, a, b} R S B'
  exact Functor.leftDerivedTransportIso_naturality U V F G e α β e'
    (tensorHeightIsoAt_natural_coefficient R S B B' f hf) n


/-- For a bimodule map f:B→B′, raising the output height of
T_(n,z) and then applying the higher coefficient transformation
equals applying the lower coefficient transformation and then
raising the output height. The source carrier world a is fixed. -/
theorem torHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B]
    (B' : Type b) [AddCommGroup B'] [Module R B'] [Module Sᵐᵒᵖ B']
    [SMulCommClass R Sᵐᵒᵖ B']
    (f : B →ₗ[R] B')
    (hf : ∀ (s : Sᵐᵒᵖ) (x : B), f (s • x) = s • f x) (n : ℕ) :
    Functor.whiskerRight (torCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n)
        (ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ) ≫
      (torHeightIsoAt.{t, z, r, s, a, b} R S B' n).hom =
    (torHeightIsoAt.{t, z, r, s, a, b} R S B n).hom ≫
      torCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf n := by
  apply NatTrans.ext
  funext X
  let A := (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj X
  let U := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r a b z t, max r a b z} Sᵐᵒᵖ
  let G := largeTensorFunctorAt.{max z t, r, s, a, b} R S B
  let G' := largeTensorFunctorAt.{max z t, r, s, a, b} R S B'
  let ε := (ModuleCat.uliftFunctorCompIso.{max r a b z, max r a b z t, a}
    Rᵐᵒᵖ).hom.app X
  let α := largeTorCoefficientTransformationAt.{z, r, s, a, b} R S B B' f hf n
  let β := largeTorCoefficientTransformationAt.{max z t, r, s, a, b} R S B B' f hf n
  let e := (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B n).hom.app A
  let e' := (largeTorHeightIsoAt.{t, z, r, s, a, b} R S B' n).hom.app A
  have hCore : V.map (α.app A) ≫ e' = e ≫ β.app (U.obj A) := by
    have h := congrArg (fun γ => γ.app A)
      (largeTorHeightIsoAt_natural_coefficient.{t, z, r, s, a, b} R S B B' f hf n)
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using h
  have hFlat : (G.leftDerived n).map ε ≫ β.app
        ((ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X) =
      β.app (U.obj A) ≫ (G'.leftDerived n).map ε := β.naturality ε
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [torHeightIsoAt_hom_app, torHeightIsoAt_hom_app]
  change V.map (α.app A) ≫ (e' ≫ (G'.leftDerived n).map ε) =
    (e ≫ (G.leftDerived n).map ε) ≫ β.app
      ((ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X)
  calc
    _ = (e ≫ β.app (U.obj A)) ≫ (G'.leftDerived n).map ε := by
      have h := congrArg (fun f => f ≫ (G'.leftDerived n).map ε) hCore
      exact (Category.assoc (V.map (α.app A)) e' ((G'.leftDerived n).map ε)).symm.trans h
    _ = _ := by
      have h := congrArg (fun f => e ≫ f) hFlat.symm
      exact (Category.assoc e (β.app (U.obj A)) ((G'.leftDerived n).map ε)).trans
        (h.trans (Category.assoc e ((G.leftDerived n).map ε)
          (β.app ((ModuleCat.uliftFunctor.{max r a b z t, a} Rᵐᵒᵖ).obj X))).symm)


end Heights

section SufficientOriginalWorld

universe vGlobal

local instance originalOppositeSmall (R : Type rGlobal) [Small.{vGlobal} R] :
    Small.{vGlobal} Rᵐᵒᵖ :=
  small_of_injective MulOpposite.unop_injective

variable (C : Type vGlobal) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
  [SMulCommClass R Sᵐᵒᵖ C] [Small.{vGlobal} R]

/-- For rings R,S and an (R,S)-bimodule C with source and
coefficient carriers in world v, assume R is small in v.
Then lifting the output of Tor formed in ModuleCat^v(Rᵒᵖ)
gives a natural isomorphism to T_(n,z), computed in
Γ=max(r,v,z). No smallness condition is imposed on S. -/
def torOriginalLiftIsoAt.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R] (n : ℕ) :
    torFunctor R S C n ⋙ ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ ≅
      torFunctorAt.{z, r, s, v, v} R S C n := by
  let F := tensorFunctor R S C
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S C
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact U
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact V
  letI : U.PreservesProjectiveObjects := inferInstance
  exact Functor.leftDerivedTransportIso U V F G
    (tensorOriginalLiftIsoAt.{z, r, s, v} R S C) n


/-- For an (R,S)-bimodule C in world v, assume R is small in v.
In degree zero, the unlifted-to-sufficient Tor comparison,
the chosen-height Tor-to-tensor map and the output tensor
comparison compose to the lift of the unlifted Tor-to-tensor map. -/
theorem torOriginalLiftIsoAt_hom_zero.{z, r, s, v} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (C : Type v) [AddCommGroup C] [Module R C] [Module Sᵐᵒᵖ C]
    [SMulCommClass R Sᵐᵒᵖ C] [Small.{v} R] :
    (torOriginalLiftIsoAt.{z, r, s, v} R S C 0).hom ≫
        (torZeroIsoAt.{z, r, s, v, v} R S C).hom ≫
          (tensorOriginalLiftIsoAt.{z, r, s, v} R S C).hom =
      Functor.whiskerRight (torZeroIso R S C).hom
        (ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ) := by
  let F := tensorFunctor R S C
  let G := largeTensorFunctorAt.{z, r, s, v, v} R S C
  let U := ModuleCat.uliftFunctor.{max r v z, v} Rᵐᵒᵖ
  let V := ModuleCat.uliftFunctor.{max r v z, v} Sᵐᵒᵖ
  let : U.PreservesHomology := Functor.preservesHomologyOfExact U
  let : V.PreservesHomology := Functor.preservesHomologyOfExact V
  let : U.PreservesProjectiveObjects := inferInstance
  let e := tensorOriginalLiftIsoAt.{z, r, s, v} R S C
  change (Functor.leftDerivedTransportIso U V F G e 0).hom ≫
    Functor.whiskerLeft U G.fromLeftDerivedZero ≫ e.hom = Functor.whiskerRight F.fromLeftDerivedZero V
  have h := congrArg (fun α => α ≫ e.hom)
    (Functor.leftDerivedTransportIso_hom_fromLeftDerivedZero U V F G e)
  exact (Category.assoc (Functor.leftDerivedTransportIso U V F G e 0).hom
      (Functor.whiskerLeft U G.fromLeftDerivedZero) e.hom).symm.trans
    (h.trans ((Category.assoc (Functor.whiskerRight F.fromLeftDerivedZero V) e.inv e.hom).trans
      ((congrArg (fun α => Functor.whiskerRight F.fromLeftDerivedZero V ≫ α) e.inv_hom_id).trans
        (Category.comp_id _))))


end SufficientOriginalWorld

section CommonHeightCoherence

/-- For rings R,S and an (R,S)-bimodule B, two height parameters
z,t give a natural isomorphism between T_(n,z) and T_(n,t)
after both outputs are lifted to Ω=max(r,a,b,z,t,u).
Their original source category in world a is the same. -/
def torCommonHeightIsoAt.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torFunctorAt.{z, r, s, a, b} R S B n ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ ≅
      torFunctorAt.{t, r, s, a, b} R S B n ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ :=
  torHeightIsoAt.{max t u, z, r, s, a, b} R S B n ≪≫
    (torHeightIsoAt.{max z u, t, r, s, a, b} R S B n).symm

/-- For rings R,S and an (R,S)-bimodule B, the underived
tensor outputs at z,t become naturally isomorphic after
lifting each whole output to Ω=max(r,a,b,z,t,u).
The comparison retains the source and coefficient factors. -/
def tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorFunctorAt.{z, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ ≅
      tensorFunctorAt.{t, r, s, a, b} R S B ⋙
        ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ :=
  tensorHeightFacadeIsoAt.{max t u, z, r, s, a, b} R S B ≪≫
    (tensorHeightFacadeIsoAt.{max z u, t, r, s, a, b} R S B).symm

/-- For an (R,S)-bimodule B and n≥0, the common-output
comparison of T_(n,z) with itself is the identity.
Both sides are lifted to Ω=max(r,a,b,z,u). -/
theorem torCommonHeightIsoAt_refl.{u, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torCommonHeightIsoAt.{u, z, z, r, s, a, b} R S B n = Iso.refl _ := by
  apply Iso.ext
  simp only [torCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id, Iso.refl_hom]

/-- For an (R,S)-bimodule B and two heights z,t, the
comparison T_(n,z)→T_(n,t) after common output lifting
has the reversed comparison as inverse.
Both functors are viewed in Ω=max(r,a,b,z,t,u). -/
theorem torCommonHeightIsoAt_symm.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    (torCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B n).symm =
      torCommonHeightIsoAt.{u, z, t, r, s, a, b} R S B n := by
  apply Iso.ext
  simp only [torCommonHeightIsoAt, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]

/-- For an (R,S)-bimodule B and three heights z,t,u,
the comparison z→t followed by t→u equals z→u after
all outputs are lifted to Ω=max(r,a,b,z,t,u).
This is an equality of natural isomorphisms in every degree n≥0. -/
theorem torCommonHeightIsoAt_trans.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] (n : ℕ) :
    torCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B n ≪≫
        torCommonHeightIsoAt.{z, u, t, r, s, a, b} R S B n =
      torCommonHeightIsoAt.{t, u, z, r, s, a, b} R S B n := by
  apply Iso.ext
  simp only [torCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- For an (R,S)-bimodule B, comparing Tensor_z with itself
after lifting its whole output to Ω=max(r,a,b,z,u) gives
the identity natural isomorphism. -/
theorem tensorCommonHeightIsoAt_refl.{u, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorCommonHeightIsoAt.{u, z, z, r, s, a, b} R S B = Iso.refl _ := by
  apply Iso.ext
  simp only [tensorCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id, Iso.refl_hom]

/-- For an (R,S)-bimodule B, the comparison of Tensor_z with
Tensor_t after their common whole-output lift is inverse to
the comparison in the reverse direction. -/
theorem tensorCommonHeightIsoAt_symm.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    (tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B).symm =
      tensorCommonHeightIsoAt.{u, z, t, r, s, a, b} R S B := by
  apply Iso.ext
  simp only [tensorCommonHeightIsoAt, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv]

/-- For an (R,S)-bimodule B and three heights z,t,u, the
underived tensor comparison z→t followed by t→u equals
z→u in Ω=max(r,a,b,z,t,u).
The identity of the original balanced factors is preserved. -/
theorem tensorCommonHeightIsoAt_trans.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B ≪≫
        tensorCommonHeightIsoAt.{z, u, t, r, s, a, b} R S B =
      tensorCommonHeightIsoAt.{t, u, z, r, s, a, b} R S B := by
  apply Iso.ext
  simp only [tensorCommonHeightIsoAt, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- For an (R,S)-bimodule B and two heights z,t, the
common-output Tor comparison in degree zero commutes with
the two Tor-to-tensor maps and the common-output tensor
comparison. All four functors have output world Ω=max(r,a,b,z,t,u). -/
theorem torCommonHeightIsoAt_hom_zero.{u, t, z, r, s, a, b} (R : Type r) (S : Type s) [Ring R] [Ring S]
    (B : Type b) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
    [SMulCommClass R Sᵐᵒᵖ B] :
    (torCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B 0).hom ≫
        Functor.whiskerRight (torZeroIsoAt.{t, r, s, a, b} R S B).hom
          (ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ) =
      Functor.whiskerRight (torZeroIsoAt.{z, r, s, a, b} R S B).hom
          (ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ) ≫
        (tensorCommonHeightIsoAt.{u, t, z, r, s, a, b} R S B).hom := by
  let ez := torHeightIsoAt.{max t u, z, r, s, a, b} R S B 0
  let et := torHeightIsoAt.{max z u, t, r, s, a, b} R S B 0
  let qz := tensorHeightFacadeIsoAt.{max t u, z, r, s, a, b} R S B
  let qt := tensorHeightFacadeIsoAt.{max z u, t, r, s, a, b} R S B
  let az := Functor.whiskerRight (torZeroIsoAt.{z, r, s, a, b} R S B).hom
    (ModuleCat.uliftFunctor.{max r a b z t u, max r a b z} Sᵐᵒᵖ)
  let augmentationT := Functor.whiskerRight (torZeroIsoAt.{t, r, s, a, b} R S B).hom
    (ModuleCat.uliftFunctor.{max r a b z t u, max r a b t} Sᵐᵒᵖ)
  let ac := (torZeroIsoAt.{max z t u, r, s, a, b} R S B).hom
  have hz : ez.hom ≫ ac = az ≫ qz.hom := torHeightIsoAt_hom_zero R S B
  have ht : et.hom ≫ ac = augmentationT ≫ qt.hom := torHeightIsoAt_hom_zero R S B
  apply (cancel_mono qt.hom).1
  change ((ez.hom ≫ et.inv) ≫ augmentationT) ≫ qt.hom =
    (az ≫ (qz.hom ≫ qt.inv)) ≫ qt.hom
  calc
    _ = ez.hom ≫ et.inv ≫ (augmentationT ≫ qt.hom) := by simp only [Category.assoc]
    _ = ez.hom ≫ et.inv ≫ (et.hom ≫ ac) := congrArg (fun f => ez.hom ≫ et.inv ≫ f) ht.symm
    _ = ez.hom ≫ ac := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = az ≫ qz.hom := hz
    _ = _ := by
      symm
      calc
        (az ≫ (qz.hom ≫ qt.inv)) ≫ qt.hom =
            az ≫ (qz.hom ≫ (qt.inv ≫ qt.hom)) := by
          exact (Category.assoc az (qz.hom ≫ qt.inv) qt.hom).trans
            (congrArg (fun α => az ≫ α) (Category.assoc qz.hom qt.inv qt.hom))
        _ = az ≫ qz.hom := by
          rw [qt.inv_hom_id, Category.comp_id]

end CommonHeightCoherence

end ModuleCat.BalancedTensorRight
