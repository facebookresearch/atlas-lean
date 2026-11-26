/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.TensorFunctor
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight.UniverseNaturality
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Square
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Tor maps under simultaneous endpoint ring and bimodule change

Let φ:R→R′ and ψ:S→S′ be maps of arbitrary rings. Let B,B′ be
(R,S)- and (R′,S′)-bimodules, and let f:B→B′ intertwine both
endpoint actions along φ,ψ. A right-module map
g:A→Res_(φᵒᵖ)(A′) gives the tensor map [x⊗y]↦[g(x)⊗f(y)].

When the two source module categories in a common carrier world v
have projective resolutions, this induces
Tor_n^R(A,B)→Res_(ψᵒᵖ)(Tor_n^(R′)(A′,B′)).
A projective R-resolution maps to the exact restriction of a chosen
R′-resolution; no preservation of projectives by restriction is
required. The result is independent of the augmentation-compatible
comparison and natural in source, target and coefficients.

For independent carrier worlds a,a′,b,b′, lift to
Γ=max(r,r′,a,a′,b,b′,z). The same construction gives a
ψᵒᵖ-semilinear Tor map, retaining all original carriers.
Neither outer-ring world s,s′ is included in Γ.
In degree zero the map agrees with the ordered balanced tensor map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MulOpposite
open ModuleCat.BalancedTensorRight
open scoped TensorProduct

universe rGlobal rGlobal' rGlobal'' sGlobal sGlobal' sGlobal'' vGlobal aGlobal aGlobal' aGlobal'' bGlobal bGlobal'
  bGlobal'' zGlobal tGlobal

namespace ModuleCat.Bimodule.Tensor

variable (R : Type rGlobal) (S : Type sGlobal) [Ring R] [Ring S]

private theorem restriction_preservesHomology
    {P : Type rGlobal} {Q : Type rGlobal'} [Ring P] [Ring Q] (f : P →+* Q) :
    (ModuleCat.restrictScalars.{vGlobal} f).PreservesHomology :=
  Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} f)

/-- For an (R,S)-bimodule B and right R-modules in a common
carrier world v, the balanced tensor functor is naturally
isomorphic to the tensor functor in the coefficient family.
The comparison retains every balanced class and right S-action. -/
def nativeTensorFunctorIso (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) :
    functor R S B ≅ (coefficientTensorObj R S B).obj := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  refine NatIso.ofComponents (fun A => Iso.refl _) ?_
  intro A A' g
  apply hom_ext R S B A
  intro x y
  change (map R S B g).hom (pairing R S B A x y) =
    (ModuleCat.BalancedTensorRight.tensorMap R S B g).hom
      (TensorProduct.Balanced.mk ℤ R A B x y)
  rw [map_pairing, ModuleCat.BalancedTensorRight.tensorMap_mk]
  rfl

/-- For an (R,S)-bimodule B and a right R-module A,
the tensor-functor comparison sends [x⊗y] to the same
balanced class [x⊗y]. -/
theorem nativeTensorFunctorIso_hom_pairing
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (x : A) (y : B) :
    ((nativeTensorFunctorIso R S B).hom.app A).hom (pairing R S B A x y) =
      pairing R S B A x y := rfl

/-- For an (R,S)-bimodule B, t∈Sᵒᵖ and a pure tensor class,
the forward tensor-presentation comparison sends
t•[x⊗y] to t•[x⊗y] in the coefficient-family presentation.
It is right S-linear. -/
theorem nativeTensorFunctorIso_hom_smul_pairing
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
    (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (t : Sᵐᵒᵖ) (x : A) (y : B) :
    ((nativeTensorFunctorIso R S B).hom.app A).hom
        ((obj R S B A).isModule.smul t (pairing R S B A x y)) =
      (((coefficientTensorObj R S B).obj).obj A).isModule.smul t
        (pairing R S B A x y) := by
  have h := ((nativeTensorFunctorIso R S B).hom.app A).hom.map_smul' t
    (pairing R S B A x y)
  exact h.trans (congrArg
    ((((coefficientTensorObj R S B).obj).obj A).isModule.smul t)
    (nativeTensorFunctorIso_hom_pairing R S B A x y))

/-- For an (R,S)-bimodule B, the inverse tensor-presentation
comparison preserves t•[x⊗y] for t∈Sᵒᵖ.
It identifies the same right S-module action on the balanced quotient. -/
theorem nativeTensorFunctorIso_inv_smul_pairing
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
    (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (t : Sᵐᵒᵖ) (x : A) (y : B) :
    ((nativeTensorFunctorIso R S B).inv.app A).hom
        ((((coefficientTensorObj R S B).obj).obj A).isModule.smul t
          (pairing R S B A x y)) =
      (obj R S B A).isModule.smul t (pairing R S B A x y) := by
  have h := ((nativeTensorFunctorIso R S B).inv.app A).hom.map_smul' t
    (pairing R S B A x y)
  have hPure : ((nativeTensorFunctorIso R S B).inv.app A).hom
      (pairing R S B A x y) = pairing R S B A x y := rfl
  exact h.trans (congrArg ((obj R S B A).isModule.smul t) hPure)

section Rings

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']
  (φ : R →+* R') (ψ : S →+* S')
  (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
  (B' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S')
  (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')

/-- For φ:R→R′, ψ:S→S′ and a coefficient map f:B→B′
intertwining both endpoints, the natural tensor transformation is
Res_(φᵒᵖ)(−)⊗_R B→Res_(ψᵒᵖ)((−)⊗_(R′)B′).
Its source variable is a right R′-module. -/
def tensorRingChangeTransformation :
    ModuleCat.restrictScalars φ.op ⋙ (coefficientTensorObj R S B).obj ⟶
      (coefficientTensorObj R' S' B').obj ⋙ ModuleCat.restrictScalars ψ.op :=
  Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) (nativeTensorFunctorIso R S B).inv ≫
    ringChangeTransformation R S φ ψ B B' f ≫
    Functor.whiskerRight (nativeTensorFunctorIso R' S' B').hom (ModuleCat.restrictScalars ψ.op)

/-- For a right R′-module A′ and a coefficient map f:B→B′
along φ,ψ, the tensor ring-change transformation sends
[x⊗y] to [x⊗f(y)].
The target is balanced over R′ and restricted to a right S-module. -/
theorem tensorRingChangeTransformation_pairing
    (A : ModuleCat.{vGlobal} R'ᵐᵒᵖ) (x : A) (y : B) :
    ((tensorRingChangeTransformation R S φ ψ B B' f).app A).hom
        (pairing R S B ((ModuleCat.restrictScalars φ.op).obj A) x y) =
      pairing R' S' B' A x (f.hom y) := rfl

/-- For projective resolutions P of A over R and Q of A′
over R′, and g:A→Res_(φᵒᵖ)(A′), there is a chain comparison
P→Res_(φᵒᵖ)(Q) compatible with their augmentations over g.
The restricted target resolution is exact; its terms are not
required to be projective over R. -/
def restrictedResolutionComparison
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') :
    {aGlobal : P.complex ⟶
        ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          Q.complex //
      aGlobal ≫ Functor.mapChainAugmentation (ModuleCat.restrictScalars φ.op) Q.π =
        P.π ≫ (ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map g} := by
  let U := ModuleCat.restrictScalars.{vGlobal} φ.op
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : QuasiIso (Functor.mapChainAugmentation U Q.π) :=
    Functor.mapChainAugmentation_quasiIso U Q.π
  exact P.comparisonToAugmentedExact
    ((U.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    (Functor.mapChainAugmentation U Q.π) g

/-- For an endpoint-intertwining coefficient map f:B→B′
and a chain map a:P→Res_(φᵒᵖ)(Q), the tensor comparison gives
P⊗_R B→Res_(ψᵒᵖ)(Q⊗_(R′)B′).
It applies a to the resolution factor and f to the coefficient. -/
def tensorRingChangeResolutionMap
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex) :
    (((coefficientTensorObj R S B).obj).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        P.complex ⟶
      ((ModuleCat.restrictScalars ψ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((((coefficientTensorObj R' S' B').obj).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Q.complex) :=
  (((coefficientTensorObj R S B).obj).mapHomologicalComplex (ComplexShape.down ℕ)).map aGlobal ≫
    (Functor.mapSquareHomologicalComplex (ModuleCat.restrictScalars φ.op)
      (ModuleCat.restrictScalars ψ.op) (coefficientTensorObj R S B).obj
      (coefficientTensorObj R' S' B').obj
      (tensorRingChangeTransformation R S φ ψ B B' f)).app Q.complex

/-- For a chain comparison a:P→Res_(φᵒᵖ)(Q) and
coefficient map f:B→B′, the degree-i tensor chain map sends
[x⊗y] to [a_i(x)⊗f(y)].
The output coefficient action is restricted along ψᵒᵖ. -/
theorem tensorRingChangeResolutionMap_pairing
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex) (i : ℕ) (x : P.complex.X i) (y : B) :
    ((tensorRingChangeResolutionMap R S φ ψ B B' f P Q aGlobal).f i).hom
        (pairing R S B (P.complex.X i) x y) =
      pairing R' S' B' (Q.complex.X i) ((aGlobal.f i).hom x) (f.hom y) := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  change ((tensorRingChangeTransformation R S φ ψ B B' f).app (Q.complex.X i)).hom
      ((ModuleCat.BalancedTensorRight.tensorMap R S B (aGlobal.f i)).hom
        (TensorProduct.Balanced.mk ℤ R (P.complex.X i) B x y)) = _
  have hMap := ModuleCat.BalancedTensorRight.tensorMap_mk R S B (aGlobal.f i) x y
  have hScalar := tensorRingChangeTransformation_pairing R S φ ψ B B' f
    (Q.complex.X i) (show Q.complex.X i from (aGlobal.f i).hom x) y
  exact (congrArg ((tensorRingChangeTransformation R S φ ψ B B' f).app
    (Q.complex.X i)).hom hMap).trans hScalar

section Derived

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{vGlobal} R'ᵐᵒᵖ)]

/-- Assume projective resolutions in the common-world right
R- and R′-module categories. For an endpoint coefficient map f,
there is a natural transformation
Tor_n^R(Res_(φᵒᵖ)(−),B)→Res_(ψᵒᵖ)(Tor_n^(R′)(−,B′))
for every n≥0. -/
def torRingChangeTransformation (n : ℕ) :
    ModuleCat.restrictScalars φ.op ⋙ (coefficientTorFunctor R S n).obj B ⟶
      (coefficientTorFunctor R' S' n).obj B' ⋙ ModuleCat.restrictScalars ψ.op := by
  let U := ModuleCat.restrictScalars.{vGlobal} φ.op
  let V := ModuleCat.restrictScalars.{vGlobal} ψ.op
  let F := (coefficientTensorObj R S B).obj
  let G := (coefficientTensorObj R' S' B').obj
  letI : U.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  change U ⋙ F.leftDerived n ⟶ G.leftDerived n ⋙ V
  exact Functor.leftDerivedSquareHom U V F G
    (tensorRingChangeTransformation R S φ ψ B B' f) n

/-- For g:A→Res_(φᵒᵖ)(A′) and an endpoint coefficient
map f:B→B′, the canonical map is
Tor_n^R(A,B)→Res_(ψᵒᵖ)(Tor_n^(R′)(A′,B′)).
The common carrier-world source categories are assumed to
have projective resolutions. -/
def torRingChangeMap (n : ℕ) {A : ModuleCat.{vGlobal} Rᵐᵒᵖ}
    {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ} (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') :
    ((coefficientTorFunctor R S n).obj B).obj A ⟶
      (ModuleCat.restrictScalars ψ.op).obj
        (((coefficientTorFunctor R' S' n).obj B').obj A') :=
  ((coefficientTorFunctor R S n).obj B).map g ≫
    (torRingChangeTransformation R S φ ψ B B' f n).app A'

/-- For coefficient map f along φ,ψ and source map
g:A→Res_(φᵒᵖ)(A′), the underlying Tor map is
ψᵒᵖ-semilinear from the right S-module Tor_n^R(A,B) to
the right S′-module Tor_n^(R′)(A′,B′).
Projective resolutions are available in both source categories. -/
def torRingChangeSemilinearMap (n : ℕ) {A : ModuleCat.{vGlobal} Rᵐᵒᵖ}
    {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ} (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') :
    (((coefficientTorFunctor R S n).obj B).obj A).carrier →ₛₗ[ψ.op]
      (((coefficientTorFunctor R' S' n).obj B').obj A').carrier :=
  (ModuleCat.semilinearMapAddEquiv ψ.op
    (((coefficientTorFunctor R S n).obj B).obj A)
    (((coefficientTorFunctor R' S' n).obj B').obj A')).symm
      (torRingChangeMap R S φ ψ B B' f n g)

/-- For the canonical Tor change map Θ along φ,ψ,
Θ(t•x)=ψᵒᵖ(t)•Θ(x) for every t∈Sᵒᵖ.
The coefficient and source maps satisfy their endpoint
semilinearity equations. -/
theorem torRingChangeSemilinearMap_smul (n : ℕ) {A : ModuleCat.{vGlobal} Rᵐᵒᵖ}
    {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ} (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (sGlobal : Sᵐᵒᵖ) (x : ((coefficientTorFunctor R S n).obj B).obj A) :
    torRingChangeSemilinearMap R S φ ψ B B' f n g (sGlobal • x) =
      ψ.op sGlobal • torRingChangeSemilinearMap R S φ ψ B B' f n g x :=
  (torRingChangeSemilinearMap R S φ ψ B B' f n g).map_smulₛₗ sGlobal x

/-- For projective resolutions P,Q and an augmentation-compatible
a:P→Res_(φᵒᵖ)(Q) over g, the canonical Tor change is the
homology map of P⊗_R B→Res_(ψᵒᵖ)(Q⊗_(R′)B′),
conjugated by the two resolution comparisons and the exact
output-restriction homology isomorphism. -/
theorem torRingChangeMap_resolution (n : ℕ)
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A')
    (aGlobal : P.complex ⟶
      ((ModuleCat.restrictScalars φ.op).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        Q.complex)
    (ha : aGlobal ≫ Functor.mapChainAugmentation (ModuleCat.restrictScalars φ.op) Q.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map g) :
    torRingChangeMap R S φ ψ B B' f n g =
      (P.isoLeftDerivedObj (coefficientTensorObj R S B).obj n).hom ≫
        HomologicalComplex.homologyMap
          (tensorRingChangeResolutionMap R S φ ψ B B' f P Q aGlobal) n ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
          (ModuleCat.restrictScalars ψ.op)).hom.app
            ((((coefficientTensorObj R' S' B').obj).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj Q.complex) ≫
        (ModuleCat.restrictScalars ψ.op).map
          (Q.isoLeftDerivedObj (coefficientTensorObj R' S' B').obj n).inv := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  exact Functor.leftDerivedSquareHom_eq_with_source_lift
    (ModuleCat.restrictScalars φ.op) (ModuleCat.restrictScalars ψ.op)
    (coefficientTensorObj R S B).obj (coefficientTensorObj R' S' B').obj
    (tensorRingChangeTransformation R S φ ψ B B' f) n g P Q aGlobal ha

/-- For projective resolutions P,Q over the source and target
rings and g:A→Res_(φᵒᵖ)(A′), the canonical Tor map is computed
by the augmentation-compatible projective-source comparison
constructed from P,Q,g. Its tensor chain map changes the
coefficient by f and the resolution by that comparison. -/
theorem torRingChangeMap_canonical_resolution (n : ℕ)
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A')
    (P : ProjectiveResolution A) (Q : ProjectiveResolution A') :
    torRingChangeMap R S φ ψ B B' f n g =
      (P.isoLeftDerivedObj (coefficientTensorObj R S B).obj n).hom ≫
        HomologicalComplex.homologyMap
          (tensorRingChangeResolutionMap R S φ ψ B B' f P Q
            (restrictedResolutionComparison R φ P Q g).val) n ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n
          (ModuleCat.restrictScalars ψ.op)).hom.app
            ((((coefficientTensorObj R' S' B').obj).mapHomologicalComplex
              (ComplexShape.down ℕ)).obj Q.complex) ≫
        (ModuleCat.restrictScalars ψ.op).map
          (Q.isoLeftDerivedObj (coefficientTensorObj R' S' B').obj n).inv :=
  torRingChangeMap_resolution R S φ ψ B B' f n g P Q
    (restrictedResolutionComparison R φ P Q g).val
    (restrictedResolutionComparison R φ P Q g).property

/-- For g:A→Res_(φᵒᵖ)(A′) and a right R-linear h:A₀→A,
the Tor change satisfies
Θ(g)∘Tor_n^R(h,B)=Θ(g∘h).
The endpoint coefficient map f is fixed. -/
theorem torRingChangeMap_naturality_source (n : ℕ)
    {A₀ A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') (h : A₀ ⟶ A) :
    ((coefficientTorFunctor R S n).obj B).map h ≫ torRingChangeMap R S φ ψ B B' f n g =
      torRingChangeMap R S φ ψ B B' f n (h ≫ g) := by
  unfold torRingChangeMap
  rw [Functor.map_comp, Category.assoc]

/-- For g:A→Res_(φᵒᵖ)(A′) and a right R′-linear h:A′→A″,
the Tor change followed by restricted Tor(h,B′) equals
the change for Res_(φᵒᵖ)(h)∘g.
The output restriction is along ψᵒᵖ. -/
theorem torRingChangeMap_naturality_target (n : ℕ)
    {A : ModuleCat.{vGlobal} Rᵐᵒᵖ} {A' A'' : ModuleCat.{vGlobal} R'ᵐᵒᵖ}
    (g : A ⟶ (ModuleCat.restrictScalars φ.op).obj A') (h : A' ⟶ A'') :
    torRingChangeMap R S φ ψ B B' f n g ≫
        (ModuleCat.restrictScalars ψ.op).map
          (((coefficientTorFunctor R' S' n).obj B').map h) =
      torRingChangeMap R S φ ψ B B' f n
        (g ≫ (ModuleCat.restrictScalars φ.op).map h) := by
  unfold torRingChangeMap
  rw [Functor.map_comp, Category.assoc]
  exact congrArg (fun aGlobal => ((coefficientTorFunctor R S n).obj B).map g ≫ aGlobal)
    ((torRingChangeTransformation R S φ ψ B B' f n).naturality h).symm

end Derived

/-- For a source bimodule map h:B₀→B and an endpoint map
f:B→Res(B′), tensoring by h then changing rings by f
equals the tensor ring-change transformation for f∘h. -/
theorem tensorRingChangeTransformation_coefficient_left
    {B₀ : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S} (g : B₀ ⟶ B) :
    Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) (coefficientTensorTransformation R S g) ≫
        tensorRingChangeTransformation R S φ ψ B B' f =
      tensorRingChangeTransformation R S φ ψ B₀ B' (g ≫ f) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B₀ ((ModuleCat.restrictScalars φ.op).obj A)
  intro x y
  rfl

/-- For an endpoint coefficient map f:B→Res(B′) and a
target bimodule map h:B′→B″, changing rings by f then
applying h equals the tensor ring-change transformation
for Res(h)∘f. -/
theorem tensorRingChangeTransformation_coefficient_right
    {B'' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S'} (g : B' ⟶ B'') :
    tensorRingChangeTransformation R S φ ψ B B' f ≫
        Functor.whiskerRight (coefficientTensorTransformation R' S' g)
          (ModuleCat.restrictScalars ψ.op) =
      tensorRingChangeTransformation R S φ ψ B B''
        (f ≫ (RingChange.restrictFunctor φ ψ).map g) := by
  apply NatTrans.ext
  funext A
  apply hom_ext R S B ((ModuleCat.restrictScalars φ.op).obj A)
  intro x y
  rfl

section DerivedCoefficients

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{vGlobal} R'ᵐᵒᵖ)]

/-- For h:B₀→B a source bimodule map, the Tor coefficient
transformation for h followed by ring change through f equals
the ring-change transformation through f∘h.
Both source categories have projective resolutions. -/
theorem torRingChangeTransformation_coefficient_left (n : ℕ)
    {B₀ : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S} (g : B₀ ⟶ B) :
    Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) ((coefficientTorFunctor R S n).map g) ≫
        torRingChangeTransformation R S φ ψ B B' f n =
      torRingChangeTransformation R S φ ψ B₀ B' (g ≫ f) n := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  change Functor.whiskerLeft (ModuleCat.restrictScalars φ.op)
      (NatTrans.leftDerived (coefficientTensorTransformation R S g) n) ≫
        Functor.leftDerivedSquareHom _ _ _ _
          (tensorRingChangeTransformation R S φ ψ B B' f) n = _
  rw [Functor.leftDerivedSquareHom_naturality_source_functor,
    tensorRingChangeTransformation_coefficient_left]
  rfl

/-- For h:B′→B″ a target bimodule map, the Tor ring-change
transformation through f followed by restricted Tor(h)
equals ring change through Res(h)∘f.
The output action is restricted along ψᵒᵖ. -/
theorem torRingChangeTransformation_coefficient_right (n : ℕ)
    {B'' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S'} (g : B' ⟶ B'') :
    torRingChangeTransformation R S φ ψ B B' f n ≫
        Functor.whiskerRight ((coefficientTorFunctor R' S' n).map g)
          (ModuleCat.restrictScalars ψ.op) =
      torRingChangeTransformation R S φ ψ B B''
        (f ≫ (RingChange.restrictFunctor φ ψ).map g) n := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  change Functor.leftDerivedSquareHom _ _ _ _
      (tensorRingChangeTransformation R S φ ψ B B' f) n ≫
      Functor.whiskerRight (NatTrans.leftDerived (coefficientTensorTransformation R' S' g) n)
        (ModuleCat.restrictScalars ψ.op) = _
  rw [Functor.leftDerivedSquareHom_naturality_target_functor,
    tensorRingChangeTransformation_coefficient_right]
  rfl

end DerivedCoefficients

end Rings

/-- For an (R,S)-bimodule B and a common-world right
R-module category with projective resolutions, right exactness
gives Tor_0^R(−,B)≅(−)⊗_R B naturally in the source. -/
def coefficientTorZeroIso [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) :
    (coefficientTorFunctor R S 0).obj B ≅ (coefficientTensorObj R S B).obj := by
  letI := coefficientLeftModule R S B
  letI := coefficientRightModule R S B
  letI := coefficientActionsCommute R S B
  exact ModuleCat.BalancedTensorRight.torZeroIso R S B

/-- The forward Tor_0^R(−,B)→(−)⊗_R B map is the
canonical degree-zero derived-to-self augmentation of the
coefficient tensor functor, in the chosen source category. -/
theorem coefficientTorZeroIso_hom [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) :
    (coefficientTorZeroIso R S B).hom = (coefficientTensorObj R S B).obj.fromLeftDerivedZero :=
  rfl

section Zero

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']
  (φ : R →+* R') (ψ : S →+* S')
  (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S)
  (B' : coefficientCategory.{rGlobal', sGlobal', vGlobal} R' S')
  (f : B ⟶ (RingChange.restrictFunctor φ ψ).obj B')
  [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{vGlobal} R'ᵐᵒᵖ)]

/-- For endpoint maps φ,ψ and coefficient map f, the
Tor ring-change transformation in degree zero commutes
with Tor_0≅tensor on both sides.
The resulting tensor map is [x⊗y]↦[x⊗f(y)]. -/
theorem torRingChangeTransformation_zero :
    torRingChangeTransformation R S φ ψ B B' f 0 ≫
        Functor.whiskerRight (coefficientTorZeroIso R' S' B').hom (ModuleCat.restrictScalars ψ.op) =
      Functor.whiskerLeft (ModuleCat.restrictScalars φ.op) (coefficientTorZeroIso R S B).hom ≫
        tensorRingChangeTransformation R S φ ψ B B' f := by
  letI : (ModuleCat.restrictScalars.{vGlobal} φ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} φ.op)
  letI : (ModuleCat.restrictScalars.{vGlobal} ψ.op).PreservesHomology :=
    Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} ψ.op)
  rw [coefficientTorZeroIso_hom, coefficientTorZeroIso_hom]
  exact Functor.leftDerivedSquareHom_zero_augmentation _ _ _ _
    (tensorRingChangeTransformation R S φ ψ B B' f)

end Zero

section Identity

variable [HasProjectiveResolutions (ModuleCat.{vGlobal} Rᵐᵒᵖ)]

/-- For identity endpoint maps, the identity coefficient and
source maps give the identity Tor map after the canonical
scalar-restriction identity comparisons.
The source category has projective resolutions in its common world. -/
theorem torRingChangeMap_id
    (B : coefficientCategory.{rGlobal, sGlobal, vGlobal} R S) (A : ModuleCat.{vGlobal} Rᵐᵒᵖ) (n : ℕ) :
    torRingChangeMap R S (RingHom.id R) (RingHom.id S) B B
        ((RingChange.restrictId (R := R) (S := S)).inv.app B) n
        ((ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext rGlobal; rfl)).inv.app A) =
      (ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext sGlobal; rfl)).inv.app
        (((coefficientTorFunctor R S n).obj B).obj A) := by
  let U := ModuleCat.restrictScalars.{vGlobal} (RingHom.id R).op
  let V := ModuleCat.restrictScalars.{vGlobal} (RingHom.id S).op
  let rId := ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext rGlobal; rfl)
  let sId := ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext sGlobal; rfl)
  let F := (coefficientTensorObj R S B).obj
  let P := projectiveResolution A
  let aGlobal : P.complex ⟶ (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex :=
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{vGlobal} Rᵐᵒᵖ) (ComplexShape.down ℕ)).inv.app
        P.complex ≫ (NatTrans.mapHomologicalComplex rId.inv (ComplexShape.down ℕ)).app P.complex
  have ha : aGlobal ≫ Functor.mapChainAugmentation U P.π =
      P.π ≫ (ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map (rId.inv.app A) := by
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | zero =>
      have ha₀ : aGlobal.f 0 = rId.inv.app (P.complex.X 0) := by
        change (𝟙 _) ≫ rId.inv.app (P.complex.X 0) = _
        rw [Category.id_comp]
      change aGlobal.f 0 ≫ (Functor.mapChainAugmentation U P.π).f 0 =
        P.π.f 0 ≫ ((ChainComplex.single₀ (ModuleCat.{vGlobal} Rᵐᵒᵖ)).map (rId.inv.app A)).f 0
      rw [ha₀, Functor.mapChainAugmentation_f_zero, ChainComplex.single₀_map_f_zero]
      exact (rId.inv.naturality (P.π.f 0)).symm
    | succ i =>
      have hρ : (Functor.mapChainAugmentation U P.π).f (i + 1) = 0 :=
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (U.obj A)
          (i + 1) (by omega)).eq_of_tgt _ _
      simp only [HomologicalComplex.comp_f, hρ, ProjectiveResolution.π_f_succ,
        Limits.comp_zero, Limits.zero_comp]
  let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let d : K ⟶ (V.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{vGlobal} Sᵐᵒᵖ) (ComplexShape.down ℕ)).inv.app K ≫
      (NatTrans.mapHomologicalComplex sId.inv (ComplexShape.down ℕ)).app K
  have hd : tensorRingChangeResolutionMap R S (RingHom.id R) (RingHom.id S) B B
      ((RingChange.restrictId (R := R) (S := S)).inv.app B) P P aGlobal = d := by
    apply HomologicalComplex.hom_ext
    intro i
    apply hom_ext R S B (P.complex.X i)
    intro x y
    rfl
  letI : V.PreservesHomology := Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{vGlobal} (RingHom.id S).op)
  letI : (𝟭 (ModuleCat.{vGlobal} Sᵐᵒᵖ)).PreservesHomology :=
    Functor.preservesHomologyOfExact (𝟭 (ModuleCat.{vGlobal} Sᵐᵒᵖ))
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{vGlobal} Sᵐᵒᵖ) (ComplexShape.down ℕ) n
  have hId : (Functor.mapHomologicalComplexIdIso (ModuleCat.{vGlobal} Sᵐᵒᵖ)
      (ComplexShape.down ℕ)).inv.app K = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  have hH : H.map d ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app K =
        sId.inv.app (H.obj K) := by
    have h := HomologicalComplex.mapHomologyFunctorIso_naturality_transformation K n
      (𝟭 (ModuleCat.{vGlobal} Sᵐᵒᵖ)) V sId.inv
    have hD : H.map d = H.map ((NatTrans.mapHomologicalComplex sId.inv
        (ComplexShape.down ℕ)).app K) := by
      rw [show d = (𝟙 K) ≫ (NatTrans.mapHomologicalComplex sId.inv
        (ComplexShape.down ℕ)).app K from congrArg
        (fun f => f ≫ (NatTrans.mapHomologicalComplex sId.inv (ComplexShape.down ℕ)).app K) hId]
      rw [Category.id_comp]
    rw [hD]
    simpa only [HomologicalComplex.mapHomologyFunctorIso_id_hom, Category.id_comp] using h
  rw [torRingChangeMap_resolution R S (RingHom.id R) (RingHom.id S) B B
    ((RingChange.restrictId (R := R) (S := S)).inv.app B) n (rId.inv.app A) P P aGlobal ha, hd]
  change (P.isoLeftDerivedObj F n).hom ≫ H.map d ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.down ℕ) n V).hom.app K ≫
      V.map (P.isoLeftDerivedObj F n).inv = _
  rw [← Category.assoc (H.map d), hH, ← sId.inv.naturality (P.isoLeftDerivedObj F n).inv]
  change (P.isoLeftDerivedObj F n).hom ≫ (P.isoLeftDerivedObj F n).inv ≫
    sId.inv.app ((F.leftDerived n).obj A) = _
  rw [Iso.hom_inv_id_assoc]
  rfl

end Identity

section IndependentCarriers

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']

/-- For an (R,S)-bimodule B, id_B is semilinear over the
enveloping map induced by id_R,id_S.
It is the coefficient identity used in ring-change coherence. -/
def coefficientSemilinearIdentity (B : coefficientCategory.{rGlobal, sGlobal, bGlobal} R S) :
    B →ₛₗ[RingChange.envelopingRingHom (RingHom.id R) (RingHom.id S)] B :=
  (ModuleCat.semilinearMapAddEquiv
    (RingChange.envelopingRingHom (RingHom.id R) (RingHom.id S)) B B).symm
      ((RingChange.restrictId (R := R) (S := S)).inv.app B)

/-- For a right R-module A, id_A is semilinear along
id_(Rᵒᵖ). It is the source identity used by the independent-carrier
ring-change construction. -/
def inputSemilinearIdentity (A : ModuleCat.{aGlobal} Rᵐᵒᵖ) : A →ₛₗ[(RingHom.id R).op] A :=
  (ModuleCat.semilinearMapAddEquiv (RingHom.id R).op A A).symm
    ((ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext rGlobal; rfl)).inv.app A)

/-- For endpoint maps φ,ψ and an enveloping-semilinear
f:B→B′ with carrier worlds b,b′, put
Γ=max(r,r′,a,a′,b,b′,z).
The lifted coefficient map is an enveloping-linear map
ULift^Γ B→Res_(φ,ψ)(ULift^Γ B′), with value up(f(y)). -/
def liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B') :
    (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B ⟶
      (RingChange.restrictFunctor φ ψ).obj
        ((ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
          (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B') := by
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let eX : ULift.{max r r' a a' b b' z} B ≃ₗ[R ⊗[ℤ] Sᵐᵒᵖ] B := ULift.moduleEquiv
  let eY : ULift.{max r r' a a' b b' z} B' ≃ₗ[R' ⊗[ℤ] S'ᵐᵒᵖ] B' := ULift.moduleEquiv
  let g : X.carrier →ₛₗ[RingChange.envelopingRingHom φ ψ] Y.carrier :=
    eY.symm.toLinearMap.comp (f.comp eX.toLinearMap)
  exact ModuleCat.semilinearMapAddEquiv (RingChange.envelopingRingHom φ ψ) X Y g

/-- For an enveloping-semilinear coefficient map f:B→B′,
the common-height lift sends up(y) to up(f(y)).
The endpoint ring actions remain restricted through φ,ψ,
and Γ=max(r,r′,a,a′,b,b′,z). -/
theorem liftCoefficientRingChangeAt_up.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B') (x : B) :
    (liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f).hom
        (ULift.up x) = ULift.up (f x) := rfl

/-- For φ:R→R′ and a φᵒᵖ-semilinear g:A→A′, the
common-height lift gives
ULift^Γ A→Res_(φᵒᵖ)(ULift^Γ A′).
Here Γ=max(r,r′,a,a′,b,b′,z), with independent source worlds a,a′. -/
def liftInputRingChangeAt.{z, r, r', a, a', b, b'} (R : Type r) [Ring R] {R' : Type r'} [Ring R'] (φ : R →+* R')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') :
    (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A ⟶
      (ModuleCat.restrictScalars φ.op).obj
        ((ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A') := by
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let eX : ULift.{max r r' a a' b b' z} A ≃ₗ[Rᵐᵒᵖ] A := ULift.moduleEquiv
  let eY : ULift.{max r r' a a' b b' z} A' ≃ₗ[R'ᵐᵒᵖ] A' := ULift.moduleEquiv
  let f : X.carrier →ₛₗ[φ.op] Y.carrier :=
    eY.symm.toLinearMap.comp (g.comp eX.toLinearMap)
  exact ModuleCat.semilinearMapAddEquiv φ.op X Y f

/-- For a φᵒᵖ-semilinear source map g:A→A′, the lift
to Γ sends up(x) to up(g(x)).
It is right R-linear after restricting the target along φᵒᵖ. -/
theorem liftInputRingChangeAt_up.{z, r, r', a, a', b, b'} (R : Type r) [Ring R] {R' : Type r'} [Ring R'] (φ : R →+* R')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (x : A) :
    (liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g).hom (ULift.up x) =
      ULift.up (g x) := rfl

/-- For endpoint maps φ:R→R′,ψ:S→S′, coefficient map
f:B→B′ along both endpoints and source g:A→A′ along φᵒᵖ,
the canonical Tor map is formed at
Γ=max(r,r′,a,a′,b,b′,z).
It maps the source-derived Tor of A,B to the restriction
along ψᵒᵖ of the target-derived Tor of A′,B′. -/
def torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S] {R' : Type r'}
  [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ) :
    (((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A) ⟶
      (ModuleCat.restrictScalars ψ.op).obj
        (((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A') := by
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} Rᵐᵒᵖ) := inferInstance
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} R'ᵐᵒᵖ) := inferInstance
  let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  exact torRingChangeMap R S φ ψ C D
    (liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f) n
    (liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g)

/-- For the independent-carrier ring-change data φ,ψ,f,g,
the map between the two common-height Tor carriers is
ψᵒᵖ-semilinear. The original source and coefficient
worlds a,a′,b,b′ are retained. -/
def torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ) :
    ((((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A)).carrier
      →ₛₗ[ψ.op]
        ((((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A')).carrier :=
  (ModuleCat.semilinearMapAddEquiv ψ.op
    (((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A)
    (((torCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S' n).obj B').obj A')).symm
      (torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n)

/-- For the common-height Tor change Θ of φ,ψ,f,g,
Θ(t•x)=ψᵒᵖ(t)•Θ(x), t∈Sᵒᵖ.
The common height contains the two acting source rings
but does not include either outer-ring world. -/
theorem torRingChangeSemilinearMapAt_smul.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s)
  [Ring S] {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') (n : ℕ)
    (s : Sᵐᵒᵖ)
    (x : ((torCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S n).obj B).obj A) :
    torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n
        (s • x) = ψ.op s •
      torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g n x :=
  (torRingChangeSemilinearMapAt.{z, r, r', s, s', a, a', b, b'}
    R S φ ψ B B' f A A' g n).map_smulₛₗ s x

/-- For endpoint maps φ,ψ, coefficient f and source g
with their semilinearity equations, the common-height
balanced tensor map has value [up(x)⊗up(y)]↦
[up(g(x))⊗up(f(y))], with output restricted along ψᵒᵖ. -/
def tensorRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S] {R' : Type r'}
  [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') :
    (((tensorCoefficientFunctorAt.{max r' a' b' z, r, s, a, b} R S).obj B).obj A) ⟶
      (ModuleCat.restrictScalars ψ.op).obj
        (((tensorCoefficientFunctorAt.{max r a b z, r', s', a', b'} R' S').obj B').obj A') := by
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let f₀ := liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  let g₀ := liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g
  exact (coefficientTensorObj R S C).obj.map g₀ ≫
    (tensorRingChangeTransformation R S φ ψ C D f₀).app Y

/-- The tensor change for φ,ψ,f,g sends the lifted pure
balanced class [up(x)⊗up(y)] to
[up(g(x))⊗up(f(y))].
The source balance is over R and target balance over R′. -/
theorem tensorRingChangeMapAt_pairing.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A')
    (x : A) (y : B) :
    let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
    let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
    let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
      (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
    let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
      (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
    (tensorRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g).hom
        (pairing R S C X (ULift.up x) (ULift.up y)) =
      pairing R' S' D Y (ULift.up (g x)) (ULift.up (f y)) := rfl

end IndependentCarriers

/-- For an (R,S)-bimodule B and source carrier world a,
Tor formed after lifting to Γ_z=max(r,a,b,z) is naturally
the lifted balanced tensor in degree zero.
The identification is the coefficient-family specialization
of the source-derived Tor_0 comparison. -/
def coefficientTorZeroIsoAt.{z, r, s, a, b} (R : Type r) [Ring R] (S : Type s) [Ring S]
    (B : coefficientCategory.{r, s, b} R S) :
    (torCoefficientFunctorAt.{z, r, s, a, b} R S 0).obj B ≅
      (tensorCoefficientFunctorAt.{z, r, s, a, b} R S).obj B := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  exact Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ)
    (coefficientTorZeroIso R S
      ((ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B))

section IndependentZero

variable {R' : Type rGlobal'} {S' : Type sGlobal'} [Ring R'] [Ring S']

/-- For endpoint and source/coefficient semilinear maps,
the common-height Tor change in degree zero, followed by
the target Tor-to-tensor map, equals the source Tor-to-tensor
map followed by the ordered tensor change. -/
theorem torRingChangeMapAt_zero.{z, r, r', s, s', a, a', b, b'} (R : Type r) [Ring R] (S : Type s) [Ring S]
  {R' : Type r'} [Ring R'] {S' : Type s'} [Ring S']
    (φ : R →+* R') (ψ : S →+* S')
    (B : coefficientCategory.{r, s, b} R S)
    (B' : coefficientCategory.{r', s', b'} R' S')
    (f : B →ₛₗ[RingChange.envelopingRingHom φ ψ] B')
    (A : ModuleCat.{a} Rᵐᵒᵖ) (A' : ModuleCat.{a'} R'ᵐᵒᵖ) (g : A →ₛₗ[φ.op] A') :
    torRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g 0 ≫
        (ModuleCat.restrictScalars ψ.op).map
          ((coefficientTorZeroIsoAt.{max r a b z, r', s', a', b'} R' S' B').hom.app A') =
      (coefficientTorZeroIsoAt.{max r' a' b' z, r, s, a, b} R S B).hom.app A ≫
        tensorRingChangeMapAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f A A' g := by
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} Rᵐᵒᵖ) := inferInstance
  letI : HasProjectiveResolutions (ModuleCat.{max r r' a a' b b' z} R'ᵐᵒᵖ) := inferInstance
  let X := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a} Rᵐᵒᵖ).obj A
  let Y := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, a'} R'ᵐᵒᵖ).obj A'
  let C := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b}
    (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let D := (ModuleCat.uliftFunctor.{max r r' a a' b b' z, b'}
    (R' ⊗[ℤ] S'ᵐᵒᵖ)).obj B'
  let f₀ := liftCoefficientRingChangeAt.{z, r, r', s, s', a, a', b, b'} R S φ ψ B B' f
  let g₀ := liftInputRingChangeAt.{z, r, r', a, a', b, b'} R φ A A' g
  have hT := congrArg (fun α => α.app Y)
    (torRingChangeTransformation_zero R S φ ψ C D f₀)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hT
  have hZ := (coefficientTorZeroIso R S C).hom.naturality g₀
  change ((((coefficientTorFunctor R S 0).obj C).map g₀) ≫
      (torRingChangeTransformation R S φ ψ C D f₀ 0).app Y) ≫
      (ModuleCat.restrictScalars ψ.op).map ((coefficientTorZeroIso R' S' D).hom.app Y) =
    (coefficientTorZeroIso R S C).hom.app X ≫
      ((coefficientTensorObj R S C).obj.map g₀ ≫
        (tensorRingChangeTransformation R S φ ψ C D f₀).app Y)
  rw [Category.assoc, hT, ← Category.assoc, hZ, Category.assoc]

end IndependentZero

/-- For identity endpoint, coefficient and source maps, the
independent-carrier Tor change is the canonical output
scalar-restriction identity comparison.
It retains the same Tor object at height Γ_z=max(r,a,b,z). -/
theorem torRingChangeMapAt_id.{z, r, s, a, b} (R : Type r) [Ring R] (S : Type s) [Ring S]
    (B : coefficientCategory.{r, s, b} R S) (A : ModuleCat.{a} Rᵐᵒᵖ) (n : ℕ) :
    torRingChangeMapAt.{z, r, r, s, s, a, a, b, b} R S (RingHom.id R) (RingHom.id S) B B
        (coefficientSemilinearIdentity R S B) A A (inputSemilinearIdentity R A) n =
      (ModuleCat.restrictScalarsId' (RingHom.id S).op (by ext s; rfl)).inv.app
        (((torCoefficientFunctorAt.{z, r, s, a, b} R S n).obj B).obj A) := by
  letI : HasProjectiveResolutions (ModuleCat.{max r a b z} Rᵐᵒᵖ) := inferInstance
  let X := (ModuleCat.uliftFunctor.{max r a b z, a} Rᵐᵒᵖ).obj A
  let C := (ModuleCat.uliftFunctor.{max r a b z, b} (R ⊗[ℤ] Sᵐᵒᵖ)).obj B
  let f₀ := liftCoefficientRingChangeAt.{z, r, r, s, s, a, a, b, b}
    R S (RingHom.id R) (RingHom.id S) B B (coefficientSemilinearIdentity R S B)
  let g₀ := liftInputRingChangeAt.{z, r, r, a, a, b, b}
    R (RingHom.id R) A A (inputSemilinearIdentity R A)
  have hf : f₀ = (RingChange.restrictId (R := R) (S := S)).inv.app C := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  have hg : g₀ =
      (ModuleCat.restrictScalarsId' (RingHom.id R).op (by ext r; rfl)).inv.app X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    cases x
    rfl
  change torRingChangeMap R S (RingHom.id R) (RingHom.id S) C C f₀ n g₀ = _
  rw [hf, hg]
  exact torRingChangeMap_id R S C X n

end ModuleCat.Bimodule.Tensor
