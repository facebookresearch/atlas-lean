/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.TorusDifferentialGeometryModels
public import MathlibExt.AlgebraicGeometry.BorelCohomologyModels

/-!
# The actual geometric source hypotheses for cohomological stable envelopes

The two-form is a section of the native algebraic exterior sheaf.
Closedness uses the coefficient-linear exterior differential normalized
on every Kähler wedge generator; nondegeneracy uses its actual contraction.
Quasiprojectivity is a closed embedding in an open of an actual projective
quotient-line model. Properness, affineness and equivariance concern the
original scheme map. Formality is the actual Borel fibre edge condition.

The torus itself can be the reductive group G in the source assumptions;
an action of a larger G restricts through its actual torus inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SymplecticTorusSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open AlgebraicWeightBundleModels AlgebraicSplitTorusModels TorusDifferentialGeometryModels
open IntegralChowChernModels ComplexAnalytification LinearizedLineBundles CoherentCurveLinearSeries

def pointData : SchemeData where
  scheme := Over.mk (𝟙 base)
  finiteType := by change LocallyOfFiniteType (𝟙 base); infer_instance
  quasiCompact := by change QuasiCompact (𝟙 base); infer_instance
  noetherian := by change IsNoetherian base; infer_instance

/-- Projective space is the actual quotient-line model of the free module at the point. -/
structure QuasiprojectiveData (X : Over base) where
  rank : ℕ
  projective : ProjectiveModel pointData
    (SheafOfModules.free (R := pointData.scheme.left.ringCatSheaf) (Fin rank)) rank
  opened : projective.total.scheme.left.Opens
  embedding : X ⟶ Over.mk (opened.ι ≫ projective.total.scheme.hom)
  [closed : IsClosedImmersion embedding.left]

attribute [instance] QuasiprojectiveData.closed

@[instance_reducible] def coefficientModule (X : Over base) (E : X.left.Modules) (U : X.left.Opens)
  :
    Module ℂ (E.val.obj (op U)) :=
  Module.compHom (E.val.obj (op U)) ((AlgebraicDifferentialSheaves.scalarMap ℂ X).app (op U)).hom

def unitValue (X : Scheme.{0}) (U : X.Opens) :
    (SheafOfModules.unit X.ringCatSheaf).val.obj (op U) :=
  (1 : X.ringCatSheaf.obj.obj (op U))

/-- The actual de Rham differential is fixed on all local coefficient/wedge generators. -/
structure ExteriorDerivativeData (X : Over base) where
  map : ∀ (U : X.left.Opens) (n : ℕ),
    letI := coefficientModule X (AlgebraicDifferentialSheaves.forms ℂ X n) U
    letI := coefficientModule X (AlgebraicDifferentialSheaves.forms ℂ X (n+1)) U
    (AlgebraicDifferentialSheaves.forms ℂ X n).val.obj (op U) →ₗ[ℂ]
      (AlgebraicDifferentialSheaves.forms ℂ X (n+1)).val.obj (op U)
  symbol : ∀ (U : X.left.Opens) (n : ℕ) (a : Γ(X.left, U)) (r : Fin n → Γ(X.left, U)),
    map U n (a • formSymbol ℂ X U n r) = formSymbol ℂ X U (n+1) (Fin.cons a r)
  naturality : ∀ (U V : X.left.Opens) (h : V≤U) (n : ℕ)
    (s : (AlgebraicDifferentialSheaves.forms ℂ X n).val.obj (op U)),
    ((AlgebraicDifferentialSheaves.forms ℂ X (n+1)).val.map (homOfLE h).op).hom (map U n s) =
      map V n (((AlgebraicDifferentialSheaves.forms ℂ X n).val.map (homOfLE h).op).hom s)

/-- Interior multiplication is fixed by its actual native Kähler wedge rule. -/
structure ContractionData (X : Over base) where
  map : ∀ U : X.left.Opens,
    (Tangent X).val.obj (op U) →ₗ[Γ(X.left, U)]
      (AlgebraicDifferentialSheaves.forms ℂ X 2).val.obj (op U) →ₗ[Γ(X.left, U)]
        (Omega X).val.obj (op U)
  symbol : ∀ (U : X.left.Opens) (v : (Tangent X).val.obj (op U)) (f g : Γ(X.left, U)),
    map U v (formSymbol ℂ X U 2 ![f,g]) =
      homApply X.left (Omega X) U v (formSymbol ℂ X U 1 ![f]) • formSymbol ℂ X U 1 ![g] -
      homApply X.left (Omega X) U v (formSymbol ℂ X U 1 ![g]) • formSymbol ℂ X U 1 ![f]
  naturality : ∀ (U V : X.left.Opens) (h : V≤U)
    (v : (Tangent X).val.obj (op U)) (w : (AlgebraicDifferentialSheaves.forms ℂ X 2).val.obj (op
      U)),
    ((Omega X).val.map (homOfLE h).op).hom (map U v w) =
      map V (((Tangent X).val.map (homOfLE h).op).hom v)
        (((AlgebraicDifferentialSheaves.forms ℂ X 2).val.map (homOfLE h).op).hom w)

/-- Closedness and nondegeneracy refer to the given actual two-form. -/
structure SymplecticData (X : Over base) where
  omega : SheafOfModules.unit X.left.ringCatSheaf ⟶ AlgebraicDifferentialSheaves.forms ℂ X 2
  exterior : ExteriorDerivativeData X
  closed : exterior.map ⊤ 2 ((omega.val.app (op ⊤)).hom (unitValue X.left ⊤)) = 0
  interior : ContractionData X
  contraction : Tangent X ⟶ Omega X
  normalized : ∀ (U : X.left.Opens) (v : (Tangent X).val.obj (op U)),
    ((contraction.val.app (op U)).hom v) = interior.map U v
      ((omega.val.app (op U)).hom (unitValue X.left U))
  [nondegenerate : IsIso contraction]

attribute [instance] SymplecticData.nondegenerate

/-- The continuous torus is the actual coordinate-unit group with the original scheme action. -/
structure AnalyticTorusAction {T : Over base} [GrpObj T] (M : TorusModel T)
    (X : Over base) [ModObj T X] where
  [action : MulAction (Fin M.rank → ℂˣ) (space X)]
  [continuous : ContinuousSMul (Fin M.rank → ℂˣ) (space X)]
  normalized : ∀ (g : Fin M.rank → ℂˣ) (x : space X),
    (g • x).hom = (lift (M.point g) (ComplexTorusTorsors.pointOf x) ≫ γ[T,X]).left

/-- The actual proper torus-equivariant map goes to an actual affine variety. -/
structure ProperToAffine {T : Over base} [GrpObj T] (X : Over base) [ModObj T X] where
  target : SchemeData
  [action : ModObj T target.scheme]
  [affine : IsAffine target.scheme.left]
  map : X ⟶ target.scheme
  [proper : IsProper map.left]
  equivariant : γ[T,X] ≫ map = (T ◁ map) ≫ γ[T,target.scheme]

attribute [instance] ProperToAffine.action ProperToAffine.affine ProperToAffine.proper

/-- All source hypotheses concern native objects and original maps. -/
structure StableEnvelopeSource {A T : Over base} [GrpObj A] [GrpObj T]
    (MA : TorusModel A) (MT : TorusModel T) (S : Subtorus A T)
    (X : SchemeData) [ModObj A X.scheme] [ModObj T X.scheme] where
  restricted : γ[A,X.scheme] = (S.inclusion ▷ X.scheme) ≫ γ[T,X.scheme]
  [smooth : Smooth X.scheme.hom]
  quasiprojective : QuasiprojectiveData X.scheme
  symplectic : SymplecticData X.scheme
  forms : TorusFormsActionData MT X.scheme
  character : Character T
  eigen : AlgebraicBundleGeometry.pullbackSection γ[T,X.scheme].left
      (AlgebraicDifferentialSheaves.forms ℂ X.scheme 2) symplectic.omega ≫
        (forms.linearization 2).comparison.hom =
    AlgebraicBundleGeometry.pullbackSection (snd T X.scheme).left
      (AlgebraicDifferentialSheaves.forms ℂ X.scheme 2) symplectic.omega ≫
      scalarEnd (T ⊗ X.scheme).left
        ((Scheme.Modules.pullback (snd T X.scheme).left).obj
          (AlgebraicDifferentialSheaves.forms ℂ X.scheme 2))
        (inverseCharacterFunction character X.scheme)
  fixedForm : IsTrivialCharacter (restrictedCharacter S character)
  proper : ProperToAffine (T := T) X.scheme
  analytic : AnalyticTorusAction MT X.scheme
  formal : letI := analytic.action
    letI := analytic.continuous
    BorelCohomologyModels.EquivariantlyFormal (Fin MT.rank → ℂˣ) (space X.scheme)

end MathlibExt.AlgebraicGeometry.SymplecticTorusSourceModels
