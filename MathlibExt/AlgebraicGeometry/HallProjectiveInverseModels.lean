/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HallFamilyStackModels
public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Actual inverse projective-space classes for the corrected regular Hall space

The coefficient ring in Bridgeland's v3 correction in §7.3, equation
(50), also inverts every projective-space class. The inverse of [P^k]
is [P_(1,k)]·[BGL_(k+1)], with P_(1,k) the actual parabolic subgroup
preserving the first coordinate line. Its scheme is the determinant
localization of the matrix polynomial ring modulo the first-column
entries below that line. BGL is the full stack of actual rank-(k+1)
bundles, coherently normalized against native module pullback.

The inverse identity is a separate proof request about these actual
geometric products. No freely assigned inverse scalar is supplied.

References: Bridgeland, arXiv:1002.4374v3, §7.3, equation (50),
Toda's rank-two example; arXiv:1002.4372v1, §3.3 (GL_n inverses).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HallProjectiveInverseModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open StackCycleGeometry GeometricHallStackFunctions HallFamilyStackModels
open IntegralChowChernModels CoherentCurveLinearSeries AlgebraicBundleGeometry

/-- The actual matrix-coordinate polynomial ring. -/
abbrev MatrixRing (n : ℕ) := MvPolynomial (Fin n × Fin n) ℂ

def matrixDeterminant (n : ℕ) : MatrixRing n :=
  Matrix.det (fun i j : Fin n => MvPolynomial.X (i,j))

/-- General linear group coordinates retain the inverse determinant. -/
abbrev GeneralLinearRing (n : ℕ) := Localization.Away (matrixDeterminant n)

instance generalLinearComplexAlgebra (n : ℕ) : Algebra ℂ (GeneralLinearRing n) :=
  Algebra.compHom (GeneralLinearRing n) (algebraMap ℂ (MatrixRing n))

/-- The first line is preserved by setting the actual lower first-column entries to zero. -/
def parabolicIdeal (k : ℕ) : Ideal (GeneralLinearRing (k+1)) :=
  Ideal.span {a | ∃ i : Fin (k+1), i≠0 ∧
    a=algebraMap (MatrixRing (k+1)) (GeneralLinearRing (k+1)) (MvPolynomial.X (i,0))}

abbrev ParabolicRing (k : ℕ) := GeneralLinearRing (k+1) ⧸ parabolicIdeal k

def parabolicScheme (k : ℕ) : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.algebraMap ℂ (ParabolicRing k))

/-- The actual groupoid of finite-rank vector bundles. -/
abbrev BundleFamily (r : ℕ) (T : Over (Spec (.of ℂ))) :=
  {E : T.left.Modules // IsBundle E r}

instance bundleFamilyCategory (r : ℕ) (T : Over (Spec (.of ℂ))) :
    Category (BundleFamily r T) where
  Hom E F := E.val ≅ F.val
  id _ := Iso.refl _
  comp a b := a ≪≫ b
  id_comp _ := by apply Iso.ext; exact Category.id_comp _
  comp_id _ := by apply Iso.ext; exact Category.comp_id _
  assoc _ _ _ := by apply Iso.ext; exact Category.assoc _ _ _

instance bundleFamilyIsGroupoid (r : ℕ) (T : Over (Spec (.of ℂ))) :
    IsGroupoid (BundleFamily r T) where
  all_isIso a :=
    ⟨⟨a.symm,by apply Iso.ext; exact a.hom_inv_id,
      by apply Iso.ext; exact a.inv_hom_id⟩⟩

def bundleModules (r : ℕ) (T : Over (Spec (.of ℂ))) : BundleFamily r T ⥤ T.left.Modules where
  obj E := E.val
  map a := a.hom
  map_id _ := rfl
  map_comp _ _ := rfl

structure ClassifyingBundleStackData (r : ℕ) where
  carrier : FiniteTypeStack
  fibre : ∀ T : Over (Spec (.of ℂ)), carrier.stack.Fibre T ≌ BundleFamily r T

def ClassifyingBundleStackData.moduleForget {r : ℕ} (B : ClassifyingBundleStackData r)
    (T : Over (Spec (.of ℂ))) := (B.fibre T).functor ⋙ bundleModules r T

/-- BGL_r is normalized on all scheme tests and both native pullback coherence diagrams. -/
structure ClassifyingBundleStackModel (r : ℕ) extends ClassifyingBundleStackData r where
  moduleComparison : ∀ {T U : Over (Spec (.of ℂ))} (f : U ⟶ T),
    pull carrier.stack f ⋙ toClassifyingBundleStackData.moduleForget U ≅
      toClassifyingBundleStackData.moduleForget T ⋙ Scheme.Modules.pullback f.left
  unit : ∀ (T : Over (Spec (.of ℂ))) (E : carrier.stack.Fibre T),
    (moduleComparison (𝟙 T)).hom.app E ≫
      (Scheme.Modules.pullbackId T.left).hom.app
        ((toClassifyingBundleStackData.moduleForget T).obj E) =
    (toClassifyingBundleStackData.moduleForget T).map
      ((Cat.Hom.toNatIso (carrier.stack.toPseudofunctor.mapId (.mk (op T)))).hom.app E)
  composition : ∀ {T U V : Over (Spec (.of ℂ))} (f : U ⟶ T) (g : V ⟶ U)
    (E : carrier.stack.Fibre T),
    (moduleComparison (g ≫ f)).hom.app E =
    (toClassifyingBundleStackData.moduleForget V).map
      ((Cat.Hom.toNatIso
        (carrier.stack.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc)).hom.app E) ≫
      (moduleComparison g).hom.app ((pull carrier.stack f).obj E) ≫
      (Scheme.Modules.pullback g.left).map ((moduleComparison f).hom.app E) ≫
      (Scheme.Modules.pullbackComp g.left f.left).hom.app
        ((toClassifyingBundleStackData.moduleForget T).obj E)

def pointScheme : SchemeData where
  scheme := Over.mk (𝟙 (Spec (.of ℂ)))
  finiteType := by change LocallyOfFiniteType (𝟙 (Spec (.of ℂ))); infer_instance
  quasiCompact := by change QuasiCompact (𝟙 (Spec (.of ℂ))); infer_instance
  noetherian := by change IsNoetherian (Spec (.of ℂ)); infer_instance

/-- The actual P^k and its actual parabolic-times-BGL inverse source. -/
structure ProjectiveInverseModel (k : ℕ) where
  projective : ProjectiveModel pointScheme
    (SheafOfModules.free (R := (Spec (.of ℂ)).ringCatSheaf) (Fin (k+1))) (k+1)
  projectiveStack : FiniteTypeStack
  projectiveSource : SchemeSource projectiveStack
  projective_normalized : projectiveSource.scheme=projective.total.scheme
  parabolic : SchemeData
  parabolic_normalized : parabolic.scheme=parabolicScheme k
  parabolicStack : FiniteTypeStack
  parabolicSource : SchemeSource parabolicStack
  parabolic_source_normalized : parabolicSource.scheme=parabolic.scheme
  bundles : ClassifyingBundleStackModel (k+1)
  product : ProductModel parabolicStack bundles.carrier

def ProjectiveInverseModel.inverseStack {k : ℕ} (P : ProjectiveInverseModel k) :
    FiniteTypeStack := P.product.apex

end MathlibExt.AlgebraicGeometry.HallProjectiveInverseModels
