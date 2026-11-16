/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CriticalFunctionSheafModels
public import MathlibExt.AlgebraicGeometry.BundleTrace
public import MathlibExt.AlgebraicGeometry.NormalizedModuleTensorMaps

/-!
# Actual normal quotients and Hessian forms of critical chart embeddings

The normal module is the cokernel of the dual of the actual pulled
cotangent derivative. Its quadratic form is normalized on every local
coordinate frame by one half of the actual Hessian, pulled along the
same scheme map. The pairing and its adjoint retain all sheaf sections;
pointwise field tests alone do not specify this data.

Reference: Joyce, arXiv:1304.4508v3, Proposition 2.25, equations
(2.15)--(2.25). Only characteristic different from two is needed.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CriticalHessianModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.AlgebraicGeometry
open CriticalSchemeCharts CriticalFunctionSheafModels AffineCriticalFunctions
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks
open CoherentCurveLinearSeries AlgebraicLineBundleFamilies
open BundleTrace NormalizedModuleTensorMaps GenericSectionMaps
open Module

variable {k : Type} [Field k]

def ambient {X : Over (Spec (.of k))} (E : AffineEmbedding X) : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E.algebra)))

/-- The affine version of an actual closed embedding of critical charts. -/
structure CriticalAffineRefinement {X : Over (Spec (.of k))}
    (E F : AffineCriticalChart X) extends
      AffineRefinement F.toAffineEmbedding E.toAffineEmbedding where
  [closed : IsClosedImmersion (Spec.map (CommRingCat.ofHom algebraMap.toRingHom))]
  function_eq : algebraMap F.function = E.function

attribute [instance] CriticalAffineRefinement.closed

def ambientMap {X : Over (Spec (.of k))} {E F : AffineCriticalChart X}
    (r : CriticalAffineRefinement E F) :
    ambient E.toAffineEmbedding ⟶ ambient F.toAffineEmbedding :=
  Over.homMk (Spec.map (CommRingCat.ofHom r.algebraMap.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom r.algebraMap.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k F.algebra)) =
        Spec.map (CommRingCat.ofHom (algebraMap k E.algebra))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    exact r.algebraMap.commutes a)

/-- Evaluation of the native restricted module-Hom on the terminal slice. -/
def dualValue {T : Scheme} (M : T.Modules) (W : T.Opens)
    (a : Γ(homSheaf T M (structureModule T),W)) (m : Γ(M,W)) : Γ(T,W) :=
  (a.app (op (Over.mk (𝟙 W)))).hom m

/-- Generic source integration of sheaf-Hom precomposition is fixed on all local values. -/
structure DualPrecomposition {T : Scheme} {M N : T.Modules} (f : M ⟶ N) where
  map : homSheaf T N (structureModule T) ⟶ homSheaf T M (structureModule T)
  normalized : ∀ (W : T.Opens) (a : Γ(homSheaf T N (structureModule T),W))
    (m : Γ(M,W)), dualValue M W (map.app W a) m = dualValue N W a (f.app W m)

variable {X : Over (Spec (.of k))} {E F : AffineCriticalChart X}
  (r : CriticalAffineRefinement E F)
  (D : PullbackDifferential (ambient F.toAffineEmbedding) (ambientMap r))

abbrev chartCotangent :=
  (Scheme.Modules.pullback E.inclusion.left).obj (forms k (ambient E.toAffineEmbedding) 1)

abbrev largerCotangent :=
  (Scheme.Modules.pullback (E.inclusion.left ≫ (ambientMap r).left)).obj
    (forms k (ambient F.toAffineEmbedding) 1)

/-- The cotangent map on the actual critical scheme is native pullback of the same derivative. -/
def chartCotangentMap : largerCotangent r ⟶ chartCotangent (E := E) :=
  (Scheme.Modules.pullbackComp E.inclusion.left (ambientMap r).left).inv.app
    (forms k (ambient F.toAffineEmbedding) 1) ≫
      (Scheme.Modules.pullback E.inclusion.left).map D.map

abbrev largerTangent := homSheaf E.domain.toScheme (largerCotangent r)
  (structureModule E.domain.toScheme)

/-- The actual quotient tangent module, with its fixed projection. -/
def normalModule (P : DualPrecomposition (chartCotangentMap r D)) : E.domain.toScheme.Modules :=
  cokernel P.map

def normalProjection (P : DualPrecomposition (chartCotangentMap r D)) :
    largerTangent r ⟶ normalModule r D P := cokernel.π P.map

abbrev Coordinates (V : (ambient F.toAffineEmbedding).left.Opens) (m : ℕ) :=
  letI : Algebra k Γ((ambient F.toAffineEmbedding).left,V) :=
    ((scalarMap k (ambient F.toAffineEmbedding)).app (op V)).hom.toAlgebra
  DifferentialCoordinates k Γ((ambient F.toAffineEmbedding).left,V) m

def coordinateValue {V : (ambient F.toAffineEmbedding).left.Opens} {m : ℕ}
    (C : Coordinates (F := F) V m) (j : Fin m) :
    Γ((ambient F.toAffineEmbedding).left,V) := by
  letI : Algebra k Γ((ambient F.toAffineEmbedding).left,V) :=
    ((scalarMap k (ambient F.toAffineEmbedding)).app (op V)).hom.toAlgebra
  exact C.coordinate j

/-- A true local tangent frame is dual to the pulled native coordinate differentials. -/
structure CoordinateFrame (V : (ambient F.toAffineEmbedding).left.Opens)
    (W : E.domain.toScheme.Opens) (m : ℕ)
    (h : W ≤ (E.inclusion.left ≫ (ambientMap r).left) ⁻¹ᵁ V) where
  coordinates : Coordinates (F := F) V m
  basis : Basis (Fin m) Γ(E.domain.toScheme,W) Γ(largerTangent r,W)
  dual : ∀ i j : Fin m,
    dualValue (largerCotangent r) W (basis i)
      (localPullbackSection (E.inclusion.left ≫ (ambientMap r).left)
        (forms k (ambient F.toAffineEmbedding) 1) V W h
        (differential (ambient F.toAffineEmbedding) V (coordinateValue coordinates j))) =
      if i = j then 1 else 0

/-- Actual Hessian coefficients, with the same regular function and scheme appLE. -/
def hessianCoefficient {V : (ambient F.toAffineEmbedding).left.Opens}
    {W : E.domain.toScheme.Opens} {m : ℕ}
    {h : W ≤ (E.inclusion.left ≫ (ambientMap r).left) ⁻¹ᵁ V}
    (C : CoordinateFrame r V W m h) (i j : Fin m) : Γ(E.domain.toScheme,W) := by
  letI : Algebra k Γ((ambient F.toAffineEmbedding).left,V) :=
    ((scalarMap k (ambient F.toAffineEmbedding)).app (op V)).hom.toAlgebra
  let g : Γ((ambient F.toAffineEmbedding).left,V) :=
    ((ambient F.toAffineEmbedding).left.presheaf.map (homOfLE le_top).op).hom
    ((Scheme.ΓSpecIso (.of F.algebra)).inv.hom F.function)
  exact (E.inclusion.left ≫ (ambientMap r).left).appLE V W h |>.hom
    (hessian C.coordinates g i j)

def halfScalar (W : E.domain.toScheme.Opens) : Γ(E.domain.toScheme,W) := by
  let φ : k →+* Γ(E.domain.toScheme,W) :=
    ((scalarMap k (Over.mk (E.domain.ι ≫ X.hom))).app (op W)).hom
  exact φ ((2 : k)⁻¹)

/-- The actual normal form and adjoint, with all coordinate Hessian comparisons. -/
structure HessianForm (P : DualPrecomposition (chartCotangentMap r D)) where
  pairing : moduleTensor E.domain.toScheme (normalModule r D P) (normalModule r D P) ⟶
    structureModule E.domain.toScheme
  adjoint : normalModule r D P ⟶
    homSheaf E.domain.toScheme (normalModule r D P) (structureModule E.domain.toScheme)
  adjoint_eq : ∀ (W : E.domain.toScheme.Opens) (a b : Γ(normalModule r D P,W)),
    dualValue (normalModule r D P) W (adjoint.app W a) b =
      pairing.app W (pureTensorSection _ _ _ W a b)
  symmetric : ∀ (W : E.domain.toScheme.Opens) (a b : Γ(normalModule r D P,W)),
    pairing.app W (pureTensorSection _ _ _ W a b) =
      pairing.app W (pureTensorSection _ _ _ W b a)
  [nondegenerate : IsIso adjoint]
  hessian_eq : ∀ (V : (ambient F.toAffineEmbedding).left.Opens) (_hV : IsAffineOpen V)
    (W : E.domain.toScheme.Opens) (_hW : IsAffineOpen W) (m : ℕ)
    (h : W ≤ (E.inclusion.left ≫ (ambientMap r).left) ⁻¹ᵁ V)
    (C : CoordinateFrame r V W m h) (i j : Fin m),
    pairing.app W (pureTensorSection _ _ _ W
      ((normalProjection r D P).app W (C.basis i))
      ((normalProjection r D P).app W (C.basis j))) =
    halfScalar (E := E) W *
      hessianCoefficient r C i j

attribute [instance] HessianForm.nondegenerate

end MathlibExt.AlgebraicGeometry.CriticalHessianModels
