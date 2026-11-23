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
cotangent derivative. Its quadratic form is the normal block of the Hessian
in Joyce's local normal form: over an open `V` of the larger ambient with a
retraction `α` onto the smaller one such that `g - f ∘ α` vanishes to second
order along the smaller ambient (Joyce, Proposition 2.22), the form is
normalized on every local coordinate frame by one half of the Hessian of
`g - f ∘ α`, pulled along the same scheme map. The full Hessian of `g` does not
descend to the normal quotient (already for an identity embedding of a chart
with nonzero Hessian), while that of `g - f ∘ α` does. Such retractions exist
Zariski-locally around the critical locus; that the form does not depend on
the retraction is part of Joyce's result. The pairing and its adjoint retain
all sheaf sections; pointwise field tests alone do not specify this data.

Reference: Joyce, arXiv:1304.4508v3, Propositions 2.22 and 2.25, equations
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

/-- The affine version of an embedding of critical charts: the ambient map is a locally
closed immersion (Joyce, Definition 2.18), so restrictions to open subcharts are included. -/
structure CriticalAffineRefinement {X : Over (Spec (.of k))}
    (E F : AffineCriticalChart X) extends
      AffineRefinement F.toAffineEmbedding E.toAffineEmbedding where
  [immersion : IsImmersion (Spec.map (CommRingCat.ofHom algebraMap.toRingHom))]
  function_eq : algebraMap F.function = E.function

attribute [instance] CriticalAffineRefinement.immersion

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

/-- The function `g` of the larger chart, restricted to the ambient open `V`. -/
def largerFunction (V : (ambient F.toAffineEmbedding).left.Opens) :
    Γ((ambient F.toAffineEmbedding).left,V) :=
  ((ambient F.toAffineEmbedding).left.presheaf.map (homOfLE le_top).op).hom
    ((Scheme.ΓSpecIso (.of F.algebra)).inv.hom F.function)

/-- The function `f` of the smaller chart, restricted to the preimage of `V`. -/
def smallerFunction (V : (ambient F.toAffineEmbedding).left.Opens) :
    Γ((ambient E.toAffineEmbedding).left,(ambientMap r).left ⁻¹ᵁ V) :=
  ((ambient E.toAffineEmbedding).left.presheaf.map (homOfLE le_top).op).hom
    ((Scheme.ΓSpecIso (.of E.algebra)).inv.hom E.function)

/-- Restriction from an open `V` of the larger ambient to its preimage in the smaller one. -/
def ambientRestriction (V : (ambient F.toAffineEmbedding).left.Opens) :
    Γ((ambient F.toAffineEmbedding).left,V) →+*
      Γ((ambient E.toAffineEmbedding).left,(ambientMap r).left ⁻¹ᵁ V) :=
  ((ambientMap r).left.appLE V ((ambientMap r).left ⁻¹ᵁ V) le_rfl).hom

/-- A local normal-form retraction over the ambient open `V` (Joyce, Proposition 2.22):
a ring section `σ` over `k` (field `sec`) of the restriction to the smaller ambient (the pullback along a
retraction `α`) such that `g - σ f = g - f ∘ α` lies in the square of the ideal of the
smaller ambient, i.e. vanishes to second order along it. -/
structure LocalNormalRetraction (V : (ambient F.toAffineEmbedding).left.Opens) where
  sec : Γ((ambient E.toAffineEmbedding).left,(ambientMap r).left ⁻¹ᵁ V) →+*
    Γ((ambient F.toAffineEmbedding).left,V)
  scalars : ∀ c : k, sec (((scalarMap k (ambient E.toAffineEmbedding)).app
      (op ((ambientMap r).left ⁻¹ᵁ V))).hom c) =
    ((scalarMap k (ambient F.toAffineEmbedding)).app (op V)).hom c
  retract : ∀ a, ambientRestriction r V (sec a) = a
  normal : largerFunction (F := F) V - sec (smallerFunction r V) ∈
    RingHom.ker (ambientRestriction r V) ^ 2

/-- Hessian coefficients of `g - f ∘ α` for a local normal-form retraction, with the same
regular functions and scheme appLE. -/
def normalHessianCoefficient {V : (ambient F.toAffineEmbedding).left.Opens}
    {W : E.domain.toScheme.Opens} {m : ℕ}
    {h : W ≤ (E.inclusion.left ≫ (ambientMap r).left) ⁻¹ᵁ V}
    (C : CoordinateFrame r V W m h) (σ : LocalNormalRetraction r V) (i j : Fin m) :
    Γ(E.domain.toScheme,W) := by
  letI : Algebra k Γ((ambient F.toAffineEmbedding).left,V) :=
    ((scalarMap k (ambient F.toAffineEmbedding)).app (op V)).hom.toAlgebra
  exact (E.inclusion.left ≫ (ambientMap r).left).appLE V W h |>.hom
    (hessian C.coordinates (largerFunction (F := F) V - σ.sec (smallerFunction r V)) i j)

def halfScalar (W : E.domain.toScheme.Opens) : Γ(E.domain.toScheme,W) := by
  let φ : k →+* Γ(E.domain.toScheme,W) :=
    ((scalarMap k (Over.mk (E.domain.ι ≫ X.hom))).app (op W)).hom
  exact φ ((2 : k)⁻¹)

/-- The actual normal form and adjoint, with all coordinate Hessian comparisons for every
local normal-form retraction. -/
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
    (C : CoordinateFrame r V W m h) (σ : LocalNormalRetraction r V) (i j : Fin m),
    pairing.app W (pureTensorSection _ _ _ W
      ((normalProjection r D P).app W (C.basis i))
      ((normalProjection r D P).app W (C.basis j))) =
    halfScalar (E := E) W *
      normalHessianCoefficient r C σ i j

attribute [instance] HessianForm.nondegenerate

end MathlibExt.AlgebraicGeometry.CriticalHessianModels
