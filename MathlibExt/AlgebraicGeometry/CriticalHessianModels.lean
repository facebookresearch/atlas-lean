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
cotangent derivative. Its quadratic form is fixed intrinsically at every
point `x` of the critical scheme: for tangent vectors of the larger ambient at
`x` that are orthogonal, under the Hessian of `g` (intrinsic at critical
points), to the tangent space of the smaller ambient, the form on their
normal classes is one half of that Hessian. In Joyce's étale-local normal form
`g = f ∘ α + z₁² + ⋯ + zₙ²` these vectors are `ker Hess f ⊕ span(∂_z)`, which maps onto
the normal space, so this is Joyce's form `q_{UV}` at every point; the full
Hessian of `g` does not descend to the normal quotient (already for an identity
embedding of a chart with nonzero Hessian). Being a pointwise condition, it
fixes the form on the reduction of the critical scheme, which is where the
canonical line and its transition coefficients live; the form on the
critical scheme itself (Joyce's normalization through étale normal forms) is
not encoded. The pairing and its adjoint retain all sheaf sections.

Reference: Joyce, arXiv:1304.4508v3, Propositions 2.23 and 2.25 and
Definition 2.26, equations (2.15)--(2.25). Only characteristic different from
two is needed.
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

/-- The dual of a morphism $f : M \to N$ of sheaves of modules on a scheme $T$, given by
precomposition: a morphism `map` from $\mathcal{H}om(N, \mathcal{O}_T)$ to
$\mathcal{H}om(M, \mathcal{O}_T)$ such that, for every open $W$, every section $a$ of
$\mathcal{H}om(N, \mathcal{O}_T)$ over $W$ and every $m \in M(W)$, the value of `map a` at $m$ is
$a(f(m))$. -/
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

/-- Actual Hessian coefficients of `g`, with the same regular function and scheme appLE. -/
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

/-- The Hessian pairing, in the frame `C`, of the vector with coordinates `s` against the
image of a tangent vector `t` of the smaller ambient. -/
def hessianAgainst {V : (ambient F.toAffineEmbedding).left.Opens}
    {W : E.domain.toScheme.Opens} {m : ℕ}
    {h : W ≤ (E.inclusion.left ≫ (ambientMap r).left) ⁻¹ᵁ V}
    (P : DualPrecomposition (chartCotangentMap r D))
    (C : CoordinateFrame r V W m h) (s : Fin m → Γ(E.domain.toScheme,W))
    (t : Γ(homSheaf E.domain.toScheme (chartCotangent (E := E))
      (structureModule E.domain.toScheme),W)) : Γ(E.domain.toScheme,W) :=
  ∑ i, ∑ j, s i * hessianCoefficient r C i j * C.basis.repr (P.map.app W t) j

def halfScalar (W : E.domain.toScheme.Opens) : Γ(E.domain.toScheme,W) := by
  let φ : k →+* Γ(E.domain.toScheme,W) :=
    ((scalarMap k (Over.mk (E.domain.ι ≫ X.hom))).app (op W)).hom
  exact φ ((2 : k)⁻¹)

/-- The actual normal form and adjoint. At every point of every framed affine open, the
form on the normal classes of Hessian-orthogonal vectors (orthogonal to the tangent space
of the smaller ambient) is one half of the Hessian of `g`. -/
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
    (C : CoordinateFrame r V W m h) (x : E.domain.toScheme) (hx : x ∈ W)
    (s s' : Fin m → Γ(E.domain.toScheme,W)),
    (∀ t, (E.domain.toScheme.evaluation W x hx).hom (hessianAgainst r D P C s t) = 0) →
    (∀ t, (E.domain.toScheme.evaluation W x hx).hom (hessianAgainst r D P C s' t) = 0) →
    (E.domain.toScheme.evaluation W x hx).hom (pairing.app W (pureTensorSection _ _ _ W
      ((normalProjection r D P).app W (∑ i, s i • C.basis i))
      ((normalProjection r D P).app W (∑ j, s' j • C.basis j)))) =
    (E.domain.toScheme.evaluation W x hx).hom (halfScalar (E := E) W *
      ∑ i, ∑ j, s i * s' j * hessianCoefficient r C i j)

attribute [instance] HessianForm.nondegenerate

end MathlibExt.AlgebraicGeometry.CriticalHessianModels
