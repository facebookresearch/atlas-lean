/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralOperationalChow
public import MathlibExt.AlgebraicGeometry.SchemeNormalBundleMaps

/-!
# Integral refined Gysin on actual intersection normal cones

Field-scheme wrappers identify the actual native pullbacks. The cone map is
the coefficient/degree-one-normalized map of Rees algebras from the actual
scheme-theoretic intersection. Specialization is fixed on every integral
closed cycle by that cycle's own intersection normal-cone fundamental class.
The final Gysin operation is inverse fixed bundle pullback after the canonical
cone closed pushforward. It applies equally to excess intersections.

Ordinary scheme specialization, homotopy invariance and refined Gysin are
completed source integration dependencies, not new Wanted results.
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Chow/BivariantLemmas/VirtualNormalConeFundamental.lean,
VirtualNormalBundleNormalConeBaseChange.lean and
VirtualNormalBundleClassConstruction.lean (0FBK), Apache 2.0.
Native Rees/cotangent credits are in `SchemeNormalBundleMaps`.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace AlgebraicGeometry.IntegralGysinRecipes

open CategoryTheory CategoryTheory.Limits IntegerSchemeChow IntegralOperationalChow
open StackCycleGeometry MathlibExt.AlgebraicGeometry
open SchemeNormalBundleMaps

variable {k : Type} [Field k]

/-- The native pullback, including both projection maps. -/
structure FieldPullback {X Y Z : FieldScheme k}
    (f : X.scheme ⟶ Z.scheme) (g : Y.scheme ⟶ Z.scheme) where
  source : FieldScheme k
  fst : source.scheme ⟶ X.scheme
  snd : source.scheme ⟶ Y.scheme
  native : source.scheme.left ≅ pullback f.left g.left
  fst_normalized : native.hom ≫ pullback.fst f.left g.left = fst.left
  snd_normalized : native.hom ≫ pullback.snd f.left g.left = snd.left

theorem FieldPullback.condition {X Y Z : FieldScheme k}
    {f : X.scheme ⟶ Z.scheme} {g : Y.scheme ⟶ Z.scheme} (B : FieldPullback f g) :
    B.fst ≫ f = B.snd ≫ g := by
  apply Over.OverMorphism.ext
  change B.fst.left ≫ f.left = B.snd.left ≫ g.left
  rw [← B.fst_normalized, ← B.snd_normalized, Category.assoc, Category.assoc,
    pullback.condition]

structure FieldClosedIntegral (T : FieldScheme k) (d : ℤ) where
  source : FieldScheme k
  [integral : IsIntegral source.scheme.left]
  inclusion : source.scheme ⟶ T.scheme
  [closed : IsClosedImmersion inclusion.left]
  dimension : ℕ
  dimension_eq : (dimension : ℤ) = d
  krullDimension_eq : topologicalKrullDim source.scheme.left = (dimension : ℕ)

attribute [instance] FieldClosedIntegral.integral FieldClosedIntegral.closed

def FieldClosedIntegral.native {T : FieldScheme k} {d : ℤ} (V : FieldClosedIntegral T d) :
    ClosedIntegralScheme T.scheme.left d where
  scheme := V.source.scheme.left
  integral := inferInstance
  noetherian := inferInstance
  inclusion := V.inclusion.left
  closed := inferInstance
  dimension := V.dimension
  dimension_eq := V.dimension_eq
  krullDimension_eq := V.krullDimension_eq

def FieldClosedIntegral.cycle {T : FieldScheme k} {d : ℤ} (V : FieldClosedIntegral T d) :
    CycleGroup T.scheme.left d := closedCycle V.native

def fundamental (X : FieldScheme k) (d : ℤ) : CycleGroup X.scheme.left d :=
  dimensionPart X.scheme.left d (integralFundamentalCycle X.scheme.left)

def chowCast (X : FieldScheme k) {d e : ℤ} (h : d = e) : ChowGroup X d →+ ChowGroup X e := by
  cases h
  exact AddMonoidHom.id _

structure FieldNormalBundle {Z Y : FieldScheme k}
    (i : Z.scheme ⟶ Y.scheme) [IsClosedImmersion i.left] (c : ℕ) where
  model : NormalBundleModel i.left c
  bundle : FieldScheme k
  projection : bundle.scheme ⟶ Z.scheme
  identifies : bundle.scheme.left ≅ model.total
  projection_normalized : identifies.hom ≫ model.projection = projection.left
  [flat : Flat projection.left]
  relativeDimension : PureRelativeDimension projection c

attribute [instance] FieldNormalBundle.flat

variable (O : CycleOperations (k := k))

def bundlePullback {Z Y : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {c : ℕ} (N : FieldNormalBundle i c) (d : ℤ) :
    ChowGroup Z (d - c) →+ ChowGroup N.bundle d :=
  (chowCast N.bundle (by omega)).comp
    (O.flat N.projection c N.relativeDimension (d - c))

/-- Bijectivity concerns the fixed, cycle-normalized bundle projection map. -/
structure BundleInverse {Z Y : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {c : ℕ} (N : FieldNormalBundle i c) : Prop where
  bijective : ∀ d, Function.Bijective (bundlePullback O N d)

def bundleInverse {Z Y : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {c : ℕ} (N : FieldNormalBundle i c)
    (B : BundleInverse O N) (d : ℤ) : ChowGroup N.bundle d ≃+ ChowGroup Z (d - c) :=
  (AddEquiv.ofBijective (bundlePullback O N d) (B.bijective d)).symm

/-- An actual vector bundle on W pulled back from the original normal bundle. -/
structure PulledNormalBundle {Z Y T : FieldScheme k}
    (i : Z.scheme ⟶ Y.scheme) [IsClosedImmersion i.left]
    (t : T.scheme ⟶ Y.scheme) (c : ℕ) (N : FieldNormalBundle i c)
    (B : FieldPullback i t) where
  square : FieldPullback N.projection B.fst
  [flat : Flat square.snd.left]
  relativeDimension : PureRelativeDimension square.snd c
  inverse : ∀ d : ℤ, Function.Bijective
    ((chowCast square.source (show (d - c) + c = d by omega)).comp
      (O.flat square.snd c relativeDimension (d - c)))

attribute [instance] PulledNormalBundle.flat

def pulledBundlePullback {Z Y T : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {t : T.scheme ⟶ Y.scheme} {c : ℕ}
    {N : FieldNormalBundle i c} {B : FieldPullback i t}
    (P : PulledNormalBundle O i t c N B) (d : ℤ) :
    ChowGroup B.source (d - c) →+ ChowGroup P.square.source d :=
  (chowCast P.square.source (by omega)).comp
    (O.flat P.square.snd c P.relativeDimension (d - c))

def pulledBundleInverse {Z Y T : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {t : T.scheme ⟶ Y.scheme} {c : ℕ}
    {N : FieldNormalBundle i c} {B : FieldPullback i t}
    (P : PulledNormalBundle O i t c N B) (d : ℤ) :
    ChowGroup P.square.source d ≃+ ChowGroup B.source (d - c) :=
  (AddEquiv.ofBijective (pulledBundlePullback O P d) (P.inverse d)).symm

structure RefinedGeometry {Z Y T : FieldScheme k}
    (i : Z.scheme ⟶ Y.scheme) [IsClosedImmersion i.left]
    (t : T.scheme ⟶ Y.scheme) (c : ℕ) where
  regular : RegularEmbedding i.left c
  square : FieldPullback i t
  [intersectionClosed : IsClosedImmersion square.snd.left]
  normal : FieldNormalBundle i c
  originalCone : IntegralOperationalChow.NormalConeModel i
  originalEmbedding : ConeEmbedding i.left normal.model originalCone.geometric
  intersectionCone : IntegralOperationalChow.NormalConeModel square.snd
  coneSquare : ConeSquare i.left originalCone.geometric square.snd.left square.fst.left t.left
    (congrArg (fun f : square.source.scheme ⟶ Y.scheme ↦ f.left) square.condition).symm
    intersectionCone.geometric
  pulledBundle : PulledNormalBundle O i t c normal square
  embedding : intersectionCone.cone.scheme ⟶ pulledBundle.square.source.scheme
  [embeddingClosed : IsClosedImmersion embedding.left]
  first_projection : embedding.left ≫ pulledBundle.square.fst.left =
    intersectionCone.identifies.hom ≫ coneSquare.map ≫ originalEmbedding.map ≫ normal.identifies.inv
  second_projection : embedding ≫ pulledBundle.square.snd = intersectionCone.projection

attribute [instance] RefinedGeometry.intersectionClosed RefinedGeometry.embeddingClosed

/-- Integral-cycle specialization uses its own scheme-theoretic intersection
normal cone, mapped by the actual closed-immersion square to the ambient cone. -/
structure ComponentSpecialization {Z Y T : FieldScheme k}
    {i : Z.scheme ⟶ Y.scheme} [IsClosedImmersion i.left]
    {t : T.scheme ⟶ Y.scheme} {c : ℕ} (G : RefinedGeometry O i t c)
    (d : ℤ) (V : FieldClosedIntegral T d) where
  intersection : FieldPullback G.square.snd V.inclusion
  [closed : IsClosedImmersion intersection.snd.left]
  cone : IntegralOperationalChow.NormalConeModel intersection.snd
  coneSquare : ConeSquare G.square.snd.left G.intersectionCone.geometric
    intersection.snd.left intersection.fst.left V.inclusion.left
    (congrArg (fun f : intersection.source.scheme ⟶ T.scheme ↦ f.left)
      intersection.condition).symm cone.geometric
  map : cone.cone.scheme ⟶ G.intersectionCone.cone.scheme
  normalized : map.left = cone.identifies.hom ≫ coneSquare.map ≫ G.intersectionCone.identifies.inv
  [proper : IsProper map.left]

attribute [instance] ComponentSpecialization.closed ComponentSpecialization.proper

structure Specialization {Z Y T : FieldScheme k}
    {i : Z.scheme ⟶ Y.scheme} [IsClosedImmersion i.left]
    {t : T.scheme ⟶ Y.scheme} {c : ℕ} (G : RefinedGeometry O i t c) where
  components : ∀ d (V : FieldClosedIntegral T d), ComponentSpecialization O G d V
  map : ∀ d, ChowGroup T d →+ ChowGroup G.intersectionCone.cone d
  normalized : ∀ d (V : FieldClosedIntegral T d),
    map d (cycleClass T d V.cycle) = O.proper (components d V).map d
      (cycleClass (components d V).cone.cone d (fundamental (components d V).cone.cone d))

/-- The operation is literally inverse bundle pullback, cone closed push,
and normal-cone specialization, in that order. -/
def refinedGysin {Z Y T : FieldScheme k} {i : Z.scheme ⟶ Y.scheme}
    [IsClosedImmersion i.left] {t : T.scheme ⟶ Y.scheme} {c : ℕ}
    (G : RefinedGeometry O i t c) (S : Specialization O G) (d : ℤ) :
    ChowGroup T d →+ ChowGroup G.square.source (d - c) :=
  (pulledBundleInverse O G.pulledBundle d).toAddMonoidHom.comp
    ((O.proper G.embedding d).comp (S.map d))

end AlgebraicGeometry.IntegralGysinRecipes
