/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedAlongDerivations
public import MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames

/-!
# Source-normalized global cotangent differentials

A differential is the Yoneda transpose of the actual based deformation
map X(E) → Y(E) over every coherent X coefficient. Its normalization
is one square of entire Hom/derivation left fibrations over the test
category. Precomposition fixes every initial coherent-frame coefficient
by actual composition with the closed DG arrow; all remaining frame
coefficients are unchanged. No independently chosen Jacobian is used.

Full DG pullback compares the entire native nerve functor to the actual
QCoh section pullback. Construction providers remain explicit requests.

Reference: HAG II math/0404373v7 §1.4.1; PTVV1111.3209v4 §2.2.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedAlongDerivations
open MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {X Y : Prestack k}

/-- A named package of the existing complete coefficient and cotangent models. -/
structure CotangentContext (R : RawModuleRealization M) (G : QCohEnhancement M U X) where
  kernels : KernelSystem N X
  sections : KernelSectionFunctor M R kernels
  dgKernels : KernelDGFunctor M R kernels G sections
  projection : JointLiftProjection M R kernels
  path : JointPath M R kernels
  derivations : JointDerivationModel M R kernels projection path
  fibration : DerivationFibration M R kernels derivations
  cotangent : CoherentGlobalCotangent dgKernels derivations fibration

/-- Full DG pullback is normalized against the actual entire QCoh section functor. -/
structure PullbackDGModel (f : X ⟶ Y)
    (GY : QCohEnhancement M U Y) (GX : QCohEnhancement M U X) where
  functor : EnrichedFunctor (Cochains (LargeScalar k)) GY.category GX.category
  comparison : SSet.Edge (X := mapping (dgNerve (k := LargeScalar k) GY.category) (qcoh M X))
    ((SimplicialCategory.homEquiv' _ _) (dgNerveMap functor ≫ GX.realization))
    ((SimplicialCategory.homEquiv' _ _) (GY.realization ≫ qcohPullback M f))
  equivalence : IsEquivalenceEdge _ comparison.edge

variable {R : RawModuleRealization M} {G : QCohEnhancement M U X}

/-- The actual initial object of a coherent left-slice frame. -/
def initialFrameIndex (n : SimplexCategoryᵒᵖ) :
    SimplicialThickening (ULift.{u + 1} (Fin (n.unop.len + 2))) := .mk (ULift.up 0)

/-- The actual noninitial object of the same frame. -/
def laterFrameIndex (n : SimplexCategoryᵒᵖ) (i : Fin (n.unop.len + 1)) :
    SimplicialThickening (ULift.{u + 1} (Fin (n.unop.len + 2))) := .mk (ULift.up i.succ)

/-- Transport the fixed closed arrow to the literally equal initial frame object. -/
def initialArrow {V W : G.category} (d : DGHom (LargeScalar k) 0 V W)
    (hd : d ∈ dgCycles (LargeScalar k) V W) {n : SimplexCategoryᵒᵖ}
    (a : (leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W)).obj n)
    (ha : frameObject a.val (initialFrameIndex n) = W) :
    DGHom (LargeScalar k) 0 V (frameObject a.val (initialFrameIndex n)) :=
  dgClosedHom (LargeScalar k)
    (dgClosedHomOf (C := G.category) (LargeScalar k) d hd ≫
      eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) ha.symm))

/-- Precomposition fixes every native Hom simplex of every source-fixed frame. -/
structure SlicePrecomposition {V W : G.category} (d : DGHom (LargeScalar k) 0 V W)
    (hd : d ∈ dgCycles (LargeScalar k) V W) where
  map : leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W) ⟶
    leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex V)
  over : map ≫ targetProjection _ (objectVertex V) = targetProjection _ (objectVertex W)
  source_value : ∀ (n : SimplexCategoryᵒᵖ)
    (a : (leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W)).obj n),
    frameObject a.val (initialFrameIndex n) = W
  first_value : ∀ (n : SimplexCategoryᵒᵖ)
    (a : (leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W)).obj n),
    frameObject (map.app n a).val (initialFrameIndex n) = V
  later_value : ∀ (n : SimplexCategoryᵒᵖ)
    (a : (leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W)).obj n)
    (i : Fin (n.unop.len + 1)),
    frameObject (map.app n a).val (laterFrameIndex n i) = frameObject a.val (laterFrameIndex n i)
  initial_coefficient : ∀ (n : SimplexCategoryᵒᵖ)
    (a : (leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W)).obj n)
    (j : Fin (n.unop.len + 1)) (m : ℕ)
    (s : (initialFrameIndex n ⟶[SSet.{u + 1}] laterFrameIndex n j) _⦋m⦌),
    HEq (frameCoefficient (map.app n a).val (initialFrameIndex n) (laterFrameIndex n j) m s)
      (dgComp (LargeScalar k) (initialArrow d hd a (source_value n a))
        (frameCoefficient a.val (initialFrameIndex n) (laterFrameIndex n j) m s) (zero_add _))
  later_coefficient : ∀ (n : SimplexCategoryᵒᵖ)
    (a : (leftSlice (dgNerve (k := LargeScalar k) G.category) (objectVertex W)).obj n)
    (i j : Fin (n.unop.len + 1)) (m : ℕ)
    (s : (laterFrameIndex n i ⟶[SSet.{u + 1}] laterFrameIndex n j) _⦋m⦌),
    HEq (frameCoefficient (map.app n a).val (laterFrameIndex n i) (laterFrameIndex n j) m s)
      (frameCoefficient a.val (laterFrameIndex n i) (laterFrameIndex n j) m s)

/-- Native pullback of this fixed precomposition to the entire coefficient-test family. -/
def homFamilyPrecomposition {K : KernelSystem N X} {F : KernelSectionFunctor M R K}
    (KG : KernelDGFunctor M R K G F) {V W : G.category}
    {d : DGHom (LargeScalar k) 0 V W} {hd : d ∈ dgCycles (LargeScalar k) V W}
    (P : SlicePrecomposition d hd) : homFamily KG W ⟶ homFamily KG V :=
  pullback.lift (pullback.fst _ _ ≫ P.map) (pullback.snd _ _) (by
    rw [Category.assoc, P.over, pullback.condition])

/-- Native precomposition preserves the same coefficient-test base. -/
theorem homFamilyPrecomposition_over {K : KernelSystem N X} {F : KernelSectionFunctor M R K}
    (KG : KernelDGFunctor M R K G F) {V W : G.category}
    {d : DGHom (LargeScalar k) 0 V W} {hd : d ∈ dgCycles (LargeScalar k) V W}
    (P : SlicePrecomposition d hd) :
    homFamilyPrecomposition KG P ≫ homFamilyProjection KG V = homFamilyProjection KG W := by
  simp only [homFamilyPrecomposition, homFamilyProjection, pullback.lift_snd]

/-- The pulled source cotangent represents the actual along-deformation fibration. Any fibrewise
equivalence over the tests is allowed, so a representation is determined only up to the action of
the automorphisms of the representing object (e.g. precomposition with `-1`). The canonical
representation, the restriction of the target cotangent's universal derivation along `f`, is not
constructed here. -/
structure AlongCotangentRepresentation (C : CotangentContext R G) (f : X ⟶ Y)
    (A : AlongLiftProjection M R C.kernels f C.projection)
    (B : AlongPath M R C.kernels Y)
    (D : AlongDerivationModel M R C.kernels f C.projection A B)
    (DF : AlongFibration M R C.kernels D) (L : G.category) where
  map : homFamily C.dgKernels L ⟶ DF.total
  over : map ≫ DF.projection = homFamilyProjection C.dgKernels L
  weak : ∀ t : CoefficientTest M R C.kernels,
    WeakEquivalence (fibreMap (homFamilyProjection C.dgKernels L) DF.projection map over
      (ComposableArrows.mk₀ t))

/-- The cotangent differential of a morphism of prestacks $f : X \to Y$ over $k$, relative to the
chosen representation `C`, by $f^*L_Y$, of the deformations of $Y$ along $f$ (`DF`); here $f^*L_Y$
is the image under the DG pullback model `PB` of the cotangent object $L_Y$ of `CY`. It consists of
a closed degree-zero morphism $df : f^*L_Y \to L_X$ to the cotangent object $L_X$ of `CX`, the
precomposition with $df$ on left slices of the DG nerve (`SlicePrecomposition`), and an edge, in
the mapping space over the coefficient tests, from precomposition with $df$ followed by `C` to the
representation of the derivations of $X$ by $L_X$ followed by the map `m` from derivations of $X$
to deformations of $Y$ along $f$: $df$ is the Yoneda transpose of the map induced by $f$. -/
structure CotangentDifferential (CX : CotangentContext R G) {GY : QCohEnhancement M U Y}
    (CY : CotangentContext R GY) (f : X ⟶ Y) (PB : PullbackDGModel f GY G)
    {A : AlongLiftProjection M R CX.kernels f CX.projection}
    {B : AlongPath M R CX.kernels Y} {T : AlongPathMap M R CX.kernels f CX.path B}
    {a : AlongRawMap M R CX.kernels f CX.projection A CX.path B T}
    {D : AlongDerivationModel M R CX.kernels f CX.projection A B}
    (r : AlongReplacementMap M R CX.kernels a CX.derivations D)
    (DF : AlongFibration M R CX.kernels D)
    (m : AlongFibrationMap M R CX.kernels r CX.fibration DF)
    (C : AlongCotangentRepresentation CX f A B D DF (PB.functor.obj CY.cotangent.object)) where
  map : DGHom (LargeScalar k) 0 (PB.functor.obj CY.cotangent.object) CX.cotangent.object
  closed : map ∈ dgCycles (LargeScalar k) (PB.functor.obj CY.cotangent.object) CX.cotangent.object
  precomposition : SlicePrecomposition map closed
  normalized : SSet.Edge (X := mappingOver
      (homFamilyProjection CX.dgKernels CX.cotangent.object) DF.projection)
    (overMapVertex _ _ (homFamilyPrecomposition CX.dgKernels precomposition ≫ C.map) (by
      rw [Category.assoc, C.over, homFamilyPrecomposition_over]))
    (overMapVertex _ _ (CX.cotangent.map ≫ m.map) (by
      rw [Category.assoc, m.over, CX.cotangent.over]))

end MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
