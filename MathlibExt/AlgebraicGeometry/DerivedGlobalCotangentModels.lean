/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations
public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels

/-!
# Cotangent mapping data over complete affine families

The coefficient kernel is fixed by a whole semilinear functor and its
enhanced localization, including every affine/simplex morphism. The
derivation space is the native based-fibre limit for the whole family.
The mapping data use actual DG Hom in a full realization of QCoh.
Full coherent corepresentability is supplied separately by the actual
left-fibration contract in `DerivedCoherentCotangentModels`.

This excludes a global object that merely has isomorphic pointwise
fibres. Closed coefficient maps are normalized by the entire raw
natural-transformation homotopy and a native coherent comparison square.
No tangent/endomorphism identification or symplectic nondegeneracy is
included in the construction input.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV arXiv:1111.3209v4, conventions
and §1.2; Lurie, Higher Algebra, §7.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open scoped Simplicial

universe u v
variable {k : Type u} [CommRing k]

/-- Native closed DG maps as actual coherent-nerve edges, in either coefficient universe. -/
def dgEdge {r : Type u} [CommRing r] {C : Type v} [DGCategory r C] {V W : C}
    (f : DGHom r 0 V W) (h : f ∈ dgCycles r V W) :
    SSet.Edge (X := dgNerve (k := r) C) (objectVertex V) (objectVertex W) := by
  let z : 𝟙_ (Cochains r) ⟶ dgHomComplex r V W :=
    ForgetEnrichment.homTo (Cochains r) (dgClosedHomOf (C := C) r f h)
  apply SimplicialNerve.edgeMk
  apply ForgetEnrichment.homOf SSet
  rw [DGSimplicialCategory.hom_eq]
  simpa only [DGSimplicialCategory.underlying_of] using
    Functor.LaxMonoidal.ε (cochainToSSet r) ≫ (cochainToSSet r).map z

/-- An actual natural map of split first-order algebra systems. -/
structure SquareZeroFamilyMap {X : Prestack k} (E F : SquareZeroFamily X) where
  map : E.algebra ⟶ F.algebra
  projection : map ≫ F.projection = E.projection
  splitting : E.splitting ≫ map = F.splitting

/-- The actual identity map of a split square-zero family. -/
def squareZeroFamilyId {X : Prestack k} (E : SquareZeroFamily X) : SquareZeroFamilyMap E E where
  map := 𝟙 _
  projection := Category.id_comp _
  splitting := Category.comp_id _

/-- Native algebra-diagram composition preserves projection and splitting. -/
def squareZeroFamilyComp {X : Prestack k} {E F H : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F) (g : SquareZeroFamilyMap F H) : SquareZeroFamilyMap E H where
  map := f.map ≫ g.map
  projection := by rw [Category.assoc, g.projection, f.projection]
  splitting := by rw [← Category.assoc, f.splitting, g.splitting]

/-- A split-family morphism is determined by its actual algebra-diagram map. -/
theorem squareZeroFamilyMap_ext {X : Prestack k} {E F : SquareZeroFamily X}
    {f g : SquareZeroFamilyMap E F} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The genuine category of split first-order affine systems. -/
instance {X : Prestack k} : Category (SquareZeroFamily X) where
  Hom E F := SquareZeroFamilyMap E F
  id E := squareZeroFamilyId E
  comp f g := squareZeroFamilyComp f g
  id_comp _f := squareZeroFamilyMap_ext (Category.id_comp _)
  comp_id _f := squareZeroFamilyMap_ext (Category.comp_id _)
  assoc _f _g _h := squareZeroFamilyMap_ext (Category.assoc _ _ _)

/-- The complete actual algebra diagram of a split-family system. -/
def squareAlgebraFunctor (X : Prestack k) : SquareZeroFamily X ⥤ (Families X ⥤ SAlg k) where
  obj E := E.algebra
  map f := f.map

/-- Kernel maps are the actual normalized square-zero projection kernels. -/
structure KernelFamilyMap {N : ShuffleAlgebraFunctor k} {X : Prestack k}
    {E F : SquareZeroFamily X} (K : KernelFamily N E) (L : KernelFamily N F)
    (f : SquareZeroFamilyMap E F) where
  map : K.functor ⟶ L.functor
  algebra : ∀ j : Families X, HEq (map.app j).algebra (𝟙 ((algebraProjection X).obj j))
  coefficient : ∀ j : Families X,
    HEq (map.app j).map
      ((K.kernel j).valueIso.hom ≫
        MathlibExt.AlgebraicGeometry.DerivedCotangentModels.kernelMap
          (E := E.extension j) (F := F.extension j) (f.map.app j)
          (congrArg (fun t => t.app j) f.projection) ≫ (L.kernel j).valueIso.inv)

/-- Ordinary natural-transformation homotopy in the exact raw module nerve.
Endpoints and every vertical edge determine all higher simplices because the
target is the nerve of the actual ordinary semilinear category. -/
structure KernelNaturalHomotopy {N : ShuffleAlgebraFunctor k} {X : Prestack k}
    {E F : SquareZeroFamily X} {K : KernelFamily N E} {L : KernelFamily N F}
    {f : SquareZeroFamilyMap E F} (a : KernelFamilyMap K L f) where
  map : nerve (Families X) ⊗ (Δ[1] : SSet.{u + 1}) ⟶ nerve (AffineModulePoint N)
  source : parameterAt _ 0 ≫ map = nerveMap K.functor
  target : parameterAt _ 1 ≫ map = nerveMap L.functor
  arrow : ∀ j : Families X,
    map.app (op ⦋1⦌)
      ((nerve (Families X)).σ 0 (ComposableArrows.mk₀ j), SSet.stdSimplex.edge 1 0 1 (by decide)) =
      (nerve.edgeMk (a.map.app j)).edge

variable {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
variable {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
variable {X : Prestack k} (G : QCohEnhancement M U X) (R : RawModuleRealization M)

/-- The actual enhanced realization of the whole normalized coefficient kernel. -/
structure KernelDGModel {E : SquareZeroFamily X} {K : KernelFamily N E}
    (KQ : KernelQCohModel M R K) where
  object : G.category
  equivalence : SSet.Edge (X := qcoh M X)
    (G.realization.app (op ⦋0⦌) (objectVertex object)) KQ.object
  is_equivalence : IsEquivalenceEdge (qcoh M X) equivalence.edge

/-- A coefficient map fixes the entire raw-family homotopy, and its actual
DG representative through the coherent comparison square. -/
structure KernelDGMap {E F : SquareZeroFamily X} {K : KernelFamily N E}
    {L : KernelFamily N F} {KQ : KernelQCohModel M R K} {LQ : KernelQCohModel M R L}
    (KD : KernelDGModel G R KQ) (LD : KernelDGModel G R LQ)
    {f : SquareZeroFamilyMap E F} {a : KernelFamilyMap K L f}
    (H : KernelNaturalHomotopy a) where
  map : DGHom (LargeScalar k) 0 KD.object LD.object
  closed : map ∈ dgCycles (LargeScalar k) KD.object LD.object
  coefficient : SSet.Edge (X := qcoh M X) KQ.object LQ.object
  normalized : ∀ (m : SimplexCategoryᵒᵖ) (g : op ⦋1⦌ ⟶ m)
    (b : (nerve (Families X)).obj m),
    (coefficient.edge.val.app m g) b =
      R.map.app m (H.map.app m (b, SSet.stdSimplex.objEquiv.symm g.unop))
  composite : SSet.Edge (X := qcoh M X)
    (G.realization.app (op ⦋0⦌) (objectVertex KD.object)) LQ.object
  left : SSet.Edge.CompStruct ((dgEdge map closed).map G.realization) LD.equivalence composite
  right : SSet.Edge.CompStruct KD.equivalence coefficient composite

/-- The actual mapping space in the full underlying QCoh realization.
Source-linear coefficient adapters are separately normalized constructions. -/
def homSpace (L K : G.category) : SSet.{u + 1} :=
  (cochainToSSet (LargeScalar k)).obj (dgHomComplex (LargeScalar k) L K)

/-- Closed coefficient maps induce native postcomposition on every Hom degree. -/
def homPostcompose (L : G.category) {K K' : G.category}
    (f : DGHom (LargeScalar k) 0 K K') (h : f ∈ dgCycles (LargeScalar k) K K') :
    homSpace G L K ⟶ homSpace G L K' :=
  (cochainToSSet (LargeScalar k)).map
    (eHomWhiskerLeft (Cochains (LargeScalar k))
      (ForgetEnrichment.of (Cochains (LargeScalar k)) L)
      (dgClosedHomOf (C := G.category) (LargeScalar k) f h))

/-- The whole coefficient-space map of actual split algebra systems. -/
def liftMap {E F : SquareZeroFamily X} (f : SquareZeroFamilyMap E F) :
    liftDiagram X E ⟶ liftDiagram X F :=
  mappingFamiliesMap X (Functor.whiskerRight f.map X)

/-- The actual map of compatible lift-fibre diagrams. Its sole square hypothesis
is the redundant native mapping form of the projection-preserving algebra equation. -/
def derivationDiagramMap {B : DerivationBase X} {E F : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E) :
    derivationDiagram B E ⟶ derivationDiagram B F :=
  pullback.lift (pullback.fst _ _ ≫ prod.map (liftMap f) (𝟙 _)) (pullback.snd _ _) (by
    have hw : prod.map (liftMap f) (𝟙 _) ≫ prod.map (liftProjection X F) (familyPoint X) =
        prod.map (liftProjection X E) (familyPoint X) := by
      apply prod.hom_ext <;> simp [h]
    rw [Category.assoc, hw, pullback.condition])

/-- The fixed map lifts through the actual source replacement augmentation. -/
def derivationMapLift {B : DerivationBase X} {E F : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F) :
    DE.replacement.diagram ⟶ DF.replacement.diagram :=
  Classical.choose (DF.replacement.fibrant _ _ DE.replacement.map
    (fun j => ⟨DE.replacement.mono j, DE.replacement.weak j⟩)
    (derivationDiagramMap f h ≫ DF.replacement.map))

/-- `ℓ` extends the replacement of `DE` along `f`: it lifts the map of derivation diagrams through
the augmentation of `DF`. Such lifts exist by injective fibrancy (`derivationMapLift` chooses one)
but are not unique. -/
def IsDerivationLift {B : DerivationBase X} {E F : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F)
    (ℓ : DE.replacement.diagram ⟶ DF.replacement.diagram) : Prop :=
  DE.replacement.map ≫ ℓ = derivationDiagramMap f h ≫ DF.replacement.map

theorem derivationMapLift_spec {B : DerivationBase X} {E F : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F) :
    IsDerivationLift f h DE DF (derivationMapLift f h DE DF) := by
  unfold IsDerivationLift derivationMapLift
  exact Classical.choose_spec (DF.replacement.fibrant _ _ DE.replacement.map
    (fun j => ⟨DE.replacement.mono j, DE.replacement.weak j⟩)
    (derivationDiagramMap f h ≫ DF.replacement.map))

/-- The map of global derivation spaces induced by a map `ℓ` from the replacement diagram of `DE`
to that of `DF`: the induced map of limits. -/
def derivationMapOf {B : DerivationBase X} {E F : SquareZeroFamily X}
    {DE : DerivationModel B E} {DF : DerivationModel B F}
    (ℓ : DE.replacement.diagram ⟶ DF.replacement.diagram) :
    derivationSpace DE ⟶ derivationSpace DF := limMap ℓ

/-- Native limit functoriality and the chosen lift `derivationMapLift` give the global map of
derivations (`derivationMapOf` with that lift); it is canonical only after inverting weak
equivalences. -/
def derivationMap {B : DerivationBase X} {E F : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F) :
    derivationSpace DE ⟶ derivationSpace DF := limMap (derivationMapLift f h DE DF)

theorem derivationMap_eq_derivationMapOf {B : DerivationBase X} {E F : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F) :
    derivationMap f h DE DF = derivationMapOf (derivationMapLift f h DE DF) := rfl

/-- The canonical split lift of the entire tautological family. -/
def splitLift (E : SquareZeroFamily X) :
    (Functor.const (Families X)).obj (Δ[0] : SSet.{u + 1}) ⟶ liftDiagram X E :=
  familyPoint X ≫ mappingFamiliesMap X (Functor.whiskerRight E.splitting X)

/-- The actual split algebra section fixes its whole-family first-order origin. -/
theorem splitLift_projection (E : SquareZeroFamily X) :
    splitLift E ≫ liftProjection X E = familyPoint X := by
  change (familyPoint X ≫ (mappingFamiliesFunctor X).map
      (Functor.whiskerRight E.splitting X)) ≫
        (mappingFamiliesFunctor X).map (Functor.whiskerRight E.projection X) = _
  rw [Category.assoc, ← (mappingFamiliesFunctor X).map_comp, ← Functor.whiskerRight_comp,
    E.splitting_projection]
  have hi : Functor.whiskerRight (𝟙 (algebraProjection X)) X =
      𝟙 (algebraProjection X ⋙ X) := by
    apply NatTrans.ext
    funext j
    exact X.map_id _
  rw [hi, (mappingFamiliesFunctor X).map_id]
  exact Category.comp_id _

/-- The native diagonal-path comparison of those actual compatible split lifts. -/
def originDiagram {B : DerivationBase X} (E : SquareZeroFamily X) :
    (Functor.const (Families X)).obj (Δ[0] : SSet.{u + 1}) ⟶ derivationDiagram B E :=
  pullback.lift (prod.lift (splitLift E) (𝟙 _)) (familyPoint X ≫ B.ι) (by
    apply prod.hom_ext <;> simp [Category.assoc, splitLift_projection])

/-- The actual whole-family zero derivation, through its fixed diagram augmentation. -/
def origin {B : DerivationBase X} {E : SquareZeroFamily X} (DE : DerivationModel B E) :
    (Δ[0] : SSet.{u + 1}) ⟶ derivationSpace DE :=
  limit.lift DE.replacement.diagram
    ⟨Δ[0], originDiagram E ≫ DE.replacement.map⟩

/-- The actual zero in the full DG Hom space, from its native coefficient unit. -/
def homZero (L K : G.category) : (Δ[0] : SSet.{u + 1}) ⟶ homSpace G L K :=
  SSet.const
    (((Functor.LaxMonoidal.ε (cochainToSSet (LargeScalar k)) ≫
      (cochainToSSet (LargeScalar k)).map
        (0 : 𝟙_ (Cochains (LargeScalar k)) ⟶ dgHomComplex (LargeScalar k) L K)).app
          (op ⦋0⦌)) PUnit.unit)

/-- Global cotangent corepresentability is a natural equivalence on the actual
whole-family derivation functor. Nothing is asserted from pointwise fibre names. Naturality is
asserted after inverting weak equivalences, for every lift defining the map of derivation spaces
(the lifts are not unique). -/
structure GlobalCotangentMappingData (B : DerivationBase X) where
  object : G.category
  map : ∀ (E : SquareZeroFamily X) (K : KernelFamily N E)
    (KQ : KernelQCohModel M R K) (KD : KernelDGModel G R KQ)
    (DE : DerivationModel B E), homSpace G object KD.object ⟶ derivationSpace DE
  weak : ∀ (E : SquareZeroFamily X) (K : KernelFamily N E)
    (KQ : KernelQCohModel M R K) (KD : KernelDGModel G R KQ)
    (DE : DerivationModel B E), WeakEquivalence (map E K KQ KD DE)
  zero : ∀ (E : SquareZeroFamily X) (K : KernelFamily N E)
    (KQ : KernelQCohModel M R K) (KD : KernelDGModel G R KQ)
    (DE : DerivationModel B E), homZero G object KD.object ≫ map E K KQ KD DE = origin DE
  naturality : ∀ (E F : SquareZeroFamily X) (K : KernelFamily N E)
    (L : KernelFamily N F) (KQ : KernelQCohModel M R K) (LQ : KernelQCohModel M R L)
    (KD : KernelDGModel G R KQ) (LD : KernelDGModel G R LQ)
    (f : SquareZeroFamilyMap E F) (a : KernelFamilyMap K L f)
    (H : KernelNaturalHomotopy a) (g : KernelDGMap G R KD LD H)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F)
    (ℓ : DE.replacement.diagram ⟶ DF.replacement.diagram) (_ : IsDerivationLift f h DE DF ℓ),
    (spaceQ.{u}).map (homPostcompose G object g.map g.closed ≫ map F L LQ LD DF) =
      (spaceQ.{u}).map (map E K KQ KD DE ≫ derivationMapOf ℓ)

end MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels
