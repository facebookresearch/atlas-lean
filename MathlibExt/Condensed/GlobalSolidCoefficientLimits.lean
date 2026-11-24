/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Condensed.LocalSolidCoefficientModels
public import MathlibExt.CategoryTheory.CategoricalCoefficientLimits
public import MathlibExt.CategoryTheory.SheafHypercoverModels
public import MathlibExt.AlgebraicGeometry.PerfectoidVStackSites

/-!
# Actual global solid coefficient limits and v-hyperdescent maps

Good charts have the source's actual finite dim.trg map of their tilt to
a totally disconnected space. Their coefficient diagrams retain the
actual local modified DG categories and scalar-changing nerve maps.
Global values are native categorical limits over all these affine tests.
Groupoid stack values use their actual comparison-preserving chart site,
so stabilizers remain in the indexing diagram.

Every reindexing and hypercover comparison is built from the displayed
diagram augmentations, native limit projections and the original maps.
Functorial categorical assembly, affine normalization and v-hyperdescent
are direct construction/proof requests, not input assumptions.

Source: Anschuetz--Mann, arXiv:2403.01951v2, Theorems 1.1 and 4.7,
Definitions 2.3--2.4 and 4.2; Scholze, arXiv:1709.07343v4, Section 21.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.GlobalSolidCoefficientLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.CategoryTheory.CategoricalCoefficientLimits
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.AlgebraicGeometry.PerfectoidGeometricBounds
open MathlibExt.AlgebraicGeometry.PerfectoidVStackSites
open LocalSolidCoefficientModels

variable (p : ℕ) [Fact p.Prime]

/-- Exactly the bounded original affines qualified for local coefficient identification. -/
abbrev GoodAffine :=
  (show ObjectProperty (AffineUntilting p) from
    fun P ↦ HasBoundedTotallyDisconnectedMap p P.tilt.pair).FullSubcategory

/-- The actual original perfectoid representable/sheafification functor. -/
def affineSheafFunctor : AffineUntilting p ⥤ Sheaf (originalVTopology p) (Type 1) :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{1, 0}) ⋙
    presheafToSheaf (originalVTopology p) (Type 1)

/-- The actual bounded-affine sheaf functor. -/
def goodAffineSheaves : GoodAffine p ⥤ Sheaf (originalVTopology p) (Type 1) :=
  (show ObjectProperty (AffineUntilting p) from
    fun P ↦ HasBoundedTotallyDisconnectedMap p P.tilt.pair).ι ⋙ affineSheafFunctor p

/-- A categorical local diagram with actual local DG scalar-extension normalization. The local
dictionaries `coefficients` and the strict pullbacks `pullback` are chosen together. The field
`scalar_normalized` identifies each arrow of the assembled functor `diagram` with the corresponding
geometric pullback up to an equivalence homotopy, one arrow at a time: no coherence of these
homotopies over composites is required. Hence statements about limits of `diagram` concern this
chosen diagram; they are not determined by the geometric pullbacks alone, and a homotopy-coherent
identification with the geometric pullback diagram is not part of this structure. -/
structure LocalDiagram where
  coefficients : ∀ P : GoodAffine p, LocalModel p P.obj
  pullback : ∀ {P Q : GoodAffine p} (f : P ⟶ Q),
    PullbackModel p f.hom (coefficients P) (coefficients Q)
  diagram : (GoodAffine p)ᵒᵖ ⥤ SSet.{2}
  innerKan : ∀ P, IsInnerKan (diagram.obj (op P))
  comparison : ∀ P : GoodAffine p, localNerve p (coefficients P) ⟶ diagram.obj (op P)
  equivalence : ∀ P, IsCategoricalEquivalence (comparison P)
  scalar_normalized : ∀ {P Q : GoodAffine p} (f : P ⟶ Q),
    EquivalenceHomotopy ((pullback f).nerveMap p ≫ comparison P)
      (comparison Q ≫ diagram.map f.op)

/-- All actual bounded affine maps into the given original v-sheaf. -/
abbrev SheafTests (F : Sheaf (originalVTopology p) (Type 1)) :=
  CostructuredArrow (goodAffineSheaves p) F

/-- Forget the test's structure map while retaining its real bounded untilt. -/
abbrev sheafProjection (F : Sheaf (originalVTopology p) (Type 1)) :
    SheafTests p F ⥤ GoodAffine p := CostructuredArrow.proj (goodAffineSheaves p) F

/-- The actual local coefficient diagram of that v-sheaf. -/
def sheafDiagram (G : LocalDiagram p) (F : Sheaf (originalVTopology p) (Type 1)) :
    (SheafTests p F)ᵒᵖ ⥤ SSet.{2} := (sheafProjection p F).op ⋙ G.diagram

/-- The actual categorical value, computed from the prescribed local diagram. -/
abbrev sheafValue (G : LocalDiagram p) (F : Sheaf (originalVTopology p) (Type 1))
    (M : DiagramModel.{2, 1, 0} (sheafDiagram p G F)) := categoricalLimit M

/-- Actual postcomposition of the bounded chart maps. -/
abbrev reindexSheafTests {F H : Sheaf (originalVTopology p) (Type 1)} (f : F ⟶ H) :
    SheafTests p F ⥤ SheafTests p H := CostructuredArrow.map f

/-- The coefficient diagram is unchanged on actual rings under this reindexing. -/
def reindexSheafIso (G : LocalDiagram p)
    {F H : Sheaf (originalVTopology p) (Type 1)} (f : F ⟶ H) :
    (reindexSheafTests p f).op ⋙ sheafDiagram p G H ≅ sheafDiagram p G F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro U V g; rfl)

/-- The native categorical restriction from the displayed augmentations and projections. -/
def sheafRestriction (G : LocalDiagram p)
    {F H : Sheaf (originalVTopology p) (Type 1)} (f : F ⟶ H)
    (MH : DiagramModel.{2, 1, 0} (sheafDiagram p G H))
    (MF : DiagramModel.{2, 1, 0} (sheafDiagram p G F)) :
    sheafValue p G H MH ⟶ sheafValue p G F MF :=
  categoricalRestriction (reindexSheafTests p f).op (reindexSheafIso p G f) MH MF

/-- Actual stack-site charts whose original untilt has the required geometric bound. -/
abbrev StackTests (F : PerfdVStack p) :=
  (show ObjectProperty (StackSite F) from
    fun T ↦ HasBoundedTotallyDisconnectedMap p T.base.tilt.pair).FullSubcategory

/-- The actual geometric projection retains all fibre arrows in its domain. -/
def stackProjection (F : PerfdVStack p) : StackTests p F ⥤ GoodAffine p where
  obj T := ⟨T.obj.base, T.property⟩
  map f := ObjectProperty.homMk f.hom.base

/-- The genuine categorical diagram on the whole comparison-preserving stack chart site. -/
def stackDiagram (G : LocalDiagram p) (F : PerfdVStack p) :
    (StackTests p F)ᵒᵖ ⥤ SSet.{2} := (stackProjection p F).op ⋙ G.diagram

/-- The actual global stack coefficient space, including its stabilizer descent data. -/
abbrev stackValue (G : LocalDiagram p) (F : PerfdVStack p)
    (M : DiagramModel.{2, 1, 1} (stackDiagram p G F)) := categoricalLimit M

/-- Reindex the actual groupoid stack charts by the whole strong transformation. -/
def reindexStackTests {F H : PerfdVStack p} (f : F.Hom H) :
    StackTests p F ⥤ StackTests p H where
  obj T := ⟨(mapSite f).obj T.obj, T.property⟩
  map g := ObjectProperty.homMk ((mapSite f).map g.hom)

/-- Reindexing retains the actual local untilt coefficients of every stack chart. -/
def reindexStackIso (G : LocalDiagram p) {F H : PerfdVStack p} (f : F.Hom H) :
    (reindexStackTests p f).op ⋙ stackDiagram p G H ≅ stackDiagram p G F :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro U V g; rfl)

/-- The fixed native global stack restriction. -/
def stackRestriction (G : LocalDiagram p) {F H : PerfdVStack p} (f : F.Hom H)
    (MH : DiagramModel.{2, 1, 1} (stackDiagram p G H))
    (MF : DiagramModel.{2, 1, 1} (stackDiagram p G F)) :
    stackValue p G H MH ⟶ stackValue p G F MF :=
  categoricalRestriction (reindexStackTests p f).op (reindexStackIso p G f) MH MF

/-- A functorial global presentation identified with these native categorical limits. -/
structure GlobalModel (G : LocalDiagram p) where
  functor : (Sheaf (originalVTopology p) (Type 1))ᵒᵖ ⥤ SSet.{2}
  models : ∀ F, DiagramModel.{2, 1, 0} (sheafDiagram p G F)
  comparison : ∀ F, functor.obj (op F) ⟶ sheafValue p G F (models F)
  equivalence : ∀ F, IsCategoricalEquivalence (comparison F)
  reindex_normalized : ∀ {F H : Sheaf (originalVTopology p) (Type 1)} (f : F ⟶ H),
    EquivalenceHomotopy (functor.map f.op ≫ comparison F)
      (comparison H ≫ sheafRestriction p G f (models H) (models F))

/-- The actual identity test of a qualified affine, with its specified original coefficients. -/
def affineTest (P : GoodAffine p) :
    SheafTests p ((goodAffineSheaves p).obj P) :=
  CostructuredArrow.mk (𝟙 ((goodAffineSheaves p).obj P))

/-- The native affine projection of the actual global categorical model. -/
def affineProjection {G : LocalDiagram p} (M : GlobalModel p G) (P : GoodAffine p) :=
  M.comparison ((goodAffineSheaves p).obj P) ≫
    limit.π (M.models ((goodAffineSheaves p).obj P)).diagram (op (affineTest p P))

/-- The local side of the same comparison span uses its actual dictionary and augmentation. -/
def affineLocalComparison {G : LocalDiagram p} (M : GlobalModel p G)
    (P : GoodAffine p) :=
  G.comparison P ≫ (M.models ((goodAffineSheaves p).obj P)).augmentation.app
    (op (affineTest p P))

/-- Affine identification is a result about the prescribed native projection span. -/
def IsAffineNormalized {G : LocalDiagram p} (M : GlobalModel p G) : Prop :=
  ∀ P : GoodAffine p, IsCategoricalEquivalence (affineProjection p M P) ∧
    IsCategoricalEquivalence (affineLocalComparison p M P)

/-- The original hypercover gives its actual cosimplicial coefficient diagram. -/
def hypercoverDiagram {G : LocalDiagram p} (M : GlobalModel p G)
    {F : Sheaf (originalVTopology p) (Type 1)}
    (H : MathlibExt.CategoryTheory.SheafHypercoverModels.Hypercover F) :
    SimplexCategory ⥤ SSet.{2} :=
  H.diagram.rightOp ⋙ (Over.forget F).op ⋙ M.functor

/-- The actual augmentation cone, obtained by the original structure maps. -/
def hypercoverCone {G : LocalDiagram p} (M : GlobalModel p G)
    {F : Sheaf (originalVTopology p) (Type 1)}
    (H : MathlibExt.CategoryTheory.SheafHypercoverModels.Hypercover F) :
    Cone (hypercoverDiagram p M H) where
  pt := M.functor.obj (op F)
  π.app n := M.functor.map (H.diagram.obj (op n)).hom.op
  π.naturality n m f := by
    change (𝟙 _) ≫ M.functor.map (H.diagram.obj (op m)).hom.op =
      M.functor.map (H.diagram.obj (op n)).hom.op ≫
        M.functor.map (H.diagram.map f.op).left.op
    rw [Category.id_comp, ← M.functor.map_comp]
    congr 1
    exact (congrArg Quiver.Hom.op (Over.w (H.diagram.map f.op))).symm

/-- The actual v-hyperdescent comparison uses the native cone lift and model augmentation. -/
def hyperdescentMap {G : LocalDiagram p} (M : GlobalModel p G)
    {F : Sheaf (originalVTopology p) (Type 1)}
    (H : MathlibExt.CategoryTheory.SheafHypercoverModels.Hypercover F)
    (R : DiagramModel.{2, 0, 0} (hypercoverDiagram p M H)) :
    M.functor.obj (op F) ⟶ categoricalLimit R :=
  limit.lift _ (hypercoverCone p M H) ≫ limitComparison R

/-- Hypercompleteness is a conclusion about these actual prescribed comparison maps: every
hypercover diagram has a replacement model, and for every replacement the hyperdescent comparison
is a categorical equivalence. -/
def IsHypercomplete {G : LocalDiagram p} (M : GlobalModel p G) : Prop :=
  ∀ (F : Sheaf (originalVTopology p) (Type 1))
    (H : MathlibExt.CategoryTheory.SheafHypercoverModels.Hypercover F),
    Nonempty (DiagramModel.{2, 0, 0} (hypercoverDiagram p M H)) ∧
      ∀ R : DiagramModel.{2, 0, 0} (hypercoverDiagram p M H),
        IsCategoricalEquivalence (hyperdescentMap p M H R)

end MathlibExt.Condensed.GlobalSolidCoefficientLimits
