/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalISuspensionCofibrantComparison
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerStablePiHo
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.SuspensionStablePi

/-!
# The original I-Q suspension on all integer homotopy groups

The original I-cone suspension after the original Q replacement is compared
with scalar one-sphere tensor using the same level-homotopy weak span. The
proved raw scalar suspension isomorphism and original Q counit then give
both integer comparison maps on every original sequential spectrum. All
functor maps, scalar-unit factors and formal weak inverses are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry

open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiHoGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.DiagonalHomotopyGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy.SuspensionStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Index := PointedCGWH.Spectra.Sequential.Index.{u, v}
private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := Index.{u, v})
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := Index.{u, v})
private abbrev S := OriginalISuspension.suspension (B := B) (I := Index.{u, v})

/-- The actual original I-Q suspension keeps the original two complete functor maps. -/
abbrev originalISuspensionQFunctor : Carrier.{u, v} ⥤ Carrier.{u, v} := Q ⋙ S

/-- Every complete original source map is sent through the same original Q and I-suspension maps. -/
theorem originalISuspensionQFunctor_map {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    originalISuspensionQFunctor.map f = S.map (Q.map f) := rfl

/-- The projected original integer classes agree through actual identity components and maps. -/
def projectedIntegerClassNatIso {C : Type w} [Category.{z} C]
    (F : C ⥤ Carrier.{u, v}) (q : ℤ) :
    (F ⋙ H) ⋙ integerStablePiHoFunctor q ≅ F ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change (integerStablePiHoFunctor q).map (H.map (F.map f)) ≫ 𝟙 _ =
      𝟙 _ ≫ (integerStablePiFunctor q).map (F.map f)
    rw [Category.comp_id, Category.id_comp, integerStablePiHoFunctor_map])

/-- Every forward projected class function is the original quotient identity. -/
theorem projectedIntegerClassNatIso_hom_app {C : Type w} [Category.{z} C]
    (F : C ⥤ Carrier.{u, v}) (q : ℤ) (X : C) :
    (projectedIntegerClassNatIso F q).hom.app X = 𝟙 ((integerStablePiFunctor q).obj (F.obj X)) :=
  rfl

/-- Every inverse projected class function is the same original quotient identity. -/
theorem projectedIntegerClassNatIso_inv_app {C : Type w} [Category.{z} C]
    (F : C ⥤ Carrier.{u, v}) (q : ℤ) (X : C) :
    (projectedIntegerClassNatIso F q).inv.app X = 𝟙 ((integerStablePiFunctor q).obj (F.obj X)) :=
  rfl

/-- The original I-Q/scalar-Q comparison acts on the same entire original integer groups. -/
def originalIQScalarIntegerNatIso (q : ℤ) :
    originalISuspensionQFunctor.{u, v} ⋙ integerStablePiFunctor q ≅
      (Q ⋙ SuspensionGeometry.suspension) ⋙ integerStablePiFunctor q :=
  (projectedIntegerClassNatIso originalISuspensionQFunctor q).symm ≪≫
    Functor.isoWhiskerRight
      (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := Index))
      (integerStablePiHoFunctor q) ≪≫
    projectedIntegerClassNatIso (Q ⋙ SuspensionGeometry.suspension) q

/-- The forward integer comparison is the image of the actual original cofibrant weak span. -/
theorem originalIQScalarIntegerNatIso_hom_app (q : ℤ) (X : Carrier.{u, v}) :
    (originalIQScalarIntegerNatIso q).hom.app X =
      (integerStablePiHoFunctor q).map
        ((OriginalISuspensionCofibrantComparison.comparisonQ (B := B) X).hom) := by
  change 𝟙 _ ≫
    (integerStablePiHoFunctor q).map
      ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).hom.app X) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id,
    OriginalISuspensionCofibrantComparison.comparisonQ_hom_eq_original]

/-- The inverse integer comparison retains the inverse of the same original weak span. -/
theorem originalIQScalarIntegerNatIso_inv_app (q : ℤ) (X : Carrier.{u, v}) :
    (originalIQScalarIntegerNatIso q).inv.app X =
      (integerStablePiHoFunctor q).map
        ((OriginalISuspensionCofibrantComparison.comparisonQ (B := B) X).inv) := by
  change 𝟙 _ ≫
    (integerStablePiHoFunctor q).map
      ((ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).inv.app X) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id,
    OriginalISuspensionCofibrantComparison.comparisonQ_inv_eq_original]

/-- The full original Q counit induces its original integer natural transformation. -/
def qCounitIntegerNatTrans (q : ℤ) : Q.{u, v} ⋙ integerStablePiFunctor q ⟶
    integerStablePiFunctor q :=
  Functor.whiskerRight ε (integerStablePiFunctor q)

/-- The original Q counit is invertible on all integer groups by its actual level weakness. -/
def qCounitIntegerNatIso (q : ℤ) : Q.{u, v} ⋙ integerStablePiFunctor q ≅
    integerStablePiFunctor q := by
  let α := qCounitIntegerNatTrans q
  let _ : ∀ X, IsIso (α.app X) := fun X =>
    integerStablePiLevelWeak_isIso q (ε.app X)
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
  let _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The whole forward Q group component is the same original counit quotient map. -/
theorem qCounitIntegerNatIso_hom_app (q : ℤ) (X : Carrier.{u, v}) :
    (qCounitIntegerNatIso q).hom.app X = (integerStablePiFunctor q).map (ε.app X) := rfl

/-- Both Q functions agree with the original level-weak filtered-group isomorphism. -/
theorem qCounitIntegerNatIso_app (q : ℤ) (X : Carrier.{u, v}) :
    (qCounitIntegerNatIso q).app X =
      integerStablePiLevelWeakIso q (ε.app X)
        (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X) := by
  apply Iso.ext
  change (qCounitIntegerNatIso q).hom.app X = _
  rw [qCounitIntegerNatIso_hom_app, integerStablePiLevelWeakIso_hom]

/-- The actual original Q projection class is sent to the same two integer functions. -/
theorem qCounitIntegerNatIso_projectionClass (q : ℤ) (X : Carrier.{u, v}) :
    (qCounitIntegerNatIso q).app X =
      (integerStablePiHoFunctor q).mapIso
        ((Replacement.cofibrantReplacementProjectionIso (B := B) (A := Index)).app X) := by
  apply Iso.ext
  change (qCounitIntegerNatIso q).hom.app X =
    (integerStablePiHoFunctor q).map (H.map (ε.app X))
  rw [qCounitIntegerNatIso_hom_app]
  exact (integerStablePiHoFunctor_map q (ε.app X)).symm

/-- The full inverse Q group component is the original level-weak quotient inverse. -/
theorem qCounitIntegerNatIso_inv_app (q : ℤ) (X : Carrier.{u, v}) :
    (qCounitIntegerNatIso q).inv.app X =
      (integerStablePiLevelWeakIso q (ε.app X)
        (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)).inv :=
  congrArg (fun e => e.inv) (qCounitIntegerNatIso_app q X)

/-- Every raw original spectrum has the complete integer I-Q suspension isomorphism. -/
def integerISuspensionPiNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    originalISuspensionQFunctor ⋙ integerStablePiFunctor (q + 1) :=
  (qCounitIntegerNatIso q).symm ≪≫
    Functor.isoWhiskerLeft Q (integerSuspensionPiNatIso q) ≪≫
      (Functor.associator Q SuspensionGeometry.suspension
        (integerStablePiFunctor (q + 1))).symm ≪≫
      (originalIQScalarIntegerNatIso (q + 1)).symm

/-- The whole I-Q forward transformation retains Q inverse, actual scalar unit and span inverse. -/
theorem integerISuspensionPiNatIso_hom (q : ℤ) :
    (integerISuspensionPiNatIso.{u, v} q).hom =
      (qCounitIntegerNatIso q).inv ≫
        Functor.whiskerLeft Q (integerSuspensionPiMap q) ≫
          (Functor.associator Q SuspensionGeometry.suspension
            (integerStablePiFunctor (q + 1))).inv ≫
              (originalIQScalarIntegerNatIso (q + 1)).inv := by
  change (qCounitIntegerNatIso q).inv ≫
    Functor.whiskerLeft Q (integerSuspensionPiNatIso q).hom ≫
      (Functor.associator Q SuspensionGeometry.suspension
        (integerStablePiFunctor (q + 1))).inv ≫
          (originalIQScalarIntegerNatIso (q + 1)).inv = _
  rw [integerSuspensionPiNatIso_hom]

/-- The whole inverse transformation retains the same span, scalar inverse and original counit. -/
theorem integerISuspensionPiNatIso_inv (q : ℤ) :
    (integerISuspensionPiNatIso.{u, v} q).inv =
      (originalIQScalarIntegerNatIso (q + 1)).hom ≫
        (Functor.associator Q SuspensionGeometry.suspension
          (integerStablePiFunctor (q + 1))).hom ≫
            Functor.whiskerLeft Q (integerSuspensionPiNatIso q).inv ≫
              (qCounitIntegerNatIso q).hom := by
  dsimp only [integerISuspensionPiNatIso]
  rfl

/-- Both complete original source functor maps are retained in the forward naturality square. -/
theorem integerISuspensionPiNatIso_hom_naturality (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor q).map f ≫ (integerISuspensionPiNatIso q).hom.app Y =
      (integerISuspensionPiNatIso q).hom.app X ≫
        (originalISuspensionQFunctor ⋙ integerStablePiFunctor (q + 1)).map f :=
  (integerISuspensionPiNatIso q).hom.naturality f

/-- The complete inverse naturality square retains the same original Q/source arrows. -/
theorem integerISuspensionPiNatIso_inv_naturality (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (originalISuspensionQFunctor ⋙ integerStablePiFunctor (q + 1)).map f ≫
        (integerISuspensionPiNatIso q).inv.app Y =
      (integerISuspensionPiNatIso q).inv.app X ≫ (integerStablePiFunctor q).map f :=
  (integerISuspensionPiNatIso q).inv.naturality f

/-- Normalization through the full original weak span recovers the same scalar-unit family. -/
theorem integerISuspensionPiNatIso_scalar_normalization (q : ℤ) :
    (integerISuspensionPiNatIso.{u, v} q).hom ≫
        (originalIQScalarIntegerNatIso (q + 1)).hom =
      (qCounitIntegerNatIso q).inv ≫
        Functor.whiskerLeft Q (integerSuspensionPiMap q) ≫
          (Functor.associator Q SuspensionGeometry.suspension
            (integerStablePiFunctor (q + 1))).inv := by
  rw [integerISuspensionPiNatIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The complete inverse normalization keeps the original scalar inverse and original Q counit. -/
theorem integerISuspensionPiNatIso_inverse_scalar_normalization (q : ℤ) :
    (originalIQScalarIntegerNatIso.{u, v} (q + 1)).inv ≫
        (integerISuspensionPiNatIso q).inv =
      (Functor.associator Q SuspensionGeometry.suspension
        (integerStablePiFunctor (q + 1))).hom ≫
          Functor.whiskerLeft Q (integerSuspensionPiNatIso q).inv ≫
            (qCounitIntegerNatIso q).hom := by
  rw [integerISuspensionPiNatIso_inv]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The same original positive-level Q counit Iso is used at every canonical integer stage. -/
def qCounitPositiveIso (q : ℤ) (X : Carrier.{u, v}) (n : ℕ) :
    ((integerDiagonalDiagramFunctor q).obj (Q.obj X)).obj n ≅
      ((integerDiagonalDiagramFunctor q).obj X).obj n :=
  levelWeakPositiveIso (ε.app X)
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)
    (integerTailLevel q + n) (integerTailPositiveIndex q + n)

/-- Every inverse Q quotient leg uses the same original level inverse and the same stage. -/
theorem qCounitIntegerNatIso_inv_leg (q : ℤ) (X : Carrier.{u, v}) (n : ℕ) :
    integerStablePiLeg q X n ≫ (qCounitIntegerNatIso q).inv.app X =
      (qCounitPositiveIso q X n).inv ≫ integerStablePiLeg q (Q.obj X) n := by
  rw [qCounitIntegerNatIso_inv_app]
  exact GrpCat.FilteredColimits.colimitMap_ι
    (levelWeakDiagonalIso (integerTailLevel q) (integerTailPositiveIndex q) (ε.app X)
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (B := B) X)).inv n

/-- The inverse Q counit sends every canonical representative by the original stage inverse. -/
theorem qCounitIntegerNatIso_inv_leg_apply (q : ℤ) (X : Carrier.{u, v}) (n : ℕ)
    (a : ((integerDiagonalDiagramFunctor q).obj X).obj n) :
    ((qCounitIntegerNatIso q).inv.app X).hom ((integerStablePiLeg q X n).hom a) =
      (integerStablePiLeg q (Q.obj X) n).hom ((qCounitPositiveIso q X n).inv.hom a) :=
  ConcreteCategory.congr_hom (qCounitIntegerNatIso_inv_leg q X n) a

/-- Every independent caller family inherits the same original all-integer I-Q comparison. -/
def callerIntegerISuspensionPiNatIso {C : Type w} [Category.{z} C]
    (F : C ⥤ Carrier.{u, v}) (q : ℤ) :
    F ⋙ integerStablePiFunctor q ≅ F ⋙
      (originalISuspensionQFunctor ⋙ integerStablePiFunctor (q + 1)) :=
  Functor.isoWhiskerLeft F (integerISuspensionPiNatIso q)

/-- Whole caller-family maps retain the actual original forward comparison on every object. -/
theorem callerIntegerISuspensionPiNatIso_hom_parameter {C : Type w} [Category.{z} C]
    {F G : C ⥤ Carrier.{u, v}} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerRight α (integerStablePiFunctor q) ≫
        (callerIntegerISuspensionPiNatIso G q).hom =
      (callerIntegerISuspensionPiNatIso F q).hom ≫
        Functor.whiskerRight α
          (originalISuspensionQFunctor ⋙ integerStablePiFunctor (q + 1)) := by
  apply NatTrans.ext
  funext X
  exact integerISuspensionPiNatIso_hom_naturality q (α.app X)

/-- Whole caller-family maps retain the actual original inverse comparison on every object. -/
theorem callerIntegerISuspensionPiNatIso_inv_parameter {C : Type w} [Category.{z} C]
    {F G : C ⥤ Carrier.{u, v}} (α : F ⟶ G) (q : ℤ) :
    Functor.whiskerRight α
        (originalISuspensionQFunctor ⋙ integerStablePiFunctor (q + 1)) ≫
          (callerIntegerISuspensionPiNatIso G q).inv =
      (callerIntegerISuspensionPiNatIso F q).inv ≫
        Functor.whiskerRight α (integerStablePiFunctor q) := by
  apply NatTrans.ext
  funext X
  exact integerISuspensionPiNatIso_inv_naturality q (α.app X)

omit B in
/-- Positive cube homotopy of the actual named native point has only its constant-loop class. -/
theorem piNPositive_namedPoint_subsingleton (n : ℕ) :
    Subsingleton ((piNPositiveFunctor.{u, v} n).obj
      (Under.mk (𝟙 CGWH.point.{u, v}))) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  obtain ⟨r, rfl⟩ := HomotopyGroup.mk_surjective b
  have h : p = r := by
    ext t
    change (p t : PUnit.{v + 1}) = r t
    exact Subsingleton.elim (α := PUnit.{v + 1}) _ _
  exact congrArg HomotopyGroup.mk h

omit B in
/-- Every actual pointed zero object has the same unique positive cube homotopy class. -/
theorem piNPositive_isZero_subsingleton (n : ℕ) (Z : PointedCGWH.{u, v}) (hZ : IsZero Z) :
    Subsingleton ((piNPositiveFunctor n).obj Z) := by
  have hPoint : IsZero (Under.mk (𝟙 CGWH.point.{u, v}) : PointedCGWH.{u, v}) :=
    (isZero_zero PointedCGWH.{u, v}).of_iso
      ((isZero_zero PointedCGWH.{u, v}).isoIsInitial Under.mkIdInitial).symm
  let e := (piNPositiveFunctor n).mapIso (hZ.iso hPoint)
  let _ := piNPositive_namedPoint_subsingleton.{u, v} n
  exact ⟨fun a b => e.groupIsoToMulEquiv.injective (Subsingleton.elim _ _)⟩

omit B in
/-- The chosen pointed zero has the same unique positive cube class through its actual point Iso. -/
theorem piNPositive_zero_subsingleton (n : ℕ) :
    Subsingleton ((piNPositiveFunctor.{u, v} n).obj (0 : PointedCGWH.{u, v})) :=
  piNPositive_isZero_subsingleton n _ (isZero_zero PointedCGWH.{u, v})

omit B in
/-- Each original diagonal stage of the original native zero is the unique positive cube class. -/
theorem integerZero_stage_subsingleton (q : ℤ) (n : ℕ) :
    Subsingleton (((integerDiagonalDiagramFunctor q).obj
      (Diagrams.zeroDiagram (A := Index.{u, v}))).obj n) :=
  piNPositive_isZero_subsingleton (integerTailPositiveIndex q + n) _
    (Diagrams.initialDiagram_component_isZero
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne
        (integerTailLevel q + n)))

omit B in
/-- Every original integer quotient class of the actual native zero is its group unit. -/
theorem integerZero_eq_one (q : ℤ)
    (a : (integerStablePiFunctor q).obj (Diagrams.zeroDiagram (A := Index.{u, v}))) :
    a = 1 := by
  let D := (integerDiagonalDiagramFunctor q).obj (Diagrams.zeroDiagram (A := Index.{u, v}))
  refine Quot.inductionOn a ?_
  intro x
  obtain ⟨n, b⟩ := x
  let _ := integerZero_stage_subsingleton.{u, v} q n
  let b' : D.obj n := b
  have hb : b' = 1 := Subsingleton.elim _ _
  change GrpCat.FilteredColimits.G.mk D ⟨n, b'⟩ = 1
  rw [hb]
  exact (GrpCat.FilteredColimits.colimit_one_eq D n).symm

omit B in
/-- The original native zero has a trivial original group in every integer degree. -/
theorem integerZero_subsingleton (q : ℤ) :
    Subsingleton ((integerStablePiFunctor q).obj (Diagrams.zeroDiagram (A := Index.{u, v}))) :=
  ⟨fun a b => (integerZero_eq_one q a).trans (integerZero_eq_one q b).symm⟩

omit B in
/-- All maps factoring through the same actual native zero induce the trivial integer map. -/
theorem integerMap_through_zero_apply (q : ℤ) {X Y : Carrier.{u, v}}
    (f : X ⟶ Diagrams.zeroDiagram) (g : Diagrams.zeroDiagram ⟶ Y)
    (a : (integerStablePiFunctor q).obj X) :
    ((integerStablePiFunctor q).map (f ≫ g)).hom a = 1 := by
  rw [Functor.map_comp]
  change ((integerStablePiFunctor q).map g).hom
    (((integerStablePiFunctor q).map f).hom a) = 1
  rw [integerZero_eq_one q (((integerStablePiFunctor q).map f).hom a)]
  exact map_one _

omit B in
/-- The actual original native null map has its original trivial integer-class function. -/
theorem integerNullMap_apply (q : ℤ) (X Y : Carrier.{u, v})
    (a : (integerStablePiFunctor q).obj X) :
    ((integerStablePiFunctor q).map (Diagrams.toZero X ≫ Diagrams.zeroTo Y)).hom a = 1 :=
  integerMap_through_zero_apply q _ _ a

/-- An actual level-weak contraction to native zero makes each original integer class the unit. -/
theorem integerContractible_eq_one (q : ℤ) (W : Carrier.{u, v})
    (hW : weakEquivalences Carrier (Diagrams.toZero W))
    (a : (integerStablePiFunctor q).obj W) : a = 1 := by
  let e := integerStablePiLevelWeakIso q (Diagrams.toZero W) hW
  apply e.groupIsoToMulEquiv.injective
  exact (integerZero_eq_one q (e.hom.hom a)).trans (map_one e.hom.hom).symm

/-- Every factorization through an actually contractible native object has a trivial class map. -/
theorem integerMap_through_contractible_apply (q : ℤ) {X Y W : Carrier.{u, v}}
    (f : X ⟶ W) (g : W ⟶ Y) (hW : weakEquivalences Carrier (Diagrams.toZero W))
    (a : (integerStablePiFunctor q).obj X) :
    ((integerStablePiFunctor q).map (f ≫ g)).hom a = 1 := by
  rw [Functor.map_comp]
  change ((integerStablePiFunctor q).map g).hom
    (((integerStablePiFunctor q).map f).hom a) = 1
  rw [integerContractible_eq_one q W hW (((integerStablePiFunctor q).map f).hom a)]
  exact map_one _

/-- The unchanged original I cone has its actual native level-weak collapse for every source. -/
theorem originalConeCollapse_weak (X : Carrier.{u, v}) :
    weakEquivalences Carrier
      (Diagrams.toZero ((OriginalICone.cone (B := B) (I := Index)).obj X)) := by
  have h := (OriginalICone.contraction_trivialFibration (B := B) X).2
  rw [OriginalICone.contraction_eq_toZero] at h
  exact h

/-- Both original cone factors induce the actual trivial integer map on every original class. -/
theorem integerMap_through_original_cone_apply (q : ℤ) {X Y W : Carrier.{u, v}}
    (f : X ⟶ (OriginalICone.cone (B := B) (I := Index)).obj W)
    (g : (OriginalICone.cone (B := B) (I := Index)).obj W ⟶ Y)
    (a : (integerStablePiFunctor q).obj X) :
    ((integerStablePiFunctor q).map (f ≫ g)).hom a = 1 :=
  integerMap_through_contractible_apply q f g (originalConeCollapse_weak W) a

private instance nativeZero : HasZeroObject Carrier.{u, v} := Diagrams.nativeHasZeroObject

/-- The actual native null Ho class induces its original trivial integer-class function. -/
theorem integerNullHom_apply (q : ℤ) (X Y : Carrier.{u, v})
    (a : (integerStablePiHoFunctor q).obj (H.obj X)) :
    ((integerStablePiHoFunctor q).map (OrdinaryHoCofiberKernel.nullHom X Y)).hom a = 1 := by
  rw [OrdinaryHoCofiberKernel.nullHom, integerStablePiHoFunctor_map]
  have h : OrdinaryHoCofiberKernel.nullMap X Y = Diagrams.toZero X ≫ Diagrams.zeroTo Y :=
    (OrdinaryHoChosenPuppe.actualNullMap_eq_chosen
      Diagrams.zeroDiagram Diagrams.zeroDiagram_isZero X Y).symm
  rw [h]
  exact integerNullMap_apply q X Y a

section CallerSuspension

open HomotopicalAlgebra.EnrichedProjective.Native.OriginalISuspensionCofibrantComparison

variable (s : ∀ X : Carrier.{u, v},
    PushoutCocone ((OriginalICone.inclusion (B := B)).app X) (Diagrams.toZero X))
  (hs : ∀ X, IsColimit (s X))

/-- A caller's actual I-Q suspension retains the same original Q and chosen suspension maps. -/
abbrev callerISuspensionQFunctor : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  Q ⋙ callerSuspensionFunctor s hs

/-- Actual colimit-choice functions induce both complete integer comparison directions. -/
def callerIQIntegerChoiceNatIso (q : ℤ) :
    originalISuspensionQFunctor.{u, v} ⋙ integerStablePiFunctor q ≅
      callerISuspensionQFunctor s hs ⋙ integerStablePiFunctor q :=
  Functor.isoWhiskerRight (callerISuspensionQNatIso s hs) (integerStablePiFunctor q)

/-- The forward choice map is the actual original quotient map of the entire chosen Iso. -/
theorem callerIQIntegerChoiceNatIso_hom_app (q : ℤ) (X : Carrier.{u, v}) :
    (callerIQIntegerChoiceNatIso s hs q).hom.app X =
      (integerStablePiFunctor q).map (callerSuspensionIso s hs (Q.obj X)).hom := rfl

/-- The inverse choice map uses the same complete original colimit-choice inverse. -/
theorem callerIQIntegerChoiceNatIso_inv_app (q : ℤ) (X : Carrier.{u, v}) :
    (callerIQIntegerChoiceNatIso s hs q).inv.app X =
      (integerStablePiFunctor q).map (callerSuspensionIso s hs (Q.obj X)).inv := rfl

/-- Every integer degree retains the original I-Q comparison for each independent caller choice. -/
def integerCallerISuspensionPiNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    callerISuspensionQFunctor s hs ⋙ integerStablePiFunctor (q + 1) :=
  integerISuspensionPiNatIso q ≪≫ callerIQIntegerChoiceNatIso s hs (q + 1)

/-- The caller forward map keeps the whole original unit/Q/span map before the choice function. -/
theorem integerCallerISuspensionPiNatIso_hom (q : ℤ) :
    (integerCallerISuspensionPiNatIso s hs q).hom =
      (integerISuspensionPiNatIso q).hom ≫
        (callerIQIntegerChoiceNatIso s hs (q + 1)).hom := rfl

/-- The caller inverse keeps its actual choice inverse before the whole original I-Q inverse. -/
theorem integerCallerISuspensionPiNatIso_inv (q : ℤ) :
    (integerCallerISuspensionPiNatIso s hs q).inv =
      (callerIQIntegerChoiceNatIso s hs (q + 1)).inv ≫
        (integerISuspensionPiNatIso q).inv := rfl

/-- Undoing a caller choice recovers the entire original forward I-Q transformation. -/
theorem integerCallerISuspensionPiNatIso_forward_original (q : ℤ) :
    (integerCallerISuspensionPiNatIso s hs q).hom ≫
        (callerIQIntegerChoiceNatIso s hs (q + 1)).inv =
      (integerISuspensionPiNatIso q).hom := by
  rw [integerCallerISuspensionPiNatIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Restoring a caller choice recovers the entire original inverse I-Q transformation. -/
theorem integerCallerISuspensionPiNatIso_inverse_original (q : ℤ) :
    (callerIQIntegerChoiceNatIso s hs (q + 1)).hom ≫
        (integerCallerISuspensionPiNatIso s hs q).inv =
      (integerISuspensionPiNatIso q).inv := by
  rw [integerCallerISuspensionPiNatIso_inv, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- Every raw caller source map retains its complete original Q and suspension functor maps. -/
theorem integerCallerISuspensionPiNatIso_hom_naturality (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (integerStablePiFunctor q).map f ≫
        (integerCallerISuspensionPiNatIso s hs q).hom.app Y =
      (integerCallerISuspensionPiNatIso s hs q).hom.app X ≫
        (callerISuspensionQFunctor s hs ⋙ integerStablePiFunctor (q + 1)).map f :=
  (integerCallerISuspensionPiNatIso s hs q).hom.naturality f

/-- Every raw caller source map retains the same whole inverse comparison square. -/
theorem integerCallerISuspensionPiNatIso_inv_naturality (q : ℤ)
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (callerISuspensionQFunctor s hs ⋙ integerStablePiFunctor (q + 1)).map f ≫
        (integerCallerISuspensionPiNatIso s hs q).inv.app Y =
      (integerCallerISuspensionPiNatIso s hs q).inv.app X ≫
        (integerStablePiFunctor q).map f :=
  (integerCallerISuspensionPiNatIso s hs q).inv.naturality f

/-- The caller scalar comparison retains the actual choice inverse and original weak span. -/
def callerIQScalarIntegerNatIso (q : ℤ) :
    callerISuspensionQFunctor s hs ⋙ integerStablePiFunctor q ≅
      (Q ⋙ SuspensionGeometry.suspension) ⋙ integerStablePiFunctor q :=
  (callerIQIntegerChoiceNatIso s hs q).symm ≪≫ originalIQScalarIntegerNatIso q

/-- Scalar normalization of every caller forward map is the same actual original unit/Q word. -/
theorem integerCallerISuspensionPiNatIso_scalar_normalization (q : ℤ) :
    (integerCallerISuspensionPiNatIso s hs q).hom ≫
        (callerIQScalarIntegerNatIso s hs (q + 1)).hom =
      (qCounitIntegerNatIso q).inv ≫
        Functor.whiskerLeft Q (integerSuspensionPiMap q) ≫
          (Functor.associator Q SuspensionGeometry.suspension
            (integerStablePiFunctor (q + 1))).inv := by
  change ((integerISuspensionPiNatIso q).hom ≫
      (callerIQIntegerChoiceNatIso s hs (q + 1)).hom) ≫
    ((callerIQIntegerChoiceNatIso s hs (q + 1)).inv ≫
      (originalIQScalarIntegerNatIso (q + 1)).hom) = _
  rw [Category.assoc, ← Category.assoc
    (callerIQIntegerChoiceNatIso s hs (q + 1)).hom,
    Iso.hom_inv_id, Category.id_comp]
  exact integerISuspensionPiNatIso_scalar_normalization q

/-- Every original canonical leg keeps the full forward colimit-choice map and same stage. -/
theorem callerIQIntegerChoiceNatIso_hom_leg (q : ℤ) (X : Carrier.{u, v}) (n : ℕ) :
    integerStablePiLeg q (originalISuspensionQFunctor.obj X) n ≫
        (callerIQIntegerChoiceNatIso s hs q).hom.app X =
      (piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (PointedCGWH.SequentialSpectrum.levelMap
          (callerSuspensionIso s hs (Q.obj X)).hom (integerTailLevel q + n)) ≫
            integerStablePiLeg q ((callerISuspensionQFunctor s hs).obj X) n := by
  rw [callerIQIntegerChoiceNatIso_hom_app]
  exact integerStablePiLeg_naturality q (callerSuspensionIso s hs (Q.obj X)).hom n

/-- Every original canonical leg keeps the full inverse colimit-choice map and same stage. -/
theorem callerIQIntegerChoiceNatIso_inv_leg (q : ℤ) (X : Carrier.{u, v}) (n : ℕ) :
    integerStablePiLeg q ((callerISuspensionQFunctor s hs).obj X) n ≫
        (callerIQIntegerChoiceNatIso s hs q).inv.app X =
      (piNPositiveFunctor (integerTailPositiveIndex q + n)).map
        (PointedCGWH.SequentialSpectrum.levelMap
          (callerSuspensionIso s hs (Q.obj X)).inv (integerTailLevel q + n)) ≫
            integerStablePiLeg q (originalISuspensionQFunctor.obj X) n := by
  rw [callerIQIntegerChoiceNatIso_inv_app]
  exact integerStablePiLeg_naturality q (callerSuspensionIso s hs (Q.obj X)).inv n

end CallerSuspension

end PointedCGWH.SequentialSpectrum.StableHomotopy.ISuspensionIntegerPiGeometry
