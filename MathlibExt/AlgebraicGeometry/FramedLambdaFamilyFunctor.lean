/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdmissibleRelativeLambdaFamilies
public import MathlibExt.AlgebraicGeometry.GeneralFlagSchemes
public import Mathlib.CategoryTheory.Limits.Indization.FilteredColimits

/-!
# The actual framed admissible lambda-family isoclass functor

The object is the equivalence quotient of the actual locally descended
admissible families by their actual parameter/bundle/BOTH-operator/frame
isomorphisms. Reindexing is the existing native family pullback. Its functor
laws use the actual identity/composition family comparisons. This produces
an actual functor on every complex scheme, not only on complex points.

The affine filtered-limit endpoint is a preservation statement for this
fixed functor after the actual Spec functor. Its comparison map is therefore
the canonical colimit map of the actual family pullbacks; it is not an
independent isomorphism or a C-valued-point shortcut on arbitrary bases.

Source: Simpson, alg-geom/9604005v1, Proposition 4.1; ordinary finite
presentation/filtered-limit descent of framed vector-bundle connections.
Native quotient, Spec and colimit primitives are Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0; imported relative
family definitions retain their pinned source and adaptation credits.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FramedLambdaFamilyFunctor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open PerverseSheaves ComplexAnalytification CompactSupportBetti ProperBettiFunctoriality
open RelativeFramedLambdaFamilies RelativeLambdaPullbackSystems AdmissibleRelativeLambdaFamilies
open RelativeDeRhamDifferential ProjectiveLineSystems

variable (X : ComplexScheme) (x : scalarBase ⟶ X) (n : ℕ) (P : PullbackSystem X x n)
  (V : UnitFibreComparison X x n P) (d : ℕ) (H : LineBundle X.left)
  (D : ∀ (Y : ComplexScheme) [IsComplexVariety Y], DualizingComplex (space Y))
  (Q : ∀ {Y Z : ComplexScheme} [IsComplexVariety Y] [IsComplexVariety Z]
    (f : Y ⟶ Z) [IsProper f.left], ProperPullback (spaceMap f))
  (T : BettiCharacteristicClasses.ProjectiveBundleTheory D Q)
  [IsComplexVariety (unitProduct X)] [SmoothOfRelativeDimension d (unitProduct X).hom]
  (F : FibreTests X x n P V d H)

abbrev AdmissibleFamily (S : ComplexScheme) :=
  {E : Family X x S (P.differential S) n // IsAdmissible X x n P V d H D Q T F E}

def familyRelation (S : ComplexScheme)
    (E G : AdmissibleFamily X x n P V d H D Q T F S) : Prop := Nonempty (Family.Iso E.val G.val)

def familySetoid (S : ComplexScheme) : Setoid (AdmissibleFamily X x n P V d H D Q T F S) :=
  Relation.EqvGen.setoid (familyRelation X x n P V d H D Q T F S)

abbrev FamilyClasses (S : ComplexScheme) := Quotient (familySetoid X x n P V d H D Q T F S)

def classOf {S : ComplexScheme} (E : AdmissibleFamily X x n P V d H D Q T F S) :
    FamilyClasses X x n P V d H D Q T F S := Quotient.mk _ E

/-- Proofs for the fixed actual family pullbacks; no representability or
quotient conclusion is a field of this ordinary functor construction. -/
structure ReindexingProofs : Prop where
  admissible : ∀ {S U : ComplexScheme} (f : S ⟶ U) (E : Family X x U (P.differential U) n),
    IsAdmissible X x n P V d H D Q T F E →
      IsAdmissible X x n P V d H D Q T F (P.pull X x n f E)
  isomorphisms : ∀ {S U : ComplexScheme} (f : S ⟶ U)
      (E G : Family X x U (P.differential U) n), Nonempty (Family.Iso E G) →
    Nonempty (Family.Iso (P.pull X x n f E) (P.pull X x n f G))

variable (RP : ReindexingProofs X x n P V d H D Q T F)

def admissiblePull {S U : ComplexScheme} (f : S ⟶ U)
    (E : AdmissibleFamily X x n P V d H D Q T F U) : AdmissibleFamily X x n P V d H D Q T F S :=
  ⟨P.pull X x n f E.val, RP.admissible f E.val E.property⟩

def classesMap {S U : ComplexScheme} (f : S ⟶ U) :
    FamilyClasses X x n P V d H D Q T F U → FamilyClasses X x n P V d H D Q T F S :=
  Quotient.map (admissiblePull X x n P V d H D Q T F RP f) (by
    intro E G h
    induction h with
    | rel E G h => exact Relation.EqvGen.rel _ _ (RP.isomorphisms f E.val G.val h)
    | refl E => exact Relation.EqvGen.refl _
    | symm E G h ih => exact Relation.EqvGen.symm _ _ ih
    | trans E G K hEG hGK ihEG ihGK => exact Relation.EqvGen.trans _ _ _ ihEG ihGK)

def familyFunctor (PC : PullbackCoherence X x n P) : ComplexSchemeᵒᵖ ⥤ Type 1 where
  obj S := FamilyClasses X x n P V d H D Q T F S.unop
  map f := TypeCat.ofHom (classesMap X x n P V d H D Q T F RP f.unop)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro E
    refine Quotient.inductionOn E ?_
    intro E
    apply Quotient.sound
    exact Relation.EqvGen.rel _ _ (PC.identity S.unop E.val)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro E
    refine Quotient.inductionOn E ?_
    intro E
    apply Quotient.sound
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (PC.composition g.unop f.unop E.val))

def affineSpecFunctor : CommAlgCat.{0} ℂ ⥤ ComplexSchemeᵒᵖ where
  obj A := op (GeneralFlagSchemes.affineScheme A)
  map f := (GeneralFlagSchemes.affineMap f).op
  map_id A := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (AlgHom.id ℂ A).toRingHom) = 𝟙 _
    rw [show CommRingCat.ofHom (AlgHom.id ℂ A).toRingHom = 𝟙 (CommRingCat.of A) by ext a; rfl]
    exact Spec.map_id _
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (g.hom.comp f.hom).toRingHom) =
      Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.hom.toRingHom)
    rw [← Spec.map_comp]
    congr 1

def affineFamilyFunctor (PC : PullbackCoherence X x n P) : CommAlgCat.{0} ℂ ⥤ Type 1 :=
  affineSpecFunctor ⋙ familyFunctor X x n P V d H D Q T F RP PC

/-- Standard finite-presentation descent for this ACTUAL functor. It
provides the canonical filtered-colimit comparison, with all pullback maps
and operator/frame data fixed above. -/
structure LimitDescent (PC : PullbackCoherence X x n P) : Prop where
  preserves : ∀ (I : Type) [SmallCategory I] [IsFiltered I] (A : I ⥤ CommAlgCat.{0} ℂ),
    PreservesColimit A (affineFamilyFunctor X x n P V d H D Q T F RP PC)

end MathlibExt.AlgebraicGeometry.FramedLambdaFamilyFunctor
