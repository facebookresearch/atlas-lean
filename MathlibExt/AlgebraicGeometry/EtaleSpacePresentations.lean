/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import MathlibExt.AlgebraicGeometry.FppfStacks

/-!
# Actual étale quotient presentations and their atlas map dictionary

An étale equivalence relation consists of actual schemes and scheme maps.
Its quotient is the coequalizer of the two represented fppf sheaf maps;
all atlas and descent maps below are the actual universal maps. The larger
sheaf universe is explicit and does not replace a representability theorem.

Quotient algebraicity and the representable étale atlas are positively
implemented in AxiomMath/Stacks, c496df0d9beea9deaeabcea8492605f9a0a2313b,
`Spaces/QuotientSheafPresentationUnconditional.lean`, using the completed
effective-descent theorem. They are not requested as new mathematical gaps.
This completed packet supplies the target carrier and normalized map laws.

References: Stacks Project, Tags 02WW, 02WV and 0263.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.EtaleSpacePresentations

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- The actual fppf sheaf category on schemes, at a sufficient value universe. -/
abbrev FppfSheaf := Sheaf Scheme.fppfTopology.{u} (Type (u + 1))

/-- The actual fully faithful represented-sheaf functor. -/
abbrev represented : Scheme.{u} ⥤ FppfSheaf.{u} :=
  Scheme.fppfTopology.{u}.yoneda ⋙
    sheafCompose Scheme.fppfTopology.{u} uliftFunctor.{u + 1, u}

/-- Scheme-valued arrows of the relation, rather than an arbitrary relation predicate. -/
def schemeRelation {R U : Scheme.{u}} (s t : R ⟶ U) (T : Scheme.{u})
    (x y : T ⟶ U) : Prop := ∃ a : T ⟶ R, a ≫ s = x ∧ a ≫ t = y

/-- An actual étale equivalence relation presenting an algebraic space.
The monomorphism to the product expresses that at most one relation arrow
connects a pair; the remaining clauses express the equivalence property. -/
structure EtaleEquivalencePresentation where
  U : Scheme.{u}
  R : Scheme.{u}
  source : R ⟶ U
  target : R ⟶ U
  source_etale : Etale source
  target_etale : Etale target
  relation_mono : Mono (Limits.prod.lift source target)
  equivalence : ∀ T : Scheme.{u}, Equivalence (schemeRelation source target T)

/-- The quotient is the actual coequalizer in fppf sheaves. -/
def quotientSheaf (P : EtaleEquivalencePresentation.{u}) : FppfSheaf.{u} :=
  coequalizer (represented.map P.source) (represented.map P.target)

/-- The actual atlas map into the quotient sheaf. -/
def atlas (P : EtaleEquivalencePresentation.{u}) : represented.obj P.U ⟶ quotientSheaf P :=
  coequalizer.π (represented.map P.source) (represented.map P.target)

theorem atlas_relation (P : EtaleEquivalencePresentation.{u}) :
    represented.map P.source ≫ atlas P = represented.map P.target ≫ atlas P :=
  coequalizer.condition _ _

instance atlas_epi (P : EtaleEquivalencePresentation.{u}) : Epi (atlas P) := by
  constructor
  intro F a b h
  exact coequalizer.hom_ext h

/-- The canonical map of the actual relation into the atlas self-fibre product. -/
def relationComparison (P : EtaleEquivalencePresentation.{u}) :
    represented.obj P.R ⟶ pullback (atlas P) (atlas P) :=
  pullback.lift (represented.map P.source) (represented.map P.target) (atlas_relation P)

@[simp] theorem relationComparison_fst (P : EtaleEquivalencePresentation.{u}) :
    relationComparison P ≫ pullback.fst (atlas P) (atlas P) = represented.map P.source :=
  pullback.lift_fst ..

@[simp] theorem relationComparison_snd (P : EtaleEquivalencePresentation.{u}) :
    relationComparison P ≫ pullback.snd (atlas P) (atlas P) = represented.map P.target :=
  pullback.lift_snd ..

/-- Descent data for a map to an actual fppf sheaf are the equalized actual
atlas map, with no quotient result assumed as part of the data. -/
abbrev MapDescentData (P : EtaleEquivalencePresentation.{u}) (F : FppfSheaf.{u}) :=
  {a : represented.obj P.U ⟶ F // represented.map P.source ≫ a = represented.map P.target ≫ a}

/-- The actual universal descent map. -/
def descend (P : EtaleEquivalencePresentation.{u}) {F : FppfSheaf.{u}}
    (a : MapDescentData P F) : quotientSheaf P ⟶ F :=
  coequalizer.desc a.1 a.2

@[simp] theorem atlas_descend (P : EtaleEquivalencePresentation.{u}) {F : FppfSheaf.{u}}
    (a : MapDescentData P F) : atlas P ≫ descend P a = a.1 := coequalizer.π_desc ..

theorem descend_unique (P : EtaleEquivalencePresentation.{u}) {F : FppfSheaf.{u}}
    (a : MapDescentData P F) (g : quotientSheaf P ⟶ F) (hg : atlas P ≫ g = a.1) :
    g = descend P a := by
  apply coequalizer.hom_ext
  exact hg.trans (atlas_descend P a).symm

/-- Maps out of the quotient are exactly maps on its actual atlas with
the actual relation compatibility. This is the family/morphism dictionary
used when changing an algebraic-space presentation. -/
def descentHomEquiv (P : EtaleEquivalencePresentation.{u}) (F : FppfSheaf.{u}) :
    (quotientSheaf P ⟶ F) ≃ MapDescentData P F where
  toFun g := ⟨atlas P ≫ g, by rw [← Category.assoc, atlas_relation P, Category.assoc]⟩
  invFun := descend P
  left_inv g := by symm; exact descend_unique P _ g rfl
  right_inv a := by apply Subtype.ext; exact atlas_descend P a

/-- A scheme map satisfying the actual relation descends by the same
normalized universal map into the represented target sheaf. -/
def descendSchemeMap (P : EtaleEquivalencePresentation.{u}) (V : Scheme.{u})
    (a : P.U ⟶ V) (ha : P.source ≫ a = P.target ≫ a) :
    quotientSheaf P ⟶ represented.obj V :=
  descend P ⟨represented.map a, by simp only [← Functor.map_comp, ha]⟩

@[simp] theorem atlas_descendSchemeMap (P : EtaleEquivalencePresentation.{u}) (V : Scheme.{u})
    (a : P.U ⟶ V) (ha : P.source ≫ a = P.target ≫ a) :
    atlas P ≫ descendSchemeMap P V a ha = represented.map a := atlas_descend P _

end AlgebraicGeometry.EtaleSpacePresentations
