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
# Étale equivalence relations and their quotient sheaves

An étale equivalence relation on a scheme `U` (`EtaleEquivalencePresentation`) is a pair of étale
morphisms `s t : R ⟶ U` such that `(s, t) : R ⟶ U × U` is a monomorphism and, for every scheme `T`,
the induced relation on the `T`-points of `U` is an equivalence relation. Its quotient `U/R`
(`quotientSheaf`) is the coequalizer of the two induced maps of represented fppf sheaves. The
sheaves take values in the next universe, where this coequalizer exists.

This file provides the atlas map `U ⟶ U/R`, the comparison map `R ⟶ U ×_{U/R} U` and the universal
property of the quotient: maps `U/R ⟶ F` to an fppf sheaf correspond to maps `U ⟶ F` that equalize
`s` and `t` (`descentHomEquiv`).

By Stacks, Theorem 65.10.5, `U/R` is an algebraic space and `U ⟶ U/R` is étale and surjective;
conversely every algebraic space arises this way (Stacks, Lemma 65.9.1). Neither theorem is
formalized here.

## References

* [Stacks Project, Lemma 65.9.1 (Tag 0262)](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Theorem 65.10.5 (Tag 02WW)](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.EtaleSpacePresentations

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- Sheaves of sets on schemes for the fppf topology, valued in the next universe so that the
colimits used below exist. -/
abbrev FppfSheaf := Sheaf Scheme.fppfTopology.{u} (Type (u + 1))

/-- The functor sending a scheme to the fppf sheaf it represents (fully faithful, since the fppf
topology is subcanonical). -/
abbrev represented : Scheme.{u} ⥤ FppfSheaf.{u} :=
  Scheme.fppfTopology.{u}.yoneda ⋙
    sheafCompose Scheme.fppfTopology.{u} uliftFunctor.{u + 1, u}

/-- The relation induced on `T`-points of `U` by a pair of morphisms `s t : R ⟶ U`: `x` and `y` are
related when `(x, y)` factors through `(s, t)`. -/
def schemeRelation {R U : Scheme.{u}} (s t : R ⟶ U) (T : Scheme.{u})
    (x y : T ⟶ U) : Prop := ∃ a : T ⟶ R, a ≫ s = x ∧ a ≫ t = y

/-- An étale equivalence relation on a scheme `U`: étale morphisms `s t : R ⟶ U` such that
`(s, t) : R ⟶ U × U` is a monomorphism (so a pair of points is related through at most one point
of `R`) and induces an equivalence relation on `T`-points for every scheme `T`. -/
structure EtaleEquivalencePresentation where
  U : Scheme.{u}
  R : Scheme.{u}
  source : R ⟶ U
  target : R ⟶ U
  source_etale : Etale source
  target_etale : Etale target
  relation_mono : Mono (Limits.prod.lift source target)
  equivalence : ∀ T : Scheme.{u}, Equivalence (schemeRelation source target T)

/-- The quotient `U/R`: the coequalizer of the two maps of represented fppf sheaves. -/
def quotientSheaf (P : EtaleEquivalencePresentation.{u}) : FppfSheaf.{u} :=
  coequalizer (represented.map P.source) (represented.map P.target)

/-- The atlas map `U ⟶ U/R`. -/
def atlas (P : EtaleEquivalencePresentation.{u}) : represented.obj P.U ⟶ quotientSheaf P :=
  coequalizer.π (represented.map P.source) (represented.map P.target)

theorem atlas_relation (P : EtaleEquivalencePresentation.{u}) :
    represented.map P.source ≫ atlas P = represented.map P.target ≫ atlas P :=
  coequalizer.condition _ _

instance atlas_epi (P : EtaleEquivalencePresentation.{u}) : Epi (atlas P) := by
  constructor
  intro F a b h
  exact coequalizer.hom_ext h

/-- The comparison map `R ⟶ U ×_{U/R} U`. -/
def relationComparison (P : EtaleEquivalencePresentation.{u}) :
    represented.obj P.R ⟶ pullback (atlas P) (atlas P) :=
  pullback.lift (represented.map P.source) (represented.map P.target) (atlas_relation P)

@[simp] theorem relationComparison_fst (P : EtaleEquivalencePresentation.{u}) :
    relationComparison P ≫ pullback.fst (atlas P) (atlas P) = represented.map P.source :=
  pullback.lift_fst ..

@[simp] theorem relationComparison_snd (P : EtaleEquivalencePresentation.{u}) :
    relationComparison P ≫ pullback.snd (atlas P) (atlas P) = represented.map P.target :=
  pullback.lift_snd ..

/-- Maps `U ⟶ F` from the represented sheaf of `U` to an fppf sheaf `F` that equalize `s` and
`t`. -/
abbrev MapDescentData (P : EtaleEquivalencePresentation.{u}) (F : FppfSheaf.{u}) :=
  {a : represented.obj P.U ⟶ F // represented.map P.source ≫ a = represented.map P.target ≫ a}

/-- The map `U/R ⟶ F` induced by a map `U ⟶ F` equalizing `s` and `t`. -/
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

/-- The universal property of the quotient: maps `U/R ⟶ F` correspond to maps `U ⟶ F` that
equalize `s` and `t`. -/
def descentHomEquiv (P : EtaleEquivalencePresentation.{u}) (F : FppfSheaf.{u}) :
    (quotientSheaf P ⟶ F) ≃ MapDescentData P F where
  toFun g := ⟨atlas P ≫ g, by rw [← Category.assoc, atlas_relation P, Category.assoc]⟩
  invFun := descend P
  left_inv g := by symm; exact descend_unique P _ g rfl
  right_inv a := by apply Subtype.ext; exact atlas_descend P a

/-- A morphism of schemes `U ⟶ V` equalizing `s` and `t` induces a map `U/R ⟶ V` of fppf
sheaves. -/
def descendSchemeMap (P : EtaleEquivalencePresentation.{u}) (V : Scheme.{u})
    (a : P.U ⟶ V) (ha : P.source ≫ a = P.target ≫ a) :
    quotientSheaf P ⟶ represented.obj V :=
  descend P ⟨represented.map a, by simp only [← Functor.map_comp, ha]⟩

@[simp] theorem atlas_descendSchemeMap (P : EtaleEquivalencePresentation.{u}) (V : Scheme.{u})
    (a : P.U ⟶ V) (ha : P.source ≫ a = P.target ≫ a) :
    atlas P ≫ descendSchemeMap P V a ha = represented.map a := atlas_descend P _

end AlgebraicGeometry.EtaleSpacePresentations
