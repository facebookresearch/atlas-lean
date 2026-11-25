/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves

/-!
# Coherent monoid charts on the actual small etale site

A chart is a finitely generated actual monoid map. Its kernel is the
actual presheaf pullback of the unit, and its quotient is the actual
presheaf pushout killing that kernel. Local bijectivity to the given
monoid sheaf is the source chart condition. No coherent label or scalar
rank substitutes for the presentation.

Reference: Borne--Vistoli, arXiv:1001.0466v2, §3.3 (charts/coherence),
Definition4.3 (coherent denominator sheaves).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MonoidSheafCharts
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
universe u

abbrev localMonoids {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale) :=
  (Over.forget U).op ⋙ A.obj

abbrev constantMonoids {X : Scheme.{u}} (U : X.Etale) (P : CommMonCat.{u}) :=
  (Functor.const (Over U)ᵒᵖ).obj P

/-- The monoid map is extended by actual restriction to the slice presheaf. -/
def chartMap {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale)
    (P : CommMonCat.{u}) (p : P →* A.obj.obj (op U)) :
    constantMonoids U P ⟶ localMonoids A U where
  app V := CommMonCat.ofHom ((A.obj.map V.unop.hom.op).hom.comp p)
  naturality {V W} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change A.obj.map W.unop.hom.op (p x) =
      A.obj.map f.unop.left.op (A.obj.map V.unop.hom.op (p x))
    rw [(Over.w f.unop).symm, op_comp]
    exact ConcreteCategory.congr_hom
      (A.obj.map_comp V.unop.hom.op f.unop.left.op) (p x)

abbrev trivialMonoids {X : Scheme.{u}} (U : X.Etale) :=
  constantMonoids U (⊤_ CommMonCat.{u})

/-- The canonical local unit map. -/
def unitMap {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale) :
    trivialMonoids U ⟶ localMonoids A U where
  app V := CommMonCat.ofHom (1 : (⊤_ CommMonCat.{u}) →* A.obj.obj (op V.unop.left))
  naturality := by intros; ext x; simp

abbrev chartKernel {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale)
    (P : CommMonCat.{u}) (p : P →* A.obj.obj (op U)) :=
  pullback (chartMap A U P p) (unitMap A U)

/-- The exact quotient/presentation map, without requiring sheafification
of a presheaf over a large site in a smaller universe. -/
def quotientMap {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale)
    (P : CommMonCat.{u}) (p : P →* A.obj.obj (op U)) :
    pushout (pullback.fst (chartMap A U P p) (unitMap A U))
      (pullback.snd (chartMap A U P p) (unitMap A U)) ⟶ localMonoids A U :=
  pushout.desc (chartMap A U P p) (unitMap A U) (by exact pullback.condition)

/-- An actual source-coherent local monoid chart. -/
structure Chart {X : Scheme.{u}} (A : MonoidSheaf X) (U : X.Etale) where
  monoid : CommMonCat.{u}
  finiteGeneration : IsMulFG monoid
  map : monoid →* A.obj.obj (op U)
  locallyInjective : Presheaf.IsLocallyInjective (X.smallEtaleTopology.over U)
    (quotientMap A U monoid map)
  locallySurjective : Presheaf.IsLocallySurjective (X.smallEtaleTopology.over U)
    (quotientMap A U monoid map)

/-- Sharpness excludes nontrivial monoid units sectionwise, equivalently locally. -/
def IsSharp {X : Scheme.{u}} (A : MonoidSheaf X) : Prop :=
  ∀ (U : X.Etale) (a : A.obj.obj (op U)), IsUnit a → a = 1

/-- Coherence is sharpness together with actual chart covers (BV Definition3.13). -/
def IsCoherent {X : Scheme.{u}} (A : MonoidSheaf X) : Prop :=
  IsSharp A ∧ ∀ U : X.Etale, ∃ (I : Type u) (V : I → X.Etale) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ X.smallEtaleTopology U ∧ ∀ i, Nonempty (Chart A (V i))

/-- The precise coherent Kummer denominator system. -/
structure DenominatorSystem {X : Scheme.{u}} (A B : MonoidSheaf X) where
  map : A ⟶ B
  kummer : LocallyKummer map
  coherentA : IsCoherent A
  coherentB : IsCoherent B

end MathlibExt.AlgebraicGeometry.MonoidSheafCharts
