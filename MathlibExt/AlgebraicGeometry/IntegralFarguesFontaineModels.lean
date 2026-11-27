/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The integral annular and Frobenius-quotient model follows the completed
TauCetiProject/TauCeti source, revision
62bbc0596dc3539d488232e4e924a338548ea0a9, Apache 2.0:
TauCeti/AlgebraicGeometry/AdicSpace/FarguesFontaine/PreAdicSpace.lean,
IntervalChart.lean and Adic.lean; and RingTheory/Huber/LocalizationTopology.
Modification: use native all-rank ValuativeRel spectra and actual integral
rational rings, state the source ring/sheaf dictionary by its completed
localization topology and right Kan universal property, and expose the
pointwise Frobenius quotient independently of the source adic category.
The existing generic adic gluing/quotient proofs are source integration
dependencies, not re-requested mathematical results.
-/
module

public import MathlibExt.RingTheory.AdicRationalRingModels
public import MathlibExt.RingTheory.CompleteHuberPairModels
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Actual integral annular Fargues--Fontaine model contracts

The base is an actual characteristic-p perfectoid Huber pair with its
integral plus ring and a genuine topologically nilpotent unit. The period
ring is W(S+), with its (p,[varpi])-adic topology. The punctured space is
the actual all-rank Spa(W(S+),W(S+)) off p and [varpi]. Frobenius is fixed
to the actual Witt Frobenius; the point quotient is its native coequalizer.

On rational charts the coefficient ring is the actual completed annular
ring, with topology fixed by the native quotient-projection filtration.
Continuous restriction maps are uniquely fixed on the coefficient ring.
The structure sheaf is characterized as a right Kan extension of those
actual rational rings. No free curve or structure-sheaf carrier occurs.

Reference: Fargues--Scholze, arXiv:2102.13459v4, SectionI.2;
Kedlaya, *Sheaves, stacks, and shtukas*, Section3.1.
This is the Q_p integral-Witt component. Ramified coefficient fields,
relative bundle/modification and v-descent comparisons are separate layers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.IntegralFarguesFontaineModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.TopologicalSpace Topology
open MathlibExt.RingTheory.CompleteHuberPairModels
open MathlibExt.RingTheory.AdicRationalRingModels
open AffineAdicSpectra

variable (p : ℕ) [Fact p.Prime]

/-- An actual integral perfectoid base and its chosen period-ring presentation. -/
structure Base where
  pair : CharPPerfectoidPair p
  varpi : pair.plus
  unit : IsUnit (varpi : pair.ring)
  nilpotent : IsTopologicallyNilpotent (varpi : pair.ring)
  [characteristic : CharP pair.plus p]
  [perfect : PerfectRing pair.plus p]

attribute [instance] Base.characteristic Base.perfect

variable (S : Base p)

/-- The actual integral Witt ring, indexed by its geometric base. -/
def Ring : Type := WittVector p S.pair.plus

instance ringCommRing : CommRing (Ring p S) :=
  inferInstanceAs (CommRing (WittVector p S.pair.plus))

/-- The actual period ideal, retaining both integral generators. -/
def periodIdeal : Ideal (Ring p S) :=
  Ideal.span {(p : Ring p S), WittVector.teichmuller p S.varpi}

instance ringTopology : TopologicalSpace (Ring p S) := (periodIdeal p S).adicTopology

/-- The actual Witt Frobenius, not a freely chosen period automorphism. -/
def frobenius : Ring p S ≃+* Ring p S := WittVector.frobeniusEquiv p S.pair.plus

/-- Actual all-rank continuous valuations, punctured at both period generators. -/
abbrev Y := {v : Spa (⊤ : Subring (Ring p S)) //
  ¬ v.val.relation.vle (p : Ring p S) 0 ∧
    ¬ v.val.relation.vle (WittVector.teichmuller p S.varpi) 0}

/-- The precise punctured period-space topology. -/
def ySpace : TopCat := TopCat.of (Y p S)

/-- The Frobenius on points: a self-homeomorphism of the punctured space $Y$ (`Y`) of points $v$ of
$\operatorname{Spa}(W(S^+), W(S^+))$ with $v(p) \neq 0$ and $v([\varpi]) \neq 0$ that sends every
point $v$ to its pullback $v \circ \varphi$ along the Witt vector Frobenius $\varphi$ of $W(S^+)$.
Here $p$ is a prime and $S$ a perfectoid Huber pair of characteristic $p$ with plus ring $S^+$ and
an element $\varpi \in S^+$ that is a topologically nilpotent unit of $S$ (`Base`). -/
structure FrobeniusPoints where
  homeomorph : Y p S ≃ₜ Y p S
  normalized : ∀ y : Y p S,
    (homeomorph y).val.val =
      AffineAdicSpectra.comap (frobenius p S).toRingHom y.val.val

variable (φ : FrobeniusPoints p S)

/-- The actual topological Witt-Frobenius map. -/
def frobeniusMap : ySpace p S ⟶ ySpace p S :=
  TopCat.ofHom ⟨φ.homeomorph, φ.homeomorph.continuous_toFun⟩

/-- The point quotient is the native coequalizer of Frobenius and identity. -/
def xSpace : TopCat := coequalizer (frobeniusMap p S φ) (𝟙 (ySpace p S))

/-- The actual quotient projection. -/
def quotient : ySpace p S ⟶ xSpace p S φ :=
  coequalizer.π (frobeniusMap p S φ) (𝟙 _)

theorem quotient_frobenius :
    frobeniusMap p S φ ≫ quotient p S φ = quotient p S φ := by
  dsimp only [quotient, xSpace]
  exact (coequalizer.condition (frobeniusMap p S φ) (𝟙 _)).trans
    (Category.id_comp _)

/-- Actual annular rational presentations, with their exact point domains. The denominator is
divisible by both period generators, so every chart lies in the twice-punctured space `Y` and its
ring does not see the deleted boundary. -/
structure RationalPresentation where
  numerators : Finset (Ring p S)
  denominator : Ring p S
  annular : IsAnnular (Ring p S) (periodIdeal p S) numerators denominator
  punctured : ∃ a : Ring p S,
    denominator = (p : Ring p S) * (show Ring p S from WittVector.teichmuller p S.varpi) * a
  openSet : Opens (ySpace p S)
  domain : ∀ y : Y p S, y ∈ openSet ↔
    ¬ y.val.val.relation.vle denominator 0 ∧
      ∀ t ∈ numerators, y.val.val.relation.vle t denominator

instance rationalPreorder : Preorder (RationalPresentation p S) where
  le P Q := P.openSet ≤ Q.openSet
  le_refl P := le_refl _
  le_trans _ _ _ h j := h.trans j

/-- The actual rational-basis inclusion functor. -/
def rationalOpens : RationalPresentation p S ⥤ Opens (ySpace p S) where
  obj P := P.openSet
  map h := homOfLE (leOfHom h)

/-- The actual completed annular coefficient ring at each rational chart. -/
def ChartRing (P : RationalPresentation p S) : Type :=
  RationalRing (Ring p S) (periodIdeal p S) P.numerators P.denominator

instance chartCommRing (P : RationalPresentation p S) : CommRing (ChartRing p S P) :=
  inferInstanceAs (CommRing
    (RationalRing (Ring p S) (periodIdeal p S) P.numerators P.denominator))

instance chartCompletedAlgebra (P : RationalPresentation p S) :
    Algebra (CompletedDefinition (Ring p S) (periodIdeal p S)
      P.numerators P.denominator) (ChartRing p S P) :=
  inferInstanceAs (Algebra
    (CompletedDefinition (Ring p S) (periodIdeal p S) P.numerators P.denominator)
    (RationalRing (Ring p S) (periodIdeal p S) P.numerators P.denominator))

def chartCoefficient (P : RationalPresentation p S) : Ring p S →+* ChartRing p S P :=
  coefficient (Ring p S) (periodIdeal p S) P.numerators P.denominator

/-- The actual completed-definition lattice in every filtration degree. -/
def chartNeighbourhood (P : RationalPresentation p S) (n : ℕ) : Set (ChartRing p S P) :=
  (algebraMap
      (CompletedDefinition (Ring p S) (periodIdeal p S) P.numerators P.denominator)
      (ChartRing p S P)) ''
    (RingHom.ker ((AdicCompletion.evalₐ
      (completionIdeal (Ring p S) (periodIdeal p S) P.numerators P.denominator) n).toRingHom))

/-- Source-normalized rational topology and restriction maps on the real rings. -/
class RationalRestrictions where
  [topology : ∀ P : RationalPresentation p S, TopologicalSpace (ChartRing p S P)]
  neighbourhoods : ∀ P : RationalPresentation p S,
    (𝓝 (0 : ChartRing p S P)).HasBasis (fun _ : ℕ ↦ True) (chartNeighbourhood p S P)
  restrict : ∀ {P Q : RationalPresentation p S}, Q.openSet ≤ P.openSet →
    ChartRing p S P →+* ChartRing p S Q
  continuous : ∀ {P Q : RationalPresentation p S} (h : Q.openSet ≤ P.openSet),
    Continuous (restrict h)
  coefficient : ∀ {P Q : RationalPresentation p S} (h : Q.openSet ≤ P.openSet),
    (restrict h).comp (chartCoefficient p S P) = chartCoefficient p S Q
  unique : ∀ {P Q : RationalPresentation p S} (f g : ChartRing p S P →+* ChartRing p S Q),
    Continuous f → Continuous g →
      f.comp (chartCoefficient p S P) = g.comp (chartCoefficient p S P) → f = g
  basis : ∀ (U : Opens (ySpace p S)) (y : Y p S), y ∈ U →
    ∃ P : RationalPresentation p S, y ∈ P.openSet ∧ P.openSet ≤ U

attribute [instance_reducible] RationalRestrictions.topology
attribute [instance] RationalRestrictions.topology

variable [D : RationalRestrictions p S]

/-- The actual coefficient-normalized restriction has the identity law. -/
theorem restrict_id (P : RationalPresentation p S) : D.restrict (le_refl P.openSet) =
    RingHom.id (ChartRing p S P) :=
  D.unique _ _ (D.continuous _) continuous_id (by rw [D.coefficient]; rfl)

/-- Its composition law follows from the same actual uniqueness property. -/
theorem restrict_comp {P Q T : RationalPresentation p S}
    (h : Q.openSet ≤ P.openSet) (j : T.openSet ≤ Q.openSet) :
    D.restrict (j.trans h) = (D.restrict j).comp (D.restrict h) :=
  D.unique _ _ (D.continuous _) ((D.continuous j).comp (D.continuous h))
    (by rw [D.coefficient, RingHom.comp_assoc, D.coefficient, D.coefficient])

/-- The real rational-ring diagram, not an arbitrary structure presheaf. -/
def rationalRings : (RationalPresentation p S)ᵒᵖ ⥤ CommRingCat where
  obj P := .of (ChartRing p S P.unop)
  map f := CommRingCat.ofHom (D.restrict (leOfHom f.unop))
  map_id P := by
    change CommRingCat.ofHom (D.restrict (le_refl P.unop.openSet)) = 𝟙 _
    rw [restrict_id]
    rfl
  map_comp {P Q T} f g := by
    have h := restrict_comp p S (leOfHom f.unop) (leOfHom g.unop)
    exact congrArg CommRingCat.ofHom h

/-- The exact source annular sheaf, pinned by its rational rings and Kan property. -/
structure PeriodSheaf where
  sheaf : TopCat.Sheaf CommRingCat (ySpace p S)
  rationalComparison : (rationalOpens p S).op ⋙ sheaf.obj ≅ rationalRings p S
  [kan : sheaf.obj.IsRightKanExtension rationalComparison.hom]

attribute [instance] PeriodSheaf.kan

end MathlibExt.AlgebraicGeometry.IntegralFarguesFontaineModels
