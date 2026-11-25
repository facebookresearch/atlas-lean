/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffinoidFormalModels
public import MathlibExt.AlgebraicGeometry.AnalyticProEtaleSiteModels
public import MathlibExt.AlgebraicGeometry.PadicFormalSchemes
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Actual smooth formal O_C generic-fibre models

The base is an algebraically closed complete nonarchimedean extension of Q_p;
it is not required to be discretely valued. O_C is its actual norm-unit
subring. Every affine formal chart has a finitely presented p-complete
O_C-model. Its generic algebra is the native localization at p, and its
Tate topology is identified with that algebra's actual Banach topology.

Formal maps are fixed on all nilpotent levels. Generic maps are fixed on
every original model coefficient through the same ring map. Whole formal
and generic overlap refinements are required, so unrelated gluing cannot
be called the generic fibre. The construction remains a separate source
integration request.

References: BMS19 arXiv:1802.03261v2, Theorem 1.15(2), Section 10;
BMS18 arXiv:1602.03148v3, Section 3; Huber's formal generic fibre.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FormalGenericFibreModels

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open TopologicalSpace Topology
open PadicFormalSchemes AffinoidFormalModels AnalyticTateAdicModels
open AnalyticDiamondEtaleSites

variable (p : ℕ) [Fact p.Prime]

structure CompletePadicField where
  carrier : Type
  [normedField : NormedField carrier]
  [ultrametric : IsUltrametricDist carrier]
  [complete : CompleteSpace carrier]
  [algebra : Algebra ℚ_[p] carrier]
  [normedAlgebra : NormedAlgebra ℚ_[p] carrier]
  [closed : IsAlgClosed carrier]

attribute [instance] CompletePadicField.normedField CompletePadicField.ultrametric
  CompletePadicField.complete CompletePadicField.algebra CompletePadicField.normedAlgebra
  CompletePadicField.closed

variable (C : CompletePadicField p)

def integers : Subring C.carrier where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖a + b‖ ≤ 1
    have h : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
      simpa [dist_eq_norm, sub_eq_add_neg] using dist_triangle_max a (0 : C.carrier) (-b)
    exact h.trans (max_le ha hb)
  mul_mem' := by
    intro a b ha hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    simpa using mul_le_mul ha hb (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)
  neg_mem' ha := by simpa using ha

abbrev FormalBase := spfDiagram p (integers p C) ⊥
abbrev FormalScheme := PadicFormalSchemes.FormalScheme p (integers p C) ⊥

variable (X : FormalScheme p C) (G : AnalyticAdicSpace p)

/-- A real finite-presentation affine formal chart and its native generic affinoid. -/
structure GenericChart where
  model : AffinoidFormalModel (integers p C) C.carrier (p : integers p C)
  presentationSize : ℕ
  presentationIdeal : Ideal (MvPolynomial (Fin presentationSize) (integers p C))
  ideal_finitely_generated : presentationIdeal.FG
  presentationIso :
    AdicCompletion ((parameterIdeal (integers p C) (p : integers p C)).map
      (algebraMap (integers p C) (MvPolynomial (Fin presentationSize) (integers p C) ⧸ presentationIdeal)))
      (MvPolynomial (Fin presentationSize) (integers p C) ⧸ presentationIdeal) ≃ₐ[integers p C]
        model.modelRing
  formal : FormalScheme p C
  formalIso : spfDiagram p model.modelRing ⊥ ≅ formal.diagram
  formal_base : formalIso.hom ≫ formal.structureMap =
    mapDiagram p (algebraMap (integers p C) model.modelRing) (I := ⊥) (J := ⊥) (by simp)
  inclusion : formal ⟶ X
  [openCharts : ∀ n, IsOpenImmersion ((PadicFormalSchemes.FormalScheme.Hom.diagram inclusion).app n)]
  pair : TatePair p
  ringIso : model.genericAlgebra ≃+* pair.ring
  ring_continuous : Continuous ringIso
  ring_inverse_continuous : Continuous ringIso.symm
  plus_normalized : ∀ a : pair.ring, a ∈ pair.plus ↔ IsIntegral model.modelRing (ringIso.symm a)
  affinoid : AffinoidModel p pair
  genericInclusion : affinoid.valued ⟶ G.obj
  generic_open : IsOpenEmbedding genericInclusion.val.base
  generic_stalk_iso : ∀ x, IsIso (genericInclusion.val.stalkMap x)
  generic_sections : AnalyticTateAdicModels.SectionsHomeomorphic genericInclusion.val

attribute [instance] GenericChart.openCharts

namespace GenericChart

variable {p C X G} (A : GenericChart p C X G)

def chart : AnalyticDiamondEtaleSites.Chart p G :=
  ⟨A.pair, A.affinoid, A.genericInclusion, A.generic_open, A.generic_stalk_iso,
    A.generic_sections⟩

end GenericChart

variable {X G}

/-- The same original O_C-algebra map controls all formal and generic chart maps. -/
structure Refinement (A B : GenericChart p C X G) where
  ring : B.model.modelRing →ₐ[integers p C] A.model.modelRing
  formal : A.formal ⟶ B.formal
  formal_normalized : PadicFormalSchemes.FormalScheme.Hom.diagram formal =
    A.formalIso.inv ≫ mapDiagram p ring.toRingHom (I := ⊥) (J := ⊥) (by simp) ≫ B.formalIso.hom
  formal_square : formal ≫ B.inclusion = A.inclusion
  generic : AffinoidMap p A.chart B.chart
  coefficient : ∀ a : B.model.modelRing,
    generic.ring.hom (B.ringIso (algebraMap B.model.modelRing B.model.genericAlgebra a)) =
      A.ringIso (algebraMap A.model.modelRing A.model.genericAlgebra (ring a))
  generic_square : A.genericInclusion = generic.valued ≫ B.genericInclusion

variable (X G)

/-- A generic fibre is bound to the whole actual affine formal atlas and overlaps. -/
structure GenericAtlas where
  index : Type 1
  chart : index → GenericChart p C X G
  formal_cover : ∀ (n : ℕ) (x : X.diagram.obj n),
    ∃ i, x ∈ Set.range ((PadicFormalSchemes.FormalScheme.Hom.diagram (chart i).inclusion).app n)
  generic_cover : ∀ x : G.obj.space, ∃ i, x ∈ Set.range (chart i).genericInclusion.val.base
  formal_overlaps : ∀ (i j : index) (n : ℕ) (x : X.diagram.obj n),
    (x ∈ Set.range ((PadicFormalSchemes.FormalScheme.Hom.diagram (chart i).inclusion).app n) ∧
      x ∈ Set.range ((PadicFormalSchemes.FormalScheme.Hom.diagram (chart j).inclusion).app n)) ↔
    ∃ (k : index) (_ri : Refinement p C (chart k) (chart i))
      (_rj : Refinement p C (chart k) (chart j)),
      x ∈ Set.range ((PadicFormalSchemes.FormalScheme.Hom.diagram (chart k).inclusion).app n)
  generic_overlaps : ∀ (i j : index) (x : G.obj.space),
    (x ∈ Set.range (chart i).genericInclusion.val.base ∧
      x ∈ Set.range (chart j).genericInclusion.val.base) ↔
    ∃ (k : index) (_ri : Refinement p C (chart k) (chart i))
      (_rj : Refinement p C (chart k) (chart j)),
      x ∈ Set.range (chart k).genericInclusion.val.base

variable {X G} {Y : FormalScheme p C} {H : AnalyticAdicSpace p}

/-- A local generic map is pinned by the same model-ring map as the original formal map. -/
structure ChartMap (f : X ⟶ Y) (g : G ⟶ H)
    (A : GenericChart p C X G) (B : GenericChart p C Y H) where
  ring : B.model.modelRing →ₐ[integers p C] A.model.modelRing
  formal : A.formal ⟶ B.formal
  formal_normalized : PadicFormalSchemes.FormalScheme.Hom.diagram formal =
    A.formalIso.inv ≫ mapDiagram p ring.toRingHom (I := ⊥) (J := ⊥) (by simp) ≫ B.formalIso.hom
  formal_square : A.inclusion ≫ f = formal ≫ B.inclusion
  generic : AffinoidMap p A.chart B.chart
  coefficient : ∀ a : B.model.modelRing,
    generic.ring.hom (B.ringIso (algebraMap B.model.modelRing B.model.genericAlgebra a)) =
      A.ringIso (algebraMap A.model.modelRing A.model.genericAlgebra (ring a))
  generic_square : A.genericInclusion ≫ g.hom = generic.valued ≫ B.genericInclusion

/-- Every original generic point is covered by a coefficient-normalized chart square. -/
structure Morphism (A : GenericAtlas p C X G) (B : GenericAtlas p C Y H)
    (f : X ⟶ Y) (g : G ⟶ H) where
  charts : ∀ x : G.obj.space, ∃ (i : A.index) (j : B.index),
    x ∈ Set.range (A.chart i).genericInclusion.val.base ∧ Nonempty (ChartMap p C f g (A.chart i) (B.chart j))

end MathlibExt.AlgebraicGeometry.FormalGenericFibreModels
