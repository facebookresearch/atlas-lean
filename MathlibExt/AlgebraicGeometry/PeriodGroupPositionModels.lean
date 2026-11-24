/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations
public import MathlibExt.AlgebraicGeometry.PeriodLatticePluckerBounds

/-!
# Actual local G positions and associated theta-adic lattices

Positive and generic group points use the original E scalar lift into
B_dR-plus and its actual localization at the filtration-one generator.
Exact relative position is the literal positive double orbit of the
actual cocharacter evaluated at that generator. Associated lattices
are computed images of the integral standard module under the actual
representation matrix.

The closed bounds are the displayed Plucker conditions for all actual
algebraic representations, with weight bases fixed by the source
cocharacter. Comparison with the group Schubert locus is separate.
Cocharacters are defined over the displayed coefficient field; a
finite coefficient extension can be supplied before specialization.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections VI.1--VI.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open LocalWittCoefficientFields RelativeFarguesFontaineRings MarkedUntiltingPeriodModels
open AffinoidPeriodRings AlgebraicGroupPointRepresentations
open MathlibExt.LinearAlgebra.LocalizedLattices

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  {S : Base p C} (T : Untilting p C S) (L : ScalarLift p C S T) (x : Parameter p C T L)
  (G : Over (Spec (.of E.field))) [GrpObj G]

def positiveTest : CommAlgCat.{0} E.field := by
  letI := L.map.toAlgebra
  exact CommAlgCat.of E.field (DeRhamPlus p T.affine.pair)

def genericTest : CommAlgCat.{0} E.field := by
  letI := ((algebraMap (DeRhamPlus p T.affine.pair)
    (FractionRing (DeRhamPlus p T.affine.pair) x.value)).comp L.map).toAlgebra
  exact CommAlgCat.of E.field (FractionRing (DeRhamPlus p T.affine.pair) x.value)

def localizationTest : positiveTest p C T L ⟶ genericTest p C T L x := by
  letI := L.map.toAlgebra
  letI := ((algebraMap (DeRhamPlus p T.affine.pair)
    (FractionRing (DeRhamPlus p T.affine.pair) x.value)).comp L.map).toAlgebra
  exact CommAlgCat.ofHom
    { __ := algebraMap (DeRhamPlus p T.affine.pair)
        (FractionRing (DeRhamPlus p T.affine.pair) x.value)
      commutes' := fun _ ↦ rfl }

abbrev PositiveGroup := (groups E.field G).obj (positiveTest p C T L)
abbrev GenericGroup := (groups E.field G).obj (genericTest p C T L x)

def positiveMap : PositiveGroup p C T L G →* GenericGroup p C T L x G :=
  ((groups E.field G).map (localizationTest p C T L x)).hom

def HasRelativePosition (g : GenericGroup p C T L x G) (μ : Cocharacter E.field G) : Prop :=
  ∃ a b : PositiveGroup p C T L G, g = positiveMap p C T L x G a *
    (μ.app (genericTest p C T L x)).hom (MarkedUntiltingPeriodModels.parameterUnit p C T L x) *
      positiveMap p C T L x G b

def representationMatrix {n : ℕ} (ρ : Representation E.field G n)
    (g : GenericGroup p C T L x G) :
    GL (Fin n) (FractionRing (DeRhamPlus p T.affine.pair) x.value) :=
  (ρ.app (genericTest p C T L x)).hom g

/-- The associated submodule is the literal representation-matrix image of the standard lattice. -/
def representedModule {n : ℕ} (ρ : Representation E.field G n)
    (g : GenericGroup p C T L x G) :
    Submodule (DeRhamPlus p T.affine.pair)
      (Ambient (DeRhamPlus p T.affine.pair) x.value n) :=
  (standard (DeRhamPlus p T.affine.pair) x.value n).map
    ((Matrix.mulVecLin (representationMatrix p C T L x G ρ g)).restrictScalars
      (DeRhamPlus p T.affine.pair))

set_option maxHeartbeats 1200000 in
-- Allow the dependent native period-ring and sheaf signatures to elaborate.
structure RepresentedLattice {n : ℕ} (ρ : Representation E.field G n)
    (g : GenericGroup p C T L x G) where
  lattice : PeriodLattice p C T L x n
  normalized : lattice.module = representedModule p C T L x G ρ g

set_option maxHeartbeats 1200000 in
-- Allow the dependent native period-ring and sheaf signatures to elaborate.
structure WeightFrame {n : ℕ} {ρ : Representation E.field G n} {μ : Cocharacter E.field G}
    (W : WeightSplitting E.field G n ρ μ) where
  lattice : PeriodLattice p C T L x n
  normalized : lattice.module = standard (DeRhamPlus p T.affine.pair) x.value n
  basis : Module.Basis (Fin n) (DeRhamPlus p T.affine.pair) lattice.module
  columns : ∀ i j, (basis i).val j = algebraMap (DeRhamPlus p T.affine.pair)
    (FractionRing (DeRhamPlus p T.affine.pair) x.value) (L.map (W.basis j i))

/-- All bounds concern actual representation lattices and source-normalized integral bases. -/
def IsRepresentationBounded (g : GenericGroup p C T L x G) (μ : Cocharacter E.field G) : Prop :=
  ∀ (n : ℕ) (ρ : Representation E.field G n) (W : WeightSplitting E.field G n ρ μ),
    ∃ (F : WeightFrame p C T L x G W) (B : RepresentedLattice p C T L x G ρ g),
      PeriodLatticePluckerBounds.IsBoundedBy (DeRhamPlus p T.affine.pair) x.value n
        F.lattice B.lattice F.basis W.weight

end MathlibExt.AlgebraicGeometry.PeriodGroupPositionModels
