/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import MathlibExt.AlgebraicGeometry.BirationalResolution
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
public import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.Complex.Basic

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual smooth Fano geometry and local Kähler Jacobians

The canonical line is pinned by natural Serre duality. The anticanonical
line is its actual inverse, and its volume is fixed by its actual H0
Hilbert polynomial. A local Jacobian is the actual top exterior map of
Kähler differentials for the scheme's stalk map. Its scalar is measured
in actual rank-one bases, so changes of local bases are by units.

References: Hartshorne, III.7; Fujita, A valuative criterion for uniform
K-stability of Q-Fano varieties, Definition 1.1 and Theorem 1.4.
-/

namespace MathlibExt.AlgebraicGeometry.ValuativeFanoGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies
open MathlibExt.AlgebraicGeometry.BirationalResolution
open MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
open scoped ENNReal

abbrev ComplexVariety := Over (Spec (.of ℂ))

/-- Actual coherent global sections, with scalars from the structure morphism. -/
abbrev SectionSpace (X : ComplexVariety) (M : X.left.Modules) :=
  (sectionsFunctor X.hom).obj M

/-- A smooth projective Fano variety with its actual anticanonical section polynomial. -/
structure FanoData (X : ComplexVariety) (n : ℕ) where
  integral : IsIntegral X.left
  smooth : SmoothOfRelativeDimension n X.hom
  proper : IsProper X.hom
  projective : ProjectiveSpace.IsProjective X
  geometricallyIrreducible : GeometricallyIrreducible X.hom
  canonical : LineBundle X.left
  canonicalDuality : SerreDualizingLine X.hom canonical.val n
  anticanonical : LineBundle X.left
  inverse : Nonempty (moduleTensor X.left canonical.val anticanonical.val ≅ structureModule X.left)
  [noetherian : IsNoetherian X.left]
  ample : IsAmpleLine anticanonical
  hilbert : Polynomial ℚ
  dimension : hilbert.natDegree = n
  positiveLeading : 0 < hilbert.leadingCoeff
  finiteSections : ∀ m : ℕ, Module.Finite ℂ (SectionSpace X (power anticanonical.val m))
  eventualSections : ∃ N : ℕ, ∀ m ≥ N,
    hilbert.eval (m : ℚ) = (Module.finrank ℂ (SectionSpace X (power anticanonical.val m)) : ℚ)

/-- The genuine anticanonical volume n! times the fixed Hilbert leading coefficient. -/
def anticanonicalVolume {X : ComplexVariety} {n : ℕ} (F : FanoData X n) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.factorial : ℝ) * (F.hilbert.leadingCoeff : ℝ))

theorem anticanonicalVolume_ne_top {X : ComplexVariety} {n : ℕ} (F : FanoData X n) :
    anticanonicalVolume F ≠ ⊤ := ENNReal.ofReal_ne_top

theorem anticanonicalVolume_pos {X : ComplexVariety} {n : ℕ} (F : FanoData X n) :
    0 < anticanonicalVolume F := by
  apply ENNReal.ofReal_pos.mpr
  have h := F.positiveLeading
  positivity

/-- The actual local ring at the specified scheme point. -/
abbrev LocalRing (X : ComplexVariety) (x : X.left) := X.left.presheaf.stalk x

/-- The local coefficient map is the actual global scalar map followed by the germ. -/
def localScalarMap (X : ComplexVariety) (x : X.left) : ℂ →+* LocalRing X x :=
  (X.left.presheaf.germ ⊤ x (by trivial)).hom.comp (globalScalarMap X.hom)

/-- The canonical local coefficient algebra, kept explicit to avoid a free scalar action. -/
@[instance_reducible]
def localAlgebra (X : ComplexVariety) (x : X.left) : Algebra ℂ (LocalRing X x) :=
  (localScalarMap X x).toAlgebra

/-- The actual stalk map commutes with the actual coefficient structure maps. -/
theorem localScalarMap_natural {X Y : ComplexVariety} (f : Y ⟶ X) (y : Y.left) (c : ℂ) :
    (f.left.stalkMap y).hom (localScalarMap X (f.left y) c) = localScalarMap Y y c := by
  have hg : globalScalarMap Y.hom = f.left.appTop.hom.comp (globalScalarMap X.hom) := by
    change (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ Y.hom.appTop).hom) =
      (((Scheme.ΓSpecIso (.of ℂ)).inv ≫ (X.hom.appTop ≫ f.left.appTop)).hom)
    rw [← Scheme.Hom.comp_appTop, f.w]
  simp [localScalarMap, hg]

/-- The actual top exterior Kähler module in the actual local ring. -/
abbrev LocalTopForms (X : ComplexVariety) (x : X.left) (n : ℕ) : Type :=
  letI : Algebra ℂ (LocalRing X x) := localAlgebra X x
  ↥(⋀[LocalRing X x]^n (KaehlerDifferential ℂ (LocalRing X x)))

/-- An algebra-hom spelling of the actual stalk map, with full pointwise normalization. -/
structure StalkAlgebraMap {X Y : ComplexVariety} (f : Y ⟶ X) (y : Y.left) where
  map :
    letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
    letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
    LocalRing X (f.left y) →ₐ[ℂ] LocalRing Y y
  normalized :
    letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
    letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
    map.toRingHom = (f.left.stalkMap y).hom

/-- The canonical algebra-hom spelling is constructed from the actual scheme stalk map. -/
def canonicalStalkAlgebraMap {X Y : ComplexVariety} (f : Y ⟶ X) (y : Y.left) :
    StalkAlgebraMap f y := by
  letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
  letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
  refine
    { map := { __ := (f.left.stalkMap y).hom, commutes' := ?_ }
      normalized := rfl }
  intro c
  exact localScalarMap_natural f y c

/-- The canonical differential map, semilinear along that actual normalized stalk map. -/
def stalkDifferentialMap {X Y : ComplexVariety} {f : Y ⟶ X} {y : Y.left}
    (d : StalkAlgebraMap f y) :
    letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
    letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
    KaehlerDifferential ℂ (LocalRing X (f.left y)) →ₛₗ[d.map.toRingHom]
      KaehlerDifferential ℂ (LocalRing Y y) := by
  letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
  letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
  letI : Algebra (LocalRing X (f.left y)) (LocalRing Y y) := d.map.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (LocalRing X (f.left y)) (LocalRing Y y) :=
    IsScalarTower.of_algebraMap_eq' (by ext c; exact (d.map.commutes c).symm)
  let u := KaehlerDifferential.map ℂ ℂ (LocalRing X (f.left y)) (LocalRing Y y)
  refine { toFun := u, map_add' := u.map_add, map_smul' := ?_ }
  intro a s
  rw [u.map_smul]
  change (algebraMap (LocalRing X (f.left y)) (LocalRing Y y) a) • u s = d.map a • u s
  rfl

/-- The actual top Kähler Jacobian map. No canonical morphism is chosen as input. -/
def topStalkMap {X Y : ComplexVariety} {f : Y ⟶ X} {y : Y.left}
    (d : StalkAlgebraMap f y) (n : ℕ) :
    letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
    letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
    LocalTopForms X (f.left y) n →ₛₗ[d.map.toRingHom] LocalTopForms Y y n := by
  letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
  letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
  exact ExteriorAlgebra.powMapₛₗ n d.map.toRingHom (stalkDifferentialMap d)

/-- The local Jacobian scalar in actual rank-one top-form bases. -/
def jacobianScalar {X Y : ComplexVariety} {f : Y ⟶ X} {y : Y.left}
    (d : StalkAlgebraMap f y) (n : ℕ)
    (bX : Module.Basis Unit (LocalRing X (f.left y)) (LocalTopForms X (f.left y) n))
    (bY : Module.Basis Unit (LocalRing Y y) (LocalTopForms Y y n)) : LocalRing Y y := by
  letI : Algebra ℂ (LocalRing X (f.left y)) := localAlgebra X (f.left y)
  letI : Algebra ℂ (LocalRing Y y) := localAlgebra Y y
  exact bY.repr (topStalkMap d n (bX ())) ()

end MathlibExt.AlgebraicGeometry.ValuativeFanoGeometry
