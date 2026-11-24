/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FormalLogSmoothness
public import MathlibExt.AlgebraicGeometry.GeometricLogGhosts
public import MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

/-!
# General marked log-curve family contracts

The underlying family is the actual proper flat marked nodal family.
The logs live on its genuine small-etale ringed sites. Integral log
smoothness is an independent infinitesimal condition, and the ordinary,
marking and node ghosts are fixed on actual geometric point maps.
At a node the monoid is Q pushout_N N² with the local smoothing element;
at a marking it is Q×N. No global split normal-crossings assumption is made.

Sources: F. Kato, Log smooth deformation and moduli of log smooth curves;
Gross--Siebert arXiv:1102.4322v2, Theorem1.1, Definitions1.3/1.5,
Discussion1.8 and Proposition1.24. Integral/fs hypotheses are retained.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LogCurveFamilies
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.EtaleLogDiagrams
open MathlibExt.AlgebraicGeometry.FormalLogSmoothness
open MathlibExt.AlgebraicGeometry.GeometricLogGhosts
open MathlibExt.AlgebraicGeometry.LogStructures
open MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

variable [InverseImageTheory.{0}]

/-- The actual free one-generator sharp monoid, with the site coefficient universe. -/
abbrev NatMonoid : CommMonCat.{1} := .of (ULift.{1} (Multiplicative ℕ))

/-- The actual smoothing homomorphism n↦rho^n. -/
def smoothingMap (Q : CommMonCat.{1}) (rho : Q) : NatMonoid ⟶ Q :=
  CommMonCat.ofHom
    { toFun := fun n => rho ^ Multiplicative.toAdd n.down
      map_one' := by simp
      map_mul' := by intro n m; exact pow_add rho _ _ }

abbrev diagonalNat : NatMonoid ⟶ prod NatMonoid NatMonoid := prod.lift (𝟙 _) (𝟙 _)
abbrev markingMonoid (Q : CommMonCat.{1}) := prod Q NatMonoid
abbrev nodeMonoid (Q : CommMonCat.{1}) (rho : Q) := pushout (smoothingMap Q rho) diagonalNat

def markingInclusion (Q : CommMonCat.{1}) : Q ⟶ markingMonoid Q :=
  prod.lift (𝟙 Q) (CommMonCat.ofHom (1 : Q →* NatMonoid))

/-- A marking is the literal factorization through an actual marked section. -/
def IsMarking {T : Scheme.{0}} {n g : ℕ} (F : MarkedFamily T n g)
    {Ω : Type} [Field Ω] (x : Spec (.of Ω) ⟶ F.X) : Prop :=
  ∃ i : Fin n, x ≫ F.π ≫ F.marking i = x

/-- For the flat nodal family, this is the actual relative nonsmooth locus. -/
def IsNode {T : Scheme.{0}} {n g : ℕ} (F : MarkedFamily T n g)
    {Ω : Type} [Field Ω] (x : Spec (.of Ω) ⟶ F.X) : Prop :=
  ¬ ∃ U : F.X.Opens, (∀ s : Spec (.of Ω), x s ∈ U) ∧ Smooth (U.ι ≫ F.π)

/-- The actual log-curve structure and all three local ghost normalizations. -/
structure LogCurve {T : Scheme.{0}} {n g : ℕ} (F : MarkedFamily T n g) where
  baseLog : LogStructure T.smallEtaleTopology (structureRing T)
  curveLog : LogStructure F.X.smallEtaleTopology (structureRing F.X)
  baseFineSaturated : HasFineSaturatedCharts T.smallEtaleTopology baseLog
  curveFineSaturated : HasFineSaturatedCharts F.X.smallEtaleTopology curveLog
  projection : MorphismAlong ⟨F.X,curveLog⟩ ⟨T,baseLog⟩ F.π
  integral : IntegralMorphism (homOfAlong ⟨F.X,curveLog⟩ ⟨T,baseLog⟩ F.π projection)
  smooth : LogSmooth (homOfAlong ⟨F.X,curveLog⟩ ⟨T,baseLog⟩ F.π projection)
  ordinaryGhost : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ F.X),
    ¬ IsMarking F x → ¬ IsNode F x → IsIso (integral.ghostMap Ω x).map
  markingGhost : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ F.X),
    IsMarking F x → ∃ e : ghost ⟨F.X,curveLog⟩ x ≅ markingMonoid (ghost ⟨T,baseLog⟩ (x ≫ F.π)),
      (integral.ghostMap Ω x).map ≫ e.hom = markingInclusion (ghost ⟨T,baseLog⟩ (x ≫ F.π))
  nodeGhost : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ F.X),
    IsNode F x → ∃ rho : ghost ⟨T,baseLog⟩ (x ≫ F.π), ¬ IsUnit rho ∧
      ∃ e : ghost ⟨F.X,curveLog⟩ x ≅ nodeMonoid (ghost ⟨T,baseLog⟩ (x ≫ F.π)) rho,
        (integral.ghostMap Ω x).map ≫ e.hom = pushout.inl _ _
  /-- Along each marked section the curve log structure is the divisorial log structure of that
  section, on the family and not only on geometric fibres: at every geometric point of the
  section an étale-local log section has characteristic the pure generator of the marking factor
  (trivial base component), and its function vanishes on the section itself. Over `ℂ[ε]/(ε²)` the charts `1 ↦ x` and
  `1 ↦ x - ε` have the same geometric ghosts, but only the first vanishes on the section `x = 0`. -/
  markingEquation : ∀ (i : Fin n) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ T),
    ∃ (U : F.X.Etale) (a : (point (t ≫ F.marking i)).fiber.obj U)
      (m : (monoid F.X.smallEtaleTopology curveLog).obj.obj (Opposite.op U))
      (e : ghost ⟨F.X,curveLog⟩ (t ≫ F.marking i) ≅
        markingMonoid (ghost ⟨T,baseLog⟩ ((t ≫ F.marking i) ≫ F.π))),
      (integral.ghostMap Ω (t ≫ F.marking i)).map ≫ e.hom =
          markingInclusion (ghost ⟨T,baseLog⟩ ((t ≫ F.marking i) ≫ F.π)) ∧
        (prod.fst : markingMonoid _ ⟶ ghost ⟨T,baseLog⟩ ((t ≫ F.marking i) ≫ F.π)).hom (e.hom
          (((point (t ≫ F.marking i)).toPresheafFiber U a
            (characteristic F.X.smallEtaleTopology curveLog).obj).hom
            ((characteristicMap F.X.smallEtaleTopology curveLog).hom.app (Opposite.op U) m))) = 1 ∧
        (prod.snd : markingMonoid _ ⟶ NatMonoid).hom (e.hom
          (((point (t ≫ F.marking i)).toPresheafFiber U a
            (characteristic F.X.smallEtaleTopology curveLog).obj).hom
            ((characteristicMap F.X.smallEtaleTopology curveLog).hom.app (Opposite.op U) m))) =
          ULift.up (Multiplicative.ofAdd 1) ∧
        ((ringSharp (F.marking i)).hom.app (Opposite.op U)).hom
          ((alpha F.X.smallEtaleTopology curveLog).hom.app (Opposite.op U) m) = 0

end MathlibExt.AlgebraicGeometry.LogCurveFamilies
