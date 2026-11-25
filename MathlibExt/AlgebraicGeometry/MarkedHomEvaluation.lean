/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes

/-!
# Actual marked fixed-Hom evaluation and fibre obstruction objects

The source is an arbitrary fixed proper marked curve, not a degree-one
projective-line map. Every evaluation is the actual universal map on
the marked section of the curve-times-parameter product. The target
is the actual finite product of the given variety over its field.

After every geometric parameter point, the marked ideal is the kernel
of the actual structure-unit maps to its actual marked points.
The obstruction object is H1 of Rπ_*(f*T_V ⊗ I_marks), with T_V the
actual dual of Kähler differentials. No evaluation or obstruction
carrier is supplied freely.
Source: Behrend--Fantechi alg-geom/9601010v1, §6, Proposition 6.2
and its extension proof, restricted at the fixed markings;
Graber--Harris--Starr math/0109220v1, §2 for the curve applications.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MarkedHomEvaluation

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.MapModuliCharts
open MathlibExt.AlgebraicGeometry.MapFamilyDeformationComplexes
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k]

/-- Actual disjoint field-rational sections of the fixed source curve. -/
structure Markings (C : Over (Spec (.of k))) (n : ℕ) where
  map : Fin n → (Spec (.of k) ⟶ C.left)
  over : ∀ i, map i ≫ C.hom = 𝟙 _
  disjoint : Pairwise fun i j => Disjoint (Set.range (map i)) (Set.range (map j))

def parameterMark {C T : Over (Spec (.of k))} {n : ℕ} (P : Markings C n) (i : Fin n) :
    T.left ⟶ (fixedCurve C T).left :=
  pullback.lift (T.hom ≫ P.map i) (𝟙 _)
    (by rw [Category.assoc, P.over]; simp)

theorem parameterMark_projection {C T : Over (Spec (.of k))} {n : ℕ}
    (P : Markings C n) (i : Fin n) :
    parameterMark (T := T) P i ≫ fixedProjection C T = 𝟙 T.left :=
  pullback.lift_snd _ _ _

variable (C V : Over (Spec (.of k))) {n : ℕ} (P : Markings C n)
  (M : FixedModel C.hom V.hom) (a : M.stack.EtaleAtlas)

def evaluation (i : Fin n) : a.U.left ⟶ V.left :=
  parameterMark (T := a.U) P i ≫ (M.family a.U a.point).map

theorem evaluation_over (i : Fin n) : evaluation C V P M a i ≫ V.hom = a.U.hom := by
  rw [evaluation, Category.assoc, (M.family a.U a.point).over, ← Category.assoc,
    parameterMark_projection]
  simp

def evaluationOver (i : Fin n) : a.U ⟶ V :=
  Over.homMk (evaluation C V P M a i) (evaluation_over C V P M a i)

/-- The true simultaneous marked evaluation into the fibre product over the field. -/
def evaluationProduct : a.U ⟶ ∏ᶜ (fun _ : Fin n => V) :=
  Pi.lift (evaluationOver C V P M a)

def geometricCurve (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ a.U.left) : Scheme.{0} :=
  pullback (fixedProjection C a.U) p

def geometricProjection (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ a.U.left) :
    geometricCurve C V M a Ω p ⟶ Spec (.of Ω) := pullback.snd _ _

def geometricMark (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ a.U.left) (i : Fin n) :
    Spec (.of Ω) ⟶ geometricCurve C V M a Ω p :=
  pullback.lift (p ≫ parameterMark (T := a.U) P i) (𝟙 _)
    (by rw [Category.assoc, parameterMark_projection]; simp)

def geometricMap (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ a.U.left) :
    geometricCurve C V M a Ω p ⟶ V.left :=
  pullback.fst _ _ ≫ (M.family a.U a.point).map

def markedIdeal (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ a.U.left) :
    (geometricCurve C V M a Ω p).Modules :=
  kernel (Pi.lift (fun i : Fin n => structureUnit (geometricMark C V P M a Ω p i)))

variable [HasDerivedPushforwards.{0}]

/-- Actual geometric-fibre H1 governing evaluation with all marked images fixed. -/
def obstruction (Ω : Type) [Field Ω] (p : Spec (.of Ω) ⟶ a.U.left) :
    (Spec (.of Ω)).Modules :=
  (DerivedCategory.homologyFunctor (Spec (.of Ω)).Modules 1).obj
    ((derivedPushforward (geometricProjection C V M a Ω p)).obj
      ((DerivedCategory.singleFunctor (geometricCurve C V M a Ω p).Modules 0).obj
        (moduleTensor (geometricCurve C V M a Ω p)
          ((Scheme.Modules.pullback (geometricMap C V M a Ω p)).obj (tangent V))
          (markedIdeal C V P M a Ω p))))

/-- Vanishing is tested on every actual algebraically closed parameter-field point. -/
def IsUnobstructed : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ a.U.left),
    IsZero (obstruction C V P M a Ω p)

end MathlibExt.AlgebraicGeometry.MarkedHomEvaluation
