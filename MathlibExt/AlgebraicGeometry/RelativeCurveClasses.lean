/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricChowOperators
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Actual curve classes over arbitrary fields

This is the scalar-general version of the completed geometric-cycle
presentation: actual dimension-graded cycles modulo differences of the
scheme-theoretic fibres of integral flat affine-line families. It gives a
curve-class carrier for Noetherian targets locally of finite type over the field,
on every geometric field base change. Local finite type preserves cycle dimensions
under transcendental scalar extension; Noetherianity makes the finite `ℚ`-span of
the family differences the whole rational equivalence (on a non-quasi-compact
target, locally finite sums of relations would be needed). The cycle
base-change map is the fixed native fibre-cycle sum; a descent proof for
that map is a dependency, not a chosen class-valued operator.

Generic cycle/flat-pullback/rational-equivalence constructions are completed
in AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/RationalEquivalenceDescent.lean
(Apache 2.0), and are not new Wanted claims. The local definitions reuse the
completed GeometricChow and GeometricChowOperators bodies without changing
the frozen complex-field specialization.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeCurveClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow

abbrev SchemeOver (k : Type) [Field k] := Over (Spec (.of k))

variable {k : Type} [Field k]

def affineLine : SchemeOver k :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))

def affinePoint (a : k) : Spec (.of k) ⟶ (affineLine (k := k)).left :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

def parameterSection (X : SchemeOver k) (a : k) :
    X.left ⟶ pullback X.hom (affineLine (k := k)).hom :=
  pullback.lift (𝟙 _) (X.hom ≫ affinePoint a) (by
    have h : CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 (CommRingCat.of k) := by
      ext z
      simp
    simp only [Category.id_comp, Category.assoc, affinePoint, affineLine, Over.mk_hom]
    rw [← Spec.map_comp, h, Spec.map_id, Category.comp_id])

structure FlatFamily (X : SchemeOver k) [LocallyOfFiniteType X.hom] (r : ℕ) where
  Y : Scheme.{0}
  inclusion : Y ⟶ pullback X.hom (affineLine (k := k)).hom
  [closed : IsClosedImmersion inclusion]
  [integral : IsIntegral Y]
  [noetherian : IsNoetherian Y]
  [flat : Flat (inclusion ≫ pullback.snd X.hom (affineLine (k := k)).hom)]
  dimension : Order.height (genericPoint Y) = r + 1
  [fibresNoetherian : ∀ a : k, IsNoetherian (pullback inclusion (parameterSection X a))]
attribute [instance] FlatFamily.closed FlatFamily.integral FlatFamily.noetherian
  FlatFamily.flat FlatFamily.fibresNoetherian

namespace FlatFamily
variable {X : SchemeOver k} [LocallyOfFiniteType X.hom] {r : ℕ} (F : FlatFamily X r)
abbrev fibre (a : k) := pullback F.inclusion (parameterSection X a)
def fibreInclusion (a : k) : F.fibre a ⟶ X.left := pullback.snd _ _
def fibreCycle (a : k) : CycleGroup X.left r :=
  dimensionPart X.left r (AlgebraicCycle.map (F.fibreInclusion a) Order.height Order.height
    (fundamentalCycle (F.fibre a)))
def difference : CycleGroup X.left r := F.fibreCycle 0 - F.fibreCycle 1
end FlatFamily

/-- Rational equivalence: the `ℚ`-span of the fibre differences of flat families. The span takes
finite combinations, which is rational equivalence because `X` is Noetherian (so its cycles are
finite); on a non-quasi-compact scheme locally finite sums of relations would be needed. -/
def relations (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (r : ℕ) : Submodule ℚ (CycleGroup X.left r) :=
  Submodule.span ℚ (Set.range (FlatFamily.difference (X := X) (r := r)))
abbrev ChowGroup (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (r : ℕ) := CycleGroup X.left r ⧸ relations X r
abbrev CurveClass (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left] :=
  ChowGroup X 1

/-- An actual geometric scalar extension of the target. -/
def fieldBaseChange (X : SchemeOver k) (Ω : Type) [Field Ω] [Algebra k Ω] : SchemeOver Ω :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))

instance fieldBaseChange_locallyOfFiniteType (X : SchemeOver k) [LocallyOfFiniteType X.hom]
    (Ω : Type) [Field Ω] [Algebra k Ω] : LocallyOfFiniteType (fieldBaseChange X Ω).hom := by
  dsimp [fieldBaseChange]
  infer_instance

def fieldProjection (X : SchemeOver k) (Ω : Type) [Field Ω] [Algebra k Ω] :
    (fieldBaseChange X Ω).left ⟶ X.left :=
  pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The class is the quotient of the actual length-weighted pushed cycle. -/
def pushedCurveClass {X : SchemeOver k} [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (C : Scheme.{0}) [IsNoetherian C]
    (f : C ⟶ X.left) [IsProper f] : CurveClass X :=
  (relations X 1).mkQ (dimensionPart X.left 1
    (AlgebraicCycle.map f Order.height Order.height (fundamentalCycle C)))

/-- Source-proved descent for the fixed field-base-change cycle sum. -/
structure FieldClassDescent (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left]
    (Ω : Type) [Field Ω] [Algebra k Ω] [IsNoetherian (fieldBaseChange X Ω).left] : Prop where
  preserves : relations X 1 ≤ (relations (fieldBaseChange X Ω) 1).comap
    (MathlibExt.AlgebraicGeometry.GeometricChowOperators.flatCyclePullback
      (fieldProjection X Ω) 1 0)

def fieldClassMap (X : SchemeOver k) [LocallyOfFiniteType X.hom]
    [IsNoetherian X.left] (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsNoetherian (fieldBaseChange X Ω).left]
    (h : FieldClassDescent X Ω) : CurveClass X →ₗ[ℚ] CurveClass (fieldBaseChange X Ω) :=
  Submodule.mapQ _ _
    (MathlibExt.AlgebraicGeometry.GeometricChowOperators.flatCyclePullback
      (fieldProjection X Ω) 1 0) h.preserves

end MathlibExt.AlgebraicGeometry.RelativeCurveClasses
