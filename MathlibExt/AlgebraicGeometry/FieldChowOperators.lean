/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeCurveClasses

/-!
# Rational Chow operators over arbitrary fields

The groups are the actual dimension-graded rational cycles modulo the actual
flat affine-line fibre relations of `RelativeCurveClasses`. The displayed
pullback map selects the dimension `d + r` part of the completed fibre-cycle
sum in `GeometricChowOperators`; closed push is
the actual residue-degree cycle sum. Quotient maps are induced by these fixed
linear maps, and the remaining descent/bijectivity data contain only proofs.
Negative degrees are actual zero modules, including in positive characteristic.

`r` is a dimension selector in this low-level API. `FlatCycleDescent` records
flatness and quotient-relation descent; it does not certify pure relative
dimension or arbitrary-flat-map functoriality. Standard geometric pullback
requires that additional geometric dimension comparison. In the global
zero-section/virtual recipe, `r` is fixed by the actual vector-bundle rank.
Generic pure-relative-dimension and composition/base-change comparisons
remain explicit source integration interfaces.

These are absolute rational Chow homology groups of schemes locally of finite
type over a field. They are not integral Chow groups, relative bivariant groups,
or a supplied virtual-class operation. Ordinary flat/rational-equivalence and
vector-bundle operations are source-complete in AxiomMath/Stacks,
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/RationalEquivalenceDescent.lean`
and `Chow/AffineBundle/VectorBundleFlatPullback.lean` (Apache 2.0).
The formulas adapt the completed local `GeometricChowOperators` definitions.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FieldChowOperators

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow
open MathlibExt.AlgebraicGeometry.RelativeCurveClasses

variable {k : Type} [Field k]

def gradedChow (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left] (d : ℤ) : ModuleCat.{0} ℚ :=
  if 0 ≤ d then ModuleCat.of ℚ (RelativeCurveClasses.ChowGroup X d.toNat)
  else ModuleCat.of ℚ (Fin 0 → ℚ)

def positiveChowIso (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left] (d : ℤ) (hd : 0 ≤ d) :
    gradedChow X d ≅ ModuleCat.of ℚ (RelativeCurveClasses.ChowGroup X d.toNat) := by
  unfold gradedChow
  rw [ite_eq_left hd]

def chowCast (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left] {d e : ℕ} (h : d = e) :
    RelativeCurveClasses.ChowGroup X d →ₗ[ℚ] RelativeCurveClasses.ChowGroup X e := by
  cases h
  exact LinearMap.id

def gradedChowCast (X : SchemeOver k) [LocallyOfFiniteType X.hom] [IsNoetherian X.left] {d e : ℤ} (h : d = e) :
    gradedChow X d →ₗ[ℚ] gradedChow X e := by
  cases h
  exact LinearMap.id

variable (X Y : SchemeOver k) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
  [IsNoetherian X.left] [IsNoetherian Y.left] (f : Y ⟶ X) (r : ℕ)

/-- Proof-only relation descent for the actual dimension-selected fibre-cycle
map. Pure relative dimension is additional geometric data, not supplied here. -/
structure FlatCycleDescent : Prop where
  flat : Flat f.left
  preserves : ∀ d : ℕ, relations X d ≤ (relations Y (d + r)).comap
    (GeometricChowOperators.flatCyclePullback f.left d r)

def chowPullbackNat (D : FlatCycleDescent X Y f r) (d : ℕ) :
    RelativeCurveClasses.ChowGroup X d →ₗ[ℚ] RelativeCurveClasses.ChowGroup Y (d + r) :=
  Submodule.mapQ _ _ (GeometricChowOperators.flatCyclePullback f.left d r) (D.preserves d)

def gradedPullback (D : FlatCycleDescent X Y f r) (d : ℤ) :
    gradedChow X d →ₗ[ℚ] gradedChow Y (d + r) := by
  by_cases hd : 0 ≤ d
  · have ht : 0 ≤ d + r := by omega
    exact (positiveChowIso Y (d + r) ht).toLinearEquiv.symm.toLinearMap ∘ₗ
      chowCast Y (by omega) ∘ₗ chowPullbackNat X Y f r D d.toNat ∘ₗ
        (positiveChowIso X d hd).toLinearEquiv.toLinearMap
  · exact 0

/-- Bijectivity concerns the fixed map above, not a selected Chow equivalence. -/
structure ChowPullbackEquivalence where
  descent : FlatCycleDescent X Y f r
  bijective : ∀ d : ℤ, Function.Bijective (gradedPullback X Y f r descent d)

def pullbackEquiv (D : ChowPullbackEquivalence X Y f r) (d : ℤ) :
    gradedChow X d ≃ₗ[ℚ] gradedChow Y (d + r) :=
  LinearEquiv.ofBijective (gradedPullback X Y f r D.descent d) (D.bijective d)

section ClosedPush

variable {Z : SchemeOver k} [LocallyOfFiniteType Z.hom] [IsNoetherian Z.left]
  (i : Z ⟶ Y)

def closedPushBasis [IsClosedImmersion i.left] (d : ℕ) (x : Z.left) : CycleGroup Y.left d := by
  classical
  exact dimensionPart Y.left d
    (Function.locallyFinsuppWithin.single (i.left x) (i.left.residueDegree x : ℚ))

def closedCyclePush [IsClosedImmersion i.left] (d : ℕ) :
    CycleGroup Z.left d →ₗ[ℚ] CycleGroup Y.left d :=
  Finsupp.linearCombination ℚ (closedPushBasis Y i d) ∘ₗ
    GeometricChowOperators.cycleFinsupp Z.left ∘ₗ (cyclesOfDimension Z.left d).subtype

/-- Proof-only rational-equivalence descent for the actual closed-cycle sum. -/
structure ClosedCycleDescent [IsClosedImmersion i.left] : Prop where
  preserves : ∀ d : ℕ, relations Z d ≤ (relations Y d).comap (closedCyclePush Y i d)

def closedChowPush [IsClosedImmersion i.left] (D : ClosedCycleDescent Y i) (d : ℕ) :
    RelativeCurveClasses.ChowGroup Z d →ₗ[ℚ] RelativeCurveClasses.ChowGroup Y d :=
  Submodule.mapQ _ _ (closedCyclePush Y i d) (D.preserves d)

def gradedClosedPush [IsClosedImmersion i.left] (D : ClosedCycleDescent Y i) (d : ℤ) :
    gradedChow Z d →ₗ[ℚ] gradedChow Y d := by
  by_cases hd : 0 ≤ d
  · exact (positiveChowIso Y d hd).toLinearEquiv.symm.toLinearMap ∘ₗ
      closedChowPush Y i D d.toNat ∘ₗ (positiveChowIso Z d hd).toLinearEquiv.toLinearMap
  · exact 0

end ClosedPush

section ComplexComparison

variable (X : GeometricChow.ComplexScheme) [LocallyOfFiniteType X.hom] [IsNoetherian X.left] (d : ℕ)

/-- The same actual family over ℂ, in the frozen complex presentation. -/
def toComplexFamily (F : RelativeCurveClasses.FlatFamily X d) : GeometricChow.FlatFamily X d where
  Y := F.Y
  inclusion := F.inclusion
  isClosedImmersion := F.closed
  isIntegral := F.integral
  isNoetherian := F.noetherian
  isFlat := F.flat
  dimension := F.dimension
  fibresNoetherian := F.fibresNoetherian

/-- The converse conversion adds only the standing finite-type hypothesis. -/
def fromComplexFamily (F : GeometricChow.FlatFamily X d) : RelativeCurveClasses.FlatFamily X d where
  Y := F.Y
  inclusion := F.inclusion
  closed := F.isClosedImmersion
  integral := F.isIntegral
  noetherian := F.isNoetherian
  flat := F.isFlat
  dimension := F.dimension
  fibresNoetherian := F.fibresNoetherian

/-- Over ℂ the two presentations generate exactly the same cycle relations. -/
theorem complexRelations_eq : relations X d = GeometricChow.rationalEquivalences X d := by
  apply congrArg (Submodule.span ℚ)
  ext c
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨toComplexFamily X d F, rfl⟩
  · rintro ⟨F, rfl⟩
    exact ⟨fromComplexFamily X d F, rfl⟩

/-- A canonical identity-on-cycles comparison with the frozen complex Chow group. -/
def complexChowEquiv :
    RelativeCurveClasses.ChowGroup X d ≃ₗ[ℚ] GeometricChow.ChowGroup X d :=
  Submodule.quotEquivOfEq _ _ (complexRelations_eq X d)

/-- The comparison sends the actual quotient cycle to that same cycle. -/
theorem complexChowEquiv_mk (c : CycleGroup X.left d) :
    complexChowEquiv X d ((relations X d).mkQ c) =
      (GeometricChow.rationalEquivalences X d).mkQ c :=
  Submodule.quotEquivOfEq_mk _ _ (complexRelations_eq X d) c

end ComplexComparison

end MathlibExt.AlgebraicGeometry.FieldChowOperators
