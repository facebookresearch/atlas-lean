/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFarguesFontaineMaps
public import MathlibExt.AlgebraicGeometry.AffinoidPeriodRings
public import MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
public import MathlibExt.LinearAlgebra.LocalizedLattices

/-!
# Actual marked-untilt period maps and modification lattices

A marked untilt includes its actual tilt isomorphism and integral marking.
The latter commutes with the native map from the plus-ring pretilt to
the powerbounded-ring pretilt and the existing tilt presentation. Its
E-action is integral and, on the Cohen--Witt scalars, agrees after theta
with the marked residue action, so the untilt lies over the specified
coefficient base.

The period map is the actual tensor lift of the marked native Witt map
into B_dR-plus and the original E scalar lift. It is normalized on every
pure tensor. The relative theta completion is the literal completion of
this source map's kernel. Its comparison to native B_dR-plus is a separate
normalized construction request.

Modification lattices are the existing actual finite-projective lattices
over native B_dR-plus, localized at a true filtration-one generator.
Framed relative position uses its actual integer-power weighted basis.

Sources: Fargues--Scholze, arXiv:2102.13459v4, Section III.3 and VI.1;
Scholze--Weinstein, arXiv:1211.6357v2, Sections 5--6.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.RingTheory.CompleteHuberPairModels
open LocalWittCoefficientFields RelativeFarguesFontaineRings
open AffineUntiltingGeometry AffinoidPeriodRings
open MathlibExt.LinearAlgebra.LocalizedLattices
open scoped TensorProduct
open scoped ValuativeRel

variable (p : ℕ) [Fact p.Prime]

/-- The actual integral inclusion from the untilt plus ring into its powerbounded ring. -/
def plusInclusion (P : PerfectoidPair p) : P.plus →+* P.powerbounded where
  toFun a := ⟨a.val, P.plus_bound a.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Its literal map on the two native p-reductions. -/
def plusReductionMap (P : PerfectoidPair p) :
    ModP P.plus p →+* ModP P.powerbounded p :=
  Ideal.quotientMap (Ideal.span {(p : P.powerbounded)}) (plusInclusion p P) (by
    apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact Ideal.subset_span (by simp))

/-- The actual map of integral inverse-Frobenius limits. -/
def preTiltInclusion (T : AffineUntilting p) [IntegralPeriodInput p T.pair] :
    PreTilt T.pair.plus p →+* IntegralTiltModels.IntegralRing p T.pair :=
  Perfection.map p (plusReductionMap p T.pair)

variable {E : MixedField p} (C : CoefficientData p E) (S : Base p C)

/-- The actual marked untilt over `E`, with its source integral dictionary and E action
(Fargues--Scholze, Definition I.2.2 and Section VI.1: an untilt over the specified coefficient
base). The `E`-action is integral on `𝒪_E`, and on the Cohen--Witt scalars `W(k_E)` it is the
marked residue action after theta. Without this compatibility an `E`-action twisted by a
nontrivial automorphism of the unramified subfield would be admitted, and no scalar lift to
B_dR-plus could exist. -/
structure Untilting where
  affine : AffineUntilting p
  [periodInput : IntegralPeriodInput p affine.pair]
  tiltIso : affine.tilt.pair ≅ S.pair
  marking : S.pair.plus ≃+* PreTilt affine.pair.plus p
  integral_normalized : ∀ x : PreTilt affine.pair.plus p,
    tiltIso.inv.hom (IntegralTiltModels.TiltModel.integralMap p affine.pair affine.tilt
      (preTiltInclusion p affine x)) = (marking.symm x : S.pair.ring)
  [fieldAction : Algebra E.field affine.pair.ring]
  integral_action : ∀ x ∈ 𝒪[E.field], algebraMap E.field affine.pair.ring x ∈ affine.pair.plus
  residue_compatible : ∀ w : WittVector p (Residue p E),
    algebraMap E.field affine.pair.ring (C.cohen w : E.field) =
      thetaPlusToRing p affine.pair (AinfToDeRham p affine.pair
        (WittVector.map marking.toRingHom
          (WittVector.map (algebraMap (Residue p E) S.pair.plus) w)))

attribute [instance] Untilting.periodInput Untilting.fieldAction

/-- The actual marked A-inf map into native B_dR-plus. -/
def wittEmbedding (T : Untilting p C S) :
    WittVector p S.pair.plus →+* DeRhamPlus p T.affine.pair :=
  (AinfToDeRham p T.affine.pair).comp (WittVector.map T.marking.toRingHom)

/-- E coefficients are constrained by actual theta and every original Cohen-Witt scalar. -/
structure ScalarLift (T : Untilting p C S) where
  map : E.field →+* DeRhamPlus p T.affine.pair
  theta : (thetaPlusToRing p T.affine.pair).comp map = algebraMap E.field T.affine.pair.ring
  balanced : ∀ w : WittVector p (Residue p E),
    wittEmbedding p C S T (WittVector.map (algebraMap (Residue p E) S.pair.plus) w) =
      map (C.cohen w : E.field)

variable {S} (T : Untilting p C S) (L : ScalarLift p C S T)

/-- The actual local-field integer factor of the period map. -/
def integerEmbedding : Integers p E →+* DeRhamPlus p T.affine.pair :=
  L.map.comp (𝒪[E.field]).subtype

/-- The original relative period ring maps by the native balanced tensor lift. -/
def periodEmbedding : RelativeFarguesFontaineRings.Ring p C S →+*
    DeRhamPlus p T.affine.pair := by
  letI := coefficientAlgebra p C
  letI : Algebra (WittVector p (Residue p E)) (WittVector p S.pair.plus) :=
    (WittVector.map (algebraMap (Residue p E) S.pair.plus)).toAlgebra
  letI : Algebra (WittVector p (Residue p E)) (DeRhamPlus p T.affine.pair) :=
    ((integerEmbedding p C T L).comp C.cohen).toAlgebra
  let f : WittVector p S.pair.plus →ₐ[WittVector p (Residue p E)]
      DeRhamPlus p T.affine.pair :=
    { __ := wittEmbedding p C S T
      commutes' := L.balanced }
  let g : Integers p E →ₐ[WittVector p (Residue p E)] DeRhamPlus p T.affine.pair :=
    { __ := integerEmbedding p C T L
      commutes' := fun _ ↦ rfl }
  exact (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- The source period map fixes every original tensor factor. -/
theorem periodEmbedding_tensor (w : WittVector p S.pair.plus) (b : Integers p E) :
    letI := coefficientAlgebra p C
    periodEmbedding p C T L
      (RelativeWittLoopTests.tensor p (Residue p E) (Integers p E) (residueTest p C S) w b) =
      wittEmbedding p C S T w * L.map (b : E.field) := by
  let := coefficientAlgebra p C
  rfl

/-- The actual ramified uniformizer is a unit in this native rational period ring. -/
theorem periodEmbedding_prime_unit :
    IsUnit (periodEmbedding p C T L (prime p C S)) := by
  have h : periodEmbedding p C T L (prime p C S) = L.map (C.uniformizer : E.field) := by
    have e : prime p C S =
        (letI := coefficientAlgebra p C
        RelativeWittLoopTests.tensor p (Residue p E) (Integers p E)
          (residueTest p C S) 1 C.uniformizer) := rfl
    rw [e, periodEmbedding_tensor, map_one, one_mul]
  rw [h]
  exact (isUnit_iff_ne_zero.mpr C.nonzero).map L.map

/-- Actual uniformizer inversion of the prescribed original period map. -/
def rationalPeriodEmbedding :
    RamifiedRational p C (residueTest p C S) →+* DeRhamPlus p T.affine.pair :=
  Localization.awayLift (periodEmbedding p C T L) (prime p C S)
    (periodEmbedding_prime_unit p C T L)

/-- Theta on the actual ramified rational source. -/
def relativeTheta :
    RamifiedRational p C (residueTest p C S) →+* T.affine.pair.ring :=
  (thetaPlusToRing p T.affine.pair).comp (rationalPeriodEmbedding p C T L)

/-- The actual relative untilt completion, with its true theta-kernel ideal. -/
abbrev RelativeCompletion :=
  AdicCompletion (RingHom.ker (relativeTheta p C T L))
    (RamifiedRational p C (residueTest p C S))

/-- A ring isomorphism from the relative completion to `B_dR^+` restricts, on the ramified
rational source, to the period embedding. -/
def CompletionComparison.UnitCondition
    (e : RelativeCompletion p C T L ≃+* DeRhamPlus p T.affine.pair) : Prop :=
  e.toRingHom.comp (algebraMap _ _) = rationalPeriodEmbedding p C T L

set_option maxHeartbeats 1200000 in
-- Allow the dependent native period-ring and sheaf signatures to elaborate.
/-- A ring isomorphism from the relative completion to `B_dR^+` matches the `n`-th filtration
ideal of `B_dR^+` with the kernel of the projection to level `n` of the completion, for every
`n`. -/
def CompletionComparison.FiltrationCondition
    (e : RelativeCompletion p C T L ≃+* DeRhamPlus p T.affine.pair) : Prop :=
  ∀ n : ℕ, Ideal.comap e.toRingHom (AffinoidPeriodRings.filtration p T.affine.pair n) =
    RingHom.ker ((AdicCompletion.evalₐ (RingHom.ker (relativeTheta p C T L)) n).toRingHom)

set_option maxHeartbeats 1200000 in
-- Allow the dependent native period-ring and sheaf signatures to elaborate.
/-- Completion comparison retains the actual source unit and every filtration projection. The two
conditions are named predicates, so that the kernel does not recheck them in every auxiliary
declaration of the structure. -/
structure CompletionComparison where
  equivalence : RelativeCompletion p C T L ≃+* DeRhamPlus p T.affine.pair
  unit : CompletionComparison.UnitCondition p C T L equivalence
  filtration : CompletionComparison.FiltrationCondition p C T L equivalence

set_option maxHeartbeats 1200000 in
-- Allow the dependent native period-ring and sheaf signatures to elaborate.
/-- The source modification parameter is a regular generator of the true first filtration ideal. -/
@[nolint unusedArguments]
structure Parameter (_L : ScalarLift p C S T) where
  value : DeRhamPlus p T.affine.pair
  regular : IsRegular value
  ideal : AffinoidPeriodRings.filtration p T.affine.pair 1 = Ideal.span {value}

/-- Actual theta-adic lattices use the existing full finite-projective submodule definition. -/
abbrev PeriodLattice (x : Parameter p C T L) (n : ℕ) :=
  MathlibExt.LinearAlgebra.LocalizedLattices.Lattice
    (DeRhamPlus p T.affine.pair) x.value n

/-- The genuine unit parameter in the punctured coefficient ring. -/
def parameterUnit (x : Parameter p C T L) :
    (MathlibExt.LinearAlgebra.LocalizedLattices.FractionRing
      (DeRhamPlus p T.affine.pair) x.value)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := MathlibExt.LinearAlgebra.LocalizedLattices.FractionRing
      (DeRhamPlus p T.affine.pair) x.value) x.value).unit

/-- Framed relative position retains every actual integer-power basis vector. -/
def HasFramedRelativePosition (x : Parameter p C T L) {n : ℕ}
    (A B : PeriodLattice p C T L x n) (weight : Fin n → ℤ) : Prop :=
  ∃ e : Module.Basis (Fin n) (DeRhamPlus p T.affine.pair) A.module,
    B.module = Submodule.span (DeRhamPlus p T.affine.pair)
      {v | ∃ i : Fin n, v = fun j ↦
        ((parameterUnit p C T L x ^ weight i :
          (MathlibExt.LinearAlgebra.LocalizedLattices.FractionRing
            (DeRhamPlus p T.affine.pair) x.value)ˣ) :
          MathlibExt.LinearAlgebra.LocalizedLattices.FractionRing
            (DeRhamPlus p T.affine.pair) x.value) * (e i).val j}

end MathlibExt.AlgebraicGeometry.MarkedUntiltingPeriodModels
