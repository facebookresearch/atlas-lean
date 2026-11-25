/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.BrauerZeroCycles
public import Mathlib.Basic.Complex.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Normalized arithmetic Brauer source-integration requests

These are explicit constructor/adapter obligations on native mathematical
objects. They do not assert that the underlying source mathematics is absent.

Source inputs are pinned to AxiomMath/Stacks
`c496df0d9beea9deaeabcea8492605f9a0a2313b` (Apache 2.0),
`EtaleCohomology/GroupCohomology/Continuous.lean`,
`EtaleCohomology/GaloisCohomology/MultiplicativeGroupGaloisModule.lean`,
and `Homology/Injectives/Module/ContinuousGroupModules.lean`;
TauCeti `62bbc0596dc3539d488232e4e924a338548ea0a9` (Apache 2.0),
`Brauer/Basic.lean`, `Brauer/Restriction.lean`, `Brauer/Invariant.lean`,
and `ContCohomology/CohomologyComparison.lean`.

The derived realization is Axiom's exact `rightDerivedPlus`, using the same
separable-closure units/action as Tau. Normalization and field naturality are
stated on actual locally constant two-cocycle classes. Geometric evaluation
is the native scheme-point Ext pullback. The additional retained arithmetic
endpoints use the existing integral rational-equivalence quotient, the actual
archimedean norm cokernel, and the exact `lim_n CH₀/n` completion of
Harpaz--Wittenberg, arXiv:1409.0993v4, pp. 1--2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.BrauerInteroperabilityWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open BrauerCoefficients BrauerEvaluation BrauerInteroperability
open BrauerCorestriction BrauerLocalInvariant BrauerZeroCycles IntegerSchemeChow
open DiscreteGModules

/-- Port the completed enough-injectives construction for the exact source category. -/
public def_wanted source_enough_injectives (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (ContinuousGModule.{0, 0} G)

/-- Port Tau's compactness proof for the Krull topology, including imperfect fields. -/
public def_wanted source_absolute_galois_compact (K : Type) [Field K] :
    CompactSpace (Field.absoluteGaloisGroup K)

/-- Compare Axiom's exact source realization with native injective-resolution homology. -/
public def_wanted source_injective_realization (K : Type) [Field K]
    [EnoughInjectives (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))] :
    InjectiveRealizationComparison K

/-- Every actual native two-cocycle has a finite Galois geometric Čech realization.
The same actual cover is used for its section, cochain and triple-point values. -/
public def_wanted source_geometric_cocycle_realization (K : Type) [Field K]
    (c : TwoCocycles K) : GeometricCocycleRealization K c

/-- Construct the field comparison normalized on the fixed geometric Ext roof
of every actual two-cocycle, with no independent class map to adjust its sign. -/
public def_wanted source_field_gm_comparison (K : Type) [Field K] : FieldGmComparison K

/-- Integrate a factorization of the comparison through Axiom's derived invariants whose composites
are the normalized comparisons (on units in degree zero, and the geometric bridge in degree two);
the legs themselves are not canonical. -/
public def_wanted source_axiom_factorization (K : Type) [Field K]
    [EnoughInjectives (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))]
    (B : FieldGmComparison K) : AxiomFieldFactorization K B

/-- Construct the unit embedding compatible with the actual closure-induced group map. -/
public def_wanted source_field_coefficient_pair (K L : Type) [Field K] [Field L]
    [Algebra K L] [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] :
    FieldCoefficientPair (K := K) L (Field.absoluteGaloisGroup.mapOfAlgebra K L)

/-- The geometric field-extension map agrees on every actual two-cocycle class. -/
public theorem_wanted geometric_restriction_normalized
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (φ : Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K)
    (P : FieldCoefficientPair (K := K) L φ) (c : TwoCocycles K) :
    fieldComparison L (❰source_field_gm_comparison❱ L)
      (BrauerEvaluation.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        ((fieldComparison K (❰source_field_gm_comparison❱ K)).symm (cocycleClass K c))) =
      restriction L φ P (cocycleClass K c)

/-- Construct the actual finite-field separable-closure and fixing-subgroup dictionary. -/
public def_wanted source_finite_field_pair (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K) :
    FiniteFieldPair K L σ

/-- Port corestriction with the complete transversal formula on every cocycle class. -/
public def_wanted source_corestriction (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
    (P : FiniteFieldPair K L σ) : NormalizedCorestriction K L σ P

/-- Supply actual unramified Frobenius layers at every positive degree. -/
public def_wanted source_unramified_layer (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : BrauerArithmeticCompletion.Modulus) : UnramifiedLayerData K n.val

/-- Construct the primitive cocycle of a Frobenius layer: an actual continuous two-cocycle whose
inhomogeneous values are the carry values `primitiveValue`, so that the normalization in
`NormalizedLocalInvariant` applies to an actual class of every layer. -/
public def_wanted source_primitive_cocycle (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K E] (F : FrobeniusLayer K E) (π : Kˣ) :
    {c : TwoCocycles K // ∀ g h, inhomogeneousValue K c g h = primitiveValue K E F π g h}

/-- Port the local invariant with arithmetic Frobenius primitive-cocycle normalization. -/
public def_wanted source_local_invariant (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : NormalizedLocalInvariant K

/-- The real invariant has the actual half-torsion subgroup of `ℚ/ℤ` as its
target. Its inclusion fixes the value of the nonzero class to `1/2`; the
comparison is retained as an archimedean construction obligation. -/
public def_wanted real_invariant_comparison :
    Br ℝ ≃+ (invariantRestriction 2).ker

/-- Restriction multiplies the normalized local invariant by the actual field degree. -/
public theorem_wanted invariant_restriction_cocycle
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (φ : Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K)
    (P : FieldCoefficientPair (K := K) L φ) (c : TwoCocycles K) :
    (❰source_local_invariant❱ L).val (restriction L φ P (cocycleClass K c)) =
      invariantRestriction (Module.finrank K L) ((❰source_local_invariant❱ K).val
        (cocycleClass K c))

/-- Corestriction preserves the normalized invariant, on actual cocycle classes. -/
public theorem_wanted invariant_corestriction_cocycle
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (σ : L →ₐ[K] SeparableClosure K) (P : FiniteFieldPair K L σ)
    (cor : NormalizedCorestriction K L σ P) (c : TwoCocycles L) :
    (❰source_local_invariant❱ K).val (cor.val (cocycleClass L c)) =
      (❰source_local_invariant❱ L).val (cocycleClass L c)

/-- Assemble the actual residue-field source dictionaries for the zero-cycle carrier. -/
public def_wanted source_residue_field_data (k : Type) [Field k] [PerfectField k]
    (X : FieldScheme k) : ∀ x : ZeroPoint X, ResidueFieldData X x

/-- Arithmetic evaluation factors through the existing integral rational-equivalence quotient. -/
public def_wanted zero_cycle_descent (k : Type) [Field k] [PerfectField k]
    (X : FieldScheme k) [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    (a : Brauer X.scheme.left) :
    ChowEvaluation X ❰source_field_gm_comparison❱ (❰source_residue_field_data❱ k X) a

/-- Integrate the ordinary completed Chow pushforward at the fixed finite field norm. -/
public def_wanted source_chow_norm (k l : Type) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (X : FieldScheme k) (Y : FieldScheme l)
    (E : CartesianFieldExtension X Y (algebraMap k l)) :
    NormalizedNorm X Y (algebraMap k l) E

/-- The field-norm projection formula uses actual scheme pullback, integral
Chow pushforward and the corestriction fixed on every two-cocycle class. -/
public theorem_wanted field_norm_evaluation
    (k l : Type) [Field k] [Field l] [PerfectField k] [PerfectField l]
    [Algebra k l] [FiniteDimensional k l]
    (X : FieldScheme k) (Y : FieldScheme l)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    [Smooth Y.scheme.hom] [IsProper Y.scheme.hom]
    (E : CartesianFieldExtension X Y (algebraMap k l))
    (N : NormalizedNorm X Y (algebraMap k l) E)
    (σ : l →ₐ[k] SeparableClosure k) (P : FiniteFieldPair k l σ)
    (cor : NormalizedCorestriction k l σ P)
    (a : Brauer X.scheme.left) (b : Brauer Y.scheme.left)
    (_hb : b.val = BrauerEvaluation.pullback E.map a.val) (z : ChowGroup Y 0) :
    (❰zero_cycle_descent❱ k X a).val (N.val z) =
      cor.val ((❰zero_cycle_descent❱ l Y b).val z)

/-- The archimedean endpoint is the actual complex/real Chow norm cokernel. -/
public def_wanted archimedean_norm_descent
    (X : FieldScheme ℝ) [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    (Y : FieldScheme ℂ) (E : CartesianFieldExtension X Y Complex.ofRealHom)
    (N : NormalizedNorm X Y Complex.ofRealHom E) (a : Brauer X.scheme.left) :
    {f : NormQuotient X Y Complex.ofRealHom E N →+ Br ℝ //
      f.comp (normQuotientMap X Y Complex.ofRealHom E N) =
        (❰zero_cycle_descent❱ ℝ X a).val}

/-- The order of the Brauer class kills its native Chow evaluation. -/
public theorem_wanted zero_cycle_evaluation_killed
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (_ha : n.val • a = 0) :
    ∀ z : ChowGroup X 0, n.val • (❰zero_cycle_descent❱ k X a).val z = 0

/-- Completed evaluation: projection of the completed Chow group to its `n`th inverse-limit
coordinate, followed by the evaluation that the Brauer class induces on that quotient. -/
public def_wanted completed_zero_cycle_evaluation
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0) :
    CompletedChow X →+ Br k :=
  BrauerArithmeticCompletion.completedEvaluation (ChowGroup X 0)
    (❰zero_cycle_descent❱ k X a).val n (❰zero_cycle_evaluation_killed❱ k X a n ha)

/-- The modified archimedean completion uses the same normalized norm quotient
and the same `n`th-coordinate evaluation. -/
public def_wanted completed_archimedean_evaluation
    (X : FieldScheme ℝ) [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    (Y : FieldScheme ℂ) (E : CartesianFieldExtension X Y Complex.ofRealHom)
    (N : NormalizedNorm X Y Complex.ofRealHom E) (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0) :
    CompletedNormQuotient X Y Complex.ofRealHom E N →+ Br ℝ :=
  BrauerArithmeticCompletion.completedEvaluation (NormQuotient X Y Complex.ofRealHom E N)
    (❰archimedean_norm_descent❱ X Y E N a).val n (by
      intro z
      induction z using QuotientAddGroup.induction_on with
      | H z =>
        have hcomp := DFunLike.congr_fun (❰archimedean_norm_descent❱ X Y E N a).property z
        change n.val • (❰archimedean_norm_descent❱ X Y E N a).val
          (normQuotientMap X Y Complex.ofRealHom E N z) = 0
        rw [← AddMonoidHom.comp_apply, hcomp]
        exact ❰zero_cycle_evaluation_killed❱ ℝ X a n ha z)

/-- The completion map is fixed on actual integer cycle classes. -/
public theorem_wanted completed_evaluation_on_cycles
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0)
    (c : CycleGroup X.scheme.left 0) :
    ❰completed_zero_cycle_evaluation❱ k X a n ha
      (BrauerArithmeticCompletion.unit (ChowGroup X 0) (cycleClass X 0 c)) =
        cycleEvaluation X ❰source_field_gm_comparison❱ (❰source_residue_field_data❱ k X) a c := by
  rw [BrauerArithmeticCompletion.completedEvaluation_unit]
  exact (❰zero_cycle_descent❱ k X a).property c

private def check_source_enough_injectives (G : Type) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    DefWanted (EnoughInjectives (ContinuousGModule.{0, 0} G)) := source_enough_injectives G

private def check_source_absolute_galois_compact (K : Type) [Field K] :
    DefWanted (CompactSpace (Field.absoluteGaloisGroup K)) := source_absolute_galois_compact K

private def check_source_injective_realization (K : Type) [Field K]
    [EnoughInjectives (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))] :
    DefWanted (InjectiveRealizationComparison K) := source_injective_realization K

private def check_source_geometric_cocycle_realization (K : Type) [Field K]
    (c : TwoCocycles K) : DefWanted (GeometricCocycleRealization K c) :=
  source_geometric_cocycle_realization K c

private def check_source_field_gm_comparison (K : Type) [Field K] :
    DefWanted (FieldGmComparison K) := source_field_gm_comparison K

private def check_source_axiom_factorization (K : Type) [Field K]
    [EnoughInjectives (ContinuousGModule.{0, 0} (Field.absoluteGaloisGroup K))]
    (B : FieldGmComparison K) : DefWanted (AxiomFieldFactorization K B) :=
  source_axiom_factorization K B

private def check_source_field_coefficient_pair (K L : Type) [Field K] [Field L]
    [Algebra K L] [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] :
    DefWanted (FieldCoefficientPair (K := K) L (Field.absoluteGaloisGroup.mapOfAlgebra K L)) :=
  source_field_coefficient_pair K L

private def check_source_finite_field_pair (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K) :
    DefWanted (FiniteFieldPair K L σ) := source_finite_field_pair K L σ

private def check_source_corestriction (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
    (P : FiniteFieldPair K L σ) : DefWanted (NormalizedCorestriction K L σ P) :=
  source_corestriction K L σ P

private def check_source_primitive_cocycle (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] [IsGalois K E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [ValuativeExtension K E] (F : FrobeniusLayer K E) (π : Kˣ) :
    DefWanted {c : TwoCocycles K //
      ∀ g h, inhomogeneousValue K c g h = primitiveValue K E F π g h} :=
  source_primitive_cocycle K E F π

private def check_source_local_invariant (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    DefWanted (NormalizedLocalInvariant K) := source_local_invariant K

private def check_real_invariant_comparison :
    DefWanted (Br ℝ ≃+ (invariantRestriction 2).ker) := real_invariant_comparison

private def check_source_unramified_layer (K : Type) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : BrauerArithmeticCompletion.Modulus) : DefWanted (UnramifiedLayerData K n.val) :=
  source_unramified_layer K n

private def check_source_residue_field_data (k : Type) [Field k] [PerfectField k]
    (X : FieldScheme k) : DefWanted (∀ x : ZeroPoint X, ResidueFieldData X x) :=
  source_residue_field_data k X

private def check_source_chow_norm (k l : Type) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (X : FieldScheme k) (Y : FieldScheme l)
    (E : CartesianFieldExtension X Y (algebraMap k l)) :
    DefWanted (NormalizedNorm X Y (algebraMap k l) E) := source_chow_norm k l X Y E

private abbrev FieldComparisonSource := FieldComparisonFamily

private abbrev LocalInvariantSource :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K], NormalizedLocalInvariant K

private abbrev ResidueDataSource :=
  ∀ (k : Type) [Field k] [PerfectField k] (X : FieldScheme k),
    ∀ x : ZeroPoint X, ResidueFieldData X x

private abbrev ChowDescentSource (B : FieldComparisonSource) (D : ResidueDataSource) :=
  ∀ (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left),
    ChowEvaluation X B (D k X) a

private abbrev KilledEvaluationSource (B : FieldComparisonSource)
    (D : ResidueDataSource) (Z : ChowDescentSource B D) :=
  ∀ (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (_ha : n.val • a = 0),
    ∀ z : ChowGroup X 0, n.val • (Z k X a).val z = 0

private abbrev ArchimedeanDescentSource (B : FieldComparisonSource)
    (D : ResidueDataSource) (Z : ChowDescentSource B D) :=
  ∀ (X : FieldScheme ℝ) [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    (Y : FieldScheme ℂ) (E : CartesianFieldExtension X Y Complex.ofRealHom)
    (N : NormalizedNorm X Y Complex.ofRealHom E) (a : Brauer X.scheme.left),
    {f : NormQuotient X Y Complex.ofRealHom E N →+ Br ℝ //
      f.comp (normQuotientMap X Y Complex.ofRealHom E N) = (Z ℝ X a).val}

private def check_geometric_restriction_normalized (B : FieldComparisonSource)
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (φ : Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K)
    (P : FieldCoefficientPair (K := K) L φ) (c : TwoCocycles K) :
    ProofWanted (fieldComparison L (B L)
      (BrauerEvaluation.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        ((fieldComparison K (B K)).symm (cocycleClass K c))) =
          restriction L φ P (cocycleClass K c)) :=
  @geometric_restriction_normalized K L _ _ _ φ P c B

private def check_invariant_restriction_cocycle (I : LocalInvariantSource)
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (φ : Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K)
    (P : FieldCoefficientPair (K := K) L φ) (c : TwoCocycles K) :
    ProofWanted ((I L).val (restriction L φ P (cocycleClass K c)) =
      invariantRestriction (Module.finrank K L) ((I K).val (cocycleClass K c))) :=
  @invariant_restriction_cocycle K L _ _ _ _ _ _ _ _ _ _ _ φ P c I

private def check_invariant_corestriction_cocycle (I : LocalInvariantSource)
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [ValuativeExtension K L]
    (σ : L →ₐ[K] SeparableClosure K) (P : FiniteFieldPair K L σ)
    (cor : NormalizedCorestriction K L σ P) (c : TwoCocycles L) :
    ProofWanted ((I K).val (cor.val (cocycleClass L c)) = (I L).val (cocycleClass L c)) :=
  @invariant_corestriction_cocycle K L _ _ _ _ _ _ _ _ _ _ _ σ P cor c I

private def check_zero_cycle_descent (B : FieldComparisonSource) (D : ResidueDataSource)
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left) :
    DefWanted (ChowEvaluation X B (D k X) a) :=
  @zero_cycle_descent k _ _ X _ _ a B D

private def check_field_norm_evaluation (B : FieldComparisonSource)
    (D : ResidueDataSource) (Z : ChowDescentSource B D)
    (k l : Type) [Field k] [Field l] [PerfectField k] [PerfectField l]
    [Algebra k l] [FiniteDimensional k l]
    (X : FieldScheme k) (Y : FieldScheme l)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    [Smooth Y.scheme.hom] [IsProper Y.scheme.hom]
    (E : CartesianFieldExtension X Y (algebraMap k l))
    (N : NormalizedNorm X Y (algebraMap k l) E)
    (σ : l →ₐ[k] SeparableClosure k) (P : FiniteFieldPair k l σ)
    (cor : NormalizedCorestriction k l σ P)
    (a : Brauer X.scheme.left) (b : Brauer Y.scheme.left)
    (hb : b.val = BrauerEvaluation.pullback E.map a.val) (z : ChowGroup Y 0) :
    ProofWanted ((Z k X a).val (N.val z) = cor.val ((Z l Y b).val z)) :=
  @field_norm_evaluation k l _ _ _ _ _ _ X Y _ _ _ _ E N σ P cor a b hb z B D Z

private def check_archimedean_norm_descent (B : FieldComparisonSource)
    (D : ResidueDataSource) (Z : ChowDescentSource B D)
    (X : FieldScheme ℝ) [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    (Y : FieldScheme ℂ) (E : CartesianFieldExtension X Y Complex.ofRealHom)
    (N : NormalizedNorm X Y Complex.ofRealHom E) (a : Brauer X.scheme.left) :
    DefWanted {f : NormQuotient X Y Complex.ofRealHom E N →+ Br ℝ //
      f.comp (normQuotientMap X Y Complex.ofRealHom E N) = (Z ℝ X a).val} :=
  @archimedean_norm_descent X _ _ Y E N a B D Z

private def check_zero_cycle_evaluation_killed
    (B : FieldComparisonSource) (D : ResidueDataSource) (Z : ChowDescentSource B D)
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0) :
    ProofWanted (∀ z : ChowGroup X 0, n.val • (Z k X a).val z = 0) :=
  @zero_cycle_evaluation_killed k _ _ X _ _ a n ha B D Z

private def check_completed_zero_cycle_evaluation
    (B : FieldComparisonSource) (D : ResidueDataSource) (Z : ChowDescentSource B D)
    (H : KilledEvaluationSource B D Z)
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0) :
    DerivedWanted (CompletedChow X →+ Br k) :=
  @completed_zero_cycle_evaluation k _ _ X _ _ a n ha B D Z H

private def check_completed_archimedean_evaluation
    (B : FieldComparisonSource) (D : ResidueDataSource) (Z : ChowDescentSource B D)
    (A : ArchimedeanDescentSource B D Z) (H : KilledEvaluationSource B D Z)
    (X : FieldScheme ℝ) [Smooth X.scheme.hom] [IsProper X.scheme.hom]
    (Y : FieldScheme ℂ) (E : CartesianFieldExtension X Y Complex.ofRealHom)
    (N : NormalizedNorm X Y Complex.ofRealHom E) (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0) :
    DerivedWanted (CompletedNormQuotient X Y Complex.ofRealHom E N →+ Br ℝ) :=
  @completed_archimedean_evaluation X _ _ Y E N a n ha B D Z A H

private def check_completed_evaluation_on_cycles
    (B : FieldComparisonSource) (D : ResidueDataSource) (Z : ChowDescentSource B D)
    (H : KilledEvaluationSource B D Z)
    (k : Type) [Field k] [PerfectField k] (X : FieldScheme k)
    [Smooth X.scheme.hom] [IsProper X.scheme.hom] (a : Brauer X.scheme.left)
    (n : BrauerArithmeticCompletion.Modulus) (ha : n.val • a = 0)
    (c : CycleGroup X.scheme.left 0) :
    ProofWanted (BrauerArithmeticCompletion.completedEvaluation (ChowGroup X 0)
      (Z k X a).val n (H k X a n ha)
        (BrauerArithmeticCompletion.unit (ChowGroup X 0) (cycleClass X 0 c)) =
          cycleEvaluation X B (D k X) a c) :=
  @completed_evaluation_on_cycles k _ _ X _ _ a n ha c B D Z H

end WantedExt.AlgebraicGeometry.BrauerInteroperabilityWanted
