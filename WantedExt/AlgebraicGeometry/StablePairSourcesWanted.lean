/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.StablePairObstructionMaps

/-!
# Shared proof and source-comparison requests for stable pairs

The payloads use the actual pair families, ideal kernels, cochain
tensors, bar/refinement diagrams and the equation (2.13) map.
Completed generic cotangent and module constructors are source ports;
their comparison with these particular native presentations remains
explicit. No generic cotangent-existence theorem is re-requested.

References: Pandharipande–Thomas, arXiv:0707.2348v5, §2.3;
Huybrechts–Thomas, arXiv:0805.3527v2, §2 and §4;
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
Cotangent/SchemeCotangentComplex.lean and ResolutionCotangentAny.lean,
Apache 2.0; Stacks 08QI, 08T2, 08EU, 0A9Y.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.StablePairSources

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries StablePairFamilies
open StablePairParameterPullbacks StablePairPerfectComplexes StablePairTraceModels
open StablePairDiagonalIdeals StablePairAtiyahKernels StablePairCochainTensorMaps
open StablePairCotangentComparisons StablePairTraceDualityModels
open StablePairFourierMukaiAtiyah StablePairProductCotangents StablePairCanonicalSources
open StablePairSerreMaps StablePairObstructionMaps NormalizedModuleTensorMaps
open GlobalPerfectObstructionTheory GlobalObstructionMorphisms QuasicoherentDualityReferences
attribute [local instance] HasDerivedCategory.standard

theorem_wanted stable_under_parameter_pullback
    {X P T : Over (Spec (.of ℂ))} (f : T ⟶ P) (F : Family X P) :
    ReindexIsFamily f F

theorem_wanted identity_preserves_section {X P : Over (Spec (.of ℂ))} (F : RawPair X P) :
    (rawReindex (𝟙 P) F).sectionMap ≫ (identityModuleIso F).hom = F.sectionMap

theorem_wanted composition_preserves_section
    {X P T U : Over (Spec (.of ℂ))} (f : T ⟶ P) (g : U ⟶ T) (F : RawPair X P) :
    (rawReindex g (rawReindex f F)).sectionMap ≫ (compositionModuleIso f g F).hom =
      (rawReindex (g ≫ f) F).sectionMap

/-- The whole fine moduli scheme may have infinitely many numerical components. -/
def_wanted fine_stable_pair_family (X : Over (Spec (.of ℂ))) (HX : Threefold X) :
    Σ P : Over (Spec (.of ℂ)), {F : Family X P // Represents P F}

def_wanted perfect_pair_resolution (X P : Over (Spec (.of ℂ)))
    (HX : Threefold X) (HP : ProjectiveParameter P) (F : Family X P) :
    PairResolution F.toRawPair

theorem_wanted end_squared_zero (Y : Scheme) (A : FiniteComplex Y) : EndSquaredZero A

theorem_wanted dual_squared_zero (Y : Scheme) (A : FiniteComplex Y) : DualSquaredZero A

def_wanted cochain_trace (Y : Scheme) (A : FiniteComplex Y) (he : EndSquaredZero A) :
    TracePacket A he

def_wanted trace_free_inclusion (Y : Scheme) (A : FiniteComplex Y) (he : EndSquaredZero A)
    (T : TracePacket A he) : TraceFreeInclusion A T

def_wanted tensor_end_comparison (Y : Scheme) (A : FiniteComplex Y)
    (hd : DualSquaredZero A) (he : EndSquaredZero A) : EndTensorComparison A hd he

def_wanted ideal_square {Y Z : Scheme} (i : Y ⟶ Z) : IdealSquare i

def_wanted diagonal_resolution {Y Z : Over (Spec (.of ℂ))}
    (i : Y ⟶ Z) [IsClosedImmersion i.left] [IsSeparated Z.hom] [IsNoetherian Z.left] :
    ResolutionAugmentation i

def_wanted truncated_kernel_projection {Y Z : Over (Spec (.of ℂ))}
    (i : Y ⟶ Z) (S : IdealSquare (diagonal Z)) : KernelProjection i S

def_wanted diagonal_differences (Z : Over (Spec (.of ℂ))) (V : Z.left.Opens)
    (W : (pullback Z.hom Z.hom).Opens)
    (h₁ : W ≤ pullback.fst Z.hom Z.hom ⁻¹ᵁ V)
    (h₂ : W ≤ pullback.snd Z.hom Z.hom ⁻¹ᵁ V) (x : Γ(Z.left,V)) :
    DiagonalDifference V W h₁ h₂ x

def_wanted diagonal_relation_generators {Y Z : Over (Spec (.of ℂ))}
    (i : Y ⟶ Z) [IsClosedImmersion i.left] (a : AffineChart Y.hom) (c : EmbeddingChart i a)
    (f : Γ(ideal i.left,c.ambient)) : RelationGenerator i c f

def_wanted diagonal_cochain_tensor (Y : Over (Spec (.of ℂ)))
    (T : PullbackTensor (diagonal Y)) (K L : Cochains Y.left) : DiagonalCochainMap Y T K L

def_wanted right_unit_cochain (Y : Over (Spec (.of ℂ))) (K : Cochains Y.left) :
    RightUnitCochainMap Y K

def_wanted normalized_universal_kernel {Y Z : Over (Spec (.of ℂ))}
    (i : Y ⟶ Z) [IsClosedImmersion i.left] [Smooth Z.hom]
    [IsSeparated Z.hom] [IsNoetherian Z.left] (A : FiniteComplex Y.left)
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}] :
    {D : UniversalKernelData Y A.cochain // D.ambient = Z ∧ HEq D.embedding i}

/-- A source bridge to compatible models, rather than existence of a new cotangent complex. -/
def_wanted compatible_product_cotangent_bridge
    (X P : Over (Spec (.of ℂ))) (HX : Threefold X) (K : Cochains (total X P))
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (D : UniversalKernelData (product X P) K) :
    Σ C : CotangentNormalization (product X P).hom,
      Σ R : CotangentNormalization (pullback.fst X.hom P.hom),
        Σ B : CotangentNormalization P.hom,
          CotangentTruncation D.embedding D.square C × ProductCotangentDiagram X P C R B

def_wanted full_universal_kernel_lift (Y : Over (Spec (.of ℂ))) (K : Cochains Y.left)
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (D : UniversalKernelData Y K) (C : CotangentNormalization Y.hom)
    (Q : CotangentTruncation D.embedding D.square C) : FullKernelLift D C Q

def_wanted perfect_tensor_adjunction (Y : Scheme) (A : FiniteComplex Y) (hd : DualSquaredZero A)
    [HasDerivedTensors.{0}] : PerfectTensorAdjunction A hd

def_wanted projection_formula_cochain {X Y : Scheme} (f : Y ⟶ X) (T : PullbackTensor f)
    (M : Cochains Y) (L : Cochains X)
    : ProjectionFormulaCochainMap f T M L

def_wanted derived_projection_formula {X Y : Scheme} (f : Y ⟶ X) (T : PullbackTensor f)
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}] :
    DerivedProjectionFormula f T

def_wanted pullback_tensor_cochain {X Y : Scheme} (f : Y ⟶ X) (T : PullbackTensor f)
    (M L : Cochains X) : PullbackTensorCochainMap f T M L

def_wanted derived_pullback_tensor {X Y : Scheme} (f : Y ⟶ X) (T : PullbackTensor f)
    [HasDerivedPullbacks.{0}] [HasDerivedTensors.{0}] :
    DerivedPullbackTensor f T

def_wanted left_unit_cochain (X : Scheme) (L : Cochains X)
    : LeftUnitCochainMap L

def_wanted tensor_twist_shift (Y : Scheme) (K : Cochains Y) (ω : Y.Modules)
    : CochainTwistShiftMap K ω

def_wanted direct_image_shifts {X Y : Scheme} (f : Y ⟶ X)
    [HasDerivedPushforwards.{0}] :
    PushforwardShift f

def_wanted proper_canonical_model (X : Over (Spec (.of ℂ))) (HX : Threefold X)
    [HasDerivedPushforwards.{0}]
    (P : ProperReference X.hom) : CanonicalModel P

theorem_wanted stable_pair_trace_rank_one
    (X P : Over (Spec (.of ℂ))) (HX : Threefold X)
    (F : Family X P) (A : PairResolution F.toRawPair)
    (he : EndSquaredZero A.toFiniteComplex) (T : TracePacket A.toFiniteComplex he) :
    T.scalar ≫ T.trace = 𝟙 _

/-- A geometric source-comparison packet; it carries no POT conclusion. -/
def_wanted normalized_stable_pair_map
    (X P : Over (Spec (.of ℂ))) (HX : Threefold X) (HP : ProjectiveParameter P) (F : Family X P)
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}] :
    MapConstruction X P F

theorem_wanted full_class_projects_to_truncated
    (Y : Over (Spec (.of ℂ))) (K : Cochains Y.left)
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (D : UniversalKernelData Y K) (C : CotangentNormalization Y.hom)
    (Q : CotangentTruncation D.embedding D.square C) (L : FullKernelLift D C Q) :
    fullClass D C Q L ≫ (derivedTensorUncurried Y.left).map
      (𝟙 (DerivedCategory.Q.obj K),DerivedCategory.Q.map (Q.projection⟦(1 : ℤ)⟧')) =
      truncatedClass D

/-- The proof obligation is on the displayed actual composite, not an assumed POT. -/
theorem_wanted stable_pair_obstruction_theory
    (X P : Over (Spec (.of ℂ))) (HX : Threefold X) (F : Family X P)
    (HF : RepresentsImage F)
    [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]
    (M : MapConstruction X P F) :
    ∃ (E : Cochains P.left) (e : DerivedCategory.Q.obj E ≅ M.source),
      LocallyPerfectAmplitude E ∧
        IsIso ((DerivedCategory.homologyFunctor P.left.Modules 0).map (e.hom ≫ M.map)) ∧
          Epi ((DerivedCategory.homologyFunctor P.left.Modules (-1)).map (e.hom ≫ M.map))

end WantedExt.AlgebraicGeometry.StablePairSources
