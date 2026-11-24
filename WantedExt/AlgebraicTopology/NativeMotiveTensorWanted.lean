/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeMotiveTensorModels

/-!
# Native tensor, complete evaluation and spectral-linearity construction requests

Native coefficients, all component maps, full ordinary source cylinders,
unit triangles and complete evaluation diagrams are fixed in MathlibExt.
These construction/coherence outputs contain no K or RHom endpoint hypothesis.
Sources: HSS Sections 2--3; HTT Section 5.5; BGT Sections 6.2/8.3/9.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeMotiveTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.SpectraSource
open QuasicategoricalModels NativeKParametrizedSource NativeMotivePresheafSources
open NativeMotiveGenerators NativeMotiveLocalizationModels NativeSpectralPresheafModels
open NativeDerivedSpectrumModels StableSpectraInfinitySource
open scoped Simplicial

def_wanted native_nerve_natural_transformation {C D : Type 1} [Category.{0} C] [Category.{0} D]
    (F G : C ⥤ D) (a : F ⟶ G) : NerveNaturalTransformation F G a

def_wanted native_spectrum_tensor_source (S : SpectrumInfinitySource) (R : SpectrumReplacements S) :
    SpectrumTensorSource S R

variable {A : StableCategoryEnrichment} {k : Cardinal.{0}} {T : SpectralCompactSource A k}
    {S : SpectrumInfinitySource} (V : MotivePresheafSetup T S) (R : SpectrumReplacements S)

def_wanted native_raw_scalar_presheaf_tensor : RawScalarTensor V R

variable {G : letI := T.enrichment; Set (RawMotiveGenerator (C := T.index))}
    (M : letI := T.enrichment; letI := V.colimits; MotiveLocalization V.presheaves V.ends V.replacements G)

def_wanted native_motive_tensor_source : MotiveTensorSource V R M

def_wanted native_motive_functor_models
    (f : letI := T.enrichment; letI := V.colimits; M.category.toSSet ⟶ S.category.toSSet)
    (colimits : letI := T.enrichment; letI := V.colimits; PreservesSmallColimits f) :
    {F : MotiveFunctorModels V M // F.functor = f}

def_wanted native_motive_spectral_linearity (F : MotiveFunctorModels V M)
    (D : SpectrumTensorSource S R) (P : MotiveTensorSource V R M) : MotiveFunctorLinearity F D P

def_wanted native_raw_motive_evaluation (P : RawScalarTensor V R)
    (E F : letI := T.enrichment; RawPresheaf T.index) : RawMotiveEvaluation (M := M) P E F

def_wanted native_motive_evaluation_diagram (P : MotiveTensorSource V R M)
    (E F : letI := T.enrichment; RawPresheaf T.index) : MotiveEvaluationSource P E F

def_wanted native_functor_evaluation_diagram (F : MotiveFunctorModels V M)
    (D : SpectrumTensorSource S R) (P : MotiveTensorSource V R M) (L : MotiveFunctorLinearity F D P)
    (E E' : letI := T.enrichment; RawPresheaf T.index) (Q : MotiveEvaluationSource P E E') :
    FunctorEvaluationSource F D P L E E' Q

end MathlibExt.AlgebraicTopology.NativeMotiveTensorModels
