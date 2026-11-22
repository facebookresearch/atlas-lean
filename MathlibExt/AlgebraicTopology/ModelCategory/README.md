# Model-category foundations

These modules extend Mathlib's model-category API with explicit generation,
homotopy and derived constructions, diagram models, and monoidal transfer.
They work with the original categories, functors and morphism classes. Most
declarations use the `HomotopicalAlgebra` namespace.

Import the entry point for the construction you need:

| Construction | Entry points |
| --- | --- |
| Generating families and recognition | [CofibrantlyGenerated](CofibrantlyGenerated.lean), [GeneratedRecognition](GeneratedRecognition.lean), [Combinatorial](Combinatorial.lean) |
| Quillen adjunctions and equivalences | [QuillenAdjunction](QuillenAdjunction.lean), [QuillenEquivalence](QuillenEquivalence.lean), [QuillenDerivedAdjunction](QuillenDerivedAdjunction.lean), [QuillenEquivalenceTotalDerived](QuillenEquivalenceTotalDerived.lean) |
| Homotopy and total derived functors | [HomotopyCategory](HomotopyCategory.lean), [GeneratedFunctorialReplacements](GeneratedFunctorialReplacements.lean), [DerivedFunctorCoherence](DerivedFunctorCoherence.lean), [DerivedAdjunctionCoherence](DerivedAdjunctionCoherence.lean) |
| Framings and homotopy function complexes | [FunctorialFramings](FunctorialFramings.lean), [HomotopyFunctionComplex](HomotopyFunctionComplex.lean), [GeneratedHomotopyFunctionComplex](GeneratedHomotopyFunctionComplex.lean), [DerivedMapping](DerivedMapping/FunctionComplex.lean) |
| Diagram models and Kan extensions | [FunctorProjective](FunctorProjective.lean), [Injective models](FunctorInjective/SourceConstruction.lean), [Projective Kan extensions](FunctorProjective/KanExtensions.lean), [Reedy](Reedy.lean) |
| Derived diagram limits and colimits | [DerivedDiagramConstructions](DerivedDiagramConstructions.lean), [Projective cofinality](OriginalProjectiveRightAdjointCofinality.lean), [Sequential homotopy colimits](NatProjectiveTailHomotopyColimit.lean) |
| Properness and under/over constructions | [Proper](Proper.lean), [Projective properness](FunctorProjective/Proper.lean), [Under](Under.lean), [UnderOverProperQuillen](UnderOverProperQuillen.lean) |
| Monoidal models and derived tensor | [Monoidal](Monoidal.lean), [MonoidalQuillen](MonoidalQuillen.lean), [DerivedTensorCoherence](DerivedTensorCoherence.lean), [DerivedTensorClosedStructure](DerivedTensorClosedStructure.lean) |
| Transfer to monoids and modules | [RightTransfer](RightTransfer.lean), [MonoidTransfer](MonoidTransfer.lean), [ModuleTransfer](ModuleTransfer.lean), [Module monoidal models](ModuleTransfer/Monoidal.lean) |
| Localization | [Smith recognition](LeftBousfieldLocalization/Smith.lean), [Left Bousfield localization](LeftBousfieldLocalization/Basic.lean), [Localization products](LocalizationFiniteProducts.lean) |

For example, importing generation data does not require the derived or
monoidal APIs:

```lean
import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated
```

`CofibrantGenerationData` records two chosen generating families at a regular
cardinal, together with their small-object and right-class identifications.
Recognition constructs a model category from compatible weak equivalences
and weak factorization systems. Smith recognition additionally requires the
stated closure and solution-set hypotheses.

Derived constructions retain their chosen cofibrant and fibrant replacement
functors. Quillen adjunctions induce adjunctions on homotopy categories;
coherence and comparison modules describe their natural transformations,
units and counits. The hypotheses specifying replacements and their
factorizations remain explicit. Generation and factor-factory constructors
couple replacements to the actual factor records; arbitrary replacement
data specifies those fields separately.

`HomotopyFunctionComplex` packages a chosen simplicial enrichment, both
factorizations, weak-equivalence invariance, comparison with alternative
choices, and detection properties. These are hypotheses of that package.
`GeneratedHomotopyFunctionComplex` constructs comparison maps for supplied
cofibrant-generation data at the two actual source cardinals.

Projective and injective diagram constructions retain the index category
and coefficient model. Their generating-family, smallness or combinatorial
hypotheses are stated by the corresponding factories. Reedy constructions
require the latching and matching shapes and their needed limits and
colimits. Properness conclusions require the relevant coefficient
properness assumptions.

Derived diagram constructions start with `lim (R F)` and `colim (Q F)` for
supplied whole-diagram replacements and the required limits or colimits.
Their Quillen and homotopy-invariance results use the stated objectwise
morphism-class identifications. The projective and injective factories
provide these identifications under their source and presentability
hypotheses. Reedy mapping comparisons additionally retain their stated
cofibrant- or fibrant-constant hypotheses.

Monoidal results start with a compatible closed symmetric monoidal model
category. Transfer requires the stated smallness and acyclicity conditions
for the free generating maps. The module APIs use the balanced tensor and
its tensor–Hom adjunction; the derived APIs retain the same replacement
choices. Basic left Bousfield localization assemblies use supplied
localization data. Smith recognition instead constructs model data from
the stated two-out-of-three, retract, generating-right-class, closure and
solution-set conditions. A comparison with an adjoint telescope alone does
not establish a localization.

Concrete spectra and the Joyal model are separate applications of these
foundations. Choose their own entry points when working with those models.
