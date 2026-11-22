# Model categories and homotopy constructions

These modules extend Mathlib's model-category API with constructions from
generators, cellular and accessible-category methods, diagram models,
homotopy mapping spaces, and transfer to algebraic categories. Derived
constructions include adjunctions, equivalences, natural comparisons and
coherence laws. The model-category interfaces use the
`HomotopicalAlgebra` namespace.

Import the entry point for the construction you need:

| Construction | Entry points |
| --- | --- |
| Generators and recognition | [Generation from source smallness](CofibrantlyGenerated/Existence.lean), [Two-family recognition](GeneratedRecognition.lean), [Smith recognition](LeftBousfieldLocalization/Smith.lean) |
| Cellular saturation and good trees | [Cellular retracts](../../CategoryTheory/SmallObject/CellularRetractsClosure.lean), [Cofibration good trees](../../CategoryTheory/SmallObject/GoodCellTree/Goodification/OriginalCofibrationGoodTree.lean) |
| Accessibility and presheaf small-object constructions | [Factorization accessibility](../../CategoryTheory/SmallObject/FactorizationAccessibility.lean), [Attachment pullbacks](../../CategoryTheory/SmallObject/PresheafAttachmentPullbacks.lean), [Iteration cardinality](../../CategoryTheory/SmallObject/PresheafIterationCardinality.lean) |
| Quillen and derived equivalences | [Quillen adjunctions](QuillenAdjunction.lean), [Derived equivalences](QuillenEquivalenceTotalDerived.lean), [Derived adjunction coherence](DerivedAdjunctionCoherence.lean) |
| Framings and generated mapping spaces | [Functorial framings](FunctorialFramings.lean), [Generated homotopy function complexes](GeneratedHomotopyFunctionComplex.lean), [Quillen mapping-space adjunction](QuillenFrameHomComplex.lean) |
| Ordinary diagram models | [Projective](FunctorProjective/SourceConstruction.lean), [Injective](FunctorInjective/SourceConstruction.lean), [Reedy](Reedy.lean), [Reedy evaluation](ReedyEvaluationQuillen.lean) |
| Derived diagram constructions | [Homotopy limits and colimits](DerivedDiagramConstructions.lean), [Derived enriched Kan adjunctions](OriginalEnrichedDerivedKanAdjunction.lean), [Right-adjoint cofinality](OriginalProjectiveRightAdjointCofinality.lean) |
| Enriched diagram models and SM7 | [Enriched projective construction](OriginalEnrichedProjective.lean), [Generator criterion for SM7](OriginalEnrichedDiagramSM7.lean) |
| Properness and homotopy fibers/cofibers | [Proper models](Proper.lean), [Functorial fibers and cofibers](FunctorialHomotopyFiberCofiber.lean), [Fibrant pullback comparison](FibrantPullbackComparison.lean) |
| Monoidal models and derived closed tensor | [Pushout-product generator criterion](PushoutProductGeneratorCriterion.lean), [Derived closed symmetric tensor](DerivedTensorBraidingCoherence.lean) |
| Monoid and module transfer | [Monoids](MonoidTransfer.lean), [Modules and bimodules](ModuleTransfer.lean), [Commutative-module monoidal models](ModuleTransfer/Monoidal.lean) |
| Derived module tensor and scalar change | [Relative tensor–Hom adjunction](ModuleTransfer/DerivedRightLeftTensorAdjunction.lean), [Derived commutative tensor](ModuleTransfer/DerivedCommutativeTensor.lean), [Scalar equivalences](ModuleTransfer/WeakScalarOfTransfers.lean) |
| Operadic and semi-model transfer | [Colored operadic algebras](OperadicTransfer/SourceBranches.lean), [Semi-model construction](SemiModel/Transfer.lean) |
| Left Bousfield localization | [Smith existence](LeftBousfieldLocalization/SmithExistence.lean), [Localization and Quillen descent](LeftBousfieldLocalization/Quillen.lean) |

`CofibrantGenerationData` records I/J generators, their lifting classes and
small-object eligibility at a regular cardinal. Presentable domains or
uniform relative source smallness yield eligibility and common generation
cardinals. Recognition then constructs the model and its functorial
factorizations. Smith recognition constructs the second generating family
from generatorwise solution sets; accessibility of both the weak-arrow
category and its inclusion supplies those sets. Cellular retracts are
proved weakly saturated without a small-object-argument premise. Good-tree
constructions describe cofibrations under the stated compactness and
colimit hypotheses. Accessibility results keep the chosen factorization
length while obtaining an accessibility rank for its functors.

The derived-functor constructions use chosen cofibrant and fibrant
replacements and the stated preservation hypotheses.
Quillen adjunctions induce derived adjunctions, and Quillen equivalences
induce equivalences of homotopy categories. Comparison and coherence
theorems retain the natural transformations, units and counits of these
constructions. Generation data also constructs functorial framings and a
Kan mapping-space bifunctor, invariant under weak equivalences in both
variables. Its components are naturally the localized Hom sets, and its
composition gives enrichment over the homotopy category of simplicial
sets. This construction needs no supplied simplicial enrichment. A
Quillen adjunction gives the corresponding mapping-space adjunction, with
the stated fibrant-target hypothesis and independent generation data on
the two categories.

The ordinary projective and injective diagram constructions produce model
structures, generating families and functorial factors under their index,
smallness and presentability hypotheses. They support Quillen Kan
extensions and comparisons under index equivalences. The Reedy
construction gives a model and functorial factors from the coefficient
factors and required latching/matching limits; evaluation theorems give
the associated Quillen adjunctions. Derived limits, colimits and Kan
extensions have weak-invariance and natural comparison theorems. Reedy
limit and colimit results retain their cofibrant-constant and
fibrant-constant hypotheses, respectively.

Enriched projective existence uses Hom-tensor preservation on generators
and source-Hom preservation of the specified ordinal colimits. The
mapping-end enrichment is constructed from products and equalizers.
Mixed scalar/diagram generator pushout-product tests then prove all three
SM7 corner conditions through the tensor–Hom adjunctions.

Functorial homotopy pushouts, pullbacks, fibers and cofibers use replacement
diagrams and preserve weak maps on all diagram vertices. Comparison with
ordinary limits or colimits uses the stated cofibrancy or fibrancy of
endpoints and a good leg; properness removes the corresponding endpoint
conditions. Fibers use a zero object. Pullback of a weak map between
fibrations over a common base is weak along any base map, by the slice
Quillen adjunction and Brown's lemma.

The pushout-product generator criterion proves the pushout-product laws from
I-by-I and J-by-I tests. A Hovey unit witness allows the derived closed
symmetric tensor on the homotopy category even when the tensor unit is
not cofibrant; associativity, unit, hexagon and tensor–Hom adjunction laws
are proved. Monoid and module transfer construct the target models from
free-generator smallness and acyclicity. The monoid axiom supplies
acyclicity for arbitrary scalars; module transfer also has cofibrant-scalar
variants. Monoid transfer retains target cocompleteness as a hypothesis.
The balanced tensor on commutative modules is a monoidal model when the
ambient unit is cofibrant. Derived relative tensor and scalar-change
theorems retain their stated scalar-cofibrancy or flatness hypotheses.

Colored operadic transfer constructs algebra limits, colimits and model
structures. Its branches use acyclic symmetric h-monoidality together
with either local presentability and transfinite closure of weak
equivalences, or strong admissible generation and free-cell source
smallness. Semi-model transfer constructs both functorial factors while
restricting the trivial-cofibration/fibration factor and lifting axiom to
cofibrant sources. Left Bousfield localization constructs models and
Quillen descent under its local-equivalence, generation, closure and
solution-set hypotheses.
