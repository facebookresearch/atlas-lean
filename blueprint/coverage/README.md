---
kind: coverage
status: in-progress
---

# ATLAS coverage

Each documented public declaration of the ATLAS v2 libraries, instances aside, gets one
roadmap article, which `scripts/sync_wiki.py declarations` writes from its docstring; a
declaration the Lean index does not select waits for an editor. The counts below are of
documented non-instance declarations, so they include any whose article that sync has
yet to write. The standalone `Atlas/` developments are not decomposed yet,
and the archived v1 release is not part of the wiki. Progress percentages and target
counts cover only the decomposed rows below; they are not repository-wide coverage.

| Area | Coverage | Evidence |
| --- | --- | --- |
| v2 / MathlibExt | DECOMPOSED | [28609 documented public non-instance declarations](../roadmap/README.md) across 28 subjects; 363 instances and 5972 undocumented public non-instance declarations are not articles. |
| v2 / CSLibExt | DECOMPOSED | [18592 documented public non-instance declarations](../roadmap/README.md) across 10 subjects; 338 instances and 4645 undocumented public non-instance declarations are not articles. |
| v2 / PhyslibExt | DECOMPOSED | [6933 documented public non-instance declarations](../roadmap/README.md) across 7 subjects; 114 instances and 5254 undocumented public non-instance declarations are not articles. |
| v2 / WantedExt | DECOMPOSED | [28584 documented public non-instance declarations](../roadmap/README.md) across 27 subjects; 165 instances and 113 undocumented public non-instance declarations are not articles. |
| v2 tests (MathlibExtTest, CSLibExtTest, PhyslibExtTest) | OUT | Tests and diagnostics rather than mathematical results. |
| Atlas/StatisticalMechanics | MAPPED | Standalone Lean files; no roadmap articles yet. |
| Atlas/CDISProbability | OUT | Standalone Lake project with its own course roadmap in Atlas/CDISProbability/roadmap. |

## Library navigation

These code-library entry points link to the same canonical articles as the
subject-organized roadmap. They do not create another graph, change a result's
credit, or give a library's progress totals. A result stays in its mathematical
subject even when its source module belongs to a different code library.

### Domains

Application-specific models. **Implemented examples** below name their current
source modules; planned destinations are listed separately when added.

- [The copy ratio is affine in the copy number](../roadmap/Biology/cancer-genomics/tumour-purity-ploidy-and-copy-ratio-algebra/copy-ratio-eq-slope-mul-add-intercept.md),
  in `Domains/Biology/CancerGenomics/Absolute.lean`.

**Planned application models:**

- [Plug-flow reactors](../roadmap/Chemistry/chemical-kinetics/plug-flow-reactor/README.md)
- [Residence-time distributions](../roadmap/Chemistry/chemical-kinetics/residence-time-distributions/README.md)
- [Chemostat dynamics](../roadmap/Biology/population-dynamics/chemostat/README.md)

**Related mathematical topics**, whose links do not assign library membership:

- [Queueing theory](../roadmap/Probability/queueing-theory/README.md)
- [Birth–death balance weights](../roadmap/Probability/markov-chains/birth-death-processes/README.md)
- [Population genetics](../roadmap/Biology/population-genetics/README.md), including selection, inbreeding, effective size and diffusion models.
- [Systems biology](../roadmap/Biology/systems-biology/README.md)
- [Phylogenetics](../roadmap/Biology/phylogenetics/README.md)
- [Neuroscience and biological oscillators](../roadmap/Biology/mathematical-neuroscience/README.md)

### CSLibExt

Computer-science developments, including algorithms applied to other domains.
**Implemented examples:**

- [Gotoh with equal gap scores is Needleman–Wunsch](../roadmap/Biology/bioinformatics/sequence-alignment/gotoh-affine-gap-alignment/gotoh-score-eq-nw-score.md),
  in `CSLibExt/Algorithms/Lean/DynamicProgramming/AffineAlignment.lean`.
  Its mathematical home is bioinformatics, not a second copy under computer science.

**Related mathematical topics**, whose links do not assign library membership:

- [Intuitionistic propositional logic](../roadmap/Logic/propositional-logic/kripke-semantics-for-intuitionistic-propositional-logic.md)
- [Proof theory](../roadmap/Logic/proof-theory/README.md)
- [Type-theoretic foundations](../roadmap/Logic/type-theoretic-foundations/README.md)
- [Propositional dynamic logic](../roadmap/Logic/modal-logic/propositional-dynamic-logic/README.md)
- [Databases](../roadmap/ComputerScience/databases/README.md)
- [Machine learning](../roadmap/ComputerScience/machine-learning/README.md)
- [Heuristic search and planning](../roadmap/ComputerScience/heuristic-search-and-planning/README.md)
- [Quantum algorithms](../roadmap/ComputerScience/quantum-algorithms/README.md)

### PhyslibExt

Physics developments. **Implemented examples:**

- [Uniqueness of pipe-network flows and heads with one anchored head](../roadmap/Physics/fluid-mechanics/pipe-flow-networks/pipe-flow-equations-unique-of-anchor.md),
  in `PhyslibExt/FluidDynamics/Hydraulics/PipeNetworkHeads.lean`.

**Related mathematical topics**, whose links do not assign library membership:

- [Linear-system stability](../roadmap/Analysis/ordinary-differential-equations/stability-of-linear-systems/README.md)
- [Controllability](../roadmap/Analysis/control-theory/controllability-of-linear-systems/README.md)
- [Observability](../roadmap/Analysis/control-theory/observability-of-linear-systems/README.md)
- [Realization theory](../roadmap/Analysis/control-theory/realization-theory/README.md)
- [Sampled-data systems](../roadmap/Analysis/control-theory/sampled-data-systems/README.md)
- [Quantum states, distances and entropy](../roadmap/QuantumInformation/quantum-states-distances-and-entropy/README.md)
- [Quantum Shannon theory](../roadmap/QuantumInformation/quantum-shannon-theory/README.md)

Shared mathematical prerequisites retain their own canonical pages. Appearing
as a prerequisite does not make them members of the dependent result's library.
