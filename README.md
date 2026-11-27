<p align="center">
  <img src="assets/logo.svg" alt="ATLAS logo" width="720" />
</p>

<h1 align="center">ATLAS</h1>

<p align="center">
  <a href="https://github.com/facebookresearch/atlas-lean/actions/workflows/ci.yml"><img src="https://github.com/facebookresearch/atlas-lean/actions/workflows/ci.yml/badge.svg?branch=main" alt="CI status" /></a>
  <a href="https://github.com/leanprover/lean4/releases/tag/v4.36.0"><img src="https://img.shields.io/badge/Lean-v4.36.0-blue" alt="Lean v4.36.0" /></a>
</p>

> [!NOTE]
> **ATLAS V2 is live.** Explore the interactive graph at
> [facebookresearch.github.io/atlas-lean](https://facebookresearch.github.io/atlas-lean/).
> The original release is preserved in [`v1/`](v1/).

## About ATLAS

ATLAS provides reusable formal building blocks for human- and machine-assisted
theorem proving across mathematics, theoretical computer science, physics, and applied domains.

The project was generated with
[AutoformBot](https://github.com/facebookresearch/autoform-bot), an
autoformalization pipeline for developing Lean libraries at scale.

## Formalized libraries

The root Lake package is organized into the following libraries:

| Directory | Purpose |
| --- | --- |
| [`MathlibExt/`](MathlibExt/README.md) | Reusable, fully proved extensions to Mathlib |
| [`MathlibExtTest/`](MathlibExtTest/README.md) | Tests, benchmarks, and diagnostics for `MathlibExt` |
| [`CSLibExt/`](CSLibExt/README.md) | Reusable, fully proved computer-science developments built on `MathlibExt` |
| [`CSLibExtTest/`](CSLibExtTest/README.md) | Tests and diagnostics for `CSLibExt` |
| [`PhyslibExt/`](PhyslibExt/README.md) | Reusable, fully proved physics developments built on Physlib |
| [`PhyslibExtTest/`](PhyslibExtTest/README.md) | Tests and diagnostics for `PhyslibExt` |
| [`Domains/`](Domains/README.md) | Proved domain models: [biology](Domains/Biology/), [economics and finance](Domains/Economics/), [operations research](Domains/OperationsResearch/), [materials science](Domains/MaterialsScience/), [chemistry](Domains/Chemistry/), [transport](Domains/Transport/), and [urban planning](Domains/Urban/) |
| [`DomainsTest/`](DomainsTest/README.md) | Tests and diagnostics for domain models |
| [`WantedExt/`](WantedExt/README.md) | Established results whose Lean implementation or proof is deferred |

Repository checks live in [`scripts/`](scripts/README.md). Run the complete
root validation with:

```bash
scripts/check.sh
```

The [CPython listsort model](CSLibExt/Algorithms/Sorting/CPythonListsort/README.md)
is integrated into `CSLibExt`, with kernel-checked proof layers and asserting
regression clients in `CSLibExtTest`. It uses the root toolchain rather than an
independent package; its original source and verification provenance are retained.

The [Formal Conjectures migration record](docs/provenance/formal-conjectures-migration.md)
links the seven mathematical developments moved into `MathlibExt`, the
existing A022030 proof reused there, and the absolutely-maximally-entangled-state
development in `PhyslibExt`, with their tests and source-statement comparisons.

Remaining `Atlas/` development material and the archived `v1/` release are not
part of this root build. `v1/` retains its original build configuration.
[`Atlas/StatisticalMechanics/`](Atlas/StatisticalMechanics/MIGRATED.md) and
[`Atlas/CDISProbability/`](Atlas/CDISProbability/README.md) retain their source
and provenance paths while their destinations or archival dispositions are
tracked in [#5408](https://github.com/facebookresearch/atlas-lean/issues/5408)
and the [remaining-Atlas record](docs/provenance/remaining-atlas.md).
That issue stays open until every remaining directory is accounted for and
`Atlas/` is retired as a development directory.

## Dependency explorer

The [blueprint](blueprint/README.md) presents the v2 libraries as a
mathematical reading tree and interactive dependency graph, with statements,
Lean-source links, and prerequisites derived from compiled Lean.

See [building and maintaining the explorer](docs/BLUEPRINT.md) for the local
build, source ownership, and opt-in GitHub Pages deployment.

## Versions

| Version | Status | Location | License |
| --- | --- | --- | --- |
| **v2** | Live | Repository root | [Apache 2.0](LICENSE) |
| **v1** | Archived and available | [`v1/`](v1/README.md) | [Original v1 license](v1/LICENSE) |

The complete first release—including its Lean sources, evaluation reports,
build configuration, documentation, and companion paper—is available under
[`v1/`](v1/README.md).

```bash
cd v1
lake build
```

Useful links:

- [ATLAS v1 documentation and statistics](v1/README.md)
- [Interactive visualizer](https://rammalahmad.github.io/atlas/)
- [Companion paper: *Formalizing Mathematics at Scale*](https://arxiv.org/abs/2605.29955)
- [AutoformBot](https://github.com/facebookresearch/autoform-bot)

## Licensing

New work outside `v1/` is licensed under the
[Apache License 2.0](LICENSE). Files inside `v1/` remain subject to the
[original v1 license](v1/LICENSE) and are not relicensed by the root license.
