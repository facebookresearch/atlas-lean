<p align="center">
  <img src="assets/logo.svg" alt="ATLAS logo" width="720" />
</p>

<h1 align="center">ATLAS</h1>

<p align="center">
  <a href="https://github.com/facebookresearch/atlas-lean/actions/workflows/ci.yml"><img src="https://github.com/facebookresearch/atlas-lean/actions/workflows/ci.yml/badge.svg?branch=main" alt="CI status" /></a>
  <a href="https://github.com/leanprover/lean4/releases/tag/v4.35.0"><img src="https://img.shields.io/badge/Lean-v4.35.0-blue" alt="Lean v4.35.0" /></a>
</p>

<p align="center">
  <strong>Autoformalized Textbook Library At Scale</strong><br />
  A large-scale Lean 4 library of textbook mathematics formalized with LLMs.
</p>

> [!NOTE]
> **ATLAS v2 is coming.** The original release is preserved in [`v1/`](v1/),
> while the repository root is being prepared for the next generation of the
> project.

## Versions

| Version | Status | Location | License |
| --- | --- | --- | --- |
| **v2** | In development | Repository root | [Apache 2.0](LICENSE) |
| **v1** | Archived and available | [`v1/`](v1/README.md) | [Original v1 license](v1/LICENSE) |

## Formalized mathematics libraries

The root Lake package is limited to five libraries:

| Directory | Purpose |
| --- | --- |
| [`MathlibExt/`](MathlibExt/README.md) | Reusable, fully proved extensions to Mathlib |
| [`MathlibExtTest/`](MathlibExtTest/README.md) | Tests, benchmarks, and diagnostics for `MathlibExt` |
| [`CSLibExt/`](CSLibExt/README.md) | Reusable, fully proved computer-science developments built on `MathlibExt` |
| [`CSLibExtTest/`](CSLibExtTest/README.md) | Tests and diagnostics for `CSLibExt` |
| [`WantedExt/`](WantedExt/README.md) | Established results whose Lean implementation or proof is deferred |

Repository checks live in [`scripts/`](scripts/README.md). Run the complete
root validation with:

```bash
scripts/check.sh
```

The existing `Atlas/` developments and archived `v1/` release are not part of
this root build. They retain their own build configuration.

## Searching ATLAS from an AutoformBot project

When CI passes on a commit of `main`, a workflow tags
`autoform-index/<first 12 characters of the commit>`: a commit on top of it
that adds `autoform-library-index.jsonl`, the index of `MathlibExt`,
`CSLibExt`, and `WantedExt` that AutoformBot searches. Commits on `main` carry
no index, so require ATLAS at one of these tags:

```toml
[[require]]
name = "atlas"
git = "https://github.com/facebookresearch/atlas-lean.git"
rev = "autoform-index/64c2773ffad3"
```

`autoform library list .` then reports ATLAS as usable, and
`autoform search <blueprint> "<words>" --lean-root . --library atlas` searches
its declarations.

## About ATLAS

ATLAS translates mathematical statements and proofs from undergraduate and
graduate textbooks into Lean. Its goal is to provide reusable formal building
blocks for human- and machine-assisted theorem proving across analysis,
algebra, geometry, topology, probability, statistics, and theoretical
computer science.

The project was generated with
[AutoformBot](https://github.com/facebookresearch/autoform-bot), an
autoformalization pipeline for developing Lean libraries at scale.

## Explore v1

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
