# Formalized Publications

This folder contains mathematics research publications by Meta, each accompanied by a complete Lean formalization.

Instead of treating Lean like an oracle to be trusted, this project intends to present formalizations intuitively, alongside the natural mathematical language of the paper. For this purpose, each publication comes with an interactive HTML copy (to see this, please download the file and open it in your browser).

- `Papers/` — each folder includes a research paper, along with its formalization and interactive HTML copy.
  Each paper's folder contains its own `Readme.md` file summarizing the results presented. For readers experienced with Lean, each paper also includes a Comparator folder.
- `Notes/` — mini papers: shorter publications presenting smaller results or counterexamples. Each note has a dedicated folder with the same structure as papers.

## Why can we trust Lean?

### 1. If I am new to Lean and computer formalization

If you are new to Lean, we recommend starting with Christoph Spiegel's
[Verification was never just about certification](https://christophspiegel.berlin/appendix/when-to-trust-lean)
as an approachable introduction to what "verified in Lean" does—and does
not—mean. For Lean's own account of the successive levels of validation,
from an ordinary build to stronger rechecking, see
[Validating a Lean Proof](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/).

Lean lets one write definitions, theorem statements, and proofs in a form
whose every deduction can be checked by its kernel. A successful check
proves the statements **as written in Lean**. It cannot decide whether
those statements faithfully capture the mathematics in the paper; judging
that translation remains a human task.

For each paper and note here, the formalized translation has been audited,
and an interactive HTML version of each publication allows readers to
compare the paper and Lean statements side by side. That audit is a check
that the Lean statements express the mathematics of the publication, as
Spiegel emphasizes they must. What cannot be checked away is trust in
Lean's kernel, in the toolchain that produced the checker, and in the
hardware it runs on.


### 2. If I already have some experience with Lean

All papers in this folder are checked with the Lean and Mathlib versions
pinned once at the top level of this repository (currently Lean and
Mathlib `v4.35.0`), in [lean-toolchain](../lean-toolchain),
[lakefile.toml](../lakefile.toml), and
[lake-manifest.json](../lake-manifest.json); to avoid version conflicts,
do not run `lake update` first.

For the full check of a paper, run the comparator as instructed in
[Validating a Lean Proof](https://lean-lang.org/doc/reference/4.35.0/ValidatingProofs/#validating-comparator),
using that paper's comparator challenge and configuration file appearing in its folder. The challenge states the paper's definitions independently of
the solution, and the configuration enumerates them under
`definition_names`, so the comparator checks the definitions as well as
the theorems.
