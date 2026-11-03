# Formalized Publications

This folder contains mathematics research publications by Meta, each accompanied by a complete Lean formalization.

Instead of treating Lean like an oracle to be trusted, this project intends to present formalizations intuitively, alongside the natural mathematical language of the paper. For this purpose, each publication comes with an interactive HTML copy (to see this, please download the file and open it in your browser).

- `Papers/` — each folder includes a research paper, along with its formalization and interactive HTML copy.
  Each paper's folder contains its own `Readme.md` file summarizing the results presented. For readers experienced with Lean, each paper also includes a Comparator folder.
- `Notes/` — mini papers: shorter publications presenting smaller results or counterexamples. Each note has a dedicated folder with the same structure as papers.

## Index

Publications are first organized by subject, and then chronologically by the publication date of the formalization.

<details open>
<summary><strong>Papers</strong></summary>

- <details open>
  <summary>Algebra</summary>

  - [On Solvable Evolution Algebras and a Conjecture by García-Martínez and Pérez-Rodríguez](Papers/EvolutionAlgebras/) (Oct 2026)

  </details>

- <details>
  <summary>Analysis</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Applied &amp; Mathematical Physics</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Combinatorics</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Differential Equations &amp; Dynamics</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Geometry &amp; Topology</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Logic &amp; Computer Science</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Number Theory</summary>

  _No papers yet._

  </details>

- <details>
  <summary>Probability &amp; Statistics</summary>

  _No papers yet._

  </details>

</details>

<br>

<details>
<summary><strong>Notes</strong></summary>

- <details>
  <summary>Algebra</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Analysis</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Applied &amp; Mathematical Physics</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Combinatorics</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Differential Equations &amp; Dynamics</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Geometry &amp; Topology</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Logic &amp; Computer Science</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Number Theory</summary>

  _No notes yet._

  </details>

- <details>
  <summary>Probability &amp; Statistics</summary>

  _No notes yet._

  </details>

</details>


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


## How do I cite these works?

The folder of each publication includes a `citation.bib` file with the citation information, as well as detailed authorship information in its own `Readme.md`.

## Adding a publication

Add one folder under `Papers/` or `Notes/`. Use a unique project name in
UpperCamelCase, such as `ExamplePaper`, with letters and digits and no spaces
or underscores. The folder has the following structure:

```text
Papers/ExamplePaper/              # Use Notes/ExamplePaper/ for a note
  Readme.md
  Papers/
    paper.pdf
    paper_interactive.html
    citation.bib
    Latex/                        # LaTeX sources, when available
  Formalization/
    ExamplePaper.lean
    ExamplePaper/
      Section1/
        A_Definitions.lean
        B_MainResult.lean
  Comparator/
    paper_comparator.lean
    paper_comparator.json
```

The PDF, HTML, and comparator files may have different names. Keep the directory
names, `Readme.md`, `citation.bib`, and the root module `ExamplePaper.lean` as
shown, substituting your project name for `ExamplePaper`.

- **Paper and front page.** Include the PDF, interactive HTML, citation,
  authorship and version information, and a short description with links to
  the main results. Include the LaTeX sources when available.
- **Formalization.** Use the Lean and dependency versions pinned at the
  repository root. The root module imports the paper's main results. Keep
  supporting modules under the project's module prefix, such as
  `ExamplePaper.Section1.A_Definitions`, and use the project's namespace for
  its declarations. This prevents collisions with other publications. Lean
  file and directory names must use letters, digits, underscores, or apostrophes,
  with a letter or underscore first.
- **Comparator.** Include the independent challenge and its JSON configuration.
  The challenge may contain `sorry` for the statements being checked; keep it
  in `Comparator/` and do not import it from the formalization. Follow the
  comparator validation instructions above for the independent check.

From the repository root, run the complete check with Python 3.11+ and the
pinned Lean toolchain:

```bash
scripts/check.sh
```

This automatically discovers all paper and note folders, builds every `.lean`
file under each `Formalization/` directory, and checks proof integrity and
library dependencies. It reports missing required files, symlinked sources,
and conflicting module prefixes. Comparator challenges are excluded from this
normal build.

For a focused build of your paper's root module and its imports:

```bash
python3 scripts/publications.py build ExamplePaper
```

Adding a publication requires no changes to the root Lake configuration,
shared check scripts, or CI workflow. Plain `lake build` builds the default
extension targets; `scripts/check.sh` is the complete repository check.
