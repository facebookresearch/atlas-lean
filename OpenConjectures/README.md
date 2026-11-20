# Open conjectures and standalone solution examples

This directory groups conjecture benchmarks and associated solution
developments that are not part of the seven root Lake libraries. It is not an
additional root Lean library and does not change the role of `WantedExt`, which
contains established results with deferred Lean work.

## Formal Conjectures examples

[`FormalConjectures/`](FormalConjectures/) replaces the opaque `Atlas/FC/`
folder name. Its nine imported examples cover Erdős and Green problems, OEIS
sequences, an open quantum problem, and graph conjectures from *Written on the
Wall II*. The original source filenames, declarations, imports, and provenance
headers are preserved.

The folder includes both conjecture statements and solution developments; its
location is not a claim that every statement is still open or that every file
is a completed proof. These sources remain outside the root Lake build, and
imports such as `FormalConjecturesUtil` still require their original supporting
environment. No root-package dependency or build target is added by the move.
