# PhyslibExt

`PhyslibExt` contains reusable, fully proved physics developments that extend
[Physlib](https://github.com/leanprover-community/physlib). It may build on
Mathlib, `MathlibExt`, and `CSLibExt`.

Follow Physlib's conventions:

- organize files by physics, mirroring Physlib's directories
  (`StatisticalMechanics/`, `CondensedMatter/`, ...);
- reuse Physlib definitions instead of restating them, and connect any
  parallel definition to Physlib's by a proved bridge lemma;
- give every definition a docstring, and give every module Physlib's module
  documentation headings (`# Title`, a one-line summary, `## i. Overview`,
  `## ii. Key results`, `## iii. Table of contents`, `## iv. References`, then
  numbered sections `## A. ...`);
- use `lemma`, reserving `theorem` (with a docstring) for results that are well
  known in the physics literature.

Keep imports narrow and put tests and diagnostics in `PhyslibExtTest`. Every
module must be free of `sorry`, `sorryAx`, `admit`, custom axioms, and
`native_decide`, and may use only Lean's standard logical axioms. It may import
`MathlibExt` and `CSLibExt`, but not `WantedExt` or any test library.
