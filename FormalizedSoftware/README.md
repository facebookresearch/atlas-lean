# Formalized software

This directory holds standalone software-formalization case studies, separate
from the reusable APIs in `CSLibExt` and their root-package clients in
`CSLibExtTest`.

## CPython listsort

[`CPythonListsort`](CPythonListsort/README.md) formalizes a Lean model of the
sorting implementation in a pinned CPython snapshot. Its own README records the
public results, source correspondence, limitations, and proof trust boundary.

The example retains its own Lake package, Mathlib pin, and Lean `v4.33.1`
toolchain. It is not included in the root Lean `v4.35.0` package. In particular,
its `Code` module prefix and twelve isolated `native_decide` review witnesses
are not silently added to the root `CSLibExtTest` glob or its trust policy.
Integrating a reusable component into `CSLibExt`, with a corresponding
`CSLibExtTest` client, requires a separate API and toolchain migration.

From the repository root, run its standalone checks with:

```sh
cd FormalizedSoftware/CPythonListsort
python3 verify/verify_trust_boundary.py
```

See [`verify/VERIFY.md`](CPythonListsort/verify/VERIFY.md) for source-excerpt
verification, the Lean build, and compiled axiom audits. The file move itself
does not claim that those builds have been rerun.
