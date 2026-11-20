# Sources

The project uses one immutable CPython snapshot, CPython's accompanying design
notes at that same snapshot, the Munro-Wild PowerSort paper, and a
project-authored theorem contract.

- [Pinned upstream revisions and checksums](upstream-pins.md)
- [Verified CPython C excerpts](listobject-excerpts.md)
- [CPython listsort design notes](listsort.md)
- [Munro-Wild source map](munro-wild-powersort-notes.md)
- [Project-authored top-level theorem contract](toplevel-theorems.md)
- [Pinned Mathlib prior-art map](mathlib-prior-art.md)

The pinned C excerpt is authoritative for adaptive minrun's implementation
expression and for the unsuffixed literal giving that expression type `int`.
The project-authored selected-platform contract fixes `int` at 32 bits.
CPython's accompanying design note is the source for the intended
arbitrary-precision quotient/remainder generator, but that ideal recurrence
agrees with the modeled 32-bit mask only under the roadmap's explicit
low-exponent premise. The 2018 Munro-Wild paper is
authoritative for PowerSort's node power, Cartesian-tree policy,
path-power monotonicity, and optional merge-cost bound; it predates CPython's
adaptive-minrun change.

<!-- AUTHORING NOTES — these comments are not published.

     One page per reference. Each page maps stable source locators to the
     roadmap articles that depend on them, so every statement can be traced
     back to the passage it came from.
-->
