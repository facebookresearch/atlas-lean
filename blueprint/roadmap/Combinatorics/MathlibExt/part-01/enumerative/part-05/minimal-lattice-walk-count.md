---
article_id: af_b6090a01b3539dd838cd435d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.minimal_lattice_walk_count
---

# Minimal Lattice Walk Count

Minimal lattice-walk counts: the number of minimal `S`-walks from the origin
to `(a, b)` with steps `(1,0)`, `(0,1)`, `(1,1)` (formalized as step
sequences of length `max a b` with coordinate sums `a` and `b`) equals
`choose (max a b) (min a b)`.

Minimal walks have length `max a b` since each step raises the max
coordinate by at most 1; for `a ≥ b` every step raises `x`, so exactly `b`
of the `a` steps are diagonal. The step-type coordinates are read off the
`![1,0,1]` / `![0,1,1]` vectors. Verified computationally for all
`a, b ∈ 0..4`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MinimalLatticeWalkCount](../../../../../../sources/v2/MathlibExt.md)
- Jackson Evoniuk, Steven Klee, and Van Magnan, "Enumerating Minimal Length Lattice Paths," Journal of Integer Sequences 21 (2018), Article 18.3.6, Theorem (section Minimal walks for S = {(1,0),(0,1),(1,1)}, label sec2), lines 273–275, https://cs.uwaterloo.ca/journals/JIS/VOL21/Klee/klee2.tex
