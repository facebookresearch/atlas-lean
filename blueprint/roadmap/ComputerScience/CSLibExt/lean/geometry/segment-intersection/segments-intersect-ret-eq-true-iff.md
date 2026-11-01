---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Geometry.segmentsIntersect_ret_eq_true_iff
---

# Segments Intersect ret eq true iff

CLRS Section 33.1: `SEGMENTS-INTERSECT(p₁, p₂, p₃, p₄)` returns `true` exactly when the
closed segments `p₁p₂` and `p₃p₄` have a common point.

## Depends on

- [Segments Intersect](segments-intersect.md)

## Proof depends on

- [Straddles](straddles.md)
- [Direction](direction.md)
- [Direction eq zero of mem](direction-eq-zero-of-mem.md)
- [Inter nonempty of straddles](inter-nonempty-of-straddles.md)
- [Mem segment of direction eq zero](mem-segment-of-direction-eq-zero.md)
- [On Segment](on-segment.md)
- [On Segment of mem](on-segment-of-mem.md)
- [Segments Intersect ret](segments-intersect-ret.md)
- [Straddles or endpoint mem](straddles-or-endpoint-mem.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Geometry.SegmentIntersection](../../../../../../sources/v2/CSLibExt.md)
