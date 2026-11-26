# Longest walk duration

The duration `ℓ(u, v)` of a longest walk from `u` to `v` in the
activity-on-arc network `tail head : E → V` with arc durations `d : E → R`: the greatest element
of the set of durations `(l.map d).sum` of the walks `l` from `u` to `v`. When that set has no
greatest element, as when no walk runs from `u` to `v` or a cycle of positive duration lies on
such a walk, the value is `0`, a junk value.
