# Successor of a boundary dart

The successor of the dart `e` along the boundary of `K`. Write `r` for `e.dir` rotated
clockwise by a quarter turn. If `e.head + r ∈ K` (a reflex corner of `K`), the successor shares the
head of `e`; if only `e.tail + r ∈ K`, it is the translate of `e` by `r`; otherwise (a convex corner
of `K`) it starts at `e.tail` in direction `r`.
