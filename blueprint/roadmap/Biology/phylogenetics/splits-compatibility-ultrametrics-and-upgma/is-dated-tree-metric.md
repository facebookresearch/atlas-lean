# Metric of a dated rooted tree

`d` is the metric of a **dated rooted tree**, encoded by its clusters: a hierarchy `H` on
the taxa with dates `h` (`0` at the leaves, strictly increasing from a cluster to any cluster
strictly containing it) such that `d x y` is the date of the smallest cluster containing `x`
and `y` (their most recent common ancestor). With edge lengths `(h D - h C) / 2` from each
cluster `C` to its parent `D`, `d x y` is the path length from `x` to `y` and all leaves are
equidistant from the root (Semple & Steel 2003, Section 7.2).
