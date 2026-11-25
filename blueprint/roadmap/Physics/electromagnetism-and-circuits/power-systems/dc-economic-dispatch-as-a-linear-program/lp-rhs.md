# Right-hand side of the dispatch linear program

For a demand `d`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`, the
right-hand side is `(-d, d, 0, 0, p_max, -p_min, f_max, -f_min)`, in the row order of the
[constraint matrix](free-constraint-matrix.md).
