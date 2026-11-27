# Grid index of a time

For a mesh $h$, the grid index of a real $t$ is the natural-number floor $\lfloor t/h\rfloor_+ = \max(\lfloor t/h\rfloor, 0)$, with $t/0 = 0$; so negative ratios give index $0$, as does $h = 0$.
