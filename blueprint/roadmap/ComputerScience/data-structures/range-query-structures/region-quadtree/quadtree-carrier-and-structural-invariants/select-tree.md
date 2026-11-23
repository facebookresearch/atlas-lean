# Quadrant selection by coordinate flags

Given two true/false flags $x$ and $y$ and four quadtrees $t_0, t_1, t_2, t_3$, quadrant selection
returns $t_0$ if $x$ and $y$ are both true, $t_1$ if $x$ is true and $y$ is false, $t_2$ if $x$
is false and $y$ is true, and $t_3$ if both are false. In lookup, a flag is true when the
corresponding coordinate is below the split.
