# Cycle Realization

A cycle realization: a cycle map (`CycleMap`) for the given `D` and `P` that is compatible with
products on transverse smooth closed intersections. Let $X$ be a smooth proper projective complex
variety of dimension $d$ and $Y \to X$, $Z \to X$ closed immersions, with $Y$ and $Z$ Noetherian and
smooth of dimensions $r$ and $s$, whose intersection $Y \times_X Z$ is Noetherian and smooth of
dimension $t$, where $r + s = d + t$. Then the cup product of the cohomology classes
(`CycleMap.cohomologyClass`, through the purity of $X$) of the pushed-forward fundamental cycles of
$Y$ and $Z$ is the cohomology class of the pushed-forward fundamental cycle of $Y \times_X Z$.
