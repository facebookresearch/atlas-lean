# Sweep order on endpoint events

Let $K$ be a linearly ordered set and $S$ a family of
segments in $K^2$, each given by its two endpoints. An endpoint event $e$ of $S$ standing for the
point $(x, y)$ gets the key $(x, \varepsilon, y)$, compared lexicographically, where
$\varepsilon = 0$ if $e$ is a left endpoint and $\varepsilon = 1$ if it is a right endpoint. So
events are ordered by $x$; at equal $x$, left endpoints come first; then by $y$. This is the
endpoint order of CLRS.
