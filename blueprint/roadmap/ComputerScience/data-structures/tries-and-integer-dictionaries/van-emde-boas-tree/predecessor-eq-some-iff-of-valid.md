# Characterization of the van Emde Boas predecessor

Let $t$ be a valid two-level van Emde
Boas tree over the universe $\{0, \dots, m^2 - 1\}$, and let $x$ and $y$ be in the universe. The
predecessor query for $x$ in $t$ returns $y$ if and only if $y$ is stored in $t$, $y < x$, and
$z \le y$ for every $z$ stored in $t$ with $z < x$.
