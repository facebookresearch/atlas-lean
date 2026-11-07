# Smaller child

Let $a$ be an array of length $|a|$ over a linearly ordered type, indexed
from $0$, and let $i$ be an index with children $\ell = 2i + 1$ and $r = 2i + 2$. If
$\ell \ge |a|$, then $i$ has no smaller child. Otherwise the smaller child of $i$ is $r$ when
$r < |a|$ and $a_r < a_\ell$, and $\ell$ in every other case, so ties go to the left child.
