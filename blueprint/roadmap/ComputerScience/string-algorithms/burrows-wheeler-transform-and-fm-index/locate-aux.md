# Step-bounded sampled-suffix-array locate

Let $L$ be a list over a linearly ordered alphabet with a least letter $\bot$ adjoined, with
LF-mapping $\mathrm{LF}$, and let a sampling assign to some rows $r$ a stored natural number $s(r)$
(intended to be the suffix-array entry of row $r$). The $k$-step locate from row $r$ is defined by
recursion on $k$. With $k = 0$ it returns $s(r)$ if row $r$ is sampled and $0$ otherwise. With
$k + 1$ steps it returns $s(r)$ if row $r$ is sampled, and otherwise $1$ plus the $k$-step locate
from row $\mathrm{LF}(r)$.
