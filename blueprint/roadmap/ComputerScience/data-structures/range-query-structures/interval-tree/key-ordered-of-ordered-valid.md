# The executable ordering check implies key ordering

Let $t$ be an interval tree and let
$\ell$ and $u$ be optional keys in $\mathbb{Z} \times \mathbb{N}$. If the executable ordering check
of $t$ with lower bound $\ell$ and upper bound $u$ succeeds, then $t$ is key-ordered, and every
entry $e$ stored in $t$ satisfies $\ell < \operatorname{key}(e)$ when $\ell$ is present and
$\operatorname{key}(e) < u$ when $u$ is present, where $<$ is the lexicographic order on keys
(low endpoint first, then identifier).
