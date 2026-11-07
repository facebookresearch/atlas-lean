# Stirling recursion for derivatives, for arbitrary multiplicities

Let $k$ and $d$ be
natural numbers, let $m \colon \mathbb{N} \to \mathbb{N}$, write $m_i = m(i)$, and let
$f(y) = \sum_{i=1}^{k} m_i y^i$ for real $y$. Then for every real $x \ne 0$,

$$f^{(d)}(x) = \sum_{i=1}^{k} i^d m_i x^{i-d} -
\sum_{j=0}^{d-1} S(d, j)\, x^{j-d} f^{(j)}(x),$$

where $S(d, j)$ are the Stirling numbers of the second kind and $f^{(j)}$ is the $j$th
derivative of $f$. No relation between $d$ and $k$ is assumed.
