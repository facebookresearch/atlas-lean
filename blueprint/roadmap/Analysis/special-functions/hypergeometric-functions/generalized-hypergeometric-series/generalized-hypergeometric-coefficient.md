# Generalized hypergeometric coefficient

Let $K$ be a field, let $a$ and $b$ be finite
multisets of elements of $K$ (the upper and lower parameters), and let $n$ be a natural number.
The $n$-th generalized hypergeometric coefficient is

$$
(n!)^{-1} \prod_{x \in a} (x)_n \Big(\prod_{y \in b} (y)_n\Big)^{-1},
$$

where $(x)_n = x(x+1)\cdots(x+n-1)$ is the rising factorial, with $(x)_0 = 1$, and the products
run over the multisets with multiplicity. It is the coefficient of $z^n$ in the generalized
hypergeometric series ${}_pF_q$ with $p = |a|$ and $q = |b|$.

Inverses are taken in $K$ with the convention $0^{-1} = 0$, so the coefficient is $0$ whenever
the lower product or $n!$ is zero in $K$; the latter can happen in positive characteristic.
