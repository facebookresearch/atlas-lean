# Locality of comparator networks

Let $\alpha$ be a linear order and let $ps$ be a list
of comparators $(i, j)$ on $\mathbb{N}$-indexed wires that all lie within $[l, h)$, that is,
$l \le i < h$ and $l \le j < h$ for every $(i, j)$ in $ps$. Then for every input
$f : \mathbb{N} \to \alpha$ and every wire $x$ with $x < l$ or $h \le x$, the value of wire $x$
after running $ps$ on $f$ is $f(x)$.
