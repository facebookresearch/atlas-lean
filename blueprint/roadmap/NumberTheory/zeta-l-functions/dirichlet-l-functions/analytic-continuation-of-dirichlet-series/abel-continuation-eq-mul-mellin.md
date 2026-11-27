# The Abel continuation as a Mellin transform

Let $f : \mathbb{N} \to \mathbb{C}$ have
partial sums $A(n) = \sum_{k=1}^{n} f(k)$ and summatory step function
$S(t) = \sum_{1 \le k \le t} f(k)$ for real $t$, and let $\sigma$ be a real number with
$A(n) = O(n^\sigma)$ as $n \to \infty$. Then for every $s \in \mathbb{C}$ with
$\operatorname{Re} s > \sigma$, the Abel continuation satisfies $F_f(s) = s\,\mathcal{M}S(-s)$,
where $\mathcal{M}S(z) = \int_0^\infty t^{z-1} S(t)\,dt$ is the Mellin transform of $S$.

This identity transfers holomorphy of the Mellin transform to the continuation.
