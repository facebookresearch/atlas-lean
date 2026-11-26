# p-stable locality-sensitive hash family

Let $\nu$ be a $p$-stable distribution on $\mathbb{R}$ ($p = 2$: standard Gaussian; $p = 1$: standard Cauchy), let $w > 0$ be a bucket width, and let $a \in \mathbb{R}^d$ have independent $\nu$-distributed coordinates and $b$ be uniform on $[0, w)$. The *$p$-stable hash* is $h_{a,b}(x) = \lfloor (\langle a, x \rangle + b)/w \rfloor$. By $p$-stability $\langle a, x - y \rangle$ is distributed as $\|x - y\|_p$ times a $\nu$-variable, so the collision probability is a function $p_w(\|x - y\|_p)$ of the $\ell_p$ distance alone.

## Depends on

- [Locality-sensitive hashing index with L tables and a stopping rule](lsh-index.md)
- [Stable distribution of a given index](../../../Probability/infinite-divisibility-regular-variation/stable-distributions-and-domains-of-attraction/is-stable.md)
- [Gaussian measures are stable of index 2](../../../Probability/infinite-divisibility-regular-variation/stable-distributions-and-domains-of-attraction/is-stable-gaussian-real.md)

## Sources

- M. Datar, N. Immorlica, P. Indyk and V. S. Mirrokni, "Locality-Sensitive Hashing Scheme Based on p-Stable Distributions", Proceedings of the 20th Symposium on Computational Geometry (SoCG), 2004.
