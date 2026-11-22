# Every graphon is a graph limit

For every graphon $W$ there is a sequence of nonempty simple graphs $G_n$ with $t(F, G_n) \to t(F, W)$ for every simple graph $F$. One can take the $W$-random graphs $G(n, W)$: pick $x_1, \dots, x_n$ uniformly in $[0, 1]$ and join $i$ and $j$ with probability $W(x_i, x_j)$; with probability $1$ this sequence converges to $W$.

## Background

- [Lovász–Szegedy limit theorem](exists-graphon-limit.md): the converse direction.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, Theorem 2.2, (b) ⇒ (a), and Corollary 2.6.
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Theorem 3.1.
