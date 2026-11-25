# Convergent graph sequence

A sequence of simple graphs $G_n$ (on vertex sets $\{0, \dots, N_n - 1\}$) is convergent, or left convergent, if $t(F, G_n)$ converges as $n \to \infty$ for every simple graph $F$. The number of vertices need not tend to infinity.

Examples: $G(n, p)$ converges with probability $1$, with $t(F, G(n, p)) \to p^{|E(F)|}$; quasirandom sequences converge to the same limit by definition; the half-graphs $H_{n,n}$ converge.

## Background

- [Lovász–Szegedy limit theorem](exists-graphon-limit.md): every convergent sequence has a graphon as its limit.

## Sources

- L. Lovász and B. Szegedy, "Limits of dense graph sequences", *J. Combin. Theory Ser. B* 96 (2006), 933–957, arXiv:math/0408173, §2.2.
- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, Definition 2.1 and the examples after it.
