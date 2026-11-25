# C-tightness: tight laws with vanishing maximal jumps have continuous limit points

Let $(E,r)$ be a metric space, $T>0$, and for $x\in D([0,T],E)$ let $J(x)=\sup_{0<t\le T}r\bigl(x(t),x(t-)\bigr)$ be its largest jump. Let $X^n$ be random elements of the [Skorokhod space](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md) $D([0,T],E)$ whose laws are tight. If $J(X^n)\to0$ in probability, then every weak limit of a subsequence of the laws of $X^n$ is concentrated on $C([0,T],E)$. The laws of $(X^n)$ are called C-tight when they are tight and every such limit is concentrated on $C([0,T],E)$.

## Depends on

- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Expansion

A proof page must establish that $J$ is continuous on $D([0,T],E)$ for the J1 topology, or at least that $\{x:J(x)\le\eta\}$ is closed for every $\eta>0$, so that the portmanteau theorem gives $\mathbb P(J(X)>\eta)\le\liminf_j\mathbb P(J(X^{n_j})>\eta)=0$ for a limit $X$; and conclude $J(X)=0$, that is $X\in C([0,T],E)$, almost surely. It should give an example of tight laws whose limit has a jump when the maximal jump does not vanish.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Chapter 3, Section 13.
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, Chapter 3, Section 10.
