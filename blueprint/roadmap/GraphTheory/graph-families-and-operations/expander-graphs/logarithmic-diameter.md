# Spectral expanders have logarithmic diameter

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector, with $d \ge 1$, and let $\ell$ be a natural number with $\lambda^\ell N < 1$. Then any two vertices $s$ and $t$ are joined by a walk of length exactly $\ell$; in particular, if $N \ge 1$, $G$ is connected with diameter at most $\ell$, which is $O(\log N/\log(1/\lambda))$ for $0 < \lambda < 1$ (O. Reingold, *Undirected ST-connectivity in log-space*, ECCC TR04-094 (2004), Proposition 2.2, proved there through vertex expansion; S. Vadhan, *Pseudorandomness* (2012), Problem 4.2 (3)). The proof is spectral: $(A^\ell)_{st} \ge d^\ell (1/N - \lambda^\ell) > 0$, and $(A^\ell)_{st}$ counts the walks of length $\ell$ from $s$ to $t$.

## Background

- [Undirected ST-connectivity is in L (Reingold)](../../../TheoryOfComputation/polynomial-time-problems/undirected-s-t-connectivity/ustcon-in-l.md):
  logarithmic diameter is why connectivity is easy in log space on graphs whose components are
  expanders: it suffices to try all walks of length $O(\log N)$.
- [Elementary lower bound on the spectral parameter](elementary-spectral-lower-bound.md): $\lambda$ cannot
  be much smaller than $1/\sqrt d$, so the diameter bound is of order $\log N/\log d$ at best.
