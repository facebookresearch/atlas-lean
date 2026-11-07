# Signed iterated partial sums

Let $(b_n)_{n \ge 0}$ be a real sequence and fix a choice of
signs, either alternating, $\varepsilon_k = (-1)^{k-1}$, or constant, $\varepsilon_k = 1$. The
signed iterated partial sums $S^{(r)}_n$ of $b$, for orders $r \in \mathbb{N}$ and
$n \in \mathbb{N}$, are defined by $S^{(0)}_n = 0$, $S^{(1)}_n = b_n$ and, for $r \ge 1$,

$$S^{(r+1)}_n = \sum_{k=1}^{n} \varepsilon_k \, S^{(r)}_k.$$

The value $0$ at order $0$ is a convention and is not used.

With $b_n = H_n^{(p)} = \sum_{j=1}^{n} j^{-p}$, constant signs give the generalized hyperharmonic
numbers $H_n^{(p,r)}$ and alternating signs give the type I alternating ones $H_n^{(p,r,1)}$; with
$b_n = \bar H_n^{(p)} = \sum_{j=1}^{n} (-1)^{j-1} j^{-p}$, constant signs give type II,
$H_n^{(p,r,2)}$, and alternating signs give type III, $H_n^{(p,r,3)}$.

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`, `i = 1, 2, 3`).
