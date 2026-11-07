# Recursion for the signed iterated partial sums

Let $(b_n)_{n \ge 0}$ be a real sequence,
fix a choice of signs, either $\varepsilon_k = (-1)^{k-1}$ for all $k$ or $\varepsilon_k = 1$ for
all $k$, and let $S^{(r)}_n$ denote the signed iterated partial sum of $b$ of order $r$ at $n$ for
this choice. Then for every $r \ge 1$ and every $n \in \mathbb{N}$,

$$S^{(r+1)}_n = \sum_{k=1}^{n} \varepsilon_k \, S^{(r)}_k.$$

## Sources

- Rusen Li, *Sums over Primes II*, Journal of Integer Sequences 27 (2024), Article 24.4.1, Section 1 (definitions of `H_n^{(p,r)}` and `H_n^{(p,r,i)}`).
