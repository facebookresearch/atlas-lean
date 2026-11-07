# Kummer's congruence

Let $p$ be a prime, let $B_j$ denote the $j$-th Bernoulli number,
with $B_1 = -1/2$, and let $t$ be a natural number. Let $m$ and $n$ be natural numbers, neither
divisible by $p - 1$, with $m \equiv n \pmod{(p-1)p^t}$. Then the rational numbers

$$\frac{(1 - p^{m-1}) B_m}{m} \quad \text{and} \quad \frac{(1 - p^{n-1}) B_n}{n}$$

are either equal, or their difference has $p$-adic valuation at least $t + 1$.

In other words, the two numbers agree modulo $p^{t+1}$; equality is listed as a separate case
because the $p$-adic valuation of $0$ is taken to be $0$.

Proof: We use Voronoi's finite-sum congruence in p-adic norm form, following
Ireland--Rosen, Ch. 15 §2, and Washington, Cor. 5.14, back to Kummer's 1851 paper.

## Sources

- Ernst Eduard Kummer, "Über eine allgemeine Eigenschaft der rationalen Entwickelungscoefficienten einer bestimmten Gattung analytischer Functionen," Journal für die reine und angewandte Mathematik 41 (1851), 368–372, DOI 10.1515/crll.1851.41.368, https://doi.org/10.1515/crll.1851.41.368.
