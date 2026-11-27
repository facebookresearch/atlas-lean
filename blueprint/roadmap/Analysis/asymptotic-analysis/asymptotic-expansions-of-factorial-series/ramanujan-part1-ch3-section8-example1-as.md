# Asymptotic expansion of a factorial series

Let $a_0, a_1, \ldots$ be complex numbers, let
$\psi : \mathbb{C} \to \mathbb{C}$, let $\lambda$ be either a real number or $-\infty$, and let
$0 < \varepsilon < \pi/2$. Suppose that for every complex $z$ that is not a negative integer and
satisfies $\operatorname{Re} z > \lambda$, the series

$$\sum_{j=0}^{\infty} \frac{(-1)^j a_j}{(z + 1)(z + 2) \cdots (z + j + 1)}$$

converges absolutely with sum $\psi(z)$. Write $S(n, k)$ for the Stirling numbers of the second
kind and $c_j = \sum_{k=0}^{j} a_k S(j + 1, k + 1)$. Then for every natural number $N$ there are
real numbers $C \ge 0$ and $R > 0$ such that

$$\Big|\psi(z) - \sum_{j=0}^{N} \frac{(-1)^j c_j}{z^{j+1}}\Big| \le \frac{C}{|z|^{N+2}}$$

for every complex $z$ that is not a negative integer, satisfies $\operatorname{Re} z > \lambda$
and $|z| \ge R$, and lies in the sector $|\arg z| \le \pi/2 - \varepsilon$ when
$\lambda = -\infty$, or $|\arg(z - \lambda)| \le \pi/2 - \varepsilon$ when $\lambda$ is real.

For $\lambda = -\infty$ the expansion is stated on the sector $|\arg z| \le \pi/2 - \varepsilon$,
as for real $\lambda$; on the wider sector $|\arg z| \le \pi - \varepsilon$ it fails, for example
for $a_j = j!\,(-2/3)^j$.

Proof: Use convergence at one real point to obtain absolute convergence two units to the right,
then expand each $1/((z + 1)\cdots(z + j + 1))$ termwise in powers of $1/z$ and bound the tail.

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 1, formula (8.1), printed p. 50 / PDF p. 60.
