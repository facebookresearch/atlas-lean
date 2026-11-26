# Evolutionary entropy of a Leslie population and its scale invariance

**Setting.** An age-structured population with survivorship $l_j$ to age class $j$ and fertility $m_j$, $j = 1, \dots, \omega$, has Leslie growth factor $\lambda > 0$ given by the Euler–Lotka equation $\sum_j l_j m_j \lambda^{-j} = 1$. The *Euler–Lotka reproductive distribution* is
$$p_j = \frac{l_j m_j}{\lambda^j}, \qquad \sum_j p_j = 1,$$
the *generation time* is $T = \sum_j j\, p_j$, and the *evolutionary entropy* is
$$H = \frac{-\sum_{j=1}^{\omega} p_j \log p_j}{T}.$$

**Theorem.**
1. *(Scale invariance.)* If the Euler–Lotka-normalised survivorship weights on the reproductive interval are multiplied by a constant $c > 0$ (and renormalised), $H$ and $T$ are unchanged; hence $H$ depends only on the normalised post-maturity reproductive distribution, not on absolute survivorship or fertility levels or on juvenile mortality alone.
2. *(Uniform reproduction.)* If the weights are constant on $n$ reproductive classes, $H = \log n / T$.
3. *(Finite geometric reproduction.)* If the weights on classes $A, \dots, A + n - 1$ form a geometric progression with ratio $q < 1$, then
$$H_n = \frac{-\log q \Bigl[\frac{q}{1-q} - \frac{n q^n}{1 - q^n}\Bigr] + \log \frac{1 - q^n}{1 - q}}{A + \frac{q}{1-q} - \frac{n q^n}{1 - q^n}} .$$
4. *(Infinite geometric tail.)* If from age $A$ onward the weights are geometric with ratio $q < 1$ and no last class,
$$H_\infty = -\frac{(1-q)\log(1-q) + q \log q}{A(1-q) + q}.$$

## Expansion

Multiplying the weights by $c$ multiplies every $p_j$ by the same factor before renormalisation, so the normalised distribution and therefore both the Shannon entropy and the mean age are unchanged. The geometric formulas follow by summing $\sum_k q^k$, $\sum_k k q^k$ and $\sum_k q^k \log q^k$ over the reproductive window, with the entropy offset by the age at first reproduction $A$ only through the generation time in the denominator. In the geometric regime the effective ratio is $q = \rho / \lambda$, adult survival discounted by population growth.

## Sources

- J. Buescu, S. Elaydi, H. Oliveira, "Evolutionary Entropy Shapes Reproductive Lifespan in Age-Structured Populations", arXiv:2606.22001 (2026), definition of evolutionary entropy (Section 2), Theorem 2.4, Propositions 3.1, 3.2 and 3.3, <https://doi.org/10.48550/arXiv.2606.22001>.
