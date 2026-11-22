# No isolated vertex at the connectivity threshold (Erdős–Rényi)

Let $c \in \mathbb{R}$ and let $p_n \in [0, 1]$ satisfy $n p_n - \log n \to c$, for instance $p_n = (\log n + c)/n$ for all large $n$. Then

$$\Pr[G(n, p_n) \text{ has no isolated vertex}] \to e^{-e^{-c}}.$$

The number of isolated vertices converges in distribution to a Poisson law with mean $e^{-c}$. The first-moment computation $n(1 - p_n)^{n-1} \to e^{-c}$ gives only an upper bound on the probability of an isolated vertex; the limit needs the factorial moments of the count, or inclusion–exclusion: the probability that a given set of $k$ vertices is isolated is exactly $(1-p)^{\binom k2 + k(n-k)}$.

## Informally uses

- [First moment of isolated vertices at the connectivity threshold](tendsto-mul-one-sub-pow.md): the mean $e^{-c}$ of the limiting Poisson law.
- [Probability that a vertex of $G(n, p)$ is isolated](measure-real-isolated.md): the case $k = 1$ of the joint isolation probabilities.

## Sources

- A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press (2016), Theorem 3.1 (ii) and (3.2) with $k = 0$; the proof there uses the method of moments.
