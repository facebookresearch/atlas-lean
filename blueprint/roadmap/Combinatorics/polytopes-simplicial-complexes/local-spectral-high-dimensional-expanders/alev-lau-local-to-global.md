# Alev–Lau local-to-global bound for the down-up walk

Let $X$ be a pure $d$-dimensional weighted complex, and for $-1 \le j \le d-2$ let

$$
\gamma_j = \max_{\tau \in X(j)} \lambda_2(M_\tau)
$$

be the worst second eigenvalue among links of $j$-faces. Then for every $1 \le k \le d$ the down-up walk on $X(k)$ has spectral gap

$$
1 - \lambda_2\bigl(N_k^{\vee}\bigr) \ge \frac{1}{k+1} \prod_{j=-1}^{k-2} (1 - \gamma_j).
$$

In particular, if $X$ is a one-sided $\gamma$-local spectral expander, the down-up walk on $X(k)$ has spectral gap at least $(1-\gamma)^{k}/(k+1)$, so as $\gamma \to 0$ it mixes almost as fast as on the complete complex.

## Proof sketch

Use the decomposition of the up-down walk on $X(k-1)$ as a mixture of the identity and of link walks to prove the operator inequality $N_{k-1}^{\wedge} - \frac{1}{k+1}I \preceq \bigl(1-\frac{1}{k+1}\bigr)\gamma_{k-2} I + \bigl(1-\frac{1}{k+1}\bigr)(1-\gamma_{k-2}) N_{k-2}^{\wedge}$ on the orthogonal complement of constants. Since $N_k^{\vee}$ and $N_{k-1}^{\wedge}$ share their nonzero spectrum, unrolling the recursion gives the product formula.

## Depends on

- [Up-down and down-up random walks on a weighted complex](up-down-walks.md)
- [Link of a face in a weighted complex](link-of-face.md)
- [Pure weighted simplicial complexes and their face distributions](pure-weighted-complex.md)

## Sources

- V. L. Alev, L. C. Lau, "Improved analysis of higher order random walks and applications", STOC (2020), arXiv:2001.02827.
- T. Kaufman, I. Oppenheim, "High order random walks: beyond spectral gap", APPROX-RANDOM (2018); Combinatorica 40 (2020), arXiv:1707.02799.
