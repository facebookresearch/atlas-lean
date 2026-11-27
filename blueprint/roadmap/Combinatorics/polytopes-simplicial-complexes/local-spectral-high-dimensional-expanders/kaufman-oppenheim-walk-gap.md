# Spectral gap of high-order walks on local spectral expanders

Let $X$ be a pure $d$-dimensional one-sided $\lambda$-local spectral expander and $1 \le k < d$. Then the up-down walk on $X(k)$ satisfies

$$
\lambda_2\bigl(N_k^{\wedge}\bigr) \le 1 - \frac{1}{k+2} + O_k(\lambda),
$$

so that its spectral gap is at least $\frac{1}{k+2} - O_k(\lambda)$. The main term is asymptotically tight but not attained: for the complete $d$-dimensional complex on $N$ vertices the up-down walk on $X(k)$ is a Johnson-scheme walk with second eigenvalue

$$
\Bigl(1 - \frac{1}{k+2}\Bigr)\frac{N-k-2}{N-k-1} < 1 - \frac{1}{k+2},
$$

which tends to $1 - \frac{1}{k+2}$ as $N \to \infty$ for fixed $k$. For example, for $d = 2$, $k = 1$ and $N = 3$ the up-step from an edge must take the unique triangle and the down-step picks each of its edges uniformly, so the second eigenvalue is $0$.

## Proof sketch

Write $N_k^{\wedge} - \frac{1}{k+2} I$ as a convex combination of operators that factor through the link walks: sampling a $(k+1)$-face that contains $\tau$ and then dropping a vertex different from the added one is a step of the $1$-skeleton walk inside the link of a $(k-1)$-face. Each such link walk has second eigenvalue at most $\lambda$, which gives the comparison $N_k^{\wedge} \preceq \frac{k+1}{k+2} N_{k-1}^{\vee\text{-lift}} + \frac{1}{k+2} I + \lambda\,\Theta(1)$, and induction on $k$ closes the argument.

## Depends on

- [Up-down and down-up random walks on a weighted complex](up-down-walks.md)
- [Local spectral expanders (one-sided and two-sided)](local-spectral-expander.md)

## Sources

- T. Kaufman, D. Mass, "High dimensional random walks and colorful expansion", ITCS (2017), arXiv:1604.02947.
- I. Dinur, T. Kaufman, "High dimensional expanders imply agreement expanders", FOCS (2017), ECCC TR17-089.
- T. Kaufman, I. Oppenheim, "High order random walks: beyond spectral gap", APPROX-RANDOM (2018); Combinatorica 40 (2020), arXiv:1707.02799.
