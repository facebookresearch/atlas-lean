# Pseudo-calibration

Pseudo-calibration builds a candidate Sum-of-Squares pseudo-expectation $\tilde{\mathbb{E}}_G$ for a random instance $G$ by demanding that, for all simple low-degree functions $f(G, x)$, its average over the null distribution equals the true expectation under a planted distribution; this fixes all low-degree Fourier coefficients of $G \mapsto \tilde{\mathbb{E}}_G$.

Let $G(n, 1/2)$ be the Erdős-Rényi distribution and $G(n, 1/2, \omega)$ the planted distribution of pairs $(G, x)$ in which $x \in \{0,1\}^n$ is the indicator of a planted clique of size $\omega$ in $G$. A family of linear maps $p \mapsto \tilde{\mathbb{E}}_G\, p$ on polynomials of degree at most $d$ in $x$ is **pseudo-calibrated** if

$$
\mathbb{E}_{G \sim G(n,1/2)} \, \tilde{\mathbb{E}}_G\, f_G = \mathbb{E}_{(G,x) \sim G(n,1/2,\omega)} \, f_G(x)
$$

for every simple function $f = f(G, x)$, i.e. every $f$ that is a low-degree polynomial both in the entries of the adjacency matrix of $G$ and in $x$.

**The pseudo-calibrated planted clique moments.** Encode $G$ by $g_e \in \{\pm 1\}$ for $e \in \binom{[n]}{2}$ and let $\chi_T = \prod_{e \in T} g_e$ for $T \subseteq \binom{[n]}{2}$, with $V(T)$ the set of vertices touched by $T$. For degree $d$, clique size $\omega$ and truncation $\tau$, define for each $S \subseteq [n]$ with $|S| \le d$

$$
\widehat{\tilde{\mathbb{E}}[x_S]}(T) = \mathbb{E}_{(G,x) \sim G(n,1/2,\omega)} [\chi_T(G) \, x_S] \quad \text{if } |V(T) \cup S| \le \tau, \qquad \text{and } 0 \text{ otherwise},
$$

and $\tilde{\mathbb{E}}[x_S] = \sum_{T} \widehat{\tilde{\mathbb{E}}[x_S]}(T) \, \chi_T(G)$, extended linearly to all multilinear polynomials of degree at most $d$.

## Expansion

The motivation is Bayesian: a computationally bounded party cannot tell $G(n, 1/2)$ from the planted model, so its best-effort estimates of conditional expectations should be calibrated against the planted distribution on simple tests. Pseudo-calibration implies that every simple strong constraint (a function vanishing on all $\omega$-cliques) has pseudo-expectation $0$, and also many weak constraints, for example that a high-degree vertex is more likely to be in the clique. Earlier planted clique pseudo-expectations satisfied the strong constraints but violate such weak ones already at degree four, while for random 3-XOR pseudo-calibration reproduces Grigoriev's construction. For the truncated moments, simple tests whose coefficients have degree at most $\tau$ in the edge indicators are fooled exactly, $\tilde{\mathbb{E}}[1]$ and $\tilde{\mathbb{E}}[\sum_i x_i]$ equal $1$ and $\omega$ up to factors $1 \pm n^{-\Omega(\epsilon)}$ with high probability, and $\tilde{\mathbb{E}}[x_S] = 0$ whenever $S$ is not a clique of $G$. Positivity of the moment matrix is the hard part and is proved by an approximate factorization over ribbons and graphical matrices.

## Depends on

None.

## Proof depends on

None.

## Sources

- Boaz Barak, Samuel B. Hopkins, Jonathan A. Kelner, Pravesh K. Kothari, Ankur Moitra, Aaron Potechin, "A nearly tight sum-of-squares lower bound for the planted clique problem", *SIAM Journal on Computing* 48(2), 2019, https://doi.org/10.1137/17M1138236; numbering of arXiv:1604.03084v2 (Section 2.1, the pseudo-calibration equation, Definition 5.1, Lemmas 5.2 to 5.5, Sections 6 and 7).
