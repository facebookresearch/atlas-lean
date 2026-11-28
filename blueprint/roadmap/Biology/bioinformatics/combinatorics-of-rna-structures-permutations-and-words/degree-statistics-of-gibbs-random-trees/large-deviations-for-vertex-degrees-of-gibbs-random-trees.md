# Large deviations for vertex degrees of Gibbs random trees

Fix $D \ge 2$, an energy function $c : \{1,\dots,D\} \to \mathbb{R}$ and an inverse temperature $\beta > 0$. On the set $\mathbb{T}_N(D)$ of labeled trees on $N$ vertices with all degrees at most $D$, let $\chi_k(T)$ be the number of vertices of degree $k$, and define the Gibbs measure

$$
P_N\{T\} = \frac{e^{-\beta H(T)}}{Z_N}, \qquad H(T) = \sum_{k=1}^D c(k)\, \chi_k(T).
$$

Let $\mathcal{M} = \{ p \in [0,1]^D : \sum_k p_k = 1,\ \sum_k k p_k = 2 \}$, and for $p \in \mathcal{M}$ set

$$
J(p) = \sum_{k=1}^D p_k \ln p_k + \beta \sum_{k=1}^D p_k c(k) + \sum_{k=1}^D p_k \ln\big((k-1)!\big).
$$

$J$ is strictly convex and continuous, so it has a unique minimizer $p^* \in \mathcal{M}$. Put $I(p) = J(p) - J(p^*)$.

**Theorem.** Let $\nu_N$ be the law of $\frac{1}{N}(\chi_1,\dots,\chi_D)$ under $P_N$. There are probability measures $Q_N$ on $[0,1]^D \times \mathcal{M}$ such that (i) the first marginal of $Q_N$ is $\nu_N$; (ii) $Q_N$ is supported on pairs $(x,y)$ with $\sum_k |x_k - y_k| \le 2/N$; and (iii) the second marginals $Q_N^{(2)}$ satisfy a large deviation principle on $\mathcal{M}$ with rate function $I$. In particular,

$$
\Big( \frac{\chi_1}{N}, \dots, \frac{\chi_D}{N} \Big) \to p^* \quad \text{in probability, with exponentially small deviation probabilities.}
$$

An analogous LDP with an explicit rate function, and the corresponding law of large numbers for the degree frequencies $(\chi_0/N,\dots,\chi_D/N)$, holds for Gibbs measures on plane (ordered) rooted trees, the combinatorial model of RNA secondary structures.

## Expansion

By Cayley–Prüfer counting, the number of labeled trees with degree sequence $(d_1,\dots,d_N)$ is the multinomial coefficient $\binom{N-2}{d_1 - 1, \dots, d_N - 1}$. Grouping trees by their degree counts gives a weight $\binom{N}{\chi}\binom{N-2}{(d_j-1)}\, e^{-\beta H}$, whose logarithm is $-N J(\chi/N) + O(\ln N)$ by Stirling's formula. Projecting $\chi/N$ onto the constraint set $\mathcal{M}$ costs at most $2/N$. Comparing with an auxiliary sequence of measures through a ratio bound polynomial in $N$ then transfers Varadhan-type estimates to the Gibbs measures. The minimizer $p^*$ predicts the typical branching statistics of thermodynamically weighted RNA folds.

## Sources

- Yuri Bakhtin, Christine Heitsch, "Large Deviations for Random Trees", Journal of Statistical Physics 132 (2008), 551–560, <https://doi.org/10.1007/s10955-008-9540-0>. Published version of arXiv:0712.2253, cited next; locators there refer to the arXiv version.
- Yuri Bakhtin, Christine Heitsch, "Large Deviations for Random Trees", arXiv (2007). Theorem 1, Corollary 1, Theorem 2, Corollary 2, Lemmas 1-3. <https://doi.org/10.48550/arXiv.0712.2253>
