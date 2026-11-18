# Beta-binomial law of the sample rank (i.i.d. atomless scores)

Let $m, N, r \in \mathbb{N}$ with $1 \le r \le m + 1$, and let the $m + 1$ real and $N$ synthetic scores be
i.i.d. with law $\nu$, a probability measure on $\mathbb{R}$ without atoms (the score vector has law
$\nu^{\otimes(m + 1 + N)}$). Then the rank $K = J + 1$ of the $r$-th real score among the synthetic
scores, $J$ being the [sample rank](sample-rank.md), satisfies for every $k \ge 1$

$$P(K = k) = \mathrm{BB}(N; r, m + 2 - r)(k - 1),$$

where $\mathrm{BB}$ is the [beta-binomial mass function](beta-binomial-pmf.md); this mass vanishes for
$k > N + 1$.
