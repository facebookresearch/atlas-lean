# Population profile shape score

Let $\mu$ be a measure on $\Omega$ and $K : \Omega \to \mathbb{N}$ a count. For a real $a$, the
population profile shape score is

$$\Sigma_\mu(a) = \int \psi_K(a)\, d\mu - \Bigl(\log\Bigl(a + \int K\, d\mu\Bigr) - \log a\Bigr),$$

with the [digamma increment](digamma-increment.md) $\psi_k(a) = \sum_{j < k} 1/(a + j)$, in which a
term with $a + j = 0$ is $0$, the real logarithm ($\log 0 = 0$, $\log x = \log |x|$ for $x < 0$)
and Bochner integrals, which are $0$ for non-integrable integrands. The intended domain is $a > 0$:
there every $a + j$ is positive and, as $\int K\, d\mu \ge 0$, so are the arguments of both
logarithms. For a probability measure $\mu$, an integrable $K$ and $a > 0$ the integrals are
expected values, and $\Sigma_\mu(a)$ is the almost-sure limit of $n^{-1} S_p(a)$, with $S_p$ the
[profile shape score](profile-shape-score.md) of pairwise independent copies $K_1, \dots, K_n$ of
$K$.
