# Wintner's mean-value theorem in several variables

Let $k \ge 1$ and let $f$ be a
complex-valued function on $k$-tuples of natural numbers. For a $k$-tuple
$n = (n_1, \dots, n_k)$ of positive integers put

$$
(\mu * f)(n) = \sum_{d_1 \mid n_1, \dots, d_k \mid n_k}
\mu(d_1) \cdots \mu(d_k) \, f(n_1/d_1, \dots, n_k/d_k),
$$

where $\mu$ is the Möbius function and the $d_i$ run over positive divisors. If the series

$$\sum_{m \in \mathbb{Z}_{\ge 1}^k} \frac{|(\mu * f)(m)|}{m_1 \cdots m_k}$$

converges, then

$$
\frac{1}{x_1 \cdots x_k} \sum_{n_1 = 1}^{x_1} \cdots \sum_{n_k = 1}^{x_k} f(n_1, \dots, n_k)
\to \sum_{m \in \mathbb{Z}_{\ge 1}^k} \frac{(\mu * f)(m)}{m_1 \cdots m_k}
$$

as the integers $x_1, \dots, x_k$ all tend to infinity.

## Sources

- László Tóth, "On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components," Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem `Th_Wintner_gen`, lines 300–311, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex>. Proved by H. Ushiroya (2012) as a generalization of Wintner's classical one-variable theorem.
