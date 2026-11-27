# Möbius-convolution series for the coprimality density

Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. Let $\delta_G(n_1, \dots, n_k)$ be $1$ if
$\gcd(n_a, n_b) = 1$ for every $(a, b) \in E$, and $0$ otherwise, and for a tuple
$n = (n_1, \dots, n_k)$ of positive integers let

$$(\mu * \delta_G)(n) = \sum_{d_1 \mid n_1, \dots, d_k \mid n_k}
\mu(d_1) \cdots \mu(d_k) \, \delta_G(n_1/d_1, \dots, n_k/d_k),$$

the sum running over positive divisors $d_i$ of $n_i$, where $\mu$ is the Möbius function. Then

$$A_G = \sum_{n_1, \dots, n_k \ge 1} \frac{(\mu * \delta_G)(n)}{n_1 \cdots n_k}.$$

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`).
