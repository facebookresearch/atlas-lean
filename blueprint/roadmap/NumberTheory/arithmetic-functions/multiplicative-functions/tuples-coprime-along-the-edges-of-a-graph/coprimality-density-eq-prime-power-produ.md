# Prime-power Euler product for the coprimality density

Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. For natural numbers $n_1, \dots, n_k$ let
$\delta_G(n_1, \dots, n_k)$ be $1$ if $\gcd(n_a, n_b) = 1$ for every $(a, b) \in E$, and $0$
otherwise. Then

$$A_G = \prod_p \left(1 - \frac{1}{p}\right)^k \sum_{\nu \in \mathbb{N}^k}
\frac{\delta_G(p^{\nu_1}, \dots, p^{\nu_k})}{p^{\nu_1 + \dots + \nu_k}},$$

the product running over all primes $p$ and the sum over all $k$-tuples $\nu$ of natural numbers
(zero allowed).

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`).
