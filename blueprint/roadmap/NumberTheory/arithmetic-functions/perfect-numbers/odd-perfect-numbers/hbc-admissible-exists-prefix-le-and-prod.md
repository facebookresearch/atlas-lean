# Stone's product bound for HBC-admissible tuples

Let $a$ and $d$ be coprime positive
integers, let $k \ge 1$, and let $y_1 < y_2 < \dots < y_k$ be positive integers with
$\prod_{i=1}^{k} (1 - 1/y_i) \le a/(a + d) < \prod_{i=1}^{k-1} (1 - 1/y_i)$ (the source calls such
a tuple HBC-admissible for $a/(a + d)$). Put $\alpha = (a + d)/d$, let $n_i = 1 + \alpha^{2^{i-1}}$
for $1 \le i < k$ and $n_k = \alpha^{2^{k-1}}$, and let $F_k(x) = x^{2^k} - x^{2^{k-1}}$. Then some
$\kappa$ with $1 \le \kappa \le k$ has $\prod_{i=1}^{\kappa} y_i \le \prod_{i=1}^{\kappa} n_i$.
Moreover, let $\kappa$ with $1 \le \kappa \le k$ satisfy this inequality while every $\kappa'$ with
$\kappa < \kappa' \le k$ satisfies $\prod_{i=1}^{\kappa'} n_i < \prod_{i=1}^{\kappa'} y_i$, so that
$\kappa$ is the largest such index. If $\kappa < k$, then
$a \prod_{i=1}^{k} y_i \le F_k(\alpha d^{1/2^{\kappa}})$; if $\kappa = k$, then
$a \prod_{i=1}^{k} y_i \le d \, F_k(\alpha)$.

## Sources

- Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24 (2024), Article A114, Theorem 1.
