# Shifted maximal blocks scale geometrically

Let $L = (e_1, \dots, e_N)$ and $\tilde L$ be
lists of natural numbers of length at least $2$ with nonzero first entries, and let $\tilde Q$ be
a strictly decreasing sequence with values in $(0, 1)$ such that
$\varepsilon \mapsto \sum_k \varepsilon_k \tilde Q_k$ is a bijection from $\tilde E^*$, the
periodic Zeckendorf collection for $(0, 1)$ determined by $\tilde L$, onto $(0, 1)$. For
$s \in \mathbb{N}$ let $\bar\beta_s$ be the maximal $L^*$-block starting at index $s$: it is $0$
at indices $i < s$ and $e_j$ at indices $i \ge s$ with $j - 1 \equiv i - s \pmod N$. Then
$\sum_k (\bar\beta_s)_k \tilde Q_k = \tilde Q_0^{\,s} \sum_k (\bar\beta_0)_k \tilde Q_k$ for every
$s \in \mathbb{N}$.

Indices are zero-based: $\bar\beta_s$ is the paper's $\bar\beta^{s+1}$ and $\tilde Q_0$ is its
$\tilde Q_1 = \tilde\omega$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Lemma 16 (`integers-2025-A25-lem-16`; arXiv:2308.12872v1, Section 4.1).
