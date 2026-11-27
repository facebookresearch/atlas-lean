# Erdős Problem 179: $\log F_3(N, \ell) / \log N$ tends to $2$

For every natural number
$\ell > 3$, $\log F_3(N, \ell) / \log N \to 2$ as $N \to \infty$ over the natural numbers, where
$F_3(N, \ell)$ is the least natural number $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ containing at least $m$ three-term arithmetic progressions
$a, a + d, a + 2d$ with $d \ge 1$ contains an $\ell$-term arithmetic progression.

Fox and Pohoata prove that $\log f_{s,k}(n) / \log n \to 2$ for all $k > s \ge 3$, where
$f_{s,k}(n)$ is the largest number of $s$-term progressions in an $n$-element set with no
$k$-term progression; since $F_3(N, \ell) = f_{3,\ell}(N) + 1$, taking $s = 3$ and $k = \ell$
gives the statement.

## Sources

- T. F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED); resolution: J. Fox and C. Pohoata, Sets without k-term progressions can have many shorter progressions, Random Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for all k > s ≥ 3, log f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of s-term progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
