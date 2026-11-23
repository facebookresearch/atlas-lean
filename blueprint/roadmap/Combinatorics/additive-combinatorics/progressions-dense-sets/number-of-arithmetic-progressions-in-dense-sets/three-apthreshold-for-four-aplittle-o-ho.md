# Erdős Problem 179: $F_3(N, 4) = o(N^2)$

As $N \to \infty$ over the natural numbers,
$F_3(N, 4) / N^2 \to 0$, that is, $F_3(N, 4) = o(N^2)$, where $F_3(N, 4)$ is the least natural
number $m$ such that every $N$-element set $A \subseteq \mathbb{N}$ containing at least $m$
three-term arithmetic progressions $a, a + d, a + 2d$ with $d \ge 1$ contains a $4$-term
arithmetic progression.

Write $F_k(N, \ell)$ for the same threshold with $k$-term progressions in place of three-term ones
and $\ell$-term progressions in place of $4$-term ones. Fox and Pohoata bound $F_k(N, \ell)$ above
by $(r_\ell(N) / N)^{O(1)} N^2$, where $r_\ell(N)$ is the largest size of a subset of
$\{1, \dots, N\}$ without $\ell$-term progressions; since $r_\ell(N) = o(N)$ by Szemerédi's
theorem, this bound is $o(N^2)$. erdosproblems.com/179 records
$F_k(N, \ell) \le N^2 / (\log \log N)^{C_\ell}$ for a constant $C_\ell$ depending only on $\ell$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED); resolution: J. Fox and C. Pohoata, Sets without k-term progressions can have many shorter progressions, Random Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for all k > s ≥ 3, log f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of s-term progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² / (log log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
