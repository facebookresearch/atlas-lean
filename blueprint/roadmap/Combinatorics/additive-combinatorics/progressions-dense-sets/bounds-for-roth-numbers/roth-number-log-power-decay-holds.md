# Kelley–Meka: Roth numbers are below every power of the logarithm

For every real $C > 0$
there is a real constant $K$ such that $r_3(N) \le K N / (\log N)^C$ for every natural number
$N \ge 2$, where $r_3(N)$ is the largest size of a subset of $\{0, 1, \dots, N - 1\}$ containing no
non-trivial three-term arithmetic progression.

This follows from the theorem of Kelley and Meka that for some $\beta > 0$ every subset of
$\{1, \dots, N\}$ of size at least $2^{-O((\log N)^\beta)} N$ contains a non-trivial three-term
progression, which gives $r_3(N) \le N \exp(-c (\log N)^\beta)$ for some $c > 0$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #140, https://www.erdosproblems.com/140 (status PROVED (LEAN)); resolution: Z. Kelley and R. Meka, Strong bounds for 3-progressions, FOCS 2023, arXiv:2302.05537, abstract: every A ⊆ {1, …, N} with |A| ≥ 2^{-O((log N)^β)} N contains a non-trivial 3-term progression; erdosproblems.com/140, https://arxiv.org/abs/2302.05537.
