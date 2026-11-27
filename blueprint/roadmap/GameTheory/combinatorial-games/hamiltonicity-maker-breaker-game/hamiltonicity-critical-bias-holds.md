# The critical bias of the Hamiltonicity game is $(1 + o(1))\, n / \ln n$

Consider the
$(1 : b)$ Maker-Breaker game on the edges of the complete graph $K_n$ in which Breaker moves
first: Breaker claims $b$ free edges per turn (all remaining free edges if fewer than $b$ are
left), Maker claims one free edge per turn, and Maker wins if, once every edge is claimed, his
edges contain a Hamilton cycle. For every real $\varepsilon > 0$ there is $n_0$ such that for
every $n \ge n_0$, Maker has a winning strategy for every natural number $b$ with
$0 < b \le (1 - \varepsilon)\, n / \ln n$, and Maker has no winning strategy for any natural
number $b \ge (1 + \varepsilon)\, n / \ln n$.

Maker's side is Krivelevich's Theorem 1, which gives Maker a win for every
$b \le (1 - 30 / \ln^{1/4} n)\, n / \ln n$ once $n$ is large. Breaker's side follows from the
Chvátal-Erdős Theorem 3.1, whose Breaker strategy claims every edge at some vertex for every
$b > (1 + \varepsilon / 2)\, n / \ln n$ once $n$ is large.

## Sources

- T. Szabó (joint with H. Gebauer and M. Krivelevich), Thresholds for positional games, in Combinatorics, Oberwolfach Reports 5 (2008), no. 1, pp. 56-59, DOI 10.4171/OWR/2008/01; resolution: M. Krivelevich, The critical bias for the Hamiltonicity game is (1 + o(1)) n / ln n, J. Amer. Math. Soc. 24 (2011), 125-131, DOI 10.1090/S0894-0347-2010-00678-9, arXiv:0909.2744; V. Chvátal and P. Erdős, Biased positional games, Ann. Discrete Math. 2 (1978), 221-229, https://users.renyi.hu/~p_erdos/1978-06.pdf, Krivelevich, Section 1 (Breaker moves first) and Theorem 1 (Maker wins for b ≤ (1 - 30/ln^{1/4} n) n/ln n); Chvátal-Erdős, Section 1 (Breaker moves first) and Theorem 3.1 (Breaker wins T(n, b) for b > (1 + ε) n/log n and n > n₀(ε), by isolating a vertex); report p. 57 (the Hamiltonicity game is harder for Maker than the connectivity game), https://arxiv.org/abs/0909.2744.
