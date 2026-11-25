# Erdős Problem 1025 (Spencer; Conlon, Fox and Sudakov)

For a natural number $n$, let $g(n)$
be the largest $k$ such that every map $f$ from the unordered pairs of elements of
$\{0, \dots, n-1\}$ to $\{0, \dots, n-1\}$ with $f(\{x, y\}) \notin \{x, y\}$ for all distinct
$x, y$ admits a set $X$ of at least $k$ elements with $f(\{x, y\}) \notin X$ for all distinct
$x, y \in X$ (and $g(n) = 0$ if no largest such $k$ exists). Then there are constants $c, C > 0$
such that $c \sqrt{n} \le g(n) \le C \sqrt{n}$ for all sufficiently large $n$, that is,
$g(n) \asymp \sqrt{n}$ as $n \to \infty$.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1025, https://www.erdosproblems.com/1025 (status SOLVED (LEAN)); resolution: J. Spencer, Turán's theorem for k-graphs, Discrete Math. (1972), 183-186; D. Conlon, J. Fox and B. Sudakov, Short proofs of some extremal results II, J. Combin. Theory Ser. B (2016), 173-196, Spencer: g(n) ≫ n^{1/2}; Conlon-Fox-Sudakov: g(n) ≪ n^{1/2} (erdosproblems.com/1025), https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1025.lean#L829.
