# Ramanujan's extension of the partial sums of a smooth function

Let
$f : \mathbb{R} \to \mathbb{R}$ be infinitely differentiable and let $\rho > 0$. Suppose that for
every $q \in \mathbb{N}$ and every $x \in \mathbb{R}$ the series
$\sum_{k \ge 0} f^{(q)}(k + 1 + x)$ converges absolutely, and that for every $q \in \mathbb{N}$
there is a summable sequence $(b_k)_{k \ge 0}$ with $|f^{(q)}(k + 1 + x)| \le b_k$ for all
$k \in \mathbb{N}$ and all $x \in [-\rho, \rho]$. Put $c_q = \sum_{k \ge 0} f^{(q)}(k + 1)$ and
$F(x) = c_0 - \sum_{k \ge 0} f(k + 1 + x)$, and suppose that $F$ is analytic at $0$. Then
(i) for every $n \in \mathbb{N}$ the series $\sum_{k \ge 0} f^{(n)}(k + 1)$ converges absolutely
with sum $c_n$; (ii) $F(0) = 0$; (iii) $F(x) - F(x - 1) = f(x)$ for every $x \in \mathbb{R}$;
(iv) $F(m) = f(1) + f(2) + \dots + f(m)$ for every $m \in \mathbb{N}$, the empty sum being $0$;
(v) $F^{(n)}(0) = -c_n$ for every integer $n \ge 1$; and (vi) there is $r$ with $0 < r \le \rho$
such that for every real $x$ with $|x| < r$ the series
$\sum_{j \ge 0} -c_{j+1} x^{j+1} / (j + 1)!$ converges absolutely with sum $F(x)$.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6. Proves `Wanted` entry `ramanujan_part1_ch6_entry6_harmonic`.
