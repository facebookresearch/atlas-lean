# Window criterion for shifted step sums of binomial coefficients

Let
$\alpha, \beta, k, \gamma, p, s$ be natural numbers with $\alpha > 1$, $k > 1$, $\gamma > 1$ and
$p < k$, and let $\delta_1, \delta_2, \ldots$ be integers. For $n \in \mathbb{N}$ let $c(n)$ be
the sum of $\binom{\alpha n + \beta}{m}$ over all $m$ with $0 \le m \le \alpha n + \beta$ and
$m \equiv \gamma n + p \pmod{k}$, that is,
$c(n) = \sum_{j \in \mathbb{Z}} \binom{\alpha n + \beta}{\gamma n + p + kj}$. If
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n$ with $s \le n \le k^2 + s - 1$, then
$c(n) = \sum_{i=1}^{s} \delta_i c(n - i)$ for all $n \ge s$.

The coefficients $\delta_i$ need only work for this one residue $p$; the source's hypothesis,
with one family $\delta_i$ for every $p$, is a special case.

## Sources

- Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Theorem 9.
