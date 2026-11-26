# Almost all pairs in the cyclotomic box are nearly equidistant

For every real
$\varepsilon > 0$ there is a natural number $A$ with the following property. Let $p$ be a prime
and $N$ a natural number with $p > A$ and $N > A$, and let $K$ be a field generated over
$\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed primitive $p$-th root of unity
$\omega \in K$. Let $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$ be the trace metric on $K$,
where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then fewer than
$\varepsilon \lvert B(p, N) \rvert^2$ pairs $(a, b) \in B(p, N)^2$ satisfy

$$
\left| \frac{d(\alpha_a, \alpha_b)}{2 N p \sqrt{p - 1}} - \frac{1}{\sqrt{6}} \right| > \varepsilon.
$$

The constant $A$ depends only on $\varepsilon$; it is not claimed to be effectively computable.

## Sources

- Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10, Theorem 1.
