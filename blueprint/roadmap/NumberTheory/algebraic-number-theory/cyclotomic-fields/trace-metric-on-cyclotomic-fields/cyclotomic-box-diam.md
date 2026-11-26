# Diameter of the cyclotomic box

Let $p$ be an odd prime, let $N$ be a natural number, and
let $K$ be a field generated over $\mathbb{Q}$ by a primitive $p$-th root of unity, with fixed
primitive $p$-th root of unity $\omega \in K$. Let $d(\alpha, \beta) = \lVert \alpha - \beta \rVert$
be the trace metric on $K$, where $\lVert \gamma \rVert \ge 0$ and
$\lVert \gamma \rVert^2 = \sum_{j=1}^{p-1} \operatorname{Tr}_{K/\mathbb{Q}}(\gamma \omega^j)^2$.
Let $B(p, N)$ be the set of integer vectors $a = (a_1, \dots, a_{p-1})$ with $-N \le a_i \le N$
for all $i$, and write $\alpha_a = a_1 \omega + \dots + a_{p-1} \omega^{p-1}$. Then
$d(\alpha_a, \alpha_b) \le 2 N p \sqrt{p - 1}$ for all $a, b \in B(p, N)$, and this bound is
attained: $d(\alpha, -\alpha) = 2 N p \sqrt{p - 1}$ for
$\alpha = N \omega - N \omega^2 + \dots + N \omega^{p-2} - N \omega^{p-1}$, the point whose
coefficient of $\omega^i$ is $(-1)^{i-1} N$.

## Sources

- Saettone, Zaharescu and Zhang, *On a Special Metric in Cyclotomic Fields*, INTEGERS 25 (2025), Article A10, Lemma 2.
