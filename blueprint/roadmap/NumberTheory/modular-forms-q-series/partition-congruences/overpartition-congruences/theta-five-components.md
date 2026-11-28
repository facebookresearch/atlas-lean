# Five-dissection of the square theta series

Let $t(q)=\sum_{j\in\mathbb{Z}}q^{j^2}$.
There are integer power series $b$ and $c$ supported in degrees $1$ and $4$ modulo $5$,
respectively, such that $t(q)=t(q^{25})+b+c$ and $bc=t(q^5)^2-t(q^{25})^2$.

## Sources

- Split the sum by $j \bmod 5$: the terms with $5 \mid j$ give $t(q^{25})$, and those with $j \equiv \pm 1$ and $j \equiv \pm 2 \pmod 5$ give $b$ and $c$, as their squares are $1$ and $4$ modulo $5$. For the product, compare the coefficients of $q^{5n}$: $t(q^{25})^2$, $bc$ and $t(q^5)^2$ have no other terms. The coefficient in $t(q^5)^2$ counts the integer solutions of $u^2 + v^2 = n$, and $(u, v) \mapsto (u + 2v, 2u - v)$, which multiplies $u^2 + v^2$ by $5$, maps them bijectively onto the solutions of $x^2 + y^2 = 5n$ with $5 \mid x + 2y$. Those with $5 \mid y$ are counted by the coefficient in $t(q^{25})^2$, and the others, with $x$ and $y$ swapped when $y \equiv \pm 1 \pmod 5$, by the coefficient in $bc$. Given the dissection, the identity for $bc$ is equivalent to $r_2(5n) = 2r_2(n) - r_2(n/5)$, where $r_2(m)$ is the number of representations of $m$ as a sum of two squares and $r_2(n/5) = 0$ when $5 \nmid n$.
