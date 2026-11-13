# Pain's signed falling-factorial identity for fixed points

Let $n$ and $k$ be natural
numbers with $n \ge 2$, $k \ge 1$ and $k + 1 \le n$, and let $x$ be a real number. For a
permutation $\sigma$ of $\lbrace 0, 1, \dots, n-1 \rbrace$, write $\operatorname{sgn}(\sigma)$ for
its sign and $\operatorname{fix}(\sigma)$ for its number of fixed points, and for a natural number
$m$ write $(m)_k = m(m-1)\cdots(m-k+1)$ for the falling factorial. Then, summing over all
permutations $\sigma$ of this set,

$$\sum_{\sigma} \operatorname{sgn}(\sigma) (\operatorname{fix}(\sigma))_k
x^{\operatorname{fix}(\sigma) - k} = \frac{n!}{(n-k)!} (x-1)^{n-k-1} (x + n - k - 1),$$

where a term with $\operatorname{fix}(\sigma) < k$ is $0$ because then
$(\operatorname{fix}(\sigma))_k = 0$.

The left side is the $k$-th derivative in $x$ of
$\sum_{\sigma} \operatorname{sgn}(\sigma) x^{\operatorname{fix}(\sigma)}$.

## Sources

- Jean-Christophe Pain, "Identities for Permutations with Fixed Points", Theorem 2.
