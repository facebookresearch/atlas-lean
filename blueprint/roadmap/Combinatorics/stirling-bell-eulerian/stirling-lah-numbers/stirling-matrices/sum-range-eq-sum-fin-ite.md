# Extending a sum over 0, …, c − 1 by zeros to 0, …, n − 1

Let $M$ be an additive commutative monoid, let $f \colon \mathbb{N} \to M$, and let $c \le n$ be natural numbers. Then

$$\sum_{k=0}^{c-1} f(k) = \sum_{b=0}^{n-1} \begin{cases} f(b) & \text{if } b < c, \\ 0 & \text{otherwise,} \end{cases}$$

where the right side is a sum over the elements $b$ of $\{0, 1, \dots, n-1\}$ (the type $\mathrm{Fin}\, n$).
