# Correctness of memoized rod cutting

Let $\alpha$ be a linearly ordered additive commutative
monoid (that is, $a \le b$ implies $a + c \le b + c$) and let $p = (p_1, \dots, p_n) \in \alpha^n$
be prices, where $p_i$ is the price of a piece of length $i$. The value returned by the memoized
cut-rod procedure on $p$ is the greatest composition revenue over compositions of $n$: it is the
revenue of some composition of $n$, and it is at least the revenue of every composition of $n$.
