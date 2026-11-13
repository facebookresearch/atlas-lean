# Witt's formula for the number of Lyndon words of given content

Let $r$ be a natural
number and let $n_0, \dots, n_{r-1}$ be natural numbers with $n = n_0 + \dots + n_{r-1} > 0$.
Order the alphabet $\{0, \dots, r-1\}$ as the natural numbers and order words over it
lexicographically. Then the number of Lyndon words over this alphabet in which each letter $i$
occurs exactly $n_i$ times equals, as a rational number, Witt's multigraded value
$M(n_0, \dots, n_{r-1}) = \frac{1}{n} \sum_{d \mid g} \mu(d) \binom{n/d}{n_0/d, \ldots, n_{r-1}/d}$,
where $g = \gcd(n_0, \dots, n_{r-1})$, the sum runs over the positive divisors $d$ of $g$, and
$\mu$ is the Möbius function.
