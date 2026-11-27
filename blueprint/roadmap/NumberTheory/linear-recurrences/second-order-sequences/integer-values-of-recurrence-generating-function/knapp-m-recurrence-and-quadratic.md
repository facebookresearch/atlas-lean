# Recurrence and quadratic relation for the quantity $M(a, b, p, q)$

For integers $a, b, p, q$ put

$$M(a, b, p, q) = \frac{(2p + q)\big((b - a)p + aq\big)}{q^2 - pq - p^2} - a + b,$$

a rational number; the denominator vanishes only for $(p, q) = (0, 0)$, where the quotient is read as $0$.

Let $a$ and $b$ be integers and $(p, q) \ne (0, 0)$ a pair of integers. Then

$$M(a, b, p + q, p + 2q) = -3M(a, b, q, p + q) - M(a, b, p, q)$$

and

$$M(a, b, p, q)^2 + 3M(a, b, p, q)\,M(a, b, q, p + q) + M(a, b, q, p + q)^2 = a^2 + ab - b^2.$$

The source also assumes $q$, $p + q$ and $p + 2q$ nonzero; the statement holds without these conditions. Since $M(a, b, p, q) = \frac{bp^2 + bq^2 - ap^2 + 2apq}{q^2 - pq - p^2}$, these identities are the case of the recurrence $A_{n+1} = A_n + A_{n-1}$ of the [relations between values of $M$ at neighbouring pairs](second-order-mvalue-relations.md), applied to the pair $(q, p + q)$.

## Sources

- Michael P. Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Lemma 11.
