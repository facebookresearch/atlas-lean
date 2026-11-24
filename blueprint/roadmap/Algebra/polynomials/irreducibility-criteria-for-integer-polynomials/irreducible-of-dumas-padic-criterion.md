# Dumas irreducibility criterion

Let $p$ be a prime, write $v_p$ for the $p$-adic
valuation on $\mathbb{Q}$, and let $f = a_0 + a_1 x + \dots + a_n x^n \in \mathbb{Z}[x]$ have
degree $n \ge 1$, with $a_0 \ne 0$ and $a_n \ne 0$. Suppose that no integer $k > 1$ dividing $n$
divides $v_p(a_0) - v_p(a_n)$, that is, $\gcd(v_p(a_0) - v_p(a_n), n) = 1$, and that for every
$0 \le i \le n$ with $a_i \ne 0$,
$n \, v_p(a_i) \ge (n - i) \, v_p(a_0) + i \, v_p(a_n)$.
Then $f$ is irreducible as a polynomial in $\mathbb{Q}[x]$.

Geometrically, the hypotheses say that the Newton polygon of $f$ with respect to $p$ is the single
segment from $(0, v_p(a_0))$ to $(n, v_p(a_n))$ and has no lattice points other than its
endpoints. Zero coefficients contribute no points to the Newton polygon, so the inequality is
required only for nonzero $a_i$.

## Sources

- Randell Heyman, *On the Number of Polynomials of Bounded Height that Satisfy the Dumas Criterion*, Journal of Integer Sequences 17 (2014), Article 14.2.4, Dumas criterion statement, lines 96–102, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Heyman/heyman2.tex>. Exact algebraic form: Martin Juras, arXiv:1505.07633v1, lines 67–100.
