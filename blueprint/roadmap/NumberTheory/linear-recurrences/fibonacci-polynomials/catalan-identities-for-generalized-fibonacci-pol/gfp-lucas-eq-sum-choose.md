# Explicit formula for Lucas-type generalized Fibonacci polynomials

Let $\alpha$ and $p_0$
be integers with $\alpha p_0 = 2$, let $p_1$ and $g$ be polynomials with integer coefficients, and
put $d = \alpha p_1$. Let $L_n$ be the generalized Fibonacci polynomials defined by $L_0 = p_0$,
$L_1 = p_1$ and $L_{n+2} = d L_{n+1} + g L_n$. Then for every $n \ge 1$, writing
$c_i = \lfloor n \binom{n-i}{i} / (n-i) \rfloor$,

$$\alpha L_n = \sum_{i=0}^{\lfloor n/2 \rfloor} c_i \, d^{n-2i} g^i.$$

The quotient $n \binom{n-i}{i} / (n-i)$ is always an integer, so the floor does not change it;
the source writes the coefficient as $\frac{n}{n-i} \binom{n-i}{i}$ and quotes the formula from
Flórez and Saunders.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Lemma 3.1 (2).
