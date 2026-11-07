# Catalan identity for Lucas-type generalized Fibonacci polynomials

Let $\alpha$ and $p_0$
be integers with $\alpha p_0 = 2$, let $p_1$ and $g$ be polynomials with integer coefficients, and
put $d = \alpha p_1$. Let $L_n$ be the generalized Fibonacci polynomials defined by $L_0 = p_0$,
$L_1 = p_1$ and $L_{n+2} = d L_{n+1} + g L_n$. Then for every natural number $n$,

$$2^n \alpha L_n = 2 \sum_{i=0}^{\lfloor n/2 \rfloor} \binom{n}{2i} d^{n-2i} (4g + d^2)^i.$$

Dividing both sides by $2$ gives the source's form, with $\alpha 2^{n-1} L_n$ on the left; the
factor $2$ is cleared so that $n = 0$ is included.

## Sources

- Maribel Diaz Noguera, Rigoberto Flórez, José L. Ramírez, and Martha Romero Rojas, *Catalan Identities for Generalized Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article florez11012023, Theorem 3.3 (2) (`fq-2024-florez11012023-thm-3.3`).
