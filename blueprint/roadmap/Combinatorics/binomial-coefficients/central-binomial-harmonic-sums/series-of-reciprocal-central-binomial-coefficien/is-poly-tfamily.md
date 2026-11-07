# Polynomial family defined by an antiderivative

Let $S$ and $T$ be sequences of real
polynomials indexed by the natural numbers, with terms $S(l)$ and $T(l)$. The pair $(S, T)$
satisfies this predicate when $T(0) = 0$; for every $l \ge 1$ the polynomial $T(l)$ is nonzero
and has degree $l - 1$; and for every $l \ge 1$ and every real $x$ with $0 < x < 4$, the function
$y \mapsto 2\sqrt{y}\,T(l)(y)$ is differentiable at $x$ with derivative

$$\frac{8x^l - S(l)(x)}{\sqrt{x}\,(4 - x)}.$$

The term $T(l)$ stands for the polynomial $T_{l-1}$ of the source, so $T(0) = 0$ encodes the
convention $T_{-1} = 0$, and the derivative condition expresses $T_{l-1}(x)$ as
$\frac{1}{2\sqrt{x}}$ times an antiderivative of the displayed integrand.

## Sources

- canonical name `polynomial T_{l-1}`, concept_id `jis_sem_267c1cca81c8b3a0062a0742`, statement `jis_d5c7f2eca643e293a3405354`, source `jis_source_34b829866c2fa232064ad7c0`.
