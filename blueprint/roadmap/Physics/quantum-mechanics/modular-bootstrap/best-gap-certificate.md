# Best gap certificate in the Virasoro functional class

For $c\ge40$, with $c'=c-1$ and $a=c'/12$, let

$$
T_V(c)=\inf\{T:\text{some }g\in\overline{\mathcal A}\text{ is feasible at }T\},
\qquad \Delta_1^{\mathrm{best}}(c)=T_V(c)+a.
$$

Use $+\infty$ for the infimum of an empty feasible set. Feasibility means **strictly positive** vacuum action and a nonnegative tail, not the weak version. This is the best certificate in the specified class, not an optimum over actual conformal field theories. The infimum need not be reached. The paper does not identify it with the infimum restricted to weak feasibility or with the infinite-order limit of the truncated derivative bounds.

## Depends on

- [Functional class and feasibility](functional-class.md)

## Comparison with finite derivative orders

For $P\ge1$, let $t_1^{(P)}(c)$ be the infimum of $t_1(g)$ over strictly feasible functions of the form $e^{-2\pi t}p(t)$, where $p$ lies in the span of $L_{2k-1}(4\pi t)$ for $1\le k\le P$ and $L_j$ is the ordinary Laguerre polynomial. Take the empty infimum to be $+\infty$. These functionals lie in $\overline{\mathcal A}$ by Lemma 2.6. Thus $T_V(c)\le t_1^{(P)}(c)$ for each $P$, and the nonincreasing limit $\Delta_1^{(\infty)}(c)=\lim_{P\to\infty}(a+t_1^{(P)}(c))$ satisfies $\Delta_1^{\mathrm{best}}(c)\le\Delta_1^{(\infty)}(c)$. Equality is not established. This comparison is not part of the definition of $T_V$.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [(2.6) and the finite-order optima, p. 9](https://hexagonmath.org/pdf/2611.00174v1#page=9).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Lemma 2.6 and (2.20), p. 14](https://hexagonmath.org/pdf/2611.00174v1#page=14).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [scope of “best,” p. 15](https://hexagonmath.org/pdf/2611.00174v1#page=15).
