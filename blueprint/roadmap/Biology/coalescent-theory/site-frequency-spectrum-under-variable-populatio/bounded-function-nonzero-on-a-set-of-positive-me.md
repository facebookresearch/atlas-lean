# A bounded function whose Laplace transform vanishes at every binomial coefficient

There is a measurable function $g$ on $[0, \infty)$ with $\lvert g \rvert \le 1$, nonzero on a set of positive Lebesgue measure, such that

$$\int_0^\infty e^{-\binom{m}{2} s}\, g(s)\, ds = 0 \qquad \text{for every } m \ge 2.$$

Construction: since $\sum_{m \ge 2} 1/\binom{m}{2} = 2 < \infty$, the Müntz–Szász theorem in $L^1[0, 1]$ shows that the span of the monomials $x^{\binom{m}{2}}$, $m \ge 2$, is not dense, so there is a nonzero $h \in L^\infty[0, 1]$ with $\int_0^1 x^{\binom{m}{2}} h(x)\, dx = 0$ for all $m \ge 2$. Then $g(s) = h(e^{-s})\, e^{-s} / \lVert h \rVert_\infty$ works, by the substitution $x = e^{-s}$.

## Proof depends on

- [Change of variables in the Lebesgue integral on the line](../../../Analysis/real-functions/integration/change-of-variables-on-an-interval.md)
- [Müntz–Szász theorem in $L^1[0,1]$: non-density for a convergent reciprocal series](../../../Analysis/approximation-theory/muntz-szasz-non-density-in-l1.md)

## Expansion

1. The Müntz–Szász theorem in $L^1[0, 1]$, an external prerequisite, and the annihilator from the Hahn–Banach theorem.
2. The sum $\sum_{m \ge 2} 1/\binom{m}{2} = 2$.
3. The substitution, which maps the annihilation identity to the Laplace-transform identity.
4. The requirement that $g$ be nonzero on a set of positive measure, which excludes a function nonzero only on a null set, such as the indicator of $\{0\}$.

## Sources

- S. Myers, C. Fefferman and N. Patterson, Can one learn history from the allelic spectrum?, *Theor. Popul. Biol.* 73 (2008), 342–348 (construction).
