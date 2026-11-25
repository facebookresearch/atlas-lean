# Existence and uniqueness of the adjustment coefficient

Consider claims $X \ge 0$ arriving at Poisson rate $\lambda > 0$ and premium income at rate $c > 0$. Suppose $P(X > 0) > 0$, the moment generating function $M(r) = E[e^{rX}]$ is finite on $[0, r_0]$ for some $r_0 > 0$, the net-profit condition $c > \lambda E[X]$ holds, and the function $h(r) = \lambda (M(r) - 1) - c r$ satisfies $h(r_0) > 0$. Then there is exactly one $R \in (0, r_0)$ with $h(R) = 0$, the adjustment coefficient; moreover $h < 0$ on $(0, R)$ and $h > 0$ on $(R, r_0]$.

Proof. On $[0, r_0]$, $h$ is continuous by dominated convergence with the bound $e^{rX} \le e^{r_0 X}$, and strictly convex because $P(X > 0) > 0$. Since $x \le e^{r_0 x}/r_0$ for $x \ge 0$, $E[X] < \infty$ and the right derivative of $h$ at $0$ is $\lambda E[X] - c < 0$, so $h < 0$ just to the right of $0 = h(0)$. The intermediate value theorem gives a zero in $(0, r_0)$, and a strictly convex function vanishing at $0$ has at most one further zero, which fixes the signs. The positive crossing $h(r_0) > 0$ is what locates the positive root inside the interval where $M$ is known to be finite; for $r_0 \le 0$ the interval $(0, r_0)$ in the conclusion is empty.

## Sources

- R. Kaas, M. Goovaerts, J. Dhaene and M. Denuit, *Modern Actuarial Risk Theory*, Springer; author recap sheet of chapters 1–6, ruin-theory section of the recap, <https://www1feb-uva.nl/ke/act/people/kaas/Recap123456.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
