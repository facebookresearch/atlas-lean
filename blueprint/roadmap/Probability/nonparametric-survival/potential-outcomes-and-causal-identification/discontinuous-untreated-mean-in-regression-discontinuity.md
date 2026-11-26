# A discontinuous untreated mean produces a jump with no treatment effect

In the sharp regression-discontinuity design, treatment is $D = \mathbf 1\{X \ge c\}$ and $Y = Y(D)$, where $X$ has a density positive on a neighborhood of $c$. If $x \mapsto E[Y(0) \mid X = x]$ and $x \mapsto E[Y(1) \mid X = x]$ have versions continuous at $c$, then $\lim_{x \downarrow c} E[Y \mid X = x] - \lim_{x \uparrow c} E[Y \mid X = x] = E[Y(1) - Y(0) \mid X = c]$ for those versions. Without continuity of the untreated mean this fails: let $X$ be uniform on $[-1, 1]$, $c = 0$ and $Y(0) = Y(1) = \mathbf 1\{X \ge 0\}$. There is no treatment effect for any unit, yet the observed one-sided limits are $1$ and $0$.

## Sources

- G. W. Imbens and T. Lemieux, "Regression discontinuity designs: a guide to practice", NBER Working Paper 13039, 2007, Assumption 2.1, <https://www.nber.org/papers/w13039>
