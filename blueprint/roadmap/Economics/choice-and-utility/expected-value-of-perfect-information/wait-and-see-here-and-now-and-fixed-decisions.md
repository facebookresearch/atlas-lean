# Wait-and-see, here-and-now and fixed decisions

Let $X$ be a finite nonempty set of decisions, used in every comparison, and let a scenario $S$ take finitely many values $s$ in $\mathbb{R}^d$ with probabilities $p_s \ge 0$, $\sum_s p_s = 1$, and mean $\bar s = E[S] = \sum_s p_ss$. Let $C : X \times \mathbb{R}^d \to \mathbb{R}$ be a real cost. Then $E[\min_x C(x, S)] \le \min_x E[C(x, S)] \le E[C(\hat x, S)]$ for every $\hat x \in X$, since $\min_x C(x, s) \le C(x', s)$ for every $x'$ and $s$. The first gap is the expected value of perfect information; when $\hat x$ minimizes $x \mapsto C(x, \bar s)$ over $X$ (an expected-value decision), the second gap $E[C(\hat x, S)] - \min_x E[C(x, S)]$ is the value of the stochastic solution. Both are nonnegative. Scenario-dependent feasible sets are not covered, and for maximization the inequalities reverse.

## Sources

- J. R. Birge and F. Louveaux, *Introduction to Stochastic Programming*, Springer, Chapter 4 (The Value of Information and the Stochastic Solution), publisher preview, §4.1, equations (1.2)–(1.3), <https://page-one.springer.com/pdf/preview/10.1007/0-387-22618-4_4>. The source states a special case or part of the statement; the rest is derived on this page.
