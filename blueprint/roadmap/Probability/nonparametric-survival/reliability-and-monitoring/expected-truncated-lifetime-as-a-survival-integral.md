# Expected truncated lifetime as a survival integral

Let $L$ be an almost surely nonnegative real-valued random variable, and let $T\ge 0$ be a finite horizon. Then

$$E[\min(L,T)] = \int_0^T P(L>t)\,dt.$$

The uncapped mean is $E[L]=\int_0^\infty P(L>t)\,dt$, where both sides are extended nonnegative integrals and may be infinite. No density assumption is needed.

Proof. Almost surely, $\min(L,T)=\int_0^T \mathbf 1\{L>t\}\,dt$. Taking expectations and exchanging integrals by Tonelli's theorem gives the first formula. The same argument over $t>0$ gives the uncapped formula. The strict inequality in the survival event also applies when the law of $L$ has atoms.

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, 2nd rev. ed., American Mathematical Society, 1997, Section 6.3, Exercise 13, <https://math.dartmouth.edu/~prob/prob/prob.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
