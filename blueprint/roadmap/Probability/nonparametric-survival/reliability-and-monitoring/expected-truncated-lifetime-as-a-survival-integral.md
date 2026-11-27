# Expected truncated lifetime as a survival integral

Let $\mu$ be a finite measure, let $L$ be an almost everywhere measurable and nonnegative real-valued function, and let $T\ge 0$. Then

$$\int \min(L,T)\,d\mu = \int_0^T \mu(\{L>t\})\,dt.$$

For a probability measure, this gives the expected capped lifetime $E[\min(L,T)]$. It includes $T=0$ and requires no density or absence of atoms.

Proof. Replacing $L$ by a measurable representative does not change either side. Almost everywhere, $\min(L,T)=\int_0^T \mathbf 1\{L>t\}\,dt$. Integrating and exchanging the two integrals by Tonelli's theorem gives the formula.

## Sources

- C. M. Grinstead and J. L. Snell, *Introduction to Probability*, online version dated 4 July 2006, §6.3, Exercise 13 (p. 280), <https://math.dartmouth.edu/~prob/prob/prob.pdf>. The exercise gives the related uncapped expectation identity; the argument above applies the same idea to the capped lifetime.
