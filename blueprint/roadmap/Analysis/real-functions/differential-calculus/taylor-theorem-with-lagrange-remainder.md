# Taylor's theorem with the Lagrange remainder

Let $f : \mathbb{R} \to \mathbb{R}$, let $x_0 \ne x$ be real numbers and $n$ a natural number, let $I$ be the closed interval between $x_0$ and $x$, and suppose that $f$ is $n$ times continuously differentiable on $I$ and that its $n$-th derivative within $I$ is differentiable on the open interval between $x_0$ and $x$. Then there is $x'$ strictly between $x_0$ and $x$ with

$$f(x) - \sum_{j=0}^{n} \frac{f^{(j)}(x_0)}{j!}(x - x_0)^j = \frac{f^{(n+1)}(x')}{(n + 1)!}(x - x_0)^{n+1},$$

where the derivatives are taken within $I$.

## Sources

- Mathlib, `Mathlib/Analysis/Calculus/Taylor.lean`: `taylor_mean_remainder_lagrange`.
- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 5.1, the Taylor expansion (5.2) with a Lagrange remainder, used for the difference quotients. <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
