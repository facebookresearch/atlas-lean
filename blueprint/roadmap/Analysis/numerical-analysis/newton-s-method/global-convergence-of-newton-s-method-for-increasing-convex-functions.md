# Global convergence of Newton's method for increasing convex functions

Let $f : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable with $f'(x) > 0$ and $f''(x) > 0$ for every $x$, and suppose that $f$ has a zero $r$. Then $r$ is the only zero of $f$, and for every starting point $x_0 \in \mathbb{R}$ the Newton iterates

$$x_{n+1} = x_n - \frac{f(x_n)}{f'(x_n)}$$

converge to $r$. Moreover $x_n \ge r$ for every $n \ge 1$, and the sequence $(x_n)_{n \ge 1}$ is nonincreasing.

By Taylor's theorem $x_{n+1} - r = \frac{f''(\xi_n)}{2 f'(x_n)} (x_n - r)^2 \ge 0$, so after one step the iterates lie to the right of $r$, where $f > 0$ makes each step move left; the limit of the decreasing bounded sequence is a zero of $f$.

## Sources

- D. Levy, *Introduction to Numerical Analysis*, lecture notes, Department of Mathematics, University of Maryland, version of 4 January 2021, Section 2.4, Theorem 2.8 and its proof, which uses $f'(x) > 0$ and $f''(x) > 0$ for every $x$ as the meaning of "monotonically increasing, convex", together with the error relation (2.12)–(2.14). <https://www.math.umd.edu/~dlevy/resources/notes.pdf>
