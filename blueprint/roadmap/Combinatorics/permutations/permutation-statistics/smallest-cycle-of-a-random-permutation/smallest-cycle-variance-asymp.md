# Variance of the smallest cycle length

Let $\omega$ be a real function with
$\omega(x) = 1/x$ for $1 \le x \le 2$ and $x\,\omega(x) = 1 + \int_1^{x-1} \omega(t)\,dt$ for
$x \ge 2$, and for $n \ge 1$ let $X_n$ be the length of the smallest cycle of a uniformly random
permutation of $\{1, \dots, n\}$. There are real constants $\varepsilon > 0$ and $C$ such that for
every $n \ge 1$

$$\left| \operatorname{Var}(X_n) - 2n \int_1^\infty \frac{\omega(x)}{x^2}\,dx \right|
\le C\, n \cdot n^{-\varepsilon}.$$

## Sources

- Claude Gravel and Daniel Panario, *Evaluating the Generalized Buchstab Function and Revisiting the Variance of the Distribution of the Smallest Components of Combinatorial Objects*, INTEGERS 24 (2024), Article A7, Theorem 2.
