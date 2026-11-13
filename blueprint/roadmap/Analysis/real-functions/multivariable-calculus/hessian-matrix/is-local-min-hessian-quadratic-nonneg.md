# Second-derivative test, necessary condition

Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice
continuously differentiable and let $x$ be a local minimum of $f$. Then the Hessian quadratic
form of $f$ at $x$ is nonnegative: writing $H$ for the Hessian matrix of $f$ at $x$, every
$v \in \mathbb{R}^n$ satisfies $\sum_{i, j} v_i H_{ij} v_j \ge 0$.

Proof: Restrict the function to the affine line through $x$ in direction $v$, apply the necessary
direction of the one-variable second derivative test, then expand the second Fréchet derivative in
the standard basis. The one-variable step argues by contradiction as in the proof of the
second-derivative test in Wikipedia's “Derivative test”: a negative second derivative makes the
first derivative negative just right of the critical point, so the function decreases there.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
