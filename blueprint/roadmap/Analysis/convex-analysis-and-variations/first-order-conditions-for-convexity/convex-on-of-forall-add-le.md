# Supporting affine minorants imply convexity

Let $E$ be a real normed space, let $s \subseteq E$ be convex, and let $f \colon E \to \mathbb{R}$. Suppose that for every $a \in s$ there is a continuous linear functional $g_a$ on $E$ with $f(a) + g_a(x - a) \le f(x)$ for all $x \in s$. Then $f$ is convex on $s$.

Proof: for $z = \alpha x + \beta y$ with $\alpha, \beta \ge 0$, $\alpha + \beta = 1$, add $\alpha$ times the inequality at $(z, x)$ and $\beta$ times the inequality at $(z, y)$; the linear terms cancel since $\alpha(x - z) + \beta(y - z) = 0$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §3.1.3 (the converse half of the first-order condition).
