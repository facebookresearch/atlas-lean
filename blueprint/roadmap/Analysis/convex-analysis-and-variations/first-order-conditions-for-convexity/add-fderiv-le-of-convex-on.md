# First-order condition for convexity

Let $E$ be a real normed space, let $s \subseteq E$, and let $f \colon E \to \mathbb{R}$ be convex on $s$. If $a, x \in s$ and $f$ is Fréchet differentiable at $a$ with derivative $Df(a)$, then

$$f(a) + Df(a)(x - a) \le f(x).$$

That is, the first-order Taylor approximation of $f$ at $a$ is a global underestimator of $f$ on $s$.

Proof: for $0 < t < 1$, convexity gives $t^{-1}\big(f(a + t(x - a)) - f(a)\big) \le f(x) - f(a)$, and the left side tends to $Df(a)(x - a)$ as $t \to 0^+$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §3.1.3, eq. (3.2).
