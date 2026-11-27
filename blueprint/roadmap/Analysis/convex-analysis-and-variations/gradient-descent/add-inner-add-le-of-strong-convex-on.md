# First-order condition for strong convexity

Let $E$ be a real Hilbert space, let $s \subseteq E$, and let $f \colon E \to \mathbb{R}$ be $m$-strongly convex on $s$, i.e. $f(a x + b y) \le a f(x) + b f(y) - \frac{m}{2} a b \|x - y\|^2$ for $x, y \in s$, $a, b \ge 0$, $a + b = 1$. If $x, y \in s$ and $f$ has gradient $g$ at $x$, then

$$f(x) + \langle g, y - x \rangle + \frac{m}{2} \|y - x\|^2 \le f(y).$$

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.1.2, eq. (9.8).
- Cf. Y. Nesterov, *Introductory Lectures on Convex Optimization: A Basic Course*, Kluwer, 2004, Ch. 2 (strongly convex functions).
