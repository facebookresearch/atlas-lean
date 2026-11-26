# Finite sums of convex functions are convex

Let $E$ be a real vector space, let $s \subseteq E$ be convex, and let $(g_i)_{i \in t}$ be a finite family of functions $E \to \mathbb{R}$, each convex on $s$. Then $x \mapsto \sum_{i \in t} g_i(x)$ is convex on $s$; for $t = \emptyset$ it is the constant $0$. Lagrangians, empirical risks and regularized losses are convex by this rule.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §3.2.1 ("Nonnegative weighted sums").
