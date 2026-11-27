# Name substitution preserves scoping

Let $n, k \in \mathbb{N}$ with $k \le n$, and let $b$ and $x$ be [channel names](../the-calculus-syntax-substitution-structural-cong/name.md) with $b$ [scoped at depth $n$](closed-at.md) and $x$ scoped at depth $n + 1$. Then the [substitution](../the-calculus-syntax-substitution-structural-cong/subst-name.md) of $b$ for the variable $\#k$ in $x$ is scoped at depth $n$: removing the binder at $k$ preserves scoping when its replacement is scoped in the remaining environment.
