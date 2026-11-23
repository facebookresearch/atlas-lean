# Instantiating the innermost binder preserves process scoping

Let $n \in \mathbb{N}$, let $P$ be a process [scoped at depth $n + 1$](closed-at-2.md) and $b$ a [channel name](../the-calculus-syntax-substitution-structural-cong/name.md) [scoped at depth $n$](closed-at.md). Then $P[b]$, the [substitution](../the-calculus-syntax-substitution-structural-cong/subst.md) of $b$ for the innermost bound variable of $P$, is scoped at depth $n$.
