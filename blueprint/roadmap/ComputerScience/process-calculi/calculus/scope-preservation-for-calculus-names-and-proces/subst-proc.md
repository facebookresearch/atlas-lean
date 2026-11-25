# Substitution at any cutoff preserves process scoping

Let $n, k \in \mathbb{N}$ with $k \le n$, let $P$ be a process [scoped at depth $n + 1$](closed-at-2.md) and $b$ a [channel name](../the-calculus-syntax-substitution-structural-cong/name.md) [scoped at depth $n$](closed-at.md). Then the [substitution](../the-calculus-syntax-substitution-structural-cong/subst-proc.md) $P[b/k]$ is scoped at depth $n$: substitution removes one ambient binder while preserving the scope of every name, under inputs and restrictions included.
