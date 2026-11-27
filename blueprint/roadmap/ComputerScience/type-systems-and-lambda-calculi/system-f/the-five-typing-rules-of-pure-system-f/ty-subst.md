# Type substitution preserves typing

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $t \in \mathrm{Tm}_{n,m}$ a term and $A \in \mathrm{Ty}_n$ a type with $\Gamma \vdash t : A$ ([typing](typing.md)). For every type substitution $\sigma$ from $n$ to $k$ type variables, $\Gamma[\sigma] \vdash t[\sigma] : A[\sigma]$, where $\Gamma[\sigma]$ applies the [type substitution](../scoped-pure-system-f/subst.md) to every type of $\Gamma$ and $t[\sigma]$ is the [type substitution in the term](../scoped-pure-system-f/ty-subst.md).
