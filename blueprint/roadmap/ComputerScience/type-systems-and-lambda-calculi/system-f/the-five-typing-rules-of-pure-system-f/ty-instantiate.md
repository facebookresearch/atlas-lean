# Instantiating a type binder preserves typing

Let $\Gamma$ be a term context with $m$ term variables over $n$ type variables, $b \in \mathrm{Tm}_{n+1,m}$ and $C \in \mathrm{Ty}_{n+1}$ with $\Gamma^{\uparrow} \vdash b : C$ ([typing](typing.md), $\Gamma^{\uparrow}$ the weakened context). Then for every type $A \in \mathrm{Ty}_n$, $\Gamma \vdash b[A] : C[A]$, where $b[A]$ is the [type substitution](../scoped-pure-system-f/ty-subst.md) of $b$ sending $0$ to $A$ and $i + 1$ to $\alpha_i$, and $C[A]$ the [instantiation](../scoped-pure-system-f/instantiate.md) of $C$.
